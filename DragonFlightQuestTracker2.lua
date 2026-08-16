-- DragonFlightQuestTracker2 Addon for WoW 1.12
-- Requires the ClassicAPI DLL injected into the client:
-- https://github.com/brues-code/ClassicAPI
-- Main frame creation and setup

-- Hard requirement gate: bail out before any frames or events are created
-- if the ClassicAPI DLL is missing or too old.
if not CLASSIC_API_VERSION or CLASSIC_API_VERSION < 10500 then
    DEFAULT_CHAT_FRAME:AddMessage(
        "|cffff2020DragonFlight Quest Tracker 2:|r ClassicAPI not detected (requires version 10500 or later). Addon not loaded.")
    return
end

-- Public namespace + settings: the addon's only intentional global. Created
-- up front so settings are readable everywhere in this file; the /script
-- entry points are attached at the bottom of the file. The future options
-- menu / slash-command layer (todo #11) will read and write DFQT2.settings.
-- Defaults below; persisted values from the DFQT2_Settings SavedVariable are
-- merged over them at PLAYER_LOGIN, after which DFQT2_Settings aliases this
-- table so every change persists automatically. Edited via the options frame
-- (/dfqt, or right-click the tracker header).
DFQT2 = {
    settings = {
        sortCurrentZoneFirst = true, -- Zone priority: sort current-zone quests to top + "**" marker
        showToolTip = false,         -- Quest tooltips on hover (incl. questID + party-member lines)
        showLevel = false,           -- "[level]" prefix on quest titles
        debugQuestEvents = true,     -- Quest-event debug prints in chat
        turnInCelebration = true,    -- Sound + chat reward summary on quest turn-in
        highlightGossipTurnIn = true -- Pulsing glow + sort-to-top for quests ready to hand in at the current NPC
    }
}

-- NOTE: no custom print() override here. The modified Turtle WoW client ships
-- a native print(), and overriding that shared global name fights every other
-- addon on the client (last loader wins) - v1 did this; v2 deliberately doesn't.

-- Global variables to store quest data and frames
local questsByType = {}
local questTypeFrames = {}
local questButtonsByType = {}        -- Track quest buttons for each type
local minimizedSections = {}         -- Track which sections are minimized
local questObjectiveStates = {}      -- Track objective completion states
local newQuestsToAnimate = nil       -- questIDs queued by QUEST_ACCEPTED, awaiting section-expand/animation
local questsToAnimateOnComplete = {} -- Track quests that just completed and need animation
local objectivesJustCompleted = {}   -- [questID][objIndex] = true for objectives completed this scan (strikethrough sweep)
local previousQuestTypes = {}        -- Track which quest types had quests in previous scan
-- (showToolTip / showLevel / debugQuestEvents migrated to DFQT2.settings)
local allSectionsHidden = false      -- Track if all sections are hidden
local initialLoad = true             -- Track if this is the first quest scan
local questScanInProgress = false    -- Guard against re-entrant calls from QUEST_LOG_UPDATE
local questScanPending = false       -- Pending flag: set by QUEST_LOG_UPDATE, consumed once per frame in OnUpdate
local questScanDelayUntil = nil      -- Postpone the pending scan until this GetTime() (lets removal fade-outs play)
local zoneChangeDebugPending = false -- Set by ZONE_CHANGED_NEW_AREA (when debug is on): next scan reports in-zone quests
local gossipReadyQuestIDs = {}       -- [questID] = true while that quest is ready to hand in at the currently-open NPC
local questTimerTotals = {}          -- [questID] = largest remaining seen (approximates the authored duration for the bar fraction)
local timerBarsByQuestID = {}        -- Visible timer bars, reset on every UI rebuild
local timerTicker = nil              -- C_Timer.NewTicker handle, alive only while a timer bar is visible
local firstFullScan = true           -- Track if this is the first full (non-deferred) scan
local questTypeOrder = { "normal", "elite", "dungeon", "raid", "pvp" }
local questTypeLabels = {
    ["normal"] = "Quests",
    ["elite"] = "Elite",
    ["dungeon"] = "Dungeon",
    ["raid"] = "Raid",
    ["pvp"] = "PvP"
}
local pendingAbandonQuestIndex = nil -- Store quest index for abandon confirmation
local questScrollOffsets = {}        -- Track scroll position for each quest type (0 = top)
local progressedQuestID = nil        -- questID that had objective progress this scan
local maxQuestsShown = {
    normal = 5,
    elite = 3,
    dungeon = 2,
    raid = 2,
    pvp = 3
}
local maxQuestsShownExpanded = 7 -- limit for secondary types when all others are minimised

-- Forward declarations: every addon function is file-local - nothing external
-- (engine, XML, other addons) ever calls them by name, so none need to be
-- global. Declared up front because Lua 5.0 resolves names at closure-creation
-- time and the definitions below reference each other out of textual order.
-- A definition written as "function Name(...)" below assigns into these locals.
-- The addon's ONLY intentional global is the DFQT2 namespace table at the
-- bottom of this file (engine-registered frame names aside).
local GetEffectiveMaxShown
local BuildQuestTrackerUI
local CreateObjectiveTracker
local CheckObjectiveCompletion
local GetPlayerQuests
local CreateQuestButtons
local HideQuestButtons
local ShowQuestButtons
local HideAllSections
local ShowAllSections
local DoAnimateFrame
local FadeOutFrame
local StrikeThroughObjective
local FindQuestLogIndexByQuestID
local FindQuestButtonByQuestID
local ShowPOIFrame
local ShowOptionsFrame

-- Returns the effective max quests to show for questType.
-- Secondary types (elite/dungeon/raid/pvp) get maxQuestsShownExpanded when every
-- other section that has quests is currently minimised.
function GetEffectiveMaxShown(questType)
    local base = maxQuestsShown[questType] or 10
    -- Only secondary types benefit from the expanded limit
    if questType == "normal" then
        return base
    end
    -- Check whether every other section with quests is minimised
    for _, otherType in ipairs(questTypeOrder) do
        if otherType ~= questType then
            local hasQuests = questsByType[otherType] and table.getn(questsByType[otherType]) > 0
            if hasQuests and not minimizedSections[otherType] then
                return base -- At least one other section is expanded
            end
        end
    end
    return maxQuestsShownExpanded
end

-- Quest source-item support (ClassicAPI srcItemID) -------------------------

local questSrcItemCache = {} -- [questID] = srcItemID (0 = quest has no source item)

--[[
    Returns the srcItemID for a quest (0 when none, or when not yet known).

    Pure cache read: on a GetQuestDetails cache miss the quest data is
    requested from the server and 0 is returned for now; the
    QUEST_DATA_LOAD_RESULT handler fills questSrcItemCache and triggers a
    tracker rebuild, so the item button appears once the data lands.
]]
local function GetQuestSrcItemID(questID)
    if not questID then
        return 0
    end
    local cached = questSrcItemCache[questID]
    if cached then
        return cached
    end
    local details = C_QuestLog.GetQuestDetails(questID)
    if not details then
        C_QuestLog.RequestLoadQuestByID(questID)
        return 0
    end
    questSrcItemCache[questID] = details.srcItemID or 0
    return questSrcItemCache[questID]
end

-- Finds the first bag slot holding itemID (ClassicAPI C_Container).
-- Returns bag, slot when found; nil when the item isn't in the bags.
local function FindBagItemByID(itemID)
    for bag = 0, 4 do
        local numSlots = GetContainerNumSlots(bag)
        if numSlots and numSlots > 0 then
            for slot = 1, numSlots do
                if C_Container.GetContainerItemID(bag, slot) == itemID then
                    return bag, slot
                end
            end
        end
    end
    return nil
end

-- Timed quest support (native 1.12 quest timers) ---------------------------

-- Formats remaining seconds as "m:ss" (or "h:mm:ss" above an hour)
local function FormatTimeRemaining(seconds)
    seconds = math.floor(seconds)
    if seconds < 0 then
        seconds = 0
    end
    if seconds >= 3600 then
        return string.format("%d:%02d:%02d",
            math.floor(seconds / 3600), math.floor(math.mod(seconds, 3600) / 60), math.mod(seconds, 60))
    end
    return string.format("%d:%02d", math.floor(seconds / 60), math.mod(seconds, 60))
end

--[[
    Returns a table of [questID] = remainingSeconds for all active quest
    timers, or nil when there are none.

    Native 1.12 plumbing: GetQuestTimers() returns one remaining-seconds
    value per active timer; GetQuestIndexForTimer(i) maps timer i to its
    quest-log index (the default QuestTimerFrame uses the same pair).
    ClassicAPI's GetQuestIDForLogIndex converts that to a stable questID.
]]
local function GetActiveQuestTimers()
    local result = nil
    local timers = { GetQuestTimers() }
    for i = 1, table.getn(timers) do
        local questIndex = GetQuestIndexForTimer(i)
        if questIndex then
            local questID = C_QuestLog.GetQuestIDForLogIndex(questIndex)
            if questID and questID > 0 then
                if not result then
                    result = {}
                end
                result[questID] = timers[i]
            end
        end
    end
    return result
end

-- Once-per-second refresh of all visible timer bars (runs via C_Timer per
-- the OnUpdate-vs-C_Timer policy: low-frequency periodic work). Cancels its
-- own ticker when no bar is visible anymore.
local function UpdateQuestTimerBars()
    local active = GetActiveQuestTimers()
    local anyVisible = false

    for questID, bar in pairs(timerBarsByQuestID) do
        if bar:IsVisible() then
            anyVisible = true
            local remaining = active and active[questID]
            if remaining then
                bar:SetValue(remaining)
                bar.timeText:SetText(FormatTimeRemaining(remaining))
                -- Urgency colors: gold, orange under 60s, red under 30s
                if remaining <= 30 then
                    bar:SetStatusBarColor(1, 0.15, 0.15)
                elseif remaining <= 60 then
                    bar:SetStatusBarColor(1, 0.5, 0)
                end
            else
                -- Timer ended between rebuilds (QUEST_TIMER_FINISHED will
                -- trigger the rebuild that removes this bar)
                bar:SetValue(0)
                bar.timeText:SetText("0:00")
            end
        end
    end

    if not anyVisible and timerTicker then
        timerTicker:Cancel()
        timerTicker = nil
    end
end

-- Starts the shared 1-second ticker if it isn't already running
local function EnsureTimerTicker()
    if not timerTicker then
        timerTicker = C_Timer.NewTicker(1, UpdateQuestTimerBars)
    end
end

-- Define the abandon quest confirmation popup
StaticPopupDialogs["DFQT_ABANDON_QUEST"] = {
    text = "Abandon: \"%s\"?",
    button1 = "Yes",
    button2 = "No",
    OnAccept = function()
        if pendingAbandonQuestIndex then
            SelectQuestLogEntry(pendingAbandonQuestIndex)
            AbandonQuest()
            pendingAbandonQuestIndex = nil -- Clear after use
        end
    end,
    OnCancel = function()
        -- Clear the pending index if user cancels
        pendingAbandonQuestIndex = nil
    end,
    timeout = 0,
    whileDead = 1,
    hideOnEscape = 1
}

-- reverse lookup cache for optimation in CreateObjectiveTracker
local questLabelToType = {}
for key, label in pairs(questTypeLabels) do
    questLabelToType[label] = key
end

-- Create the main frame
QuestTrackerFrame = CreateFrame("Frame", "QuestTrackerFrame", UIParent)

-- Set frame properties
QuestTrackerFrame:SetWidth(300)
QuestTrackerFrame:SetHeight(38) -- was 32 but looked too narrow vs retail
-- Default position will be set after PLAYER_LOGIN when we check for saved position
-- Temporarily set a position (will be overridden)
QuestTrackerFrame:SetPoint("CENTER", UIParent, "CENTER", 0, 0)

-- Set the background texture
local bgTexture = QuestTrackerFrame:CreateTexture(nil, "BACKGROUND")
bgTexture:SetAllPoints(QuestTrackerFrame)
bgTexture:SetTexture("Interface\\AddOns\\DragonFlightQuestTracker2\\textures\\df_main_header.blp")

-- Make the frame moveable
QuestTrackerFrame:SetMovable(true)
QuestTrackerFrame:EnableMouse(true)
QuestTrackerFrame:RegisterForDrag("LeftButton")
QuestTrackerFrame:SetClampedToScreen(true)
QuestTrackerFrame:SetScript("OnDragStart", function()
    this:StartMoving()
end)
QuestTrackerFrame:SetScript("OnDragStop", function()
    this:StopMovingOrSizing()

    -- Save the frame position to SavedVariables
    local point, relativeTo, relativePoint, xOfs, yOfs = this:GetPoint()
    DFQT_FramePosition = {
        point = point,
        relativePoint = relativePoint,
        xOfs = xOfs,
        yOfs = yOfs
    }
    --print("DragonFlight Quest Tracker - Position saved")
end)

-- Right-click on the "All Objectives" header: context menu with an Options
-- entry (left-click drag still moves the frame; drag is LeftButton-only)
QuestTrackerFrame:SetScript("OnMouseUp", function()
    if arg1 == "RightButton" then
        if not QuestTrackerDropDown then
            CreateFrame("Frame", "QuestTrackerDropDown", UIParent, "UIDropDownMenuTemplate")
        end

        UIDropDownMenu_Initialize(QuestTrackerDropDown, function()
            local info = {}
            info.text = "DragonFlight Quest Tracker 2"
            info.isTitle = 1
            info.notCheckable = 1
            UIDropDownMenu_AddButton(info)

            info = {}
            info.text = "Options..."
            info.notCheckable = 1
            info.func = function()
                ShowOptionsFrame()
            end
            UIDropDownMenu_AddButton(info)

            info = {}
            info.text = "Rescan Tracker"
            info.notCheckable = 1
            info.func = function()
                questScanPending = true
            end
            UIDropDownMenu_AddButton(info)
        end, "MENU")

        ToggleDropDownMenu(1, nil, QuestTrackerDropDown, "cursor", 0, 0)
    end
end)

-- Create the "All Objectives" text on the left side
local objectivesText = QuestTrackerFrame:CreateFontString("QuestTrackerObjectivesText", "OVERLAY", "GameFontNormalLarge")
objectivesText:SetPoint("LEFT", QuestTrackerFrame, "LEFT", 25, 3)
objectivesText:SetText("All Objectives")

-- Create the minimize button on the right side
local minimizeButton = CreateFrame("Button", "QuestTrackerMinimizeButton", QuestTrackerFrame)
minimizeButton:SetWidth(20)
minimizeButton:SetHeight(20)
minimizeButton:SetPoint("RIGHT", QuestTrackerFrame, "RIGHT", -10, 0)

-- Set button textures
minimizeButton:SetNormalTexture("Interface\\Addons\\DragonFlightQuestTracker2\\textures\\main_header_minimise_all.blp")
minimizeButton:SetPushedTexture(
    "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\main_header_minimise_all_pushed.blp")
minimizeButton:SetHighlightTexture(
    "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\main_header_minimise_all_highlight.blp")
local highlightTexture = minimizeButton:GetHighlightTexture()
highlightTexture:SetVertexColor(1, 1, 1, 0.3)

-- Functions Below

-- Add click handler
minimizeButton:SetScript("OnClick", function()
    if allSectionsHidden then
        ShowAllSections()
        minimizeButton:SetNormalTexture(
            "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\main_header_minimise_all.blp")
        PlaySoundFile("Sound\\interface\\uChatScrollButton.wav")
    else
        HideAllSections()
        minimizeButton:SetNormalTexture(
            "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\main_header_maximise_all.blp")
        minimizeButton:SetPushedTexture(
            "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\main_header_maximise_all_pushed.blp")
        PlaySoundFile("Sound\\interface\\uChatScrollButton.wav")
    end
end)

--[[
    Builds the complete quest tracker UI from current quest data

    Called from:
    - GetPlayerQuests() after quest data is processed
    - HideQuestButtons() after marking a section as minimized
    - ShowQuestButtons() after marking a section as not minimized
    - ShowAllSections() after clearing the global hide flag

    Process:
    1. Destroys all existing frames and buttons (full rebuild)
    2. Returns early if all sections are globally hidden
    3. Iterates through quest types in defined order
    4. Creates section header for each type that has quests
    5. Creates quest buttons if the section is not minimized
    6. Chains frames vertically by anchoring to previous frame
]]
function BuildQuestTrackerUI()
    -- Clear existing quest type frames (section headers)
    for questType, frame in pairs(questTypeFrames) do
        if frame then
            frame:Hide()
            frame = nil
        end
    end
    questTypeFrames = {}

    -- Clear existing quest buttons
    for questType, buttons in pairs(questButtonsByType) do
        if buttons then
            for _, button in ipairs(buttons) do
                if button then
                    -- Hide associated info button if it exists
                    if button.infoButton then
                        button.infoButton:Hide()
                        button.infoButton = nil
                    end
                    -- Hide associated quest item button if it exists
                    if button.itemButton then
                        button.itemButton:Hide()
                        button.itemButton = nil
                    end
                    button:Hide()
                    button = nil
                end
            end
        end
    end
    -- Clear existing quest type frames (section headers)
    for questType, frame in pairs(questTypeFrames) do
        if frame then
            -- Clean up scroll buttons if they exist
            if frame.scrollUpButton then
                frame.scrollUpButton:Hide()
                frame.scrollUpButton = nil
            end
            if frame.scrollDownButton then
                frame.scrollDownButton:Hide()
                frame.scrollDownButton = nil
            end
            frame:Hide()
            frame = nil
        end
    end

    questButtonsByType = {}
    timerBarsByQuestID = {} -- Bars die with their buttons; the ticker repopulates from the new build

    -- If all sections hidden via main minimize button, exit early
    if allSectionsHidden then
        return
    end

    -- Build frames for each quest type that has quests, maintaining defined order
    local lastFrame = QuestTrackerFrame -- Start anchoring below main header
    local yOffset = -10                 -- Vertical spacing between frames

    for _, questType in ipairs(questTypeOrder) do
        -- Only create section if this type has quests
        if questsByType[questType] and table.getn(questsByType[questType]) > 0 then
            -- Create the section header frame
            local typeFrame = CreateObjectiveTracker(questTypeLabels[questType], lastFrame, yOffset)
            questTypeFrames[questType] = typeFrame

            -- Only create quest buttons if this section is not minimized
            local lastQuestButton = nil
            if not minimizedSections[questType] then
                lastQuestButton = CreateQuestButtons(questType, typeFrame, questsByType[questType])
            end

            -- Update anchor point for next section (chain vertically)
            if lastQuestButton then
                -- Anchor to last quest button if buttons were created
                lastFrame = lastQuestButton
            else
                -- Anchor to section header if section is minimized
                lastFrame = typeFrame
            end
            yOffset = -10
        end
    end
end

--[[
    Creates a quest type section header frame with minimize/maximize button

    Called from:
    - BuildQuestTrackerUI() for each quest type that has quests

    Parameters:
    - type: Display label for the quest type (e.g., "Quests", "Elite", "Dungeon")
    - parentFrame: Frame to anchor this section header below
    - yOffset: Vertical offset from the parent frame (typically -10)

    Returns:
    - The created child frame (section header)

    Features:
    - Creates 300x32 frame with custom background texture
    - Displays section label text on left side
    - Creates minimize/maximize button on right side
    - Button texture reflects current minimized state
    - Button click toggles section visibility
]]
function CreateObjectiveTracker(type, parentFrame, yOffset)
    local lType = type
    local lParentFrame = parentFrame
    local lYOffset = yOffset

    -- Create the child frame for this quest type section header
    local childFrame = CreateFrame("Frame", "DFQT_Section_" .. lType, QuestTrackerFrame)
    childFrame.isSectionHeader = true
    childFrame:SetWidth(300)
    childFrame:SetHeight(32)
    childFrame:SetPoint("TOP", lParentFrame, "BOTTOM", 0, lYOffset)


    -- Apply custom background texture
    local bgTexture = childFrame:CreateTexture(nil, "BACKGROUND")
    bgTexture:SetAllPoints(childFrame)
    bgTexture:SetTexture("Interface\\AddOns\\DragonFlightQuestTracker2\\textures\\df_section_header.blp")


    -- Create section label text (e.g., "Quests [3]", "Elite [1]")
    local typeText = childFrame:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
    typeText:SetPoint("LEFT", childFrame, "LEFT", 25, 0)

    -- Create minimize/maximize toggle button
    local minimizeButton = CreateFrame("Button", nil, childFrame)
    minimizeButton:SetWidth(16)
    minimizeButton:SetHeight(16)
    minimizeButton:SetPoint("RIGHT", childFrame, "RIGHT", -10, 0)

    -- Use cached reverse lookup to find quest type key from display label
    local questTypeKey = questLabelToType[lType]
    local questCount = questTypeKey and questsByType[questTypeKey] and table.getn(questsByType[questTypeKey]) or 0
    typeText:SetText(lType .. " (" .. questCount .. ")")

    -- Set button textures based on current minimized state
    if questTypeKey and minimizedSections[questTypeKey] then
        -- Section is minimized, show maximize button
        minimizeButton:SetNormalTexture(
            "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_maximise.blp")
        minimizeButton:SetPushedTexture(
            "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_maximise_pushed.blp")
    else
        -- Section is expanded, show minimize button
        minimizeButton:SetNormalTexture(
            "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_minimise.blp")
        minimizeButton:SetPushedTexture(
            "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_minimise_pushed.blp")
    end
    minimizeButton:SetHighlightTexture(
        "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_highlight.blp")

    -- Section minimize/maximize button click handler
    minimizeButton:SetScript("OnClick", function()
        --DoAnimateFrame(childFrame) -- DEBUG CALL - Commented out
        -- Reuse the cached questTypeKey from outer scope
        if questTypeKey then
            if minimizedSections[questTypeKey] then
                -- Currently minimized, so expand section
                ShowQuestButtons(questTypeKey)
                minimizeButton:SetNormalTexture(
                    "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_minimise.blp")
                minimizeButton:SetPushedTexture(
                    "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_minimise_pushed.blp")
                PlaySoundFile("Sound\\interface\\uChatScrollButton.wav")
            else
                -- Currently expanded, so minimize section
                HideQuestButtons(questTypeKey)
                minimizeButton:SetNormalTexture(
                    "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_maximise.blp")
                minimizeButton:SetPushedTexture(
                    "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\section_header_maximise_pushed.blp")
                PlaySoundFile("Sound\\interface\\uChatScrollButton.wav")
            end
        end
    end)

    -- Add scroll buttons if this quest type needs scrolling
    if questTypeKey and not minimizedSections[questTypeKey] then -- Added minimized check
        local totalQuests = questsByType[questTypeKey] and table.getn(questsByType[questTypeKey]) or 0
        local maxShown = GetEffectiveMaxShown(questTypeKey)

        if totalQuests > maxShown then
            -- Create scroll up button
            local scrollUpButton = CreateFrame("Button", nil, childFrame)
            scrollUpButton:SetWidth(24)
            scrollUpButton:SetHeight(24)
            scrollUpButton:SetPoint("TOPRIGHT", childFrame, "BOTTOMRIGHT", -7, -5)

            scrollUpButton:SetNormalTexture("Interface\\MainMenuBar\\UI-MainMenu-ScrollUpButton-Up")
            scrollUpButton:SetPushedTexture("Interface\\MainMenuBar\\UI-MainMenu-ScrollUpButton-Down")
            scrollUpButton:SetDisabledTexture("Interface\\Buttons\\UI-ScrollBar-ScrollUpButton-Disabled")
            scrollUpButton:SetHighlightTexture("Interface\\MainMenuBar\\UI-MainMenu-ScrollUpButton-Highlight")
            local highlightUp = scrollUpButton:GetHighlightTexture()
            highlightUp:SetBlendMode("ADD")

            -- Create scroll down button
            local scrollDownButton = CreateFrame("Button", nil, childFrame)
            scrollDownButton:SetWidth(24)
            scrollDownButton:SetHeight(24)
            scrollDownButton:SetPoint("TOP", scrollUpButton, "BOTTOM", 0, -2)

            scrollDownButton:SetNormalTexture("Interface\\MainMenuBar\\UI-MainMenu-ScrollDownButton-Up")
            scrollDownButton:SetPushedTexture("Interface\\MainMenuBar\\UI-MainMenu-ScrollDownButton-Down")
            scrollDownButton:SetDisabledTexture("Interface\\Buttons\\UI-ScrollBar-ScrollDownButton-Disabled")
            scrollDownButton:SetHighlightTexture("Interface\\MainMenuBar\\UI-MainMenu-ScrollDownButton-Highlight")
            local highlightDown = scrollDownButton:GetHighlightTexture()
            highlightDown:SetBlendMode("ADD")

            -- Update button states
            local scrollOffset = questScrollOffsets[questTypeKey] or 0
            if scrollOffset <= 0 then
                scrollUpButton:Disable()
            else
                scrollUpButton:Enable()
            end

            if scrollOffset >= totalQuests - maxShown then
                scrollDownButton:Disable()
            else
                scrollDownButton:Enable()
            end

            -- Scroll up click handler
            scrollUpButton:SetScript("OnClick", function()
                if questScrollOffsets[questTypeKey] > 0 then
                    questScrollOffsets[questTypeKey] = questScrollOffsets[questTypeKey] - 1
                    BuildQuestTrackerUI()
                    PlaySound("UChatScrollButton")
                end
            end)

            -- Scroll down click handler
            scrollDownButton:SetScript("OnClick", function()
                local maxScroll = totalQuests - maxShown
                if questScrollOffsets[questTypeKey] < maxScroll then
                    questScrollOffsets[questTypeKey] = questScrollOffsets[questTypeKey] + 1
                    BuildQuestTrackerUI()
                    PlaySound("UChatScrollButton")
                end
            end)

            childFrame.scrollUpButton = scrollUpButton
            childFrame.scrollDownButton = scrollDownButton
        end
    end

    childFrame:Show()
    return childFrame
end

--[[
    Checks for quest objective completion changes and triggers animations/sounds

    Called from:
    - GetPlayerQuests() for each quest during the quest log scan

    Parameters:
    - logIndex: The quest's position in the quest log (used for API calls)
    - questID: The quest's questID from ClassicAPI (used as unique identifier/key)

    Functionality:
    - Tracks objective states between updates to detect changes
    - Plays sound when individual objectives complete
    - Queues quest for animation when all objectives complete
    - Skips all actions during initial load to prevent false positives
]]
function CheckObjectiveCompletion(logIndex, questID)
    local lLogIndex = logIndex
    local lQuestID = questID
    local numObjectives = GetNumQuestLeaderBoards(lLogIndex)
    local questKey = lQuestID

    -- Initialize state tracking table for this quest if it doesn't exist
    if not questObjectiveStates[questKey] then
        questObjectiveStates[questKey] = {}
    end

    local allCompleted = true
    local anyJustCompleted = false

    -- Check each objective for completion state changes
    for j = 1, numObjectives do
        local description, type, finished = GetQuestLogLeaderBoard(j, lLogIndex)
        if description then
            local previousState = questObjectiveStates[questKey][j]
            -- Detect objective that just completed (was false, now true)
            -- Skip during initial load or first full scan to avoid triggering on existing completions
            if finished and (previousState == false or previousState == nil) and not initialLoad and not firstFullScan then
                PlaySoundFile("Interface\\AddOns\\DragonFlightQuestTracker2\\sounds\\quest_objective_complete.ogg", "SFX")
                anyJustCompleted = true

                -- Flag for the retail-style strikethrough sweep on the next UI build
                if not objectivesJustCompleted[questKey] then
                    objectivesJustCompleted[questKey] = {}
                end
                objectivesJustCompleted[questKey][j] = true
            end

            -- Detect any objective progress (description text changes mean count went up)
            if not initialLoad and not firstFullScan then
                local previousDesc = questObjectiveStates[questKey]["desc_" .. j]
                if previousDesc and previousDesc ~= description then
                    progressedQuestID = lQuestID
                end
            end

            -- Update stored state and description for next comparison
            questObjectiveStates[questKey][j] = finished
            questObjectiveStates[questKey]["desc_" .. j] = description

            -- Track whether all objectives are complete
            if not finished then
                allCompleted = false
            end
        end
    end

    -- Quest fully completed: all objectives done AND at least one just finished
    -- This ensures we only animate once when the last objective completes
    if allCompleted and numObjectives > 0 and anyJustCompleted and not initialLoad and not firstFullScan then
        table.insert(questsToAnimateOnComplete, lQuestID)
    end
end

--[[
    Scans the quest log and builds/updates the tracker UI

    Called from:
    - PLAYER_LOGIN event (initial addon load)
    - QUEST_LOG_UPDATE event (whenever quest log changes)

    Process Flow:
    1. Expands all quest log headers for consistent indexing
    2. Scans all quests and categorizes by type (normal, elite, dungeon, raid, pvp)
    3. Checks each quest for objective completion changes
    4. Expands sections for quests accepted via the ClassicAPI QUEST_ACCEPTED event
    5. On initial load only: sets elite/raid/pvp sections to minimized
    6. Rebuilds entire UI with current data
    7. Animates newly accepted quests
    8. Animates newly completed quests

    Note: This function is called frequently so optimization is important
]]
function GetPlayerQuests()
    if questScanInProgress then return end
    questScanInProgress = true
    progressedQuestID = nil

    --print("GetPlayerQuests() called")

    local numEntries = GetNumQuestLogEntries()

    -- DEBUG: Print quest count on initial load
    --[[if initialLoad then
        print("DEBUG - Initial Load: Found " .. numEntries .. " quest log entries")
    end]]

    -- First pass: Expand all quest headers to ensure consistent indexing
    -- Collapsed headers can cause index shifts, breaking quest lookups
    for i = 1, numEntries do
        local questTitle, level, questTag, isHeader, isCollapsed = GetQuestLogTitle(i)
        if isHeader and isCollapsed then
            ExpandQuestHeader(i)
        end
    end

    -- Refresh count after expanding (count may have changed)
    numEntries = GetNumQuestLogEntries()

    questsByType = {} -- Reset quest data for fresh scan

    -- Second pass: Process all quests and categorize by type.
    -- Header rows name the zone/category the quest is filed under (QuestSort
    -- data) - looked up per-quest via GetHeaderIndexForQuest rather than
    -- tracked across loop iterations, so it doesn't depend on header rows
    -- being visited before their quests in this pass.
    local currentZone = GetRealZoneText()
    for i = 1, numEntries do
        local questTitle, level, questTag = GetQuestLogTitle(i)
        -- ClassicAPI: authoritative questID for this log slot (0 for header rows)
        local questID = C_QuestLog.GetQuestIDForLogIndex(i)

        if questID and questID > 0 then
            -- Check for objective completion changes (state keyed by questID)
            CheckObjectiveCompletion(i, questID)

            -- Determine quest type from tag (defaults to "normal")
            local questType = "normal"
            if questTag then
                if string.lower(questTag) == "pvp" then
                    questType = "pvp"
                elseif string.lower(questTag) == "raid" then
                    questType = "raid"
                elseif string.lower(questTag) == "dungeon" then
                    questType = "dungeon"
                elseif string.lower(questTag) == "elite" then
                    questType = "elite"
                else
                    -- Handle any other quest tags by using lowercase tag as type
                    questType = string.lower(questTag)
                end
            end

            -- Apply local override if one exists (questID keys preferred, title keys legacy)
            if DFQT_QuestTypeOverrides then
                local override = DFQT_QuestTypeOverrides[questID] or DFQT_QuestTypeOverrides[questTitle]
                if override then
                    questType = override
                end
            end

            -- Store quest data organized by type
            if not questsByType[questType] then
                questsByType[questType] = {}
            end

            -- Filed under the zone the player is standing in? (Sort-zone, not
            -- objective location - see todo.md item 10 for limits)
            local headerIndex = C_QuestLog.GetHeaderIndexForQuest(questID)
            local questZone = headerIndex and GetQuestLogTitle(headerIndex)

            table.insert(questsByType[questType], {
                title = questTitle,
                level = level,
                logIndex = i,
                questID = questID,
                inZone = (questZone ~= nil and questZone == currentZone),
                -- Ready to hand in at the currently-open NPC (set by the
                -- GOSSIP_SHOW/QUEST_GREETING handler, cleared on window close)
                readyToHandIn = gossipReadyQuestIDs[questID] or false
            })
        end
    end

    -- Zone priority (toggleable: DFQT2.settings.sortCurrentZoneFirst): float
    -- current-zone quests to the top of each section. Stable partition rather
    -- than table.sort (Lua 5.0's sort isn't stable) so quests otherwise keep
    -- their quest-log order.
    if DFQT2.settings.sortCurrentZoneFirst then
        for questType, questList in pairs(questsByType) do
            local inZoneQuests = {}
            local elsewhereQuests = {}
            for _, quest in ipairs(questList) do
                if quest.inZone then
                    table.insert(inZoneQuests, quest)
                else
                    table.insert(elsewhereQuests, quest)
                end
            end
            -- Only replace the list when the partition actually changes order
            if table.getn(inZoneQuests) > 0 and table.getn(elsewhereQuests) > 0 then
                for _, quest in ipairs(elsewhereQuests) do
                    table.insert(inZoneQuests, quest)
                end
                questsByType[questType] = inZoneQuests
            end
        end
    end

    -- Gossip turn-in highlight (toggleable: DFQT2.settings.highlightGossipTurnIn):
    -- float quests ready to hand in at the currently-open NPC above everything
    -- else, including zone-priority quests - this is a more time-sensitive
    -- signal ("you are standing at the turn-in right now") than zone matching.
    -- Same stable-partition approach as zone priority, run second so it wins.
    if DFQT2.settings.highlightGossipTurnIn and next(gossipReadyQuestIDs) then
        for questType, questList in pairs(questsByType) do
            local readyQuests = {}
            local otherQuests = {}
            for _, quest in ipairs(questList) do
                if quest.readyToHandIn then
                    table.insert(readyQuests, quest)
                else
                    table.insert(otherQuests, quest)
                end
            end
            if table.getn(readyQuests) > 0 and table.getn(otherQuests) > 0 then
                for _, quest in ipairs(otherQuests) do
                    table.insert(readyQuests, quest)
                end
                questsByType[questType] = readyQuests
            end
        end
    end

    -- Debug: after a zone change (flag set by the ZONE_CHANGED_NEW_AREA
    -- handler when debugQuestEvents is on), report which quests this scan
    -- filed under the new zone - the same inZone flags the sort/chevron use
    if zoneChangeDebugPending then
        zoneChangeDebugPending = false
        local inZoneCount = 0
        local inZoneNames = nil
        for _, questList in pairs(questsByType) do
            for _, quest in ipairs(questList) do
                if quest.inZone then
                    inZoneCount = inZoneCount + 1
                    if inZoneNames then
                        inZoneNames = inZoneNames .. ", " .. quest.title
                    else
                        inZoneNames = quest.title
                    end
                end
            end
        end
        if inZoneCount > 0 then
            print("DFQT2: zone changed to \"" .. tostring(currentZone) .. "\" - " ..
                inZoneCount .. " quest(s) in zone: " .. inZoneNames)
        else
            print("DFQT2: zone changed to \"" .. tostring(currentZone) .. "\" - no quests filed under this zone")
        end
    end

    -- Detect newly appearing quest type sections (not on initial load or first full scan)
    local newSectionsToAnimate = {}
    if not initialLoad and not firstFullScan then
        for _, questType in ipairs(questTypeOrder) do
            -- Check if this type now has quests but didn't before
            if questsByType[questType] and table.getn(questsByType[questType]) > 0 then
                if not previousQuestTypes[questType] then
                    -- This is a new section - queue for animation
                    table.insert(newSectionsToAnimate, questType)
                end
            end
        end
    end

    -- Update previousQuestTypes for next scan
    previousQuestTypes = {}
    for questType, quests in pairs(questsByType) do
        if table.getn(quests) > 0 then
            previousQuestTypes[questType] = true
        end
    end

    -- Newly accepted quests arrive via the ClassicAPI QUEST_ACCEPTED event
    -- (queued into newQuestsToAnimate as questIDs by the event handler).
    -- The event never fires on login resync, so no initialLoad guard is needed.
    -- Here we just expand the section a new quest landed in if it's minimized;
    -- the animation itself runs after BuildQuestTrackerUI below.
    if newQuestsToAnimate then
        for _, newQuestID in ipairs(newQuestsToAnimate) do
            for questType, questList in pairs(questsByType) do
                for _, quest in ipairs(questList) do
                    if quest.questID == newQuestID then
                        -- Found the quest's section - expand it if minimized
                        if minimizedSections[questType] then
                            minimizedSections[questType] = false
                        end
                        break
                    end
                end
            end
        end
    end

    -- On initial load only: minimize elite/raid/pvp/dungeon sections if they exist
    -- This runs BEFORE BuildQuestTrackerUI so sections are created minimized
    --
    -- NOTE: On fresh login, QUEST_LOG_UPDATE fires multiple times. The first fire
    -- may have numEntries = 0 because quest data isn't loaded yet. We must wait
    -- until we have actual quest data before running minimize logic and setting
    -- initialLoad = false. This retry logic ensures we only proceed when data exists.
    if initialLoad then
        --print("DEBUG - Initial Load: Processing minimize logic")

        -- Only proceed if we actually have quest data available
        -- If numEntries = 0, keep initialLoad = true and retry on next QUEST_LOG_UPDATE
        if numEntries > 0 then
            --print("DEBUG - Initial Load: Quest data is available, proceeding with minimize logic")

            -- Minimize non-standard quest type sections on initial load; leave "normal" expanded
            for _, questType in ipairs({ "elite", "raid", "pvp", "dungeon" }) do
                if questsByType[questType] then
                    local questCount = table.getn(questsByType[questType])
                    --print("DEBUG - Initial Load: Quest type '" .. questType .. "' has " .. questCount .. " quests")
                    if questCount > 0 then
                        --print("DEBUG - Initial Load: Minimizing section: " .. questType)
                        minimizedSections[questType] = true
                    end
                end
            end

            --print("DEBUG - Initial Load: Setting initialLoad = false")
            initialLoad = false -- Mark initial load complete ONLY when we have data
        else
            --print("DEBUG - Initial Load: No quest data yet (numEntries = 0), keeping initialLoad = true")
            -- initialLoad stays TRUE, so this logic will run again on next QUEST_LOG_UPDATE
        end
    end

    -- Initialize scroll offsets for new quest types
    for questType, quests in pairs(questsByType) do
        if not questScrollOffsets[questType] then
            questScrollOffsets[questType] = 0
        end
        -- Reset scroll if we now have fewer quests than the offset
        local maxShown = GetEffectiveMaxShown(questType)
        local totalQuests = table.getn(quests)
        if questScrollOffsets[questType] > 0 and questScrollOffsets[questType] >= totalQuests - maxShown + 1 then
            questScrollOffsets[questType] = math.max(0, totalQuests - maxShown)
        end
    end

    -- Rebuild the entire UI with current quest data
    BuildQuestTrackerUI()

    -- Scroll the progressed quest into view (if any objective made progress this scan)
    if progressedQuestID then
        for questType, questList in pairs(questsByType) do
            for questIndex, quest in ipairs(questList) do
                if quest.questID == progressedQuestID then
                    local maxShown = GetEffectiveMaxShown(questType)
                    local totalQuests = table.getn(questList)
                    if totalQuests > maxShown then
                        -- Clamp so quest appears at top of the visible window, without going out of bounds
                        local desiredOffset = questIndex - 1
                        local maxOffset = totalQuests - maxShown
                        local newOffset = math.max(0, math.min(desiredOffset, maxOffset))
                        if newOffset ~= (questScrollOffsets[questType] or 0) then
                            questScrollOffsets[questType] = newOffset
                            BuildQuestTrackerUI()
                        end
                    end
                    break
                end
            end
        end
        progressedQuestID = nil
    end

    -- Animate newly accepted quests (if any)
    if newQuestsToAnimate then
        for _, questID in ipairs(newQuestsToAnimate) do
            local questButton = FindQuestButtonByQuestID(questID)
            if questButton then
                DoAnimateFrame(questButton)
            end
        end
        newQuestsToAnimate = nil -- Clear queue
    end

    -- Animate newly completed quests (if any)
    if table.getn(questsToAnimateOnComplete) > 0 then
        for _, questID in ipairs(questsToAnimateOnComplete) do
            local questButton = FindQuestButtonByQuestID(questID)
            if questButton then
                DoAnimateFrame(questButton)
            end
        end
        questsToAnimateOnComplete = {} -- Clear queue
    end

    -- Animate newly appearing section headers (if any)
    if table.getn(newSectionsToAnimate) > 0 then
        for _, questType in ipairs(newSectionsToAnimate) do
            local sectionFrame = questTypeFrames[questType]
            if sectionFrame then
                DoAnimateFrame(sectionFrame)
            end
        end
    end

    -- Strikethrough flags were consumed by the build(s) in this scan; clear
    -- them so later rebuilds (scroll clicks, section toggles) don't replay
    -- the sweep on objectives that completed earlier
    objectivesJustCompleted = {}

    -- Mark first full scan as complete to enable animations/sounds on subsequent updates
    if firstFullScan then
        firstFullScan = false
    end

    questScanInProgress = false
end

--[[
    Creates quest button frames with objectives for a specific quest type

    Called from:
    - BuildQuestTrackerUI() for each non-minimized quest type section

    Parameters:
    - questType: Type key (e.g., "normal", "elite", "dungeon")
    - parentFrame: Section header frame to anchor quest buttons below
    - quests: Table of quest data for this type (from questsByType)

    Returns:
    - The last quest button created (used for anchoring next section)

    Features:
    - Creates one button per quest with dynamic height based on objectives
    - Shows quest title with optional level prefix
    - Lists all objectives or "Ready for turn-in" if complete
    - Green checkmark texture for completed objectives
    - Hover effects (alpha changes on text and icons)
    - Left click opens quest log to that specific quest
    - Right click shows context menu with Show/Abandon options
    - Caches objective count to avoid redundant API calls
    - pfQuest integration: Creates info button if pfQuest addon is detected
]]
function CreateQuestButtons(questType, parentFrame, quests)
    local lQuestType = questType
    local lParentFrame = parentFrame
    local lQuests = quests
    local buttonHeight = 20 -- Height of quest title line
    local lastButton = nil
    local questButtons = {}
    local activeQuestTimers = GetActiveQuestTimers() -- [questID] = remaining seconds, or nil

    -- Calculate which quests to show based on scroll offset
    local scrollOffset = questScrollOffsets[lQuestType] or 0
    local maxShown = GetEffectiveMaxShown(lQuestType)
    local totalQuests = table.getn(lQuests)
    local startIndex = scrollOffset + 1
    local endIndex = math.min(scrollOffset + maxShown, totalQuests)

    for i = startIndex, endIndex do
        local quest = lQuests[i]
        -- Create quest button frame
        local questButton = CreateFrame("Button", nil, lParentFrame)
        questButton:SetWidth(280)
        questButton.questID = quest.questID -- Store for later lookup via FindQuestButtonByQuestID

        -- Gossip turn-in glow (todo #6): a soft pulsing gold border, shown
        -- only while a nearby NPC's gossip/greeting window has this quest
        -- ready to turn in (GOSSIP_SHOW/QUEST_GREETING handlers), hidden on
        -- GOSSIP_CLOSED/QUEST_FINISHED. State-driven, not a one-shot animation
        -- - deliberately reuses neither DoAnimateFrame nor the completion
        -- sound, since this marks an ongoing condition, not a momentary event.
        -- Textures have no SetScript (that's a Frame-only method), so the
        -- pulse (OnUpdate) lives on a small parent Frame; the gossip event
        -- handlers Show()/Hide() that same frame via questButton.readyGlow.
        -- Sized/anchored below (after content height is known) so it hugs
        -- the title+objectives text instead of the button's full fixed
        -- height, which includes trailing dead space on short quests.
        -- Shown state comes straight from quest.readyToHandIn (set during the
        -- scan from gossipReadyQuestIDs) - the gossip event handlers only
        -- ever change that table and trigger a rescan, never poke buttons
        -- directly, so this is the single source of truth.
        local glowFrame = CreateFrame("Frame", nil, questButton)
        if quest.readyToHandIn then
            glowFrame:Show()
        else
            glowFrame:Hide()
        end

        local readyGlow = glowFrame:CreateTexture(nil, "BACKGROUND")
        readyGlow:SetAllPoints(glowFrame)
        readyGlow:SetTexture("Interface\\QuestFrame\\UI-QuestLogTitleHighlight")
        readyGlow:SetBlendMode("ADD")
        readyGlow:SetVertexColor(1, 0.82, 0)

        local pulseStart = GetTime()
        glowFrame:SetScript("OnUpdate", function()
            -- Slow sine pulse between ~0.35 and ~0.75 alpha
            local phase = math.sin((GetTime() - pulseStart) * 3)
            readyGlow:SetAlpha(0.55 + phase * 0.2)
        end)

        questButton.readyGlow = glowFrame
        -- Get objectives and check completion status (only once for efficiency)
        local numObjectives = GetNumQuestLeaderBoards(quest.logIndex)
        local allObjectivesCompleted = true

        for j = 1, numObjectives do
            local description, type, finished = GetQuestLogLeaderBoard(j, quest.logIndex)
            if description and not finished then
                allObjectivesCompleted = false
                break -- Exit early if any incomplete objective found
            end
        end

        -- pfQuest integration: Create info button if pfQuest addon is loaded
        if pfQuest then
            ----print("pfQUest Detected - adding integration buttons")
            local infoButton = CreateFrame("Button", "DFQT_InfoButton_" .. lQuestType .. "_" .. i, questButton)
            infoButton:SetWidth(32)
            infoButton:SetHeight(32)
            infoButton:SetPoint("TOPRIGHT", questButton, "TOPLEFT", 10, 10)

            -- Set normal texture
            local normalTexture = infoButton:CreateTexture(nil, "ARTWORK")
            normalTexture:SetAllPoints(infoButton)
            normalTexture:SetTexture("Interface\\Addons\\DragonFlightQuestTracker2\\textures\\quest-info-bubble.blp")
            infoButton:SetNormalTexture(normalTexture)

            -- Set highlight texture
            local highlightTexture = infoButton:CreateTexture(nil, "HIGHLIGHT")
            highlightTexture:SetAllPoints(infoButton)
            highlightTexture:SetTexture(
                "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\quest-info-bubble-highlight.blp")
            infoButton:SetHighlightTexture(highlightTexture)

            -- Determine button text based on quest completion status
            local buttonTextString = "..."
            if numObjectives == 0 or allObjectivesCompleted then
                buttonTextString = "?"
            end

            -- Add text to the button
            local buttonText = infoButton:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
            if buttonTextString == "?" then
                buttonText:SetPoint("CENTER", infoButton, "CENTER", 0, 0)
            else
                buttonText:SetPoint("CENTER", infoButton, "CENTER", 0, 5)
            end

            buttonText:SetText(buttonTextString)
            buttonText:SetAlpha(1.0)

            -- Store questID for click handler (authoritative, from ClassicAPI -
            -- no more pfDatabase:GetQuestIDs title/level guessing)
            local infoQuestID = quest.questID

            -- Click handler
            infoButton:SetScript("OnClick", function()
                local questIndex = FindQuestLogIndexByQuestID(infoQuestID)
                local id = infoQuestID
                if not questIndex or not id then return end

                local maps, meta = {}, { ["addon"] = "PFQUEST", ["qlogid"] = questIndex }
                maps = pfDatabase:SearchQuestID(id, meta, maps)
                local foundBestMap = pfMap:ShowMapID(pfDatabase:GetBestMap(maps))
                if not foundBestMap then
                    --print("No pfQuest Map found, here's the world map!")
                    SetMapZoom(0)
                end
            end)

            infoButton:Show()

            -- Store reference to info button on quest button for cleanup
            questButton.infoButton = infoButton
        end -- END OF pfQuest integration block

        -- Quest source-item button (ClassicAPI): when the questgiver handed the
        -- player an item on accept (srcItemID) and it's currently in the bags,
        -- show a clickable icon next to the quest so the player doesn't have to
        -- dig through bags. Click = use the item; hover = real item tooltip
        -- (always shown, independent of showToolTip - an unlabelled icon
        -- without a tooltip would be useless).
        local srcItemID = GetQuestSrcItemID(quest.questID)
        if srcItemID > 0 then
            local itemBag = FindBagItemByID(srcItemID)

            -- Only show the button when the item has an on-use effect -
            -- delivery-only source items (no "Use:" line) get no button,
            -- matching retail. C_Item.GetItemSpell returns the ON_USE spell
            -- name or nil. If the item data isn't cached yet we fail OPEN
            -- (show the button): the item is in the bags so the cache fills
            -- immediately and the next rebuild corrects it. Known upstream
            -- limit: trigger 5 (ON_USE_NO_DELAY) items aren't surfaced by
            -- GetItemSpell and would wrongly lose their button.
            local hasUseEffect = true
            if itemBag and C_Item.IsItemDataCachedByID(srcItemID) then
                hasUseEffect = C_Item.GetItemSpell(srcItemID) ~= nil
            end

            if itemBag and hasUseEffect then
                local itemButton = CreateFrame("Button", "DFQT_ItemButton_" .. lQuestType .. "_" .. i, questButton)
                itemButton:SetWidth(26)
                itemButton:SetHeight(26)
                if questButton.infoButton then
                    -- pfQuest info button occupies the near-left slot; sit left of it
                    itemButton:SetPoint("TOPRIGHT", questButton.infoButton, "TOPLEFT", -1, -3)
                else
                    itemButton:SetPoint("TOPRIGHT", questButton, "TOPLEFT", 8, 4)
                end

                -- Item icon as the button face
                local iconTexture = itemButton:CreateTexture(nil, "ARTWORK")
                iconTexture:SetAllPoints(itemButton)
                iconTexture:SetTexture(GetItemIcon(srcItemID) or "Interface\\Icons\\INV_Misc_QuestionMark")
                itemButton:SetNormalTexture(iconTexture)
                itemButton:SetHighlightTexture("Interface\\Buttons\\ButtonHilight-Square")
                local itemHighlight = itemButton:GetHighlightTexture()
                itemHighlight:SetBlendMode("ADD")

                -- Capture for the click/tooltip closures
                local srcItem = srcItemID

                itemButton:SetScript("OnClick", function()
                    -- Re-locate at click time; bag position may have changed
                    local bag, slot = FindBagItemByID(srcItem)
                    if bag then
                        UseContainerItem(bag, slot)
                    end
                end)

                itemButton:SetScript("OnEnter", function()
                    GameTooltip:SetOwner(this, "ANCHOR_LEFT")
                    local bag, slot = FindBagItemByID(srcItem)
                    if bag then
                        GameTooltip:SetBagItem(bag, slot)
                    else
                        -- Item left the bags since build; show static item info
                        GameTooltip:SetItemByID(srcItem)
                    end
                    GameTooltip:Show()
                end)

                itemButton:SetScript("OnLeave", function()
                    GameTooltip:Hide()
                end)

                itemButton:Show()
                questButton.itemButton = itemButton
            end
        end

        -- Calculate button height based on number of objectives
        local totalHeight
        if numObjectives > 0 and allObjectivesCompleted then
            totalHeight = buttonHeight + 16                   -- Title + single "Ready for turn-in" line
        else
            totalHeight = buttonHeight + (numObjectives * 16) -- Title + all objective lines
        end

        -- An active quest timer adds a countdown bar line (retail-style)
        local timerRemaining = activeQuestTimers and activeQuestTimers[quest.questID]
        if timerRemaining then
            totalHeight = totalHeight + 14
        end

        questButton:SetHeight(totalHeight)

        -- Anchor to section header or previous quest button
        if i == startIndex then -- Changed from: if i == 1 then
            questButton:SetPoint("TOP", lParentFrame, "BOTTOM", 0, -10)
        else
            questButton:SetPoint("TOP", lastButton, "BOTTOM", 0, -2)
        end

        -- Create quest title text
        local questText = questButton:CreateFontString(nil, "OVERLAY", "GameFontNormal")
        questText:SetPoint("TOPLEFT", questButton, "TOPLEFT", 10, 0)

        -- Truncate long titles so they don't overrun the tracker width. Only
        -- the displayed string is shortened - quest.title stays intact for the
        -- tooltip, right-click menu and abandon popup.
        local displayTitle = quest.title
        if string.len(displayTitle) > 45 then
            displayTitle = string.sub(displayTitle, 1, 41) .. " ..."
        end

        -- Zone-priority marker: light-blue "**" after current-zone quest
        -- titles. ASCII only - the client's font silently drops multibyte
        -- glyphs (confirmed in-game with U+00BB even as valid UTF-8)
        local titleSuffix = ""
        if quest.inZone and DFQT2.settings.sortCurrentZoneFirst then
            titleSuffix = " |cff88ccff**|r"
        end

        -- Include level if the showLevel setting is enabled, colored the same
        -- way the native quest log does (GetDifficultyColor - renamed to
        -- GetQuestDifficultyColor in 3.2, but 1.12.1 still uses the original
        -- name: green for trivial, yellow/orange/red as the quest outlevels
        -- the player, grey for greyed-out quests) so it matches an existing
        -- WoW convention.
        if DFQT2.settings.showLevel then
            local diffColor = GetDifficultyColor(quest.level)
            local hex = string.format("%02x%02x%02x", diffColor.r * 255, diffColor.g * 255, diffColor.b * 255)
            questText:SetText("|cff" .. hex .. "[" .. quest.level .. "]|r " .. displayTitle .. titleSuffix)
        else
            questText:SetText(displayTitle .. titleSuffix)
        end

        questText:SetAlpha(0.85) -- Semi-transparent by default

        -- Create objective texts
        local objectiveTexts = {} -- Track for hover alpha changes
        local currentY = -16      -- Start below quest title

        if numObjectives > 0 and allObjectivesCompleted then
            -- All objectives complete - show single "Ready for turn-in" line
            local objectiveText = questButton:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
            objectiveText:SetPoint("TOPLEFT", questButton, "TOPLEFT", 20, currentY)
            objectiveText:SetWidth(250)
            objectiveText:SetJustifyH("LEFT")
            objectiveText:SetAlpha(0.85)
            objectiveText:SetText("Ready for turn-in")
            objectiveText:SetTextColor(1, 1, 1) -- White

            table.insert(objectiveTexts, objectiveText)
        else
            -- Show individual objectives with completion status
            for j = 1, numObjectives do
                local description, type, finished = GetQuestLogLeaderBoard(j, quest.logIndex)
                if description and description ~= "" then
                    local objectiveText = questButton:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
                    objectiveText:SetPoint("TOPLEFT", questButton, "TOPLEFT", 20, currentY)
                    objectiveText:SetWidth(250)
                    objectiveText:SetJustifyH("LEFT")
                    objectiveText:SetAlpha(0.85)

                    if finished then
                        -- Completed objective - green text with checkmark icon
                        objectiveText:SetText(description)
                        objectiveText:SetTextColor(0, 1, 0) -- Green

                        -- Create checkmark texture to left of text
                        local tickTexture = questButton:CreateTexture(nil, "OVERLAY")
                        tickTexture:SetWidth(12)
                        tickTexture:SetHeight(12)
                        tickTexture:SetTexture(
                            "Interface\\Addons\\DragonFlightQuestTracker2\\textures\\objective_complete_tick.blp")
                        tickTexture:SetPoint("RIGHT", objectiveText, "LEFT", -2, 0)
                        tickTexture:SetAlpha(0.85)
                        objectiveText.tickTexture = tickTexture -- Store for hover alpha changes

                        -- Retail-style strikethrough sweep for objectives that
                        -- completed during this scan (flags are cleared at the
                        -- end of GetPlayerQuests so later rebuilds don't replay)
                        if objectivesJustCompleted[quest.questID] and objectivesJustCompleted[quest.questID][j] then
                            StrikeThroughObjective(questButton, objectiveText)
                        end
                    else
                        -- Incomplete objective - white text with hyphen prefix
                        objectiveText:SetText("- " .. description)
                        objectiveText:SetTextColor(1, 1, 1) -- White
                    end

                    table.insert(objectiveTexts, objectiveText)
                    currentY = currentY - 16 -- Move down for next objective
                end
            end
        end

        -- Timed quest countdown bar (retail-style), below the objective lines.
        -- Creation only sets the initial state; the shared 1-second C_Timer
        -- ticker (UpdateQuestTimerBars) keeps it live between UI rebuilds.
        if timerRemaining then
            local barY = currentY
            if numObjectives > 0 and allObjectivesCompleted then
                barY = -32 -- below the single "Ready for turn-in" line
            end

            local timerBar = CreateFrame("StatusBar", nil, questButton)
            timerBar:SetWidth(240)
            timerBar:SetHeight(10)
            timerBar:SetPoint("TOPLEFT", questButton, "TOPLEFT", 20, barY - 2)
            timerBar:SetStatusBarTexture("Interface\\TargetingFrame\\UI-StatusBar")
            timerBar:SetStatusBarColor(1, 0.82, 0) -- gold; ticker shifts to orange/red near expiry

            local barBackground = timerBar:CreateTexture(nil, "BACKGROUND")
            barBackground:SetAllPoints(timerBar)
            barBackground:SetTexture(0, 0, 0, 0.4)

            -- The authored duration isn't exposed by any API, so use the
            -- largest remaining value seen for this quest as the bar total:
            -- exact when the timer started while we were watching, and a
            -- full-looking bar counting down after a mid-timer login/reload.
            local total = questTimerTotals[quest.questID]
            if not total or timerRemaining > total then
                total = timerRemaining
                questTimerTotals[quest.questID] = total
            end
            timerBar:SetMinMaxValues(0, total)
            timerBar:SetValue(timerRemaining)

            local timeText = timerBar:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
            timeText:SetPoint("CENTER", timerBar, "CENTER", 0, 0)
            timeText:SetText(FormatTimeRemaining(timerRemaining))
            timerBar.timeText = timeText

            timerBarsByQuestID[quest.questID] = timerBar
            questButton.timerBar = timerBar
            EnsureTimerTicker()

            -- Bar bottom becomes the content bottom for the glow sizing below
            currentY = barY - 2 - timerBar:GetHeight()
        end

        -- Now that all content (title, objectives/ready line, timer bar) is
        -- laid out, size the glow to hug it rather than the button's full
        -- fixed height (which includes trailing dead space on short quests)
        questButton.readyGlow:ClearAllPoints()
        questButton.readyGlow:SetPoint("TOPLEFT", questButton, "TOPLEFT", -6, 6)
        questButton.readyGlow:SetPoint("TOPRIGHT", questButton, "TOPRIGHT", 6, 6)
        questButton.readyGlow:SetHeight(-currentY + 6 + 4) -- content depth below title + top pad + bottom pad

        -- Store quest data for event handlers (cache numObjectives to avoid redundant API calls)
        local questData = {
            title = quest.title,
            level = quest.level,
            logIndex = quest.logIndex,
            questID = quest.questID,
            type = lQuestType,
            numObjectives = numObjectives -- Cached for tooltip
        }

        -- Mouse enter: Increase alpha for hover highlight effect
        questButton:SetScript("OnEnter", function()
            questText:SetAlpha(1.0)
            for _, objText in ipairs(objectiveTexts) do
                objText:SetAlpha(1.0)
                if objText.tickTexture then
                    objText.tickTexture:SetAlpha(1.0)
                end
            end

            -- Show detailed tooltip if enabled
            if DFQT2.settings.showToolTip then
                GameTooltip:SetOwner(questButton, "ANCHOR_TOPLEFT", questButton:GetWidth(), 0)
                GameTooltip:SetText(questData.title)
                GameTooltip:AddLine("Quest Type: " .. questData.type, 1, 1, 1)
                GameTooltip:AddLine("Level: " .. questData.level, 0.8, 0.8, 0.8)
                GameTooltip:AddLine("Quest ID: " .. tostring(questData.questID), 0.8, 0.8, 0.8)

                -- Party members on this quest (ClassicAPI IsUnitOnQuest).
                -- Only members within the client's quest-sync range report true,
                -- so false means "not on it OR unknown" - we therefore only list
                -- confirmed matches and omit the line entirely when there are none.
                if GetNumPartyMembers() > 0 then
                    local partyOnQuest = nil
                    for p = 1, GetNumPartyMembers() do
                        local unit = "party" .. p
                        if C_QuestLog.IsUnitOnQuest(unit, questData.questID) then
                            local name = UnitName(unit)
                            if name then
                                if partyOnQuest then
                                    partyOnQuest = partyOnQuest .. ", " .. name
                                else
                                    partyOnQuest = name
                                end
                            end
                        end
                    end
                    if partyOnQuest then
                        GameTooltip:AddLine("Party on quest: " .. partyOnQuest, 0.4, 0.8, 1)
                    end
                end

                -- Use cached numObjectives instead of calling API again
                if questData.numObjectives > 0 then
                    GameTooltip:AddLine(" ", 1, 1, 1)
                    GameTooltip:AddLine("Objectives:", 1, 1, 0)

                    for j = 1, questData.numObjectives do
                        local description, type, finished = GetQuestLogLeaderBoard(j, questData.logIndex)
                        if description then
                            -- ASCII markers: the client font drops multibyte
                            -- glyphs (same issue as the zone chevron)
                            if finished then
                                GameTooltip:AddLine("+ " .. description, 0, 1, 0)
                            else
                                GameTooltip:AddLine("- " .. description, 0.8, 0.8, 0.8)
                            end
                        end
                    end
                end

                GameTooltip:Show()
            end
        end)

        -- Mouse leave: Restore normal alpha
        questButton:SetScript("OnLeave", function()
            questText:SetAlpha(0.85)
            for _, objText in ipairs(objectiveTexts) do
                objText:SetAlpha(0.85)
                if objText.tickTexture then
                    objText.tickTexture:SetAlpha(0.85)
                end
            end

            if DFQT2.settings.showToolTip then
                GameTooltip:Hide()
            end
        end)

        -- Click: Left click opens quest log, Right click shows menu
        questButton:SetScript("OnClick", function()
            if arg1 == "LeftButton" then
                -- Left click: Open quest log
                -- Resolve the log index at click time via questID; indices can
                -- shift if the quest log changed since this button was built.
                local logIndex = FindQuestLogIndexByQuestID(questData.questID) or questData.logIndex
                SelectQuestLogEntry(logIndex)

                if not QuestLogFrame:IsVisible() then
                    ToggleQuestLog()
                else
                    QuestLog_Update()
                    QuestLog_UpdateQuestDetails(true)
                end
            elseif arg1 == "RightButton" then
                -- Right click: Show context menu
                if not QuestTrackerDropDown then
                    CreateFrame("Frame", "QuestTrackerDropDown", UIParent, "UIDropDownMenuTemplate")
                end

                -- Capture questData in local for menu functions
                local menuQuestData = questData

                UIDropDownMenu_Initialize(QuestTrackerDropDown, function()
                    -- Title
                    local info = {}
                    info.text = menuQuestData.title
                    info.isTitle = 1
                    info.notCheckable = 1
                    UIDropDownMenu_AddButton(info)

                    -- Show Quest option
                    info = {}
                    info.text = "Open Quest Details"
                    info.notCheckable = 1
                    info.func = function()
                        local logIndex = FindQuestLogIndexByQuestID(menuQuestData.questID) or menuQuestData.logIndex
                        SelectQuestLogEntry(logIndex)
                        if not QuestLogFrame:IsVisible() then
                            ToggleQuestLog()
                        else
                            QuestLog_Update()
                            QuestLog_UpdateQuestDetails(true)
                        end
                    end
                    UIDropDownMenu_AddButton(info)

                    -- Show Quest option
                    info = {}
                    info.text = "Open Quest Map"
                    info.notCheckable = 1
                    info.func = function()
                        -- Authoritative questID from ClassicAPI; resolve current log index for pfQuest meta
                        local questIndex = FindQuestLogIndexByQuestID(menuQuestData.questID)
                        local id = menuQuestData.questID
                        if not questIndex or not id then return end

                        local maps, meta = {}, { ["addon"] = "PFQUEST", ["qlogid"] = questIndex }
                        maps = pfDatabase:SearchQuestID(id, meta, maps)
                        --print("RC ID: " .. id)
                        local foundBestMap = pfMap:ShowMapID(pfDatabase:GetBestMap(maps))
                        --print("RC Did we find a pfQuest Map: " .. tostring(foundBestMap))
                        if not foundBestMap then
                            --print("RC No pfQuest Map found, here's the world map!")
                            SetMapZoom(0)
                        end
                    end
                    UIDropDownMenu_AddButton(info)

                    -- Show POI option - only when ClassicAPI has POI data cached
                    -- for this quest. GetQuestDetails is a pure cache probe; log
                    -- quests are normally cached by the engine already, but if
                    -- not, queue a load so the option can appear on a later click.
                    local details = C_QuestLog.GetQuestDetails(menuQuestData.questID)
                    if not details then
                        C_QuestLog.RequestLoadQuestByID(menuQuestData.questID)
                    elseif details.poi then
                        info = {}
                        info.text = "Show POI"
                        info.notCheckable = 1
                        local poiTitle = menuQuestData.title
                        local poiQuestID = menuQuestData.questID
                        local poiTable = details.poi
                        info.func = function()
                            ShowPOIFrame(poiTitle, poiQuestID, poiTable)
                        end
                        UIDropDownMenu_AddButton(info)
                    end

                    -- Share Quest if in a group or raid with other players
                    if GetNumPartyMembers() > 0 or GetNumRaidMembers() > 0 then
                        info = {}
                        info.text = "Share Quest"
                        info.notCheckable = 1
                        info.func = function()
                            local logIndex = FindQuestLogIndexByQuestID(menuQuestData.questID) or
                                menuQuestData.logIndex
                            SelectQuestLogEntry(logIndex)
                            QuestLogPushQuest()
                        end
                        UIDropDownMenu_AddButton(info)
                    end

                    -- Abandon Quest option
                    info = {}
                    info.text = "Abandon Quest"
                    info.notCheckable = 1
                    info.func = function()
                        local logIndex = FindQuestLogIndexByQuestID(menuQuestData.questID) or menuQuestData.logIndex
                        SelectQuestLogEntry(logIndex)
                        SetAbandonQuest()
                        -- Store the quest index globally for the popup callback
                        pendingAbandonQuestIndex = logIndex
                        StaticPopup_Show("DFQT_ABANDON_QUEST", menuQuestData.title)
                    end
                    UIDropDownMenu_AddButton(info)
                end, "MENU")

                ToggleDropDownMenu(1, nil, QuestTrackerDropDown, "cursor", 0, 0)
            end
        end)

        -- Register for both left and right clicks
        questButton:RegisterForClicks("LeftButtonUp", "RightButtonUp")

        questButton:Show()

        lastButton = questButton
        table.insert(questButtons, questButton)
    end

    -- Store buttons for this type and return last button for anchoring next section
    questButtonsByType[lQuestType] = questButtons
    return lastButton
end

--[[
    Hides all quest buttons for a specific quest type section

    Called from:
    - CreateObjectiveTracker() when section minimize button is clicked

    Parameters:
    - questType: Type key to hide (e.g., "normal", "elite", "dungeon", "raid", "pvp")

    Process:
    1. Hides all quest button frames for this type
    2. Marks section as minimized in global state
    3. Rebuilds entire UI to adjust positioning

    Note: Rebuilding UI is necessary because hiding buttons affects
    the vertical positioning of subsequent sections
]]
function HideQuestButtons(questType)
    local lQuestType = questType

    -- Check if this quest type has any buttons
    if questButtonsByType[lQuestType] then
        -- Hide all quest buttons for this type
        for _, button in ipairs(questButtonsByType[lQuestType]) do
            if button then
                button:Hide()
            end
        end
        -- Mark this section as minimized for future UI builds
        minimizedSections[lQuestType] = true
        -- Rebuild UI to adjust positioning of subsequent sections
        BuildQuestTrackerUI()
    end
end

--[[
    Shows all quest buttons for a specific quest type section

    Called from:
    - CreateObjectiveTracker() when section maximize button is clicked

    Parameters:
    - questType: Type key to show (e.g., "normal", "elite", "dungeon", "raid", "pvp")

    Process:
    1. If this is the first section expansion, trigger quest log scan
    2. Marks section as not minimized in global state
    3. Rebuilds entire UI to create buttons and adjust positioning

    Note: Rather than showing existing buttons, we rebuild the UI
    which recreates all buttons with current data
]]
function ShowQuestButtons(questType)
    local lQuestType = questType

    -- Mark this section as not minimized before any UI build
    minimizedSections[lQuestType] = false
    BuildQuestTrackerUI()
end

--[[
    Hides all section headers and quest buttons

    Called from:
    - Main header minimize button click (in minimizeButton:SetScript("OnClick"))

    Process:
    1. Hides all quest type section header frames
    2. Hides all quest button frames across all types
    3. Hides all pfQuest info buttons
    4. Sets global flag to prevent UI rebuild until ShowAllSections is called

    Note: This is different from minimizing individual sections.
    This globally hides everything until the main minimize button is clicked again.
    When allSectionsHidden is true, BuildQuestTrackerUI() exits early.
]]
function HideAllSections()
    -- Hide all quest type section headers
    for questType, frame in pairs(questTypeFrames) do
        if frame then
            frame:Hide()
        end
    end

    -- Hide all quest buttons and their associated info buttons across all types
    for questType, buttons in pairs(questButtonsByType) do
        if buttons then
            for _, button in ipairs(buttons) do
                if button then
                    -- Hide associated info button if it exists
                    if button.infoButton then
                        button.infoButton:Hide()
                    end
                    -- Hide associated quest item button if it exists
                    if button.itemButton then
                        button.itemButton:Hide()
                    end
                    button:Hide()
                end
            end
        end
    end
    -- Set global flag to prevent BuildQuestTrackerUI from creating new frames
    allSectionsHidden = true
end

--[[
    Shows all section headers and quest buttons

    Called from:
    - Main header maximize button click (in minimizeButton:SetScript("OnClick"))

    Process:
    1. Clears global hide flag
    2. Rebuilds entire UI which will show all sections

    Note: Individual section minimized states (in minimizedSections table)
    are preserved, so previously minimized sections remain minimized
]]
function ShowAllSections()
    -- Clear global hide flag
    allSectionsHidden = false
    -- Rebuild UI - BuildQuestTrackerUI will now create all frames
    BuildQuestTrackerUI()
end

--[[
    Animates a quest button with a sliding/filling texture effect

    Called from:
    - Quest button click (CreateQuestButtons OnClick handler)
    - GetPlayerQuests() when new quest is accepted
    - GetPlayerQuests() when quest is completed

    Parameters:
    - questButton: The quest button frame to animate

    Animation phases:
    1. Fill animation (0.75s): Status bar fills left to right at 0.75 alpha
    2. Fade out (0.15s): Full bar fades from 0.75 alpha to 0 (complete transparency)

    Technical notes:
    - Uses StatusBar frame for fill effect
    - Parented to UIParent (not questButton) for visibility
    - TOOLTIP strata ensures it renders on top of other UI elements
    - Self-cleaning: removes frame after animation completes
]]
function DoAnimateFrame(frame)
    local lFrame = frame

    -- Safety check: exit if no button provided
    if not lFrame then
        return
    end

    -- Create animation frame as StatusBar (provides fill effect)
    local buttonWidth = lFrame:GetWidth()
    local animFrame = CreateFrame("StatusBar", nil, UIParent)
    animFrame:SetFrameStrata("TOOLTIP") -- High strata to render on top
    ----print("The frame that was clicked was: " .. tostring(lFrame:GetName()))

    if lFrame.isSectionHeader then
        animFrame:SetWidth(buttonWidth + 100)
        animFrame:SetHeight(27)
        animFrame:SetPoint("TOPLEFT", lFrame, "TOPLEFT", 10, -3)
    else
        animFrame:SetWidth(buttonWidth + 80)
        animFrame:SetHeight(20)
        animFrame:SetPoint("TOPLEFT", lFrame, "TOPLEFT", 20, 5)
    end

    -- Set the sliding texture
    animFrame:SetStatusBarTexture("Interface\\Addons\\DragonFlightQuestTracker2\\textures\\quest-title-flash.blp")

    local statusBarTexture = animFrame:GetStatusBarTexture()
    statusBarTexture:SetAlpha(0.75) -- Semi-transparent

    -- Configure status bar for fill animation
    animFrame:SetMinMaxValues(0, 1)
    animFrame:SetValue(0) -- Start empty

    -- Animation timing constants
    local animDuration = 0.75    -- Fill duration in seconds
    local fadeOutDuration = 0.15 -- Fade out duration in seconds
    local totalDuration = animDuration + fadeOutDuration
    local startTime = GetTime()

    -- OnUpdate: Called every frame to progress the animation
    animFrame:SetScript("OnUpdate", function()
        local currentTime = GetTime()
        local elapsed = currentTime - startTime

        if elapsed >= totalDuration then
            -- Animation complete - clean up
            animFrame:SetScript("OnUpdate", nil)
            animFrame:Hide()
            animFrame = nil
        elseif elapsed <= animDuration then
            -- Phase 1: Filling animation (0 to 0.75 seconds)
            local progress = elapsed / animDuration -- 0 to 1
            animFrame:SetValue(progress)            -- Fill bar left to right
            statusBarTexture:SetAlpha(0.75)         -- Maintain constant alpha
        else
            -- Phase 2: Fade out (0.75 to 0.90 seconds)
            animFrame:SetValue(1)                                           -- Keep bar full
            local fadeProgress = (elapsed - animDuration) / fadeOutDuration -- 0 to 1
            local currentAlpha = 0.75 - (fadeProgress * 0.75)               -- 0.75 to 0
            statusBarTexture:SetAlpha(currentAlpha)
        end
    end)

    animFrame:Show()
end

--[[
    Fades a frame (and its child regions) out over duration seconds, then hides it.

    Called from:
    - QUEST_REMOVED event handler, on the removed quest's tracker button. The
      quest-log rescan is postponed via questScanDelayUntil so the fade can
      play before the rebuild destroys the button.

    Parameters:
    - frame: The frame to fade out (quest button, including its child
      item/info buttons since frame alpha propagates to children)
    - duration: Fade time in seconds (defaults to 0.7)
]]
function FadeOutFrame(frame, duration)
    if not frame then
        return
    end

    local lDuration = duration or 0.7
    local startTime = GetTime()

    frame:SetScript("OnUpdate", function()
        local elapsed = GetTime() - startTime
        if elapsed >= lDuration then
            this:SetScript("OnUpdate", nil)
            this:Hide()
        else
            this:SetAlpha(1 - (elapsed / lDuration))
        end
    end)
end

--[[
    Retail-style strikethrough sweep across a just-completed objective line.

    Called from:
    - CreateQuestButtons() when rendering a finished objective that is flagged
      in objectivesJustCompleted (i.e. it completed during this scan)

    Animation phases:
    1. Sweep (0.25s): thin line grows left-to-right across the text width
    2. Hold (0.75s): line sits at full width over the text
    3. Fade (0.3s): line fades out, leaving the normal green-plus-tick look

    Technical notes:
    - Line width comes from objectiveText:GetStringWidth() so it matches the
      actual text, not the full 250px FontString
    - Parented to the quest button, so a mid-animation rebuild (scroll click,
      section toggle) hides it along with the old button - self-cleaning
]]
function StrikeThroughObjective(questButton, objectiveText)
    local textWidth = objectiveText:GetStringWidth()
    if not textWidth or textWidth <= 0 then
        return
    end

    local strikeFrame = CreateFrame("Frame", nil, questButton)
    strikeFrame:SetFrameLevel(questButton:GetFrameLevel() + 2)
    strikeFrame:SetWidth(1)
    strikeFrame:SetHeight(2)
    strikeFrame:SetPoint("LEFT", objectiveText, "LEFT", 0, 0)

    local lineTexture = strikeFrame:CreateTexture(nil, "OVERLAY")
    lineTexture:SetAllPoints(strikeFrame)
    lineTexture:SetTexture(0.9, 0.9, 0.9, 0.9) -- solid light line (vanilla solid-color texture)

    local growDuration = 0.25
    local holdDuration = 0.75
    local fadeDuration = 0.3
    local totalDuration = growDuration + holdDuration + fadeDuration
    local startTime = GetTime()

    strikeFrame:SetScript("OnUpdate", function()
        local elapsed = GetTime() - startTime
        if elapsed >= totalDuration then
            -- Animation complete - clean up
            this:SetScript("OnUpdate", nil)
            this:Hide()
        elseif elapsed <= growDuration then
            -- Phase 1: sweep across the text
            this:SetWidth(math.max(1, textWidth * (elapsed / growDuration)))
        elseif elapsed <= growDuration + holdDuration then
            -- Phase 2: hold at full width
            this:SetWidth(textWidth)
        else
            -- Phase 3: fade out
            local fadeProgress = (elapsed - growDuration - holdDuration) / fadeDuration
            this:SetAlpha(1 - fadeProgress)
        end
    end)

    strikeFrame:Show()
end

--[[
    Finds a quest's current index in the quest log by questID (ClassicAPI)

    Called from:
    - Quest button click handlers (left click, right-click menu options)
    - pfQuest info button click handler

    Parameters:
    - questID: The questID to search for

    Returns:
    - Quest log index (number) if found
    - nil if quest not found

    Note: Unlike title matching, questID lookup is unambiguous (duplicate
    quest titles cannot collide) and safe to call at click time even if
    log indices have shifted since the tracker UI was built.
]]
function FindQuestLogIndexByQuestID(questID)
    local lQuestID = questID
    if not lQuestID then
        return nil
    end
    local numEntries = GetNumQuestLogEntries()

    -- Iterate through quest log entries
    for i = 1, numEntries do
        -- GetQuestIDForLogIndex returns 0 for header rows, so headers never match
        if C_QuestLog.GetQuestIDForLogIndex(i) == lQuestID then
            return i
        end
    end

    return nil -- Quest not found
end

--[[
    Finds a quest button frame by questID

    Called from:
    - GetPlayerQuests() to find buttons for newly accepted quests (for animation)
    - GetPlayerQuests() to find buttons for completed quests (for animation)

    Parameters:
    - questID: The questID to search for

    Returns:
    - Quest button frame if found
    - nil if button not found

    Note: Searches through all quest types since we don't know which type
    the quest belongs to. The questID property is set on buttons during
    CreateQuestButtons() for this lookup purpose.

    Performance: This is O(n) where n is total number of quest buttons.
    Could be optimized with a separate questID->button lookup table if needed.
]]
function FindQuestButtonByQuestID(questID)
    local lQuestID = questID

    -- Iterate through all quest types
    for questType, buttons in pairs(questButtonsByType) do
        if buttons then
            -- Check each button in this type
            for _, button in ipairs(buttons) do
                -- Match button with stored questID property
                if button and button.questID == lQuestID then
                    return button
                end
            end
        end
    end

    return nil -- Button not found
end

--[[
    Shows a basic diagnostic frame dumping a quest's POI table (ClassicAPI)

    Called from:
    - Quest button right-click menu, "Show POI" option (only present when
      C_QuestLog.GetQuestDetails(questID).poi exists)

    Parameters:
    - questTitle: Quest title for the header line
    - questID: questID for the header line
    - poi: The poi table from GetQuestDetails - documented shape is
      {mapID, x, y, opt}, but we dump every key/value pair raw because the
      field is flagged as unverified upstream and we want to see exactly
      what the engine returns (e.g. whether x/y are world or zone coords).
]]
function ShowPOIFrame(questTitle, questID, poi)
    if not DFQT_POIFrame then
        local frame = CreateFrame("Frame", "DFQT_POIFrame", UIParent)
        frame:SetWidth(320)
        frame:SetHeight(160)
        frame:SetPoint("CENTER", UIParent, "CENTER", 0, 100)
        frame:SetFrameStrata("DIALOG")
        frame:SetBackdrop({
            bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
            edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
            tile = true,
            tileSize = 32,
            edgeSize = 32,
            insets = { left = 11, right = 12, top = 12, bottom = 11 }
        })
        frame:SetMovable(true)
        frame:EnableMouse(true)
        frame:RegisterForDrag("LeftButton")
        frame:SetScript("OnDragStart", function()
            this:StartMoving()
        end)
        frame:SetScript("OnDragStop", function()
            this:StopMovingOrSizing()
        end)

        local closeButton = CreateFrame("Button", nil, frame, "UIPanelCloseButton")
        closeButton:SetPoint("TOPRIGHT", frame, "TOPRIGHT", -5, -5)

        local text = frame:CreateFontString("DFQT_POIFrameText", "OVERLAY", "GameFontNormal")
        text:SetPoint("TOPLEFT", frame, "TOPLEFT", 20, -20)
        text:SetWidth(280)
        text:SetJustifyH("LEFT")
        frame.text = text
    end

    -- Build the raw dump: header plus every key/value in the poi table
    local textStr = questTitle .. " (ID " .. tostring(questID) .. ")\n\npoi table:"
    for k, v in pairs(poi) do
        textStr = textStr .. "\n  " .. tostring(k) .. " = " .. tostring(v)
    end

    DFQT_POIFrame.text:SetText(textStr)
    DFQT_POIFrame:Show()
end

--[[
    Shows the options frame (created lazily on first call)

    Called from:
    - /dfqt and /dfqt2 slash commands
    - Right-click menu on the tracker's "All Objectives" header

    One checkbox per DFQT2.settings key. Checkbox states are re-synced from
    the settings table every time the frame is shown, and clicking a box
    writes straight back to DFQT2.settings (persisted via the DFQT2_Settings
    SavedVariable alias) followed by a tracker rebuild so visual settings
    apply immediately.
]]
function ShowOptionsFrame()
    if not DFQT2_OptionsFrame then
        local frame = CreateFrame("Frame", "DFQT2_OptionsFrame", UIParent)
        frame:SetWidth(300)
        frame:SetHeight(238)
        frame:SetPoint("CENTER", UIParent, "CENTER", 0, 80)
        frame:SetFrameStrata("DIALOG")
        frame:SetBackdrop({
            bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
            edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
            tile = true,
            tileSize = 32,
            edgeSize = 32,
            insets = { left = 11, right = 12, top = 12, bottom = 11 }
        })
        frame:SetMovable(true)
        frame:EnableMouse(true)
        frame:RegisterForDrag("LeftButton")
        frame:SetScript("OnDragStart", function()
            this:StartMoving()
        end)
        frame:SetScript("OnDragStop", function()
            this:StopMovingOrSizing()
        end)

        local closeButton = CreateFrame("Button", nil, frame, "UIPanelCloseButton")
        closeButton:SetPoint("TOPRIGHT", frame, "TOPRIGHT", -5, -5)

        local title = frame:CreateFontString(nil, "OVERLAY", "GameFontNormal")
        title:SetPoint("TOP", frame, "TOP", 0, -16)
        title:SetText("DragonFlight Quest Tracker 2")

        -- One checkbox per setting; label kept short so it fits the frame
        local optionDefs = {
            { key = "sortCurrentZoneFirst", label = "Sort current-zone quests to top" },
            { key = "showLevel", label = "Show quest level in title" },
            { key = "showToolTip", label = "Show quest tooltips" },
            { key = "turnInCelebration", label = "Turn-in celebration (sound + summary)" },
            { key = "highlightGossipTurnIn", label = "Highlight Quest Hand-In at NPC" },
            { key = "debugQuestEvents", label = "Debug messages in chat" }
        }

        frame.checkboxes = {}
        for index, def in ipairs(optionDefs) do
            local checkbox = CreateFrame("CheckButton", "DFQT2_OptionsCheck" .. index, frame,
                "UICheckButtonTemplate")
            checkbox:SetWidth(24)
            checkbox:SetHeight(24)
            checkbox:SetPoint("TOPLEFT", frame, "TOPLEFT", 20, -34 - (index - 1) * 28)
            getglobal(checkbox:GetName() .. "Text"):SetText(def.label)
            checkbox.settingKey = def.key

            checkbox:SetScript("OnClick", function()
                -- GetChecked() returns 1 or nil; store a proper boolean
                DFQT2.settings[this.settingKey] = (this:GetChecked() == 1)
                -- Rebuild so visual settings (marker, level, etc.) apply now
                questScanPending = true
            end)

            table.insert(frame.checkboxes, checkbox)
        end
    end

    -- Sync checkbox states from the live settings every time we open
    for _, checkbox in ipairs(DFQT2_OptionsFrame.checkboxes) do
        if DFQT2.settings[checkbox.settingKey] then
            checkbox:SetChecked(1)
        else
            checkbox:SetChecked(nil)
        end
    end

    DFQT2_OptionsFrame:Show()
end

-- EVENT HANDLING CODE
-- Quest-event debug prints are controlled by DFQT2.settings.debugQuestEvents
-- (options frame / DFQT2.SetDebug). Useful for verifying event order
-- (QUEST_TURNED_IN fires before QUEST_REMOVED on turn-ins) and that neither
-- fires on login/character-switch resyncs.

-- Formats the QUEST_TURNED_IN payload as "+N XP, Ng Ns Nc", omitting zero
-- parts. Returns nil when there is nothing to report (0 XP and 0 copper).
local function FormatRewardSummary(xp, money)
    local summary = nil
    if xp and xp > 0 then
        summary = "+" .. xp .. " XP"
    end
    if money and money > 0 then
        local gold = math.floor(money / 10000)
        local silver = math.floor(math.mod(money, 10000) / 100)
        local copper = math.mod(money, 100)
        local moneyText = ""
        if gold > 0 then
            moneyText = gold .. "g "
        end
        if silver > 0 or gold > 0 then
            moneyText = moneyText .. silver .. "s "
        end
        moneyText = moneyText .. copper .. "c"
        if summary then
            summary = summary .. ", " .. moneyText
        else
            summary = moneyText
        end
    end
    return summary
end

-- POI probe: the poi field in C_QuestLog.GetQuestDetails is unverified upstream
-- and rarely authored in vanilla quest data. Announce loudly whenever a quest
-- carrying POI data enters the log so a live example is never missed (todo.md).
-- Deliberately NOT gated on debugQuestEvents - this must survive debug-off.
local function CheckQuestForPOI(questID)
    local details = C_QuestLog.GetQuestDetails(questID)
    if not details then
        -- Not cached yet; QUEST_DATA_LOAD_RESULT re-runs this check when it lands
        C_QuestLog.RequestLoadQuestByID(questID)
        return
    end
    if details.poi then
        print("|cff33ff99DFQT2: POI data found on \"" .. tostring(details.title) ..
            "\" (questID " .. tostring(questID) ..
            ") - right-click it in the tracker and choose Show POI!|r")
    end
end

local eventFrame = CreateFrame("Frame")

--eventFrame:RegisterEvent("ADDON_LOADED")
eventFrame:RegisterEvent("PLAYER_LOGIN")
eventFrame:RegisterEvent("QUEST_LOG_UPDATE")
eventFrame:RegisterEvent("QUEST_ACCEPTED")  -- ClassicAPI: (questLogIndex, questID)
eventFrame:RegisterEvent("QUEST_TURNED_IN") -- ClassicAPI: (questID, xpReward, moneyReward)
eventFrame:RegisterEvent("QUEST_REMOVED")   -- ClassicAPI: (questID) - fires on turn-ins AND abandons
eventFrame:RegisterEvent("QUEST_DATA_LOAD_RESULT") -- ClassicAPI: (questID, success 1/nil) - for the POI probe
eventFrame:RegisterEvent("QUEST_TIMER_START")      -- native 1.12: a quest timer began
eventFrame:RegisterEvent("QUEST_TIMER_FINISHED")   -- native 1.12: a quest timer ended or expired
eventFrame:RegisterEvent("ZONE_CHANGED_NEW_AREA")  -- native 1.12: entered a new zone - re-sort zone priority
eventFrame:RegisterEvent("GOSSIP_SHOW")            -- native 1.12: gossip NPC window opened
eventFrame:RegisterEvent("QUEST_GREETING")         -- native 1.12: quest-only NPC window opened
eventFrame:RegisterEvent("GOSSIP_CLOSED")          -- native 1.12: NPC window closed
eventFrame:RegisterEvent("QUEST_FINISHED")         -- native 1.12: quest window closed (greeting path)

eventFrame:SetScript("OnEvent", function()
    if event == "PLAYER_LOGIN" then
        -- Merge persisted settings over the defaults, then alias the
        -- SavedVariable to the live table so every later change (options
        -- frame, /script) persists automatically at logout
        if DFQT2_Settings then
            for key, value in pairs(DFQT2_Settings) do
                DFQT2.settings[key] = value
            end
        end
        DFQT2_Settings = DFQT2.settings

        -- Load or set frame position
        if DFQT_FramePosition then
            -- Restore saved position
            QuestTrackerFrame:ClearAllPoints()
            QuestTrackerFrame:SetPoint(
                DFQT_FramePosition.point,
                UIParent,
                DFQT_FramePosition.relativePoint,
                DFQT_FramePosition.xOfs,
                DFQT_FramePosition.yOfs
            )
            --print("DragonFlight Quest Tracker - Restored saved position")
        else
            -- No saved position, use default: bottom of MinimapCluster
            QuestTrackerFrame:ClearAllPoints()
            QuestTrackerFrame:SetPoint("TOP", "Minimap", "BOTTOM", -20, -60)
            --print("DragonFlight Quest Tracker - Using default position (below minimap)")
        end

        eventFrame:UnregisterEvent("PLAYER_LOGIN")
    elseif event == "QUEST_ACCEPTED" then
        -- ClassicAPI event: arg1 = questLogIndex, arg2 = questID.
        -- Fires once per genuinely accepted quest (NPC accept, party share,
        -- auto-grant) and never on login resync, so no initialLoad guard needed.
        if DFQT2.settings.debugQuestEvents then
            print("DFQT2: QUEST_ACCEPTED - logIndex " .. tostring(arg1) .. ", questID " .. tostring(arg2))
        end
        if not newQuestsToAnimate then
            newQuestsToAnimate = {}
        end
        table.insert(newQuestsToAnimate, arg2)
        questScanPending = true

        -- Probe the newly accepted quest for POI data (requests a cache load
        -- if needed; the check re-runs on QUEST_DATA_LOAD_RESULT below)
        CheckQuestForPOI(arg2)
    elseif event == "QUEST_DATA_LOAD_RESULT" then
        -- ClassicAPI event: arg1 = questID, arg2 = 1 on success / nil on failure.
        -- Fired in response to CheckQuestForPOI's RequestLoadQuestByID (and any
        -- other cache loads, e.g. the right-click menu's probe) - re-run the
        -- POI check now that the quest's static data is cached.
        if arg2 == 1 then
            CheckQuestForPOI(arg1)

            -- Fill the source-item cache and rebuild the tracker so the quest
            -- item button can appear for this quest
            local details = C_QuestLog.GetQuestDetails(arg1)
            if details then
                questSrcItemCache[arg1] = details.srcItemID or 0
                if questSrcItemCache[arg1] > 0 then
                    questScanPending = true
                end
            end
        end
    elseif event == "QUEST_TURNED_IN" then
        -- ClassicAPI event: arg1 = questID, arg2 = xpReward, arg3 = moneyReward.
        -- Server-confirmed turn-in only (never fires on abandon or window close).
        -- Objective-state cleanup happens in QUEST_REMOVED, which fires after
        -- this event.
        if DFQT2.settings.debugQuestEvents then
            print("DFQT2: QUEST_TURNED_IN - questID " .. tostring(arg1) ..
                ", xp " .. tostring(arg2) .. ", money " .. tostring(arg3) .. " copper")
        end

        -- Turn-in celebration (toggleable): completion sound + gold chat line
        -- with the server-confirmed rewards. The visual send-off is the
        -- existing QUEST_REMOVED fade-out, so no extra animation here.
        if DFQT2.settings.turnInCelebration then
            PlaySoundFile("Interface\\AddOns\\DragonFlightQuestTracker2\\sounds\\quest_objective_complete.ogg", "SFX")
            local questTitle = C_QuestLog.GetTitleForQuestID(arg1)
            local message = "|cffffd100" .. (questTitle or "Quest") .. " completed!|r"
            local summary = FormatRewardSummary(arg2, arg3)
            if summary then
                message = message .. " " .. summary
            end
            print(message)
        end

        questScanPending = true
    elseif event == "QUEST_REMOVED" then
        -- ClassicAPI event: arg1 = questID. Fires once per quest leaving the
        -- log, covering BOTH turn-ins and abandons (never on login/character
        -- resync). Drop the quest's tracked objective state so it doesn't leak
        -- for the session, and so a later re-accept of the same quest starts
        -- clean (stale objective descriptions would otherwise trigger a false
        -- progress detection on the first scan after re-accept).
        if DFQT2.settings.debugQuestEvents then
            print("DFQT2: QUEST_REMOVED - questID " .. tostring(arg1) .. " (objective state cleared)")
        end
        questObjectiveStates[arg1] = nil
        questSrcItemCache[arg1] = nil
        questTimerTotals[arg1] = nil

        -- Retail-style exit: fade the removed quest's button out and postpone
        -- the rebuild briefly so the fade is visible. Applies to both turn-ins
        -- and abandons. No button (minimized section, scrolled out of view,
        -- sections hidden) means no fade and no delay.
        local removedButton = FindQuestButtonByQuestID(arg1)
        if removedButton then
            FadeOutFrame(removedButton, 0.7)
            questScanDelayUntil = GetTime() + 0.75
        end
        questScanPending = true
    elseif event == "QUEST_TIMER_START" or event == "QUEST_TIMER_FINISHED" then
        -- Native 1.12 events. Rebuild so the countdown bar appears/disappears;
        -- the per-second value updates run on the C_Timer ticker, not here.
        questScanPending = true
    elseif event == "GOSSIP_SHOW" or event == "QUEST_GREETING" then
        -- Record which tracked quests this NPC will accept turn-in for right
        -- now. GetActiveQuests()'s isComplete is server-confirmed accurate on
        -- Turtle (verified in-game 2026-07-06). A rescan applies both the glow
        -- (CreateQuestButtons, gated on gossipReadyQuestIDs) and the sort-to-
        -- top (below), so both come from one source of truth. Cleared on
        -- GOSSIP_CLOSED/QUEST_FINISHED.
        if DFQT2.settings.highlightGossipTurnIn then
            gossipReadyQuestIDs = {}
            local activeQuests = C_GossipInfo.GetActiveQuests()
            for i = 1, table.getn(activeQuests) do
                local q = activeQuests[i]
                if q.isComplete then
                    gossipReadyQuestIDs[q.questID] = true
                end
            end
            questScanPending = true
        end
    elseif event == "GOSSIP_CLOSED" or event == "QUEST_FINISHED" then
        -- Clear any turn-in highlight/sort - the player has left this NPC's window
        if next(gossipReadyQuestIDs) then
            gossipReadyQuestIDs = {}
            questScanPending = true
        end
    elseif event == "ZONE_CHANGED_NEW_AREA" then
        -- Re-scan so zone-priority sorting and chevrons reflect the new zone.
        -- With debug on, ask the scan to report what it files under the new
        -- zone (the scan computes the inZone flags, so it does the reporting)
        if DFQT2.settings.debugQuestEvents then
            zoneChangeDebugPending = true
        end
        questScanPending = true
    elseif event == "QUEST_LOG_UPDATE" then
        -- Set pending flag instead of calling directly.
        -- Multiple QUEST_LOG_UPDATE events fired by ExpandQuestHeader() in a single
        -- frame are collapsed into one scan by the OnUpdate handler below, preventing
        -- repeated full UI rebuilds that freeze the client with a full quest log.
        questScanPending = true

        -- Hide the default QuestTracker Frame
        if QuestWatchFrame then
            --QuestWatchFrame:Hide()
            --QuestWatchFrame:UnregisterAllEvents()
        end
    end
end)

-- Consume the pending scan flag once per frame.
-- OnUpdate fires after all queued events for the frame have been processed,
-- so no matter how many QUEST_LOG_UPDATE events fired this frame, we only
-- call GetPlayerQuests() once.
eventFrame:SetScript("OnUpdate", function()
    if questScanPending then
        -- Postpone while a removal fade-out is playing (set by QUEST_REMOVED);
        -- the pending flag survives, so the scan runs as soon as the delay ends
        if questScanDelayUntil and GetTime() < questScanDelayUntil then
            return
        end
        questScanDelayUntil = nil
        questScanPending = false
        GetPlayerQuests()
    end
end)
QuestTrackerFrame:Show()

-- Suppress Blizzard's default quest timer frame (top of screen) - the tracker's
-- own countdown bars replace it. Unregistering the events stops it reacting to
-- timer starts, and the no-op Show() blocks any code path that force-shows it
-- (QuestTimer_Update calls Show directly when a timer is running at login).
QuestTimerFrame:UnregisterAllEvents()
QuestTimerFrame:Hide()
QuestTimerFrame.Show = function() end

-- ============================================================================
-- Public namespace entry points. The DFQT2 table itself (with its settings)
-- is created near the top of the file so settings are in scope everywhere;
-- anything worth reaching from /script macros is attached here. Every other
-- function in this file is file-local.

-- /script DFQT2.Rescan() - force a full quest-log rescan and tracker rebuild
function DFQT2.Rescan()
    questScanPending = true
end

-- /dfqt (or /dfqt2) - open the options window
SLASH_DFQT21 = "/dfqt"
SLASH_DFQT22 = "/dfqt2"
SlashCmdList["DFQT2"] = function()
    ShowOptionsFrame()
end

-- /script DFQT2.SetDebug(true|false) - toggle quest-event debug chat output
function DFQT2.SetDebug(enabled)
    DFQT2.settings.debugQuestEvents = enabled
end

-- /script DFQT2.ZoneReport() - diagnose zone-priority matching: prints the
-- exact current zone text, every quest-log header (bracketed so stray spaces
-- are visible), whether each header matches, and a chevron render test
function DFQT2.ZoneReport()
    local zone = GetRealZoneText()
    print("DFQT2: GetRealZoneText() = [" .. tostring(zone) .. "]")
    print("DFQT2: GetZoneText()     = [" .. tostring(GetZoneText()) .. "]")
    print("DFQT2: marker render test: |cff88ccff**|r  <- should be a blue **")
    local numEntries = GetNumQuestLogEntries()
    for i = 1, numEntries do
        local title, _, _, isHeader = GetQuestLogTitle(i)
        if isHeader then
            if title == zone then
                print("DFQT2: header [" .. tostring(title) .. "]  <== MATCHES current zone")
            else
                print("DFQT2: header [" .. tostring(title) .. "]")
            end
        end
    end
end

-- /script DFQT2.ShowPOI(questID) - dump POI data for ANY questID, not just
-- quests in the log. Requests a cache load when the quest isn't cached yet;
-- run it again a moment later in that case.
function DFQT2.ShowPOI(questID)
    local details = C_QuestLog.GetQuestDetails(questID)
    if not details then
        C_QuestLog.RequestLoadQuestByID(questID)
        print("DFQT2: quest " .. tostring(questID) .. " not cached yet - load requested, try again in a second")
    elseif details.poi then
        ShowPOIFrame(details.title or "?", questID, details.poi)
    else
        print("DFQT2: quest " .. tostring(questID) .. " (" .. tostring(details.title) .. ") has no POI data")
    end
end
