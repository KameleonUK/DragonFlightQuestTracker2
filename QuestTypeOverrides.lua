-- QuestTypeOverrides.lua
-- Local overrides for quest categorisation when the server tag is wrong.
-- Valid types: "normal", "elite", "dungeon", "raid", "pvp"
--
-- Keys can be either a questID (preferred - unambiguous and locale-proof)
-- or an exact quest title (legacy v1 style). If both exist for the same
-- quest, the questID key wins.
--
-- Usage:
--   [questID] = "type",
--   ["Exact Quest Title"] = "type",
--
-- Example:
--   [7734] = "dungeon",                -- questID key (preferred)
--   ["Warsong Gulch"] = "pvp",         -- title key (legacy)

DFQT_QuestTypeOverrides = {
    -- Add overrides below this line
    ["Tainted Brambleheart"] = 'dungeon'
}
