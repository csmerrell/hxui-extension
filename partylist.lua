require('common');
require('helpers');
local imgui = require('imgui');
local fonts = require('fonts');
local primitives = require('primitives');
local statusHandler = require('statushandler');
local buffTable = require('bufftable');
local progressbar = require('progressbar');
local encoding = require('gdifonts.encoding');
local ashita_settings = require('settings');
local ffi = require('ffi');
local struct = require('struct');
local chat = require('chat');

-- Treasure pool library will be initialized when needed
local treasurePoolLib = require('treasurepool');
local treasurePoolInitialized = false;

local fullMenuWidth = {};
local fullMenuHeight = {};
local buffWindowX = {};
local debuffWindowX = {};

-- local backgroundPrim = {};
local partyWindowPrim = {};
partyWindowPrim[1] = {
    background = {},
}
partyWindowPrim[2] = {
    background = {},
}
partyWindowPrim[3] = {
    background = {},
}

local selectionPrim;
local arrowPrim;
local treasureIconPrim;
local partyTargeted;
local partySubTargeted;
local memberText = {};
local partyMaxSize = 6;
local memberTextCount = partyMaxSize * 3;

local borderConfig = {1, '#243e58'};

local bgImageKeys = { 'bg', 'tl', 'tr', 'br', 'bl' };
local bgTitleAtlasItemCount = 4;
local bgTitleItemHeight;
local loadedBg = nil;

local partyList = {};

-- Treasure Pool variables
local treasurePoolVisible = true;
local treasurePoolWindowPos = { x = 300, y = 200 };
local treasurePoolWindowPrim = {
    background = {},
};

-- Treasure Pool data structures
local treasurePoolWinnableItems = {}; -- Winnable items (player hasn't lotted or is currently winning)
local treasurePoolLostItems = {}; -- Lost items (player has lost or passed)
local treasurePoolLastUpdate = 0; -- Timer for polling
local treasurePoolLastMode = nil; -- Track mock vs real data mode
local treasurePoolActivePollInterval = 0.25; -- 4x per second when items present
local treasurePoolIdlePollInterval = 1.0; -- 1x per second when no items


-- Treasure Pool Controller variables
local treasurePoolControllerActive = false; -- Whether controller has focus
local treasurePoolSelected = 1; -- Currently selected item index (1-based)
local treasurePoolInputCB = false; -- Track if input callback is registered

-- Debug variables
local lastDebugTime = 0;
local debugInterval = 5.0; -- Print debug every 5 seconds
local lastPruningMessages = {}; -- Track last pruning messages to prevent spam
local pruningDebounceTime = 5.0; -- 5 seconds between repeat pruning messages

-- Trigger state tracking for tCrossBar conflict avoidance
local triggerPressed = {
    L2 = false,
    R2 = false
};

-- Treasure pool timestamp tracking
local treasurePoolTimestamps = {}; -- Track when items entered the pool
local treasurePoolAutoDistributeTime = 5 * 60; -- 5 minutes in seconds

-- RB hold tracking for toggle functionality
local rbPressTime = 0; -- Time when RB was pressed
local rbHoldThreshold = 1.0; -- 1 second to trigger toggle
local rbPressed = false; -- Track if RB is currently pressed
local rbToggleTriggered = false; -- Flag to prevent multiple toggles during single hold

-- Format remaining time for treasure pool items
local function FormatRemainingTime(remainingSeconds)
    if (remainingSeconds <= 0) then
        return "(0s)";
    elseif (remainingSeconds >= 60) then
        local minutes = math.floor(remainingSeconds / 60);
        return string.format("(%dm)", minutes);
    else
        return string.format("(%ds)", math.floor(remainingSeconds));
    end
end

-- Update treasure pool item timestamps
local function UpdateTreasurePoolTimestamps(items)
    local currentTime = os.clock();
    
    -- Track new items and update timestamps
    for i, item in ipairs(items) do
        local itemKey = item.item; -- Use item name as key
        if (not treasurePoolTimestamps[itemKey]) then
            -- New item detected, record timestamp
            treasurePoolTimestamps[itemKey] = currentTime;
        end
    end
    
    -- Clean up timestamps for items that are no longer in the pool
    local activeItems = {};
    for i, item in ipairs(items) do
        activeItems[item.item] = true;
    end
    
    for itemKey, timestamp in pairs(treasurePoolTimestamps) do
        if (not activeItems[itemKey]) then
            treasurePoolTimestamps[itemKey] = nil;
        end
    end
end

-- Mock data initialization (only for preview mode)
local treasurePoolMockData = {
    { item = "Damascus Ingot", slotIndex = 0, myLot = "--", waitingFor = "Player1, Player2", currentWinner = "(450) Player3" },
    { item = "Damascus Ingot", slotIndex = 2, myLot = "--", waitingFor = "Player1, Player2", currentWinner = "--" },
    { item = "Damascus Ingot", slotIndex = 5, myLot = "250, 300", waitingFor = "Player3", currentWinner = "(300) Player1" },
    { item = "Damascus Ingot", slotIndex = 7, myLot = "150", waitingFor = "", currentWinner = "(150) Player1" },
    { item = "Hi-Potion", slotIndex = 1, myLot = "--", waitingFor = "Player1, Player2, Player3", currentWinner = "--" },
    { item = "Hi-Potion", slotIndex = 3, myLot = "PASS", waitingFor = "", currentWinner = "(999) Player5" },
    { item = "Ancient Currency", slotIndex = 4, myLot = "--", waitingFor = "Player2", currentWinner = "(300) Player4" },
};

-- Consolidate mock treasure pool items by name into separate rows per lot status (for preview mode)
local function ConsolidateMockTreasurePoolItems(mockData)
    local winnableItems = {};
    local lostItems = {};
    
    -- First, categorize mock data into winnable/lost based on lot status
    for _, item in ipairs(mockData) do
        if (item.myLot == "PASS") then
            item.winner = item.currentWinner:match("%((%d+)%) (.+)") or "Unknown";
            table.insert(lostItems, item);
        else
            table.insert(winnableItems, item);
        end
    end
    
    -- Now consolidate by item name and lot status separately
    local itemCategories = {}; -- [itemName] = { notLotted = {}, winning = {}, lost = {} }
    
    -- Process winnable items
    for _, item in ipairs(winnableItems) do
        local itemName = item.item;
        if (not itemCategories[itemName]) then
            itemCategories[itemName] = { notLotted = {}, winning = {}, lost = {} };
        end
        
        if (item.myLot == "--") then
            table.insert(itemCategories[itemName].notLotted, item);
        else
            table.insert(itemCategories[itemName].winning, item);
        end
    end
    
    -- Process lost items
    for _, item in ipairs(lostItems) do
        local itemName = item.item;
        if (not itemCategories[itemName]) then
            itemCategories[itemName] = { notLotted = {}, winning = {}, lost = {} };
        end
        table.insert(itemCategories[itemName].lost, item);
    end
    
    local consolidatedWinnable = {};
    local consolidatedLost = {};
    
    -- Create consolidated entries with separate rows per lot status
    for itemName, categories in pairs(itemCategories) do
        local notLottedCount = #categories.notLotted;
        local winningCount = #categories.winning;
        local lostCount = #categories.lost;
        
        -- Create "not lotted" row if we have items we haven't lotted
        if (notLottedCount > 0) then
            -- Sort by slot index (ascending for consistent ordering)
            table.sort(categories.notLotted, function(a, b) return a.slotIndex < b.slotIndex end);
            local firstItem = categories.notLotted[1]; -- For sorting position
            local lastItem = categories.notLotted[#categories.notLotted]; -- For actions
            
            local displayName = itemName;
            if (notLottedCount > 1) then
                displayName = string.format("%s x%d", itemName, notLottedCount);
            end
            
            -- Aggregate waiting players (remove duplicates)
            local allWaitingPlayers = {};
            local waitingPlayerSet = {};
            for _, item in ipairs(categories.notLotted) do
                if (item.waitingFor and item.waitingFor ~= "") then
                    for player in string.gmatch(item.waitingFor, "([^,]+)") do
                        player = player:match("^%s*(.-)%s*$"); -- trim whitespace
                        if (player ~= "" and not waitingPlayerSet[player]) then
                            waitingPlayerSet[player] = true;
                            table.insert(allWaitingPlayers, player);
                        end
                    end
                end
            end
            
            -- Get current winner info
            local currentWinner = "--";
            for _, item in ipairs(categories.notLotted) do
                if (item.currentWinner and item.currentWinner ~= "--") then
                    currentWinner = item.currentWinner;
                    break;
                end
            end
            
            local consolidatedItem = {
                item = displayName,
                slotIndex = firstItem.slotIndex, -- Use first item's slot for sorting
                actionSlotIndex = lastItem.slotIndex, -- Use last item's slot for actions
                myLot = "--",
                currentWinner = currentWinner,
                waitingFor = table.concat(allWaitingPlayers, ", "),
                consolidatedCount = notLottedCount
            };
            
            table.insert(consolidatedWinnable, consolidatedItem);
        end
        
        -- Create "winning" row if we have items we're winning
        if (winningCount > 0) then
            -- Sort by slot index (ascending for consistent ordering)
            table.sort(categories.winning, function(a, b) return a.slotIndex < b.slotIndex end);
            local firstItem = categories.winning[1]; -- For sorting position
            local lastItem = categories.winning[#categories.winning]; -- For actions
            
            local displayName = itemName;
            if (winningCount > 1) then
                displayName = string.format("%s x%d", itemName, winningCount);
            end
            
            -- Collect my lot values for display
            local myLots = {};
            for _, item in ipairs(categories.winning) do
                if (item.myLot and item.myLot ~= "--" and item.myLot ~= "PASS") then
                    table.insert(myLots, item.myLot);
                end
            end
            local lotDisplay = table.concat(myLots, ", ");
            
            -- Aggregate waiting players (remove duplicates)
            local allWaitingPlayers = {};
            local waitingPlayerSet = {};
            for _, item in ipairs(categories.winning) do
                if (item.waitingFor and item.waitingFor ~= "") then
                    for player in string.gmatch(item.waitingFor, "([^,]+)") do
                        player = player:match("^%s*(.-)%s*$"); -- trim whitespace
                        if (player ~= "" and not waitingPlayerSet[player]) then
                            waitingPlayerSet[player] = true;
                            table.insert(allWaitingPlayers, player);
                        end
                    end
                end
            end
            
            -- Get current winner info
            local currentWinner = "--";
            for _, item in ipairs(categories.winning) do
                if (item.currentWinner and item.currentWinner ~= "--") then
                    currentWinner = item.currentWinner;
                    break;
                end
            end
            
            local consolidatedItem = {
                item = displayName,
                slotIndex = firstItem.slotIndex, -- Use first item's slot for sorting
                actionSlotIndex = lastItem.slotIndex, -- Use last item's slot for actions
                myLot = lotDisplay,
                currentWinner = currentWinner,
                waitingFor = table.concat(allWaitingPlayers, ", "),
                consolidatedCount = winningCount
            };
            
            table.insert(consolidatedWinnable, consolidatedItem);
        end
        
        -- Create consolidated lost entry if we have lost items
        if (lostCount > 0) then
            -- Sort by slot index (ascending for consistent ordering)
            table.sort(categories.lost, function(a, b) return a.slotIndex < b.slotIndex end);
            local firstItem = categories.lost[1]; -- For sorting position
            
            local displayName = itemName;
            if (lostCount > 1) then
                displayName = string.format("%s x%d", itemName, lostCount);
            end
            
            local consolidatedItem = {
                item = displayName,
                slotIndex = firstItem.slotIndex,
                winner = firstItem.winner or "Unknown",
                consolidatedCount = lostCount
            };
            
            table.insert(consolidatedLost, consolidatedItem);
        end
    end
    
    -- Sort consolidated items by slot index (ascending)
    table.sort(consolidatedWinnable, function(a, b) return a.slotIndex < b.slotIndex end);
    table.sort(consolidatedLost, function(a, b) return a.slotIndex < b.slotIndex end);
    
    return consolidatedWinnable, consolidatedLost;
end

-- Refresh real treasure pool data from Ashita APIs using the treasure pool library
local function RefreshTreasurePoolData()
    -- Initialize treasure pool library if not already done
    if (not treasurePoolInitialized) then
        treasurePoolLib.Initialize(AshitaCore);
        treasurePoolInitialized = true;
    end
    
    local winnableItems, lostItems;
    
    -- Check if consolidation is enabled and use appropriate function
    if (gConfig and gConfig.treasurePoolConsolidateItems) then
        winnableItems, lostItems = treasurePoolLib.GetConsolidatedTreasurePoolData();
    else
        winnableItems, lostItems = treasurePoolLib.GetTreasurePoolData();
    end
    
    -- Update our local data structures
    treasurePoolWinnableItems = winnableItems;
    treasurePoolLostItems = lostItems;
    
    -- Update timestamps for winnable items
    UpdateTreasurePoolTimestamps(treasurePoolWinnableItems);
end

-- Initialize treasure pool items with mock data (for preview mode)
local function InitializeTreasurePoolItems()
    -- Clear any existing data first
    treasurePoolWinnableItems = {};
    treasurePoolLostItems = {};
    
    local currentTime = os.clock();
    
    -- Check if consolidation is enabled
    if (gConfig and gConfig.treasurePoolConsolidateItems) then
        -- Use consolidated mock data
        treasurePoolWinnableItems, treasurePoolLostItems = ConsolidateMockTreasurePoolItems(treasurePoolMockData);
        
        -- Set timestamps for consolidated items
        for i, item in ipairs(treasurePoolWinnableItems) do
            local itemKey = item.item;
            if (not treasurePoolTimestamps[itemKey]) then
                treasurePoolTimestamps[itemKey] = currentTime - (i * 30);
            end
        end
        for i, item in ipairs(treasurePoolLostItems) do
            local itemKey = item.item;
            if (not treasurePoolTimestamps[itemKey]) then
                treasurePoolTimestamps[itemKey] = currentTime - (i * 30);
            end
        end
    else
        -- Use original mock data without consolidation
        for i, item in ipairs(treasurePoolMockData) do
            if (item.myLot == "PASS") then
                -- Extract winner name from currentWinner string
                local winner = item.currentWinner:match("%((%d+)%) (.+)") or "Unknown";
                table.insert(treasurePoolLostItems, {
                    item = item.item,
                    winner = winner
                });
            else
                table.insert(treasurePoolWinnableItems, {
                    item = item.item,
                    myLot = item.myLot,
                    waitingFor = item.waitingFor,
                    currentWinner = item.currentWinner
                });
            end
            
            -- For mock data, stagger timestamps to show different countdown times
            local itemKey = item.item;
            if (not treasurePoolTimestamps[itemKey]) then
                -- Add some variation to timestamps for demo purposes
                treasurePoolTimestamps[itemKey] = currentTime - (i * 30); -- Each item 30 seconds older
            end
        end
    end
end

-- Force a complete reset of treasure pool data
local function ResetTreasurePoolData()
    treasurePoolWinnableItems = {};
    treasurePoolLostItems = {};
    treasurePoolLastUpdate = 0; -- Force immediate refresh on next update
end

-- Check if we should use mock data (preview mode)
local function ShouldUseMockData()
    -- Use mock data when config menu is open AND "Preview full party list" is active
    return (showConfig[1] and gConfig.partyListPreview);
end

-- Update treasure pool data with polling timer
local function UpdateTreasurePoolData()
    local currentTime = os.clock();
    local shouldUseMock = ShouldUseMockData();
    local hasItems = (#treasurePoolWinnableItems > 0);
    local pollInterval = hasItems and treasurePoolActivePollInterval or treasurePoolIdlePollInterval;
    
    -- Always force a reset when switching between mock and real data modes
    local lastMode = treasurePoolLastMode or false; -- Track previous mode
    if shouldUseMock ~= lastMode then
        ResetTreasurePoolData();
        treasurePoolLastMode = shouldUseMock;
    end
    
    if (currentTime - treasurePoolLastUpdate) >= pollInterval then
        if shouldUseMock then
            InitializeTreasurePoolItems();
        else
            RefreshTreasurePoolData();
        end
        treasurePoolLastUpdate = currentTime;
    end
end


local function getScale(partyIndex)
    if (partyIndex == 3) then
        return {
            x = gConfig.partyList3ScaleX,
            y = gConfig.partyList3ScaleY,
            icon = gConfig.partyList3JobIconScale,
        }
    elseif (partyIndex == 2) then
        return {
            x = gConfig.partyList2ScaleX,
            y = gConfig.partyList2ScaleY,
            icon = gConfig.partyList2JobIconScale,
        }
    else
        return {
            x = gConfig.partyListScaleX,
            y = gConfig.partyListScaleY,
            icon = gConfig.partyListJobIconScale,
        }
    end
end

local function showPartyTP(partyIndex)
    if (partyIndex == 3) then
        return gConfig.partyList3TP
    elseif (partyIndex == 2) then
        return gConfig.partyList2TP
    else
        return gConfig.partyListTP
    end
end

local function UpdateTextVisibilityByMember(memIdx, visible)

    memberText[memIdx].hp:SetVisible(visible);
    memberText[memIdx].mp:SetVisible(visible);
    memberText[memIdx].tp:SetVisible(visible);
    memberText[memIdx].name:SetVisible(visible);
end

local function UpdateTextVisibility(visible, partyIndex)
    if partyIndex == nil then
        for i = 0, memberTextCount - 1 do
            UpdateTextVisibilityByMember(i, visible);
        end
    else
        local firstPlayerIndex = (partyIndex - 1) * partyMaxSize;
        local lastPlayerIndex = firstPlayerIndex + partyMaxSize - 1;
        for i = firstPlayerIndex, lastPlayerIndex do
            UpdateTextVisibilityByMember(i, visible);
        end
    end

    for i = 1, 3 do
        if (partyIndex == nil or i == partyIndex) then
            partyWindowPrim[i].bgTitle.visible = visible and gConfig.showPartyListTitle;
            local backgroundPrim = partyWindowPrim[i].background;
            for _, k in ipairs(bgImageKeys) do
                backgroundPrim[k].visible = visible and backgroundPrim[k].exists;
            end
        end
    end
end

local function GetMemberInformation(memIdx)

    if (showConfig[1] and gConfig.partyListPreview) then
        local memInfo = {};
        memInfo.hpp = memIdx == 4 and 0.1 or memIdx == 2 and 0.5 or memIdx == 0 and 0.75 or 1;
        memInfo.maxhp = 1250;
        memInfo.hp = math.floor(memInfo.maxhp * memInfo.hpp);
        memInfo.mpp = memIdx == 1 and 0.1 or 0.75;
        memInfo.maxmp = 1000;
        memInfo.mp = math.floor(memInfo.maxmp * memInfo.mpp);
        memInfo.tp = 1500;
        memInfo.job = memIdx + 1;
        memInfo.level = 99;
        memInfo.targeted = memIdx == 4;
        memInfo.serverid = 0;
        memInfo.buffs = nil;
        memInfo.sync = false;
        memInfo.subTargeted = false;
        memInfo.zone = 100;
        memInfo.inzone = memIdx ~= 3;
        memInfo.name = 'Player ' .. (memIdx + 1);
        memInfo.leader = memIdx == 0 or memIdx == 6 or memIdx == 12;
        return memInfo
    end

    local party = AshitaCore:GetMemoryManager():GetParty();
    local player = AshitaCore:GetMemoryManager():GetPlayer();
    if (player == nil or party == nil or party:GetMemberIsActive(memIdx) == 0) then
        return nil;
    end

    local playerTarget = AshitaCore:GetMemoryManager():GetTarget();

    local partyIndex = math.ceil((memIdx + 1) / partyMaxSize);
    local partyLeaderId = nil
    if (partyIndex == 3) then
        partyLeaderId = party:GetAlliancePartyLeaderServerId3();
    elseif (partyIndex == 2) then
        partyLeaderId = party:GetAlliancePartyLeaderServerId2();
    else
        partyLeaderId = party:GetAlliancePartyLeaderServerId1();
    end

    local memberInfo = {};
    memberInfo.zone = party:GetMemberZone(memIdx);
    memberInfo.inzone = memberInfo.zone == party:GetMemberZone(0);
    memberInfo.name = party:GetMemberName(memIdx);
    memberInfo.leader = partyLeaderId == party:GetMemberServerId(memIdx);

    if (memberInfo.inzone == true) then
        memberInfo.hp = party:GetMemberHP(memIdx);
        memberInfo.hpp = party:GetMemberHPPercent(memIdx) / 100;
        memberInfo.maxhp = memberInfo.hp / memberInfo.hpp;
        memberInfo.mp = party:GetMemberMP(memIdx);
        memberInfo.mpp = party:GetMemberMPPercent(memIdx) / 100;
        memberInfo.maxmp = memberInfo.mp / memberInfo.mpp;
        memberInfo.tp = party:GetMemberTP(memIdx);
        memberInfo.job = party:GetMemberMainJob(memIdx);
        memberInfo.level = party:GetMemberMainJobLevel(memIdx);
        memberInfo.serverid = party:GetMemberServerId(memIdx);
        if (playerTarget ~= nil) then
            local t1, t2 = GetTargets();
            local sActive = GetSubTargetActive();
            local thisIdx = party:GetMemberTargetIndex(memIdx);
            memberInfo.targeted = (t1 == thisIdx and not sActive) or (t2 == thisIdx and sActive);
            memberInfo.subTargeted = (t1 == thisIdx and sActive);
        else
            memberInfo.targeted = false;
            memberInfo.subTargeted = false;
        end
        if (memIdx == 0) then
            memberInfo.buffs = player:GetBuffs();
        else
            memberInfo.buffs = statusHandler.get_member_status(memberInfo.serverid);
        end
        memberInfo.sync = bit.band(party:GetMemberFlagMask(memIdx), 0x100) == 0x100;

    else
        memberInfo.hp = 0;
        memberInfo.hpp = 0;
        memberInfo.maxhp = 0;
        memberInfo.mp = 0;
        memberInfo.mpp = 0;
        memberInfo.maxmp = 0;
        memberInfo.tp = 0;
        memberInfo.job = '';
        memberInfo.level = '';
        memberInfo.targeted = false;
        memberInfo.serverid = 0;
        memberInfo.buffs = nil;
        memberInfo.sync = false;
        memberInfo.subTargeted = false;
    end

    return memberInfo;
end

local function DrawMember(memIdx, settings)

    local memInfo = GetMemberInformation(memIdx);
    if (memInfo == nil) then
        -- dummy data to render an empty space
        memInfo = {};
        memInfo.hp = 0;
        memInfo.hpp = 0;
        memInfo.maxhp = 0;
        memInfo.mp = 0;
        memInfo.mpp = 0;
        memInfo.maxmp = 0;
        memInfo.tp = 0;
        memInfo.job = '';
        memInfo.level = '';
        memInfo.targeted = false;
        memInfo.serverid = 0;
        memInfo.buffs = nil;
        memInfo.sync = false;
        memInfo.subTargeted = false;
        memInfo.zone = '';
        memInfo.inzone = false;
        memInfo.name = '';
        memInfo.leader = false;
    end

    local partyIndex = math.ceil((memIdx + 1) / partyMaxSize);
    local scale = getScale(partyIndex);
    local showTP = showPartyTP(partyIndex);

    local subTargetActive = GetSubTargetActive();
    local nameSize = SIZE.new();
    local hpSize = SIZE.new();
    memberText[memIdx].name:GetTextSize(nameSize);
    memberText[memIdx].hp:GetTextSize(hpSize);

    -- Get the hp color for bars and text
    local hpNameColor, hpGradient = GetHpColors(memInfo.hpp);

    local bgGradientOverride = {'#000813', '#000813'};

    local hpBarWidth = settings.hpBarWidth * scale.x;
    local mpBarWidth = settings.mpBarWidth * scale.x;
    local tpBarWidth = settings.tpBarWidth * scale.x;
    local barHeight = settings.barHeight * scale.y;

    local allBarsLengths = hpBarWidth + mpBarWidth + imgui.GetStyle().FramePadding.x + imgui.GetStyle().ItemSpacing.x;
    if (showTP) then
        allBarsLengths = allBarsLengths + tpBarWidth + imgui.GetStyle().FramePadding.x + imgui.GetStyle().ItemSpacing.x;
    end

    local hpStartX, hpStartY = imgui.GetCursorScreenPos();

    -- Draw the job icon before we draw anything else
    local namePosX = hpStartX;
    local jobIconSize = settings.iconSize * 1.1 * scale.icon;
    local offsetStartY = hpStartY - jobIconSize - settings.nameTextOffsetY;
    imgui.SetCursorScreenPos({namePosX, offsetStartY});
    local jobIcon = statusHandler.GetJobIcon(memInfo.job);
    if (jobIcon ~= nil) then
        namePosX = namePosX + jobIconSize + settings.nameTextOffsetX;
        imgui.Image(jobIcon, {jobIconSize, jobIconSize});
    end
    imgui.SetCursorScreenPos({hpStartX, hpStartY});

    -- Update the hp text
    memberText[memIdx].hp:SetColor(hpNameColor);
    memberText[memIdx].hp:SetPositionX(hpStartX + hpBarWidth + settings.hpTextOffsetX);
    memberText[memIdx].hp:SetPositionY(hpStartY + barHeight + settings.hpTextOffsetY);
    memberText[memIdx].hp:SetText(tostring(memInfo.hp));

    -- Draw the HP bar
    if (memInfo.inzone) then
        progressbar.ProgressBar({{memInfo.hpp, hpGradient}}, {hpBarWidth, barHeight}, {borderConfig=borderConfig, backgroundGradientOverride=bgGradientOverride, decorate = gConfig.showPartyListBookends});
    elseif (memInfo.zone == '' or memInfo.zone == nil) then
        imgui.Dummy({allBarsLengths, barHeight});
    else
        imgui.ProgressBar(0, {allBarsLengths, barHeight}, encoding:ShiftJIS_To_UTF8(AshitaCore:GetResourceManager():GetString("zones.names", memInfo.zone), true));
    end

    -- Draw the leader icon
    if (memInfo.leader) then
        draw_circle({hpStartX + settings.dotRadius/2, hpStartY + settings.dotRadius/2}, settings.dotRadius, {1, 1, .5, 1}, settings.dotRadius * 3, true);
    end

    -- Update the name text
    memberText[memIdx].name:SetColor(0xFFFFFFFF);
    memberText[memIdx].name:SetPositionX(namePosX);
    memberText[memIdx].name:SetPositionY(hpStartY - nameSize.cy - settings.nameTextOffsetY);
    memberText[memIdx].name:SetText(tostring(memInfo.name));

    local nameSize = SIZE.new();
    memberText[memIdx].name:GetTextSize(nameSize);
    local offsetSize = nameSize.cy > settings.iconSize and nameSize.cy or settings.iconSize;

    if (memInfo.inzone) then
        imgui.SameLine();

        -- Draw the MP bar
        local mpStartX, mpStartY;
        imgui.SetCursorPosX(imgui.GetCursorPosX());
        mpStartX, mpStartY = imgui.GetCursorScreenPos();
        progressbar.ProgressBar({{memInfo.mpp, {'#9abb5a', '#bfe07d'}}}, {mpBarWidth, barHeight}, {borderConfig=borderConfig, backgroundGradientOverride=bgGradientOverride, decorate = gConfig.showPartyListBookends});

        -- Update the mp text
        memberText[memIdx].mp:SetColor(gAdjustedSettings.mpColor);
        memberText[memIdx].mp:SetPositionX(mpStartX + mpBarWidth + settings.mpTextOffsetX);
        memberText[memIdx].mp:SetPositionY(mpStartY + barHeight + settings.mpTextOffsetY);
        memberText[memIdx].mp:SetText(tostring(memInfo.mp));

        -- Draw the TP bar
        if (showTP) then
            imgui.SameLine();
            local tpStartX, tpStartY;
            imgui.SetCursorPosX(imgui.GetCursorPosX());
            tpStartX, tpStartY = imgui.GetCursorScreenPos();

            local tpGradient = {'#3898ce', '#78c4ee'};
            local tpOverlayGradient = {'#0078CC', '#0078CC'};
            local mainPercent;
            local tpOverlay;
            
            if (memInfo.tp >= 1000) then
                mainPercent = (memInfo.tp - 1000) / 2000;
                tpOverlay = {{1, tpOverlayGradient}, math.ceil(barHeight * 2/7), 1};
            else
                mainPercent = memInfo.tp / 1000;
            end
            
            progressbar.ProgressBar({{mainPercent, tpGradient}}, {tpBarWidth, barHeight}, {overlayBar=tpOverlay, borderConfig=borderConfig, backgroundGradientOverride=bgGradientOverride, decorate = gConfig.showPartyListBookends});

            -- Update the tp text
            if (memInfo.tp >= 1000) then
                memberText[memIdx].tp:SetColor(gAdjustedSettings.tpFullColor);
            else
                memberText[memIdx].tp:SetColor(gAdjustedSettings.tpEmptyColor);
            end
            memberText[memIdx].tp:SetPositionX(tpStartX + tpBarWidth + settings.tpTextOffsetX);
            memberText[memIdx].tp:SetPositionY(tpStartY + barHeight + settings.tpTextOffsetY);
            memberText[memIdx].tp:SetText(tostring(memInfo.tp));
        end

        -- Draw targeted
        local entrySize = hpSize.cy + offsetSize + settings.hpTextOffsetY + barHeight + settings.cursorPaddingY1 + settings.cursorPaddingY2;
        if (memInfo.targeted == true) then
            selectionPrim.visible = true;
            selectionPrim.position_x = hpStartX - settings.cursorPaddingX1;
            selectionPrim.position_y = hpStartY - offsetSize - settings.cursorPaddingY1;
            selectionPrim.scale_x = (allBarsLengths + settings.cursorPaddingX1 + settings.cursorPaddingX2) / 346;
            selectionPrim.scale_y = entrySize / 108;
            partyTargeted = true;
        end

        -- Draw subtargeted
        if ((memInfo.targeted == true and not subTargetActive) or memInfo.subTargeted) then
            arrowPrim.visible = true;
            local newArrowX =  memberText[memIdx].name:GetPositionX() - arrowPrim:GetWidth();
            if (jobIcon ~= nil) then
                newArrowX = newArrowX - jobIconSize;
            end
            arrowPrim.position_x = newArrowX;
            arrowPrim.position_y = (hpStartY - offsetSize - settings.cursorPaddingY1) + (entrySize/2) - arrowPrim:GetHeight()/2;
            arrowPrim.scale_x = settings.arrowSize;
            arrowPrim.scale_y = settings.arrowSize;
            if (subTargetActive) then
                arrowPrim.color = settings.subtargetArrowTint;
            else
                arrowPrim.color = 0xFFFFFFFF;
            end
            partySubTargeted = true;
        end

        -- Draw the different party list buff / debuff themes
        if (partyIndex == 1 and memInfo.buffs ~= nil and #memInfo.buffs > 0) then
            if (gConfig.partyListStatusTheme == 0 or gConfig.partyListStatusTheme == 1) then
                local buffs = {};
                local debuffs = {};
                for i = 0, #memInfo.buffs do
                    if (buffTable.IsBuff(memInfo.buffs[i])) then
                        table.insert(buffs, memInfo.buffs[i]);
                    else
                        table.insert(debuffs, memInfo.buffs[i]);
                    end
                end

                if (buffs ~= nil and #buffs > 0) then
                    if (gConfig.partyListStatusTheme == 0 and buffWindowX[memIdx] ~= nil) then
                        imgui.SetNextWindowPos({hpStartX - buffWindowX[memIdx] - settings.buffOffset , hpStartY - settings.iconSize*1.2});
                    elseif (gConfig.partyListStatusTheme == 1 and fullMenuWidth[partyIndex] ~= nil) then
                        local thisPosX, _ = imgui.GetWindowPos();
                        imgui.SetNextWindowPos({ thisPosX + fullMenuWidth[partyIndex], hpStartY - settings.iconSize * 1.2 });
                    end
                    if (imgui.Begin('PlayerBuffs'..memIdx, true, bit.bor(ImGuiWindowFlags_NoDecoration, ImGuiWindowFlags_AlwaysAutoResize, ImGuiWindowFlags_NoFocusOnAppearing, ImGuiWindowFlags_NoNav, ImGuiWindowFlags_NoBackground, ImGuiWindowFlags_NoSavedSettings))) then
                        imgui.PushStyleVar(ImGuiStyleVar_ItemSpacing, {3, 1});
                        DrawStatusIcons(buffs, settings.iconSize, 32, 1, true);
                        imgui.PopStyleVar(1);
                    end
                    local buffWindowSizeX, _ = imgui.GetWindowSize();
                    buffWindowX[memIdx] = buffWindowSizeX;
    
                    imgui.End();
                end

                if (debuffs ~= nil and #debuffs > 0) then
                    if (gConfig.partyListStatusTheme == 0 and debuffWindowX[memIdx] ~= nil) then
                        imgui.SetNextWindowPos({hpStartX - debuffWindowX[memIdx] - settings.buffOffset , hpStartY});
                    elseif (gConfig.partyListStatusTheme == 1 and fullMenuWidth[partyIndex] ~= nil) then
                        local thisPosX, _ = imgui.GetWindowPos();
                        imgui.SetNextWindowPos({ thisPosX + fullMenuWidth[partyIndex], hpStartY });
                    end
                    if (imgui.Begin('PlayerDebuffs'..memIdx, true, bit.bor(ImGuiWindowFlags_NoDecoration, ImGuiWindowFlags_AlwaysAutoResize, ImGuiWindowFlags_NoFocusOnAppearing, ImGuiWindowFlags_NoNav, ImGuiWindowFlags_NoBackground, ImGuiWindowFlags_NoSavedSettings))) then
                        imgui.PushStyleVar(ImGuiStyleVar_ItemSpacing, {3, 1});
                        DrawStatusIcons(debuffs, settings.iconSize, 32, 1, true);
                        imgui.PopStyleVar(1);
                    end
                    local buffWindowSizeX, buffWindowSizeY = imgui.GetWindowSize();
                    debuffWindowX[memIdx] = buffWindowSizeX;
                    imgui.End();
                end
            elseif (gConfig.partyListStatusTheme == 2) then
                -- Draw FFXIV theme
                local resetX, resetY = imgui.GetCursorScreenPos();
                imgui.PushStyleVar(ImGuiStyleVar_WindowPadding, {0, 0} );
                imgui.SetNextWindowPos({mpStartX, mpStartY - settings.iconSize - settings.xivBuffOffsetY})
                if (imgui.Begin('XIVStatus'..memIdx, true, bit.bor(ImGuiWindowFlags_NoDecoration, ImGuiWindowFlags_AlwaysAutoResize, ImGuiWindowFlags_NoFocusOnAppearing, ImGuiWindowFlags_NoNav, ImGuiWindowFlags_NoBackground, ImGuiWindowFlags_NoSavedSettings))) then
                    imgui.PushStyleVar(ImGuiStyleVar_ItemSpacing, {0, 0});
                    DrawStatusIcons(memInfo.buffs, settings.iconSize, 32, 1);
                    imgui.PopStyleVar(1);
                end
                imgui.PopStyleVar(1);
                imgui.End();
                imgui.SetCursorScreenPos({resetX, resetY});
            elseif (gConfig.partyListStatusTheme == 3) then
                if (buffWindowX[memIdx] ~= nil) then
                    imgui.SetNextWindowPos({hpStartX - buffWindowX[memIdx] - settings.buffOffset , memberText[memIdx].name:GetPositionY() - settings.iconSize/2});
                end
                if (imgui.Begin('PlayerBuffs'..memIdx, true, bit.bor(ImGuiWindowFlags_NoDecoration, ImGuiWindowFlags_AlwaysAutoResize, ImGuiWindowFlags_NoFocusOnAppearing, ImGuiWindowFlags_NoNav, ImGuiWindowFlags_NoBackground, ImGuiWindowFlags_NoSavedSettings))) then
                    imgui.PushStyleVar(ImGuiStyleVar_ItemSpacing, {0, 3});
                    DrawStatusIcons(memInfo.buffs, settings.iconSize, 7, 3);
                    imgui.PopStyleVar(1);
                end
                local buffWindowSizeX, _ = imgui.GetWindowSize();
                buffWindowX[memIdx] = buffWindowSizeX;

                imgui.End();
            end
        end
    end

    if (memInfo.sync) then
        draw_circle({hpStartX + settings.dotRadius/2, hpStartY + barHeight}, settings.dotRadius, {.5, .5, 1, 1}, settings.dotRadius * 3, true);
    end

    memberText[memIdx].hp:SetVisible(memInfo.inzone);
    memberText[memIdx].mp:SetVisible(memInfo.inzone);
    memberText[memIdx].tp:SetVisible(memInfo.inzone and showTP);

    if (memInfo.inzone) then
        imgui.Dummy({0, settings.entrySpacing[partyIndex] + hpSize.cy + settings.hpTextOffsetY + settings.nameTextOffsetY});
    else
        imgui.Dummy({0, settings.entrySpacing[partyIndex] + settings.nameTextOffsetY});
    end

    local lastPlayerIndex = (partyIndex * 6) - 1;
    if (memIdx + 1 <= lastPlayerIndex) then
        imgui.Dummy({0, offsetSize});
    end
end

partyList.DrawWindow = function(settings)

    -- Obtain the player entity..
    local party = AshitaCore:GetMemoryManager():GetParty();
    local player = AshitaCore:GetMemoryManager():GetPlayer();

	if (party == nil or player == nil or player.isZoning or player:GetMainJob() == 0) then
		UpdateTextVisibility(false);
		return;
	end

    -- Handle RB hold detection for treasure pool toggle (always check, regardless of window visibility)
    local currentTime = os.clock();
    if (rbPressed and (currentTime - rbPressTime) >= rbHoldThreshold and not rbToggleTriggered) then
        -- Long hold detected - call the same function as /hxui loot command
        if (ToggleTreasurePoolSuppression) then
            ToggleTreasurePoolSuppression();
        else
            -- Fallback to local toggle if global function not available
            treasurePoolVisible = not treasurePoolVisible;
            local status = treasurePoolVisible and "enabled" or "disabled";
            print(string.format('[HXUI] Treasure pool %s for this session.', status));
        end
        rbToggleTriggered = true; -- Prevent multiple toggles
        
        -- Exit controller mode when toggling
        if (treasurePoolControllerActive) then
            treasurePoolControllerActive = false;
        end
    end

    partyTargeted = false;
    partySubTargeted = false;

    -- Main party window
    partyList.DrawPartyWindow(settings, party, 1);

    -- Alliance party windows
    if (gConfig.partyListAlliance) then
        partyList.DrawPartyWindow(settings, party, 2);
        partyList.DrawPartyWindow(settings, party, 3);
    else
        UpdateTextVisibility(false, 2);
        UpdateTextVisibility(false, 3);
    end

    -- Treasure Pool window
    if (gConfig.showTreasurePool and treasurePoolVisible) then
        partyList.DrawTreasurePoolWindow();
    else
        -- Hide treasure pool background primitives when window is not being drawn
        local backgroundPrim = treasurePoolWindowPrim.background;
        if (backgroundPrim and type(backgroundPrim) == "table") then
            for _, k in ipairs(bgImageKeys) do
                if (backgroundPrim[k]) then
                    backgroundPrim[k].visible = false;
                end
            end
        end
        -- Also hide the arrow if it was being used for treasure pool controller
        if (treasurePoolControllerActive) then
            treasurePoolControllerActive = false;
            if (not partySubTargeted) then
                arrowPrim.visible = false;
            end
        end
    end

    selectionPrim.visible = partyTargeted;
    -- Show arrow for party subtargeting OR treasure pool controller mode, but don't override if already set by treasure pool
    if (not arrowPrim.visible) then
        arrowPrim.visible = partySubTargeted;
    end
end

partyList.DrawPartyWindow = function(settings, party, partyIndex)
    local firstPlayerIndex = (partyIndex - 1) * partyMaxSize;
    local lastPlayerIndex = firstPlayerIndex + partyMaxSize - 1;

    -- Get the party size by checking active members
    local partyMemberCount = 0;
    if (showConfig[1] and gConfig.partyListPreview) then
        partyMemberCount = partyMaxSize;
    else
        for i = firstPlayerIndex, lastPlayerIndex do
            if (party:GetMemberIsActive(i) ~= 0) then
                partyMemberCount = partyMemberCount + 1
            else
                break
            end
        end
    end

    if (partyIndex == 1 and not gConfig.showPartyListWhenSolo and partyMemberCount <= 1) then
		UpdateTextVisibility(false);
        return;
	end

    if(partyIndex > 1 and partyMemberCount == 0) then
        UpdateTextVisibility(false, partyIndex);
        return;
    end

    local bgTitlePrim = partyWindowPrim[partyIndex].bgTitle;
    local backgroundPrim = partyWindowPrim[partyIndex].background;

    -- Graphic has multiple titles
    -- 0 = Solo
    -- bgTitleItemHeight = Party
    -- bgTitleItemHeight*2 = Party B
    -- bgTitleItemHeight*3 = Party C
    if (partyIndex == 1) then
        bgTitlePrim.texture_offset_y = partyMemberCount == 1 and 0 or bgTitleItemHeight;
    else
        bgTitlePrim.texture_offset_y = bgTitleItemHeight * partyIndex
    end

    local imguiPosX, imguiPosY;

    local windowFlags = bit.bor(ImGuiWindowFlags_NoDecoration, ImGuiWindowFlags_AlwaysAutoResize, ImGuiWindowFlags_NoFocusOnAppearing, ImGuiWindowFlags_NoNav, ImGuiWindowFlags_NoBackground, ImGuiWindowFlags_NoBringToFrontOnFocus);
    if (gConfig.lockPositions) then
        windowFlags = bit.bor(windowFlags, ImGuiWindowFlags_NoMove);
    end

    local windowName = 'PartyList';
    if (partyIndex > 1) then
        windowName = windowName .. partyIndex
    end

    local scale = getScale(partyIndex);
    local iconSize = 0; --settings.iconSize * scale.icon;

    -- Remove all padding and start our window
    imgui.PushStyleVar(ImGuiStyleVar_FramePadding, {0,0});
    imgui.PushStyleVar(ImGuiStyleVar_ItemSpacing, { settings.barSpacing * scale.x, 0 });
    if (imgui.Begin(windowName, true, windowFlags)) then
        imguiPosX, imguiPosY = imgui.GetWindowPos();

        local nameSize = SIZE.new();
        memberText[(partyIndex - 1) * 6].name:GetTextSize(nameSize);
        local offsetSize = nameSize.cy > iconSize and nameSize.cy or iconSize;
        imgui.Dummy({0, settings.nameTextOffsetY + offsetSize});

        UpdateTextVisibility(true, partyIndex);

        for i = firstPlayerIndex, lastPlayerIndex do
            local relIndex = i - firstPlayerIndex
            if ((partyIndex == 1 and settings.expandHeight) or relIndex < partyMemberCount or relIndex < settings.minRows) then
                DrawMember(i, settings);
            else
                UpdateTextVisibilityByMember(i, false);
            end
        end
    end

    local menuWidth, menuHeight = imgui.GetWindowSize();

    fullMenuWidth[partyIndex] = menuWidth;
    fullMenuHeight[partyIndex] = menuHeight;

    local bgWidth = fullMenuWidth[partyIndex] + (settings.bgPadding * 2);
    local bgHeight = fullMenuHeight[partyIndex] + (settings.bgPadding * 2);

    backgroundPrim.bg.visible = backgroundPrim.bg.exists;
    backgroundPrim.bg.position_x = imguiPosX - settings.bgPadding;
    backgroundPrim.bg.position_y = imguiPosY - settings.bgPadding;
    backgroundPrim.bg.width = math.ceil(bgWidth / gConfig.partyListBgScale);
    backgroundPrim.bg.height = math.ceil(bgHeight / gConfig.partyListBgScale);

    backgroundPrim.br.visible = backgroundPrim.br.exists;
    backgroundPrim.br.position_x = backgroundPrim.bg.position_x + bgWidth - math.floor((settings.borderSize * gConfig.partyListBgScale) - (settings.bgOffset * gConfig.partyListBgScale));
    backgroundPrim.br.position_y = backgroundPrim.bg.position_y + bgHeight - math.floor((settings.borderSize * gConfig.partyListBgScale) - (settings.bgOffset * gConfig.partyListBgScale));
    backgroundPrim.br.width = settings.borderSize;
    backgroundPrim.br.height = settings.borderSize;

    backgroundPrim.tr.visible = backgroundPrim.tr.exists;
    backgroundPrim.tr.position_x = backgroundPrim.br.position_x;
    backgroundPrim.tr.position_y = backgroundPrim.bg.position_y - settings.bgOffset * gConfig.partyListBgScale;
    backgroundPrim.tr.width = backgroundPrim.br.width;
    backgroundPrim.tr.height = math.ceil((backgroundPrim.br.position_y - backgroundPrim.tr.position_y) / gConfig.partyListBgScale);

    backgroundPrim.tl.visible = backgroundPrim.tl.exists;
    backgroundPrim.tl.position_x = backgroundPrim.bg.position_x - settings.bgOffset * gConfig.partyListBgScale;
    backgroundPrim.tl.position_y = backgroundPrim.tr.position_y
    backgroundPrim.tl.width = math.ceil((backgroundPrim.tr.position_x - backgroundPrim.tl.position_x) / gConfig.partyListBgScale);
    backgroundPrim.tl.height = backgroundPrim.tr.height;

    backgroundPrim.bl.visible = backgroundPrim.bl.exists;
    backgroundPrim.bl.position_x = backgroundPrim.tl.position_x;
    backgroundPrim.bl.position_y = backgroundPrim.br.position_y;
    backgroundPrim.bl.width = backgroundPrim.tl.width;
    backgroundPrim.bl.height = backgroundPrim.br.height;

    bgTitlePrim.visible = gConfig.showPartyListTitle;
    bgTitlePrim.position_x = imguiPosX + math.floor((bgWidth / 2) - (bgTitlePrim.width * bgTitlePrim.scale_x / 2));
    bgTitlePrim.position_y = imguiPosY - math.floor((bgTitlePrim.height * bgTitlePrim.scale_y / 2) + (2 / bgTitlePrim.scale_y));

    -- Show treasure icon in top-right corner when treasure pool has items (only for main party list)
    if (partyIndex == 1 and gConfig.showPartyListTreasureIcon) then
        -- Get treasure pool count from Ashita SDK
        local treasureCount = 0;
        if (AshitaCore ~= nil) then
            local inventory = AshitaCore:GetMemoryManager():GetInventory();
            if (inventory ~= nil) then
                treasureCount = inventory:GetTreasurePoolItemCount();
            end
        end
        
        local hasTreasureItems = (treasureCount > 0);
        treasureIconPrim.visible = hasTreasureItems;
        if (hasTreasureItems) then
            local iconSize = 16 * gConfig.partyListBgScale; -- Scale with party list background
            treasureIconPrim.position_x = imguiPosX + bgWidth - iconSize - 30; -- 5px padding from right edge
            treasureIconPrim.position_y = imguiPosY - iconSize - 2; -- 2px above party list
            treasureIconPrim.scale_x = gConfig.partyListBgScale;
            treasureIconPrim.scale_y = gConfig.partyListBgScale;
        end
    elseif (partyIndex == 1) then
        -- Hide treasure icon if disabled in config
        treasureIconPrim.visible = false;
    end

	imgui.End();
    imgui.PopStyleVar(2);

    if (settings.alignBottom and imguiPosX ~= nil) then
        -- Migrate old settings
        if (partyIndex == 1 and gConfig.partyListState ~= nil and gConfig.partyListState.x ~= nil) then
            local oldValues = gConfig.partyListState;
            gConfig.partyListState = {};
            gConfig.partyListState[partyIndex] = oldValues;
            ashita_settings.save();
        end

        if (gConfig.partyListState == nil) then
            gConfig.partyListState = {};
        end

        local partyListState = gConfig.partyListState[partyIndex];

        if (partyListState ~= nil) then
            -- Move window if size changed
            if (menuHeight ~= partyListState.height) then
                local newPosY = partyListState.y + partyListState.height - menuHeight;
                imguiPosY = newPosY; --imguiPosY + (partyListState.height - menuHeight]);
                imgui.SetWindowPos(windowName, { imguiPosX, imguiPosY });
            end
        end

        -- Update if the state changed
        if (partyListState == nil or
                imguiPosX ~= partyListState.x or imguiPosY ~= partyListState.y or
                menuWidth ~= partyListState.width or menuHeight ~= partyListState.height) then
            gConfig.partyListState[partyIndex] = {
                x = imguiPosX,
                y = imguiPosY,
                width = menuWidth,
                height = menuHeight,
            };
            ashita_settings.save();
        end
    end
end

partyList.Initialize = function(settings)
    -- Reset treasure pool state on initialization/reload
    ResetTreasurePoolData();
    
    -- Initialize all our font objects we need
    local name_font_settings = deep_copy_table(settings.name_font_settings);
    local hp_font_settings = deep_copy_table(settings.hp_font_settings);
    local mp_font_settings = deep_copy_table(settings.mp_font_settings);
    local tp_font_settings = deep_copy_table(settings.tp_font_settings);

    for i = 0, memberTextCount-1 do
        local partyIndex = math.ceil((i + 1) / partyMaxSize);

        local partyListFontOffset = gConfig.partyListFontOffset;
        if (partyIndex == 2) then
            partyListFontOffset = gConfig.partyList2FontOffset;
        elseif (partyIndex == 3) then
            partyListFontOffset = gConfig.partyList3FontOffset;
        end

        name_font_settings.font_height = math.max(settings.name_font_settings.font_height + partyListFontOffset, 1);
        hp_font_settings.font_height = math.max(settings.hp_font_settings.font_height + partyListFontOffset, 1);
        mp_font_settings.font_height = math.max(settings.mp_font_settings.font_height + partyListFontOffset, 1);
        tp_font_settings.font_height = math.max(settings.tp_font_settings.font_height + partyListFontOffset, 1);

        memberText[i] = {};
        memberText[i].name = fonts.new(name_font_settings);
        memberText[i].hp = fonts.new(hp_font_settings);
        memberText[i].mp = fonts.new(mp_font_settings);
        memberText[i].tp = fonts.new(tp_font_settings);
    end

    -- Initialize images
    loadedBg = nil;

    for i = 1, 3 do
        local backgroundPrim = {};

        for _, k in ipairs(bgImageKeys) do
            backgroundPrim[k] = primitives:new(settings.prim_data);
            backgroundPrim[k].visible = false;
            backgroundPrim[k].can_focus = false;
            backgroundPrim[k].exists = false;
        end

        partyWindowPrim[i].background = backgroundPrim;

        local bgTitlePrim = primitives.new(settings.prim_data);
        bgTitlePrim.color = 0xFFC5CFDC;
        bgTitlePrim.texture = string.format('%s/assets/PartyList-Titles.png', addon.path);
        bgTitlePrim.visible = false;
        bgTitlePrim.can_focus = false;
        bgTitleItemHeight = bgTitlePrim.height / bgTitleAtlasItemCount;
        bgTitlePrim.height = bgTitleItemHeight;

        partyWindowPrim[i].bgTitle = bgTitlePrim;
    end

    -- Initialize treasure pool background primitives
    local treasurePoolBackgroundPrim = {};
    for _, k in ipairs(bgImageKeys) do
        treasurePoolBackgroundPrim[k] = primitives:new(settings.prim_data);
        treasurePoolBackgroundPrim[k].visible = false;
        treasurePoolBackgroundPrim[k].can_focus = false;
        treasurePoolBackgroundPrim[k].exists = false;
    end
    treasurePoolWindowPrim.background = treasurePoolBackgroundPrim;

    selectionPrim = primitives.new(settings.prim_data);
    selectionPrim.color = 0xFFFFFFFF;
    selectionPrim.texture = string.format('%s/assets/Selector.png', addon.path);
    selectionPrim.visible = false;
    selectionPrim.can_focus = false;

    arrowPrim = primitives.new(settings.prim_data);
    arrowPrim.color = 0xFFFFFFFF;
    arrowPrim.visible = false;
    arrowPrim.can_focus = false;

    treasureIconPrim = primitives.new(settings.prim_data);
    treasureIconPrim.color = 0xFFFFFFFF;
    treasureIconPrim.texture = string.format('%s/assets/gil.png', addon.path);
    treasureIconPrim.visible = false;
    treasureIconPrim.can_focus = false;

    partyList.UpdateFonts(settings);
    
    -- Initialize treasure pool controller
    partyList.InitializeTreasurePoolController();
end

partyList.UpdateFonts = function(settings)
    -- Update fonts
    for i = 0, memberTextCount-1 do
        local partyIndex = math.ceil((i + 1) / partyMaxSize);

        local partyListFontOffset = gConfig.partyListFontOffset;
        if (partyIndex == 2) then
            partyListFontOffset = gConfig.partyList2FontOffset;
        elseif (partyIndex == 3) then
            partyListFontOffset = gConfig.partyList3FontOffset;
        end

        local name_font_settings_font_height = math.max(settings.name_font_settings.font_height + partyListFontOffset, 1);
        local hp_font_settings_font_height = math.max(settings.hp_font_settings.font_height + partyListFontOffset, 1);
        local mp_font_settings_font_height = math.max(settings.mp_font_settings.font_height + partyListFontOffset, 1);
        local tp_font_settings_font_height = math.max(settings.tp_font_settings.font_height + partyListFontOffset, 1);

        memberText[i].name:SetFontHeight(name_font_settings_font_height);
        memberText[i].hp:SetFontHeight(hp_font_settings_font_height);
        memberText[i].mp:SetFontHeight(mp_font_settings_font_height);
        memberText[i].tp:SetFontHeight(tp_font_settings_font_height);
    end

    -- Update images
    local bgChanged = gConfig.partyListBackgroundName ~= loadedBg;
    loadedBg = gConfig.partyListBackgroundName;

    local bgColor = tonumber(string.format('%02x%02x%02x%02x', gConfig.partyListBgColor[4], gConfig.partyListBgColor[1], gConfig.partyListBgColor[2], gConfig.partyListBgColor[3]), 16);
    local borderColor = tonumber(string.format('%02x%02x%02x%02x', gConfig.partyListBorderColor[4], gConfig.partyListBorderColor[1], gConfig.partyListBorderColor[2], gConfig.partyListBorderColor[3]), 16);

    for i = 1, 3 do
        partyWindowPrim[i].bgTitle.scale_x = gConfig.partyListBgScale / 2.30;
        partyWindowPrim[i].bgTitle.scale_y = gConfig.partyListBgScale / 2.30;

        local backgroundPrim = partyWindowPrim[i].background;

        for _, k in ipairs(bgImageKeys) do
            local file_name = string.format('%s-%s.png', gConfig.partyListBackgroundName, k);
            backgroundPrim[k].color = k == 'bg' and bgColor or borderColor;
            if (bgChanged) then
                -- Keep width/height to prevent flicker when switching to new texture
                local width, height = backgroundPrim[k].width, backgroundPrim[k].height;
                local filepath = string.format('%s/assets/backgrounds/%s', addon.path, file_name);
                backgroundPrim[k].texture = filepath;
                backgroundPrim[k].width, backgroundPrim[k].height = width, height;

                backgroundPrim[k].exists = ashita.fs.exists(filepath);
            end
            backgroundPrim[k].scale_x = gConfig.partyListBgScale;
            backgroundPrim[k].scale_y = gConfig.partyListBgScale;
        end
    end

    -- Update treasure pool background
    local treasurePoolBackgroundPrim = treasurePoolWindowPrim.background;
    if (treasurePoolBackgroundPrim) then
        for _, k in ipairs(bgImageKeys) do
            local file_name = string.format('%s-%s.png', gConfig.partyListBackgroundName, k);
            treasurePoolBackgroundPrim[k].color = k == 'bg' and bgColor or borderColor;
            if (bgChanged) then
                local width, height = treasurePoolBackgroundPrim[k].width, treasurePoolBackgroundPrim[k].height;
                local filepath = string.format('%s/assets/backgrounds/%s', addon.path, file_name);
                treasurePoolBackgroundPrim[k].texture = filepath;
                treasurePoolBackgroundPrim[k].width, treasurePoolBackgroundPrim[k].height = width, height;
                treasurePoolBackgroundPrim[k].exists = ashita.fs.exists(filepath);
            end
            treasurePoolBackgroundPrim[k].scale_x = gConfig.partyListBgScale;
            treasurePoolBackgroundPrim[k].scale_y = gConfig.partyListBgScale;
        end
    end

    arrowPrim.texture = string.format('%s/assets/cursors/%s', addon.path, gConfig.partyListCursor);
end

-- ================================
--   Treasure Pool Window Drawing
-- ================================
partyList.DrawTreasurePoolWindow = function()
    -- Safety checks to prevent config menu conflicts
    if (not gConfig or not gConfig.treasurePoolScaleX) then
        return;
    end
    
    -- Additional safety check for gAdjustedSettings
    if (not gAdjustedSettings or not gAdjustedSettings.partyListSettings) then
        return;
    end
    
    -- Update treasure pool data with polling
    UpdateTreasurePoolData();
    
    -- Only show if there are winnable items (lost items are shown within the same window)
    if #treasurePoolWinnableItems == 0 then
        -- Hide arrow when no treasure pool items
        if (not partySubTargeted) then
            arrowPrim.visible = false;
        end
        -- Hide background primitives when no active items
        local backgroundPrim = treasurePoolWindowPrim.background;
        if (backgroundPrim and type(backgroundPrim) == "table") then
            for _, k in ipairs(bgImageKeys) do
                if (backgroundPrim[k]) then
                    backgroundPrim[k].visible = false;
                end
            end
        end
        return;
    end
    
    -- Initialize controller if not already done
    if (not treasurePoolInputCB) then
        partyList.InitializeTreasurePoolController();
    end
    
    local scale = gConfig.treasurePoolScaleX or 1.0;
    local fontOffset = gConfig.treasurePoolFontOffset or 0;
    
    local windowFlags = bit.bor(ImGuiWindowFlags_NoDecoration, ImGuiWindowFlags_NoFocusOnAppearing, ImGuiWindowFlags_NoNav, ImGuiWindowFlags_NoBackground, ImGuiWindowFlags_NoBringToFrontOnFocus);
    if (gConfig.lockPositions) then
        windowFlags = bit.bor(windowFlags, ImGuiWindowFlags_NoMove);
    end
    
    -- Calculate window dimensions based on content and scale
    local baseWidth = 550; -- Increased base width for additional column
    local baseRowHeight = 20; -- Base height per row
    local baseHeaderHeight = 25; -- Base height for header row
    local baseSectionHeight = 30; -- Height for section headers
    local padding = 5; -- Padding around the table
    
    -- Apply font scaling to heights
    local baseFontSize = 13;
    local scaledFontSize = math.max(baseFontSize + fontOffset, 1);
    local fontScale = scaledFontSize / baseFontSize;
    local rowHeight = baseRowHeight * fontScale;
    local headerHeight = baseHeaderHeight * fontScale;
    local sectionHeight = baseSectionHeight * fontScale;
    
    local numWinnableItems = #treasurePoolWinnableItems;
    local numLostItems = #treasurePoolLostItems;
    local numSections = 0;
    if numWinnableItems > 0 then numSections = numSections + 1; end
    if numLostItems > 0 then numSections = numSections + 1; end
    
    local calculatedWidth = baseWidth * scale; -- Width is affected by scale
    local calculatedHeight = (numSections * (sectionHeight + headerHeight)) + ((numWinnableItems + numLostItems) * rowHeight) + (padding * 2);
    
    -- Add space for controller legend when controller is active and config allows it
    if (treasurePoolControllerActive and gConfig.showTreasurePoolControllerLegend) then
        calculatedHeight = calculatedHeight + 17; -- Reduced from 25 to 17 (8px less when focused)
    else
        calculatedHeight = calculatedHeight + 4; -- Add 4px padding when not focused
    end
    
    -- CONTROLLER CONSTRAINT: Only validate selection bounds for winnable items
    -- Controller navigation is limited to winnable items only, never lost items
    if (treasurePoolControllerActive and numWinnableItems > 0) then
        if (treasurePoolSelected > numWinnableItems) then
            treasurePoolSelected = numWinnableItems;
        elseif (treasurePoolSelected < 1) then
            treasurePoolSelected = 1;
        end
    elseif (treasurePoolControllerActive and numWinnableItems == 0) then
        -- No winnable items left, exit controller mode
        treasurePoolControllerActive = false;
    end
    
    -- Set window position and calculated size
    imgui.SetNextWindowPos(treasurePoolWindowPos, ImGuiCond_FirstUseEver);
    imgui.SetNextWindowSize({calculatedWidth, calculatedHeight}, ImGuiCond_Always);
    
    -- Remove all padding to match party window style
    imgui.PushStyleVar(ImGuiStyleVar_FramePadding, {0,0});
    imgui.PushStyleVar(ImGuiStyleVar_ItemSpacing, {0, 0});
    
    local imguiPosX, imguiPosY;
    
    if (imgui.Begin('HXUI_TreasurePool', true, windowFlags)) then
        -- Update window position if moved
        imguiPosX, imguiPosY = imgui.GetWindowPos();
        treasurePoolWindowPos.x, treasurePoolWindowPos.y = imguiPosX, imguiPosY;
        
        -- Focus the window when controller becomes active
        if (treasurePoolControllerActive) then
            imgui.SetWindowFocus();
        end
        
        -- Apply font scaling based on treasurePoolFontOffset
        local baseFontSize = 13; -- Base font size for treasure pool
        local scaledFontSize = math.max(baseFontSize + fontOffset, 1);
        local fontScale = scaledFontSize / baseFontSize;
        imgui.SetWindowFontScale(fontScale);
        
        -- Add RB controls display in top right corner (only when controller legend is enabled)
        if (gConfig.showTreasurePoolControllerLegend) then
            local windowWidth, windowHeight = imgui.GetWindowSize();
            local rbText = "[RB]: Focus  |  [RB(hold)]: Show/Hide Treasure Pool";
            -- Use a more conservative estimated width to prevent overflow
            local estimatedTextWidth = string.len(rbText) * 8; -- Increase to 8 pixels per character for safety
            imgui.SetCursorPos({windowWidth - estimatedTextWidth - 10, 5}); -- 10px padding from right edge
            imgui.PushStyleColor(ImGuiCol_Text, {0.8, 0.8, 0.8, 0.9}); -- Light gray
            imgui.TextUnformatted(rbText);
            imgui.PopStyleColor();
        end
        
        -- Winnable Items Section
        if numWinnableItems > 0 then
            -- Section header
            imgui.PushStyleColor(ImGuiCol_Text, {0.7, 1.0, 0.7, 1.0}); -- Light green
            imgui.TextUnformatted('--Winnable Items--');
            imgui.PopStyleColor();
            
            -- Set up the table with proper styling and constraints
            imgui.PushStyleColor(ImGuiCol_TableBorderStrong, {0.2, 0.3, 0.4, 1.0});
            imgui.PushStyleColor(ImGuiCol_TableBorderLight, {0.2, 0.3, 0.4, 1.0});
            
            -- Add controller focus indication with different header color
            if (treasurePoolControllerActive) then
                imgui.PushStyleColor(ImGuiCol_TableHeaderBg, {0.2, 0.3, 0.5, 0.8});
            end
            
            -- Make table fill the available window width and handle overflow properly
            local tableFlags = ImGuiTableFlags_Borders + ImGuiTableFlags_SizingFixedFit + ImGuiTableFlags_NoHostExtendX;
            if (imgui.BeginTable('ActiveTreasurePoolTable', 4, tableFlags)) then
                -- Calculate column widths to fit within window width
                local availableWidth = calculatedWidth - 20; -- Account for padding/borders
                -- Ensure we have a valid number
                if (availableWidth <= 0) then
                    availableWidth = 410; -- Fallback width
                end
                
                local col1Width = availableWidth * 0.25; -- 25% for Drops (increased by 10%)
                local col2Width = availableWidth * 0.12; -- 12% for My Lot(s) (reduced by 20%)
                local col3Width = availableWidth * 0.15; -- 15% for Current Winner (reduced by 40%)
                local col4Width = availableWidth * 0.48; -- 48% for Waiting for (adjusted to fit)
                
                -- Set up columns with calculated widths
                imgui.TableSetupColumn('Drops', ImGuiTableColumnFlags_WidthFixed, col1Width);
                imgui.TableSetupColumn('My Lot(s)', ImGuiTableColumnFlags_WidthFixed, col2Width);
                imgui.TableSetupColumn('Top Lot', ImGuiTableColumnFlags_WidthFixed, col3Width);
                imgui.TableSetupColumn('Waiting for', ImGuiTableColumnFlags_WidthFixed, col4Width);
                imgui.TableHeadersRow();
                
                -- Table data with selection highlighting
                local selectedRowPos = {}; -- Store position of selected row for arrow positioning
                for i, item in ipairs(treasurePoolWinnableItems) do
                    imgui.TableNextRow(ImGuiTableRowFlags_None, rowHeight);
                    
                    -- Highlight selected row if controller is active (using distinct selection color)
                    -- Note: i corresponds to data row number, but table row is i+1 due to header
                    local isSelected = (treasurePoolControllerActive and i == treasurePoolSelected);
                    
                    if (isSelected) then
                        imgui.TableSetBgColor(ImGuiTableBgTarget_RowBg0, imgui.ColorConvertFloat4ToU32({0.4, 0.6, 0.8, 0.9}));
                        -- Store the row position for arrow placement (get position before setting column)
                        selectedRowPos.x, selectedRowPos.y = imgui.GetCursorScreenPos();
                        selectedRowPos.height = rowHeight;
                    end
                    
                    imgui.TableSetColumnIndex(0);
                    
                    -- Display timestamp and item name
                    local itemName = item.item;
                    local timestamp = treasurePoolTimestamps[itemName];
                    if (timestamp) then
                        local elapsed = os.clock() - timestamp;
                        local remaining = treasurePoolAutoDistributeTime - elapsed;
                        if (remaining > 0) then
                            local timeText = FormatRemainingTime(remaining);
                            imgui.TextUnformatted(timeText .. ' ' .. itemName);
                        else
                            imgui.TextUnformatted(itemName);
                        end
                    else
                        imgui.TextUnformatted(itemName);
                    end
                    
                    imgui.TableSetColumnIndex(1);
                    imgui.TextUnformatted(item.myLot);
                    
                    imgui.TableSetColumnIndex(2);
                    imgui.TextUnformatted(item.currentWinner);
                    
                    imgui.TableSetColumnIndex(3);
                    imgui.TextUnformatted(item.waitingFor);
                end
                
                imgui.EndTable();
                
                -- Draw arrow next to selected treasure pool item when controller is active
                if (treasurePoolControllerActive and selectedRowPos.x) then
                    arrowPrim.visible = true;
                    -- Position arrow to the left of the selected row, using arrow primitive dimensions
                    local arrowScale = gConfig.treasurePoolArrowScale;
                    arrowPrim.position_x = selectedRowPos.x - (32 * arrowScale) - 5; -- 32 is typical arrow width, 5px padding
                    arrowPrim.position_y = selectedRowPos.y + (selectedRowPos.height / 2) - (16 * arrowScale); -- 16 is typical arrow height/2
                    arrowPrim.scale_x = arrowScale;
                    arrowPrim.scale_y = arrowScale;
                    arrowPrim.color = 0xFFFFFFFF; -- White color for treasure pool arrow
                elseif (not partySubTargeted) then
                    -- Hide arrow if treasure pool controller is not active and party is not subtargeted
                    arrowPrim.visible = false;
                end
            end
            
            -- Pop style colors (2 for borders + 1 if controller active)
            local colorsToPop = treasurePoolControllerActive and 3 or 2;
            imgui.PopStyleColor(colorsToPop);
            
            -- Add spacing between sections
            if numLostItems > 0 then
                imgui.Spacing();
            end
        end
        
        -- Lost Items Section
        if numLostItems > 0 then
            -- Section header
            imgui.PushStyleColor(ImGuiCol_Text, {1.0, 0.7, 0.7, 1.0}); -- Light red
            imgui.TextUnformatted('--Lost Items--');
            imgui.PopStyleColor();
            
            -- Set up the table with proper styling and constraints
            imgui.PushStyleColor(ImGuiCol_TableBorderStrong, {0.2, 0.3, 0.4, 1.0});
            imgui.PushStyleColor(ImGuiCol_TableBorderLight, {0.2, 0.3, 0.4, 1.0});
            imgui.PushStyleColor(ImGuiCol_TableHeaderBg, {0.3, 0.2, 0.2, 0.8}); -- Darker red header
            
            -- Make table fill the available window width and handle overflow properly
            local tableFlags = ImGuiTableFlags_Borders + ImGuiTableFlags_SizingFixedFit + ImGuiTableFlags_NoHostExtendX;
            if (imgui.BeginTable('PendingTreasurePoolTable', 2, tableFlags)) then
                -- Calculate column widths to fit within window width
                local availableWidth = calculatedWidth - 20; -- Account for padding/borders
                -- Ensure we have a valid number
                if (availableWidth <= 0) then
                    availableWidth = 410; -- Fallback width
                end
                
                local col1Width = availableWidth * 0.25; -- 25% for Drops (matches active table)
                local col2Width = availableWidth * 0.75; -- 75% for Winner
                
                -- Set up columns with calculated widths
                imgui.TableSetupColumn('Drops', ImGuiTableColumnFlags_WidthFixed, col1Width);
                imgui.TableSetupColumn('Winner', ImGuiTableColumnFlags_WidthFixed, col2Width);
                imgui.TableHeadersRow();
                
                -- Table data (no selection highlighting for lost items)
                for i, item in ipairs(treasurePoolLostItems) do
                    imgui.TableNextRow(ImGuiTableRowFlags_None, rowHeight);
                    
                    imgui.TableSetColumnIndex(0);
                    imgui.PushStyleColor(ImGuiCol_Text, {0.7, 0.7, 0.7, 1.0}); -- Gray text
                    imgui.TextUnformatted(item.item);
                    imgui.PopStyleColor();
                    
                    imgui.TableSetColumnIndex(1);
                    imgui.PushStyleColor(ImGuiCol_Text, {0.7, 0.7, 0.7, 1.0}); -- Gray text
                    imgui.TextUnformatted(item.winner or "--");
                    imgui.PopStyleColor();
                end
                
                imgui.EndTable();
            end
            
            imgui.PopStyleColor(3); -- Pop 3 style colors
        end
        
        -- Add controller legend when controller is active and config allows it
        if (treasurePoolControllerActive and gConfig.showTreasurePoolControllerLegend) then
            imgui.Separator();
            imgui.Spacing();
            
            -- Add a visible header for the legend
            imgui.PushStyleColor(ImGuiCol_Text, {0.9, 0.9, 0.9, 1.0}); -- Bright white text
            imgui.TextUnformatted("Controller:");
            imgui.PopStyleColor();
            
            -- Create a simple text-based legend that won't cause errors
            imgui.SameLine();
            imgui.PushStyleColor(ImGuiCol_Text, {0.0, 1.0, 0.0, 1.0}); -- Bright green
            imgui.TextUnformatted("  [A] Lot");
            imgui.PopStyleColor();
            
            imgui.SameLine();
            imgui.PushStyleColor(ImGuiCol_Text, {1.0, 0.0, 0.0, 1.0}); -- Bright red
            imgui.TextUnformatted("  [X] Pass");
            imgui.PopStyleColor();
            
            imgui.SameLine();
            imgui.PushStyleColor(ImGuiCol_Text, {1.0, 1.0, 0.0, 1.0}); -- Bright yellow
            imgui.TextUnformatted("  [Y] Ignore");
            imgui.PopStyleColor();
            
            -- Add some spacing
            imgui.Spacing();
        end
        
        imgui.SetWindowFontScale(1); -- Reset font scale
        imgui.End();
    end
    
    -- Handle background primitives after window is drawn (same as party windows)
    if (imguiPosX and imguiPosY) then
        local backgroundPrim = treasurePoolWindowPrim.background;
        -- Use our calculated dimensions instead of imgui.GetWindowSize()
        local menuWidth = calculatedWidth;
        local menuHeight = calculatedHeight;
        
        -- Safety check: ensure backgroundPrim is a table and has the bg property
        if (backgroundPrim and type(backgroundPrim) == "table" and backgroundPrim.bg) then
            -- Use same settings as party windows
            local settings = gAdjustedSettings.partyListSettings;
            local bgWidth = menuWidth + (settings.bgPadding * 2);
            local bgHeight = menuHeight + (settings.bgPadding * 2);

            backgroundPrim.bg.visible = backgroundPrim.bg.exists;
            backgroundPrim.bg.position_x = imguiPosX - settings.bgPadding;
            backgroundPrim.bg.position_y = imguiPosY - settings.bgPadding;
            backgroundPrim.bg.width = math.ceil(bgWidth / gConfig.partyListBgScale);
            backgroundPrim.bg.height = math.ceil(bgHeight / gConfig.partyListBgScale);

            backgroundPrim.br.visible = backgroundPrim.br.exists;
            backgroundPrim.br.position_x = backgroundPrim.bg.position_x + bgWidth - math.floor((settings.borderSize * gConfig.partyListBgScale) - (settings.bgOffset * gConfig.partyListBgScale));
            backgroundPrim.br.position_y = backgroundPrim.bg.position_y + bgHeight - math.floor((settings.borderSize * gConfig.partyListBgScale) - (settings.bgOffset * gConfig.partyListBgScale));
            backgroundPrim.br.width = settings.borderSize;
            backgroundPrim.br.height = settings.borderSize;

            backgroundPrim.tr.visible = backgroundPrim.tr.exists;
            backgroundPrim.tr.position_x = backgroundPrim.br.position_x;
            backgroundPrim.tr.position_y = backgroundPrim.bg.position_y - settings.bgOffset * gConfig.partyListBgScale;
            backgroundPrim.tr.width = backgroundPrim.br.width;
            backgroundPrim.tr.height = math.ceil((backgroundPrim.br.position_y - backgroundPrim.tr.position_y) / gConfig.partyListBgScale);

            backgroundPrim.tl.visible = backgroundPrim.tl.exists;
            backgroundPrim.tl.position_x = backgroundPrim.bg.position_x - settings.bgOffset * gConfig.partyListBgScale;
            backgroundPrim.tl.position_y = backgroundPrim.tr.position_y;
            backgroundPrim.tl.width = math.ceil((backgroundPrim.tr.position_x - backgroundPrim.tl.position_x) / gConfig.partyListBgScale);
            backgroundPrim.tl.height = backgroundPrim.tr.height;

            backgroundPrim.bl.visible = backgroundPrim.bl.exists;
            backgroundPrim.bl.position_x = backgroundPrim.tl.position_x;
            backgroundPrim.bl.position_y = backgroundPrim.br.position_y;
            backgroundPrim.bl.width = backgroundPrim.tl.width;
            backgroundPrim.bl.height = backgroundPrim.br.height;
        end
    end
    
    imgui.PopStyleVar(2); -- Pop the style vars
end

partyList.SetHidden = function(hidden)
	if (hidden == true) then
        UpdateTextVisibility(false);
        selectionPrim.visible = false;
        arrowPrim.visible = false;
        treasureIconPrim.visible = false;
	end
end

partyList.SetTreasurePoolHidden = function(hidden)
	if (hidden == true) then
		treasurePoolVisible = false;
		-- Exit controller mode when hiding
		treasurePoolControllerActive = false;
		-- Hide treasure icon
		treasureIconPrim.visible = false;
		-- Hide background primitives
		local backgroundPrim = treasurePoolWindowPrim.background;
		if (backgroundPrim and type(backgroundPrim) == "table") then
			for _, k in ipairs(bgImageKeys) do
				if (backgroundPrim[k]) then
					backgroundPrim[k].visible = false;
				end
			end
		end
	else
		treasurePoolVisible = true;
	end
end

partyList.HandleZonePacket = function(e)
    statusHandler.clear_cache();
end

-- ============================
-- Treasure Pool Controller Functions
-- ============================

-- Initialize controller input for treasure pool
partyList.InitializeTreasurePoolController = function()
    if (not treasurePoolInputCB) then
        -- Register input callbacks following tCrossBar pattern
        ashita.events.register('dinput_button', 'treasurepool_dinput_cb', partyList.HandleTreasurePoolInput);
        ashita.events.register('xinput_button', 'treasurepool_xinput_cb', partyList.HandleTreasurePoolInput);
        
        treasurePoolInputCB = true;
    end
end

-- Cleanup controller input
partyList.CleanupTreasurePoolController = function()
    if (treasurePoolInputCB) then
        ashita.events.unregister('dinput_button', 'treasurepool_dinput_cb');
        ashita.events.unregister('xinput_button', 'treasurepool_xinput_cb');
        
        treasurePoolInputCB = false;
    end
    
    -- Reset RB hold state
    rbPressed = false;
    rbToggleTriggered = false;
    rbPressTime = 0;
end

-- Check if any shoulder buttons besides R1 are pressed (defer to tCrossBar)
local function ShouldDeferToTCrossBar(buttonName, pressed)
    -- Define shoulder buttons (these names match tCrossBar's button mapping)
    local shoulderButtons = {
        ['L1'] = true,
        ['L2'] = true, 
        ['R2'] = true,
    };
    
    -- If any shoulder button other than R1 is involved, defer to tCrossBar
    if (shoulderButtons[buttonName] and pressed) then
        return true;
    end
    
    return false;
end

-- Get number of items in treasure pool (abstraction for real vs mock data)
local function GetLocalTreasurePoolItemCount()
    if (#treasurePoolWinnableItems > 0) then
        return #treasurePoolWinnableItems;
    end
    -- In preview mode, return mock data count
    if (showConfig[1] and gConfig.partyListPreview) then
        return #treasurePoolMockData;
    end
    return 0;
end

-- Check if player's inventory has space
local function HasInventorySpace()
    local inventory = AshitaCore:GetMemoryManager():GetInventory();
    if (not inventory) then
        return false; -- Assume no space if we can't check
    end
    
    -- Check main inventory container (0)
    local containerMax = inventory:GetContainerCountMax(0);
    local containerCount = inventory:GetContainerCount(0);
    
    return containerCount < containerMax;
end

-- Lot on treasure pool item using treasure pool library
local function LotOnTreasurePoolItem(slotIndex)
    -- Validate slot index (must be 0-9 for treasure pool)
    if (slotIndex < 0 or slotIndex > 9) then
        print('[HXUI] Invalid slot index for lot: ' .. tostring(slotIndex));
        return false;
    end
    
    -- Check if inventory has space before lotting
    if (not HasInventorySpace()) then
        print(chat.header('[HotTub]') + chat.message('Cannot cast lots. Your inventory is full.'));
        return false;
    end
    
    -- Use treasure pool library's lot function (based on lootwhore)
    if (treasurePoolLib and treasurePoolLib.LotItem) then
        local success = treasurePoolLib.LotItem(slotIndex);
        if (success) then
            print('[HXUI] Lotting on item in slot ' .. (slotIndex + 1));
            return true;
        else
            print('[HXUI] Failed to lot on item in slot ' .. (slotIndex + 1));
            return false;
        end
    end
    
    print('[HXUI] Treasure pool library not available for lotting');
    return false;
end

-- Pass on treasure pool item using treasure pool library
local function PassOnTreasurePoolItem(slotIndex)
    -- Validate slot index (must be 0-9 for treasure pool)
    if (slotIndex < 0 or slotIndex > 9) then
        print('[HXUI] Invalid slot index for pass: ' .. tostring(slotIndex));
        return false;
    end
    
    -- Use treasure pool library's pass function (based on lootwhore)
    if (treasurePoolLib and treasurePoolLib.PassItem) then
        local success = treasurePoolLib.PassItem(slotIndex);
        if (success) then
            print('[HXUI] Passing on item in slot ' .. (slotIndex + 1));
            return true;
        else
            print('[HXUI] Failed to pass on item in slot ' .. (slotIndex + 1));
            return false;
        end
    end
    
    print('[HXUI] Treasure pool library not available for passing');
    return false;
end

-- Ignore treasure pool item using treasure pool library
local function IgnoreTreasurePoolItem(slotIndex)
    -- Validate slot index (must be 0-9 for treasure pool)
    if (slotIndex < 0 or slotIndex > 9) then
        print('[HXUI] Invalid slot index for ignore: ' .. tostring(slotIndex));
        return false;
    end
    
    -- Use treasure pool library's ignore function
    if (treasurePoolLib and treasurePoolLib.IgnoreItem) then
        local success = treasurePoolLib.IgnoreItem(slotIndex);
        if (success) then
            print('[HXUI] Ignored item in slot ' .. (slotIndex + 1));
            return true;
        else
            print('[HXUI] Failed to ignore item in slot ' .. (slotIndex + 1));
            return false;
        end
    end
    
    print('[HXUI] Treasure pool library not available for ignoring');
    return false;
end

-- Main controller input handler
partyList.HandleTreasurePoolInput = function(e)
    -- Following tCrossBar pattern: e.button is numeric ID, e.state is 1/0
    local buttonId = e.button;
    -- Handle different state systems: triggers use >120, other buttons use 1/0
    local pressed = (e.state == 1 or e.state > 120);
    
    -- Map button IDs to names (using correct key mappings)
    local buttonNames = {
        [0] = 'Dpad_Up',      -- Up
        [1] = 'Dpad_Down',    -- Down  
        [2] = 'Dpad_Left',    -- Left
        [3] = 'Dpad_Right',   -- Right
        [4] = 'Start',        -- Start
        [5] = 'Select',       -- Select/Back
        [8] = 'L1',           -- Left bumper
        [9] = 'R1',           -- Right bumper (RB)
        [10] = 'L2',          -- Left trigger (original mapping)
        [11] = 'R2',          -- Right trigger (original mapping)
        [12] = 'A',           -- A button
        [13] = 'B',           -- B button  
        [14] = 'X',           -- X button
        [15] = 'Y',           -- Y button
        [16] = 'L2',          -- Left trigger (actual mapping)
        [17] = 'R2',          -- Right trigger (actual mapping)
    };
    
    local buttonName = buttonNames[buttonId];
    if (not buttonName) then
        return; -- Unknown button, don't handle
    end
    
    -- Update trigger state tracking first
    if (buttonName == 'L2') then
        triggerPressed.L2 = pressed;
    elseif (buttonName == 'R2') then
        triggerPressed.R2 = pressed;
    end
    
    -- If any trigger is currently pressed, ignore ALL inputs (let tCrossBar handle)
    if (triggerPressed.L2 or triggerPressed.R2) then
        return; -- Don't handle any inputs when triggers are active
    end
    
    -- Defer to tCrossBar if other shoulder buttons are involved
    if (ShouldDeferToTCrossBar(buttonName, pressed)) then
        return; -- Allow tCrossBar to handle
    end
    
    local itemCount = GetLocalTreasurePoolItemCount();
    local shouldBlock = false;
    
    -- R1 (RB) hold/press handling for focus vs toggle
    if (buttonName == 'R1') then
        local hasItems = (itemCount > 0);
        local isPreviewMode = (showConfig[1] and gConfig.partyListPreview);
        local canActivate = (hasItems or isPreviewMode) and gConfig.showTreasurePool;
        
        if (pressed) then
            -- RB pressed - start timing for hold detection
            rbPressed = true;
            rbPressTime = os.clock();
            rbToggleTriggered = false;
            shouldBlock = true; -- Always block RB from going to game
        else
            -- RB released
            if (rbPressed and not rbToggleTriggered) then
                -- Short press detected - focus treasure pool if visible and has items
                if (canActivate and treasurePoolVisible) then
                    treasurePoolControllerActive = true;
                    treasurePoolSelected = 1; -- Reset to first item
                end
            end
            
            -- Reset RB tracking state
            rbPressed = false;
            rbToggleTriggered = false;
            shouldBlock = true; -- Always block RB from going to game
        end
    end
    
    -- Handle other inputs only if controller is active and button is pressed
    if (treasurePoolControllerActive and pressed) then
        -- D-pad navigation (only through data rows, not header)
        if (buttonName == 'Dpad_Up') then
            if (treasurePoolSelected > 1) then
                treasurePoolSelected = treasurePoolSelected - 1;
            end
            shouldBlock = true;
        elseif (buttonName == 'Dpad_Down') then
            if (treasurePoolSelected < itemCount) then
                treasurePoolSelected = treasurePoolSelected + 1;
            end
            shouldBlock = true;
        elseif (buttonName == 'Dpad_Left' or buttonName == 'Dpad_Right') then
            -- Block left/right dpad but don't handle (no horizontal navigation)
            shouldBlock = true;
        end
        
        -- Block system buttons when controller is active
        if (buttonName == 'Start' or buttonName == 'Select') then
            shouldBlock = true;
        end
        
        -- Action buttons
        if (buttonName == 'B') then
            -- Exit treasure pool controller mode
            treasurePoolControllerActive = false;
            -- Reset trigger state when exiting
            triggerPressed.L2 = false;
            triggerPressed.R2 = false;
            shouldBlock = true;
        elseif (buttonName == 'A') then
            -- A button: Lot on selected item
            if (treasurePoolSelected >= 1 and treasurePoolSelected <= GetLocalTreasurePoolItemCount()) then
                -- Get the actual slot index from the selected item data
                local selectedItem = treasurePoolWinnableItems[treasurePoolSelected];
                if (selectedItem and selectedItem.slotIndex ~= nil) then
                    -- Use actionSlotIndex for consolidated items, slotIndex for regular items
                    local targetSlotIndex = selectedItem.actionSlotIndex or selectedItem.slotIndex;
                    LotOnTreasurePoolItem(targetSlotIndex);
                else
                    print('[HXUI] Invalid item selection for lotting');
                end
            end
            shouldBlock = true;
        elseif (buttonName == 'X') then
            -- X button: Pass on selected item
            if (treasurePoolSelected >= 1 and treasurePoolSelected <= GetLocalTreasurePoolItemCount()) then
                -- Get the actual slot index from the selected item data
                local selectedItem = treasurePoolWinnableItems[treasurePoolSelected];
                if (selectedItem and selectedItem.slotIndex ~= nil) then
                    -- Use actionSlotIndex for consolidated items, slotIndex for regular items
                    local targetSlotIndex = selectedItem.actionSlotIndex or selectedItem.slotIndex;
                    PassOnTreasurePoolItem(targetSlotIndex);
                else
                    print('[HXUI] Invalid item selection for passing');
                end
            end
            shouldBlock = true;
        elseif (buttonName == 'Y') then
            -- Y button: Ignore selected item
            if (treasurePoolSelected >= 1 and treasurePoolSelected <= GetLocalTreasurePoolItemCount()) then
                -- Get the actual slot index from the selected item data
                local selectedItem = treasurePoolWinnableItems[treasurePoolSelected];
                if (selectedItem and selectedItem.slotIndex ~= nil) then
                    -- Use actionSlotIndex for consolidated items, slotIndex for regular items
                    local targetSlotIndex = selectedItem.actionSlotIndex or selectedItem.slotIndex;
                    IgnoreTreasurePoolItem(targetSlotIndex);
                else
                    print('[HXUI] Invalid item selection for ignoring');
                end
            end
            shouldBlock = true;
        end
    end
    
    -- Block input from reaching game engine following tCrossBar pattern
    if (shouldBlock) then
        e.blocked = true;
    end
end

-- Update treasure pool selection state
partyList.SetTreasurePoolSelection = function(index)
    local itemCount = GetLocalTreasurePoolItemCount();
    if (index >= 1 and index <= itemCount) then
        treasurePoolSelected = index;
    end
end

-- Get current selection index
partyList.GetTreasurePoolSelection = function()
    return treasurePoolSelected;
end

-- Check if controller is active
partyList.IsTreasurePoolControllerActive = function()
    return treasurePoolControllerActive;
end

-- Force exit controller mode (for external use)
partyList.ExitTreasurePoolController = function()
    treasurePoolControllerActive = false;
    -- Reset trigger state when exiting controller mode
    triggerPressed.L2 = false;
    triggerPressed.R2 = false;
    -- Reset RB hold state
    rbPressed = false;
    rbToggleTriggered = false;
    rbPressTime = 0;
end

-- Clear ignored items (for command interface)
partyList.ClearIgnoredItems = function()
    if (treasurePoolLib and treasurePoolLib.ClearIgnoredItems) then
        treasurePoolLib.ClearIgnoredItems();
    else
        print('[HXUI] Treasure pool library not available.');
    end
end

-- Ignore specific slot (for command interface)
partyList.IgnoreSlot = function(slotIndex)
    if (treasurePoolLib and treasurePoolLib.IgnoreItem) then
        local success = treasurePoolLib.IgnoreItem(slotIndex);
        if (not success) then
            print('[HXUI] Failed to ignore item in slot ' .. (slotIndex + 1));
        end
    else
        print('[HXUI] Treasure pool library not available.');
    end
end

-- Cleanup function for addon unload
partyList.Cleanup = function()
    ResetTreasurePoolData(); -- Clear all treasure pool state on addon unload
    partyList.CleanupTreasurePoolController();
end

-- Handle treasure pool packets
partyList.HandleTreasurePoolPacket = function(packetId, data, ashitaCore)
    
    -- Initialize treasure pool library if not already done
    if (not treasurePoolInitialized) then
        treasurePoolLib.Initialize(ashitaCore);
        treasurePoolInitialized = true;
    end
    
    -- Forward packet to treasure pool library
    treasurePoolLib.HandleIncomingPacket(packetId, data);
end

return partyList;