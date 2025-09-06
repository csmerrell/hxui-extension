require('common');
local chat = require('chat');
local struct = require('struct');

local treasurePool = {};

-- File logging helper function
-- local function LogMessage(message)
--     -- Print to chat (automatically logged to chat log file)
--     print(string.format('[TreasurePool] %s', message));
-- end

-- Module dependencies (to be injected by parent)
local ashitaCore = nil;

-- Treasure Pool State Enums (borrowed from Lootwhore)
local LotState = {
    Untouched = 0,
    Lotted = 1,
    Passed = 2
};

-- Generate a simple UUID for treasure pool items
local function GenerateUUID()
    local chars = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz';
    local uuid = '';
    for i = 1, 16 do
        local rand = math.random(1, #chars);
        uuid = uuid .. chars:sub(rand, rand);
    end
    return uuid;
end

-- Treasure Pool Slot Structure (based on Lootwhore's TreasurePoolSlot_t)
local function CreateTreasurePoolSlot(itemId, lockoutDelay)
    return {
        Id = itemId or 0,
        UUID = GenerateUUID(), -- Unique identifier for ignore functionality
        Status = LotState.Untouched,
        PacketAttempts = 0,
        Lockout = os.clock() + (lockoutDelay or 0) / 1000, -- Convert ms to seconds
        LastUpdateTime = os.clock(),
        PlayerLots = {} -- Track all player lots/passes: [serverId] = {lot = number, name = string}
    };
end

-- Internal state tracking
local treasurePoolSlots = {}; -- Array of 10 slots (0-9)
local ignoredItems = {}; -- Set of ignored item UUIDs: [uuid] = true
local myServerId = 0;
local myName = "";
local inventoryLoading = false; -- Start as false since we're not tracking packet-based loading
local lastPacketTime = 0;

-- Configuration
local maxRetries = 3;
local retryDelay = 5.0; -- seconds
local randomDelayMin = 0;
local randomDelayMax = 1000; -- milliseconds

-- Item name cache to prevent lookup failures
local itemNameCache = {};

-- Callbacks for UI updates
local onTreasurePoolUpdated = nil;
local onItemEntered = nil;
local onItemRemoved = nil;

-- Helper function to clear a treasure pool slot and clean up ignored items
local function ClearTreasurePoolSlot(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return;
    end
    
    local slot = treasurePoolSlots[slotIndex];
    if (slot and slot.UUID) then
        -- Remove from ignored list if it was ignored
        if (ignoredItems[slot.UUID]) then
            ignoredItems[slot.UUID] = nil;
        end
    end
    
    -- Create fresh slot
    treasurePoolSlots[slotIndex] = CreateTreasurePoolSlot();
end

-- Initialize treasure pool slots
local function InitializeTreasurePoolSlots()
    for i = 0, 9 do
        ClearTreasurePoolSlot(i);
    end
end

-- Get item name with caching
local function GetItemName(itemId)
    if (itemNameCache[itemId]) then
        return itemNameCache[itemId];
    end
    
    if (not ashitaCore) then
        itemNameCache[itemId] = 'Item #' .. tostring(itemId);
        return itemNameCache[itemId];
    end
    
    local resource = ashitaCore:GetResourceManager():GetItemById(itemId);
    if (resource) then
        local name = resource.Name[1] or resource.LogNameSingular[1] or 'Unknown Item';
        itemNameCache[itemId] = name;
        return name;
    end
    
    itemNameCache[itemId] = 'Unknown Item #' .. tostring(itemId);
    return itemNameCache[itemId];
end

-- Helper function to get party member name by server ID
local function GetPartyMemberNameByServerId(serverId)
    if (not ashitaCore) then
        return nil;
    end
    
    local party = ashitaCore:GetMemoryManager():GetParty();
    if (not party) then
        return nil;
    end
    
    for i = 0, 17 do
        if (party:GetMemberIsActive(i) ~= 0 and party:GetMemberServerId(i) == serverId) then
            return party:GetMemberName(i);
        end
    end
    
    return nil;
end

-- Helper function to check if party member can lot (not Trust, in same zone)
local function CanMemberLot(memIdx)
    if (not ashitaCore) then
        return false;
    end
    
    local party = ashitaCore:GetMemoryManager():GetParty();
    if (not party or party:GetMemberIsActive(memIdx) == 0) then
        return false;
    end
    
    local playerZone = party:GetMemberZone(0);
    
    -- Check if member is in same zone
    if (party:GetMemberZone(memIdx) ~= playerZone) then
        return false;
    end
    
    -- Check if member is a Trust (target index range 0x700-0x8FF indicates Trust)
    local targetIndex = party:GetMemberTargetIndex(memIdx);
    if (targetIndex > 0x6FF and targetIndex <= 0x8FF) then
        return false;
    end
    
    return true;
end

-- Get list of party members waiting to lot on an item
local function GetWaitingMembers(slotIndex)
    if (not ashitaCore) then
        return "";
    end
    
    local party = ashitaCore:GetMemoryManager():GetParty();
    if (not party) then
        return "";
    end
    
    local waitingNames = {};
    
    for i = 0, 17 do
        if (CanMemberLot(i)) then
            local lot = party:GetMemberTreasureLot(i, slotIndex);
            -- 0 means no lot, 0xFFFF means passed
            if (lot == 0) then
                table.insert(waitingNames, party:GetMemberName(i));
            end
        end
    end
    
    return table.concat(waitingNames, ", ");
end

-- Get current winner information for an item
local function GetCurrentWinner(treasureItem)
    if (not treasureItem or treasureItem.WinningLot == 0) then
        return "--";
    end
    
    -- Extract winner name from treasure item
    local winnerName = "";
    if (treasureItem.WinningEntityName) then
        -- Convert byte array to string (Ashita style)
        local nameBytes = treasureItem.WinningEntityName;
        for i = 0, 15 do
            if (nameBytes[i] == 0) then
                break;
            end
            winnerName = winnerName .. string.char(nameBytes[i]);
        end
    end
    
    if (winnerName and winnerName ~= "") then
        return string.format("%s (%d)", winnerName, treasureItem.WinningLot);
    end
    
    return string.format("(%d)", treasureItem.WinningLot);
end

-- Get player's lot on an item
local function GetMyLot(treasureItem)
    if (not treasureItem) then
        return "--";
    end
    
    if (treasureItem.Lot == 0) then
        return "--";
    elseif (treasureItem.Lot == 0xFFFF) then
        return "PASS";
    else
        return tostring(treasureItem.Lot);
    end
end

-- Determine if item is winnable or lost for the player
local function IsItemWinnable(treasureItem, slotIndex)
    if (not treasureItem) then
        return false;
    end
    
    -- If we haven't lotted or passed, it's winnable
    if (treasureItem.Lot == 0) then
        return true;
    end
    
    -- If we passed, it's lost
    if (treasureItem.Lot == 0xFFFF) then
        return false;
    end
    
    -- If we lotted and we're currently winning, it's winnable
    if (treasureItem.WinningEntityServerId == myServerId) then
        return true;
    end
    
    -- If we lotted but someone else is winning with a higher lot, it's lost
    if (treasureItem.WinningLot > treasureItem.Lot) then
        return false;
    end
    
    -- If we lotted and tied for highest, it's winnable
    return true;
end

-- Consolidate treasure pool items by name into separate rows per lot status
local function ConsolidateTreasurePoolItems(winnableItems, lostItems)
    local consolidatedWinnable = {};
    local consolidatedLost = {};
    
    -- Categorize items by name and lot status
    local itemCategories = {}; -- [itemName] = { notLotted = {}, winning = {}, lost = {} }
    
    -- Process winnable items
    for _, item in ipairs(winnableItems) do
        local itemName = item.item;
        if (not itemCategories[itemName]) then
            itemCategories[itemName] = { notLotted = {}, winning = {}, lost = {} };
        end
        if (item.myLot == "--") then
            table.insert(itemCategories[itemName].notLotted, item);
        elseif (item.myLot == "PASS") then
            table.insert(itemCategories[itemName].lost, item);
        elseif (item.myLot == "LOT") then
            -- Use server ID for winner check
            local slot = treasurePoolSlots[item.slotIndex];
            if slot and slot.PlayerLots and slot.PlayerLots[myServerId] and slot.PlayerLots[myServerId].lot then
                local highestLot = 0;
                local winnerServerId = nil;
                for serverId, lotData in pairs(slot.PlayerLots) do
                    if lotData.lot ~= 0xFFFF and lotData.lot > highestLot then
                        highestLot = lotData.lot;
                        winnerServerId = serverId;
                    end
                end
                if winnerServerId == myServerId and slot.PlayerLots[myServerId].lot == highestLot then
                    table.insert(itemCategories[itemName].winning, item);
                else
                    table.insert(itemCategories[itemName].lost, item);
                end
            else
                table.insert(itemCategories[itemName].lost, item);
            end
        else
            table.insert(itemCategories[itemName].lost, item);
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
            -- Find item with shortest timer
            local shortestItem = categories.notLotted[1];
            for _, item in ipairs(categories.notLotted) do
                if item.timeToLive and shortestItem.timeToLive and item.timeToLive < shortestItem.timeToLive then
                    shortestItem = item;
                end
            end
            local displayName = itemName;
            if (notLottedCount > 1) then
                displayName = string.format("x%d %s", notLottedCount, itemName);
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
                itemId = lastItem.itemId,
                slotIndex = firstItem.slotIndex, -- Use first item's slot for sorting
                actionSlotIndex = lastItem.slotIndex, -- Use last item's slot for actions
                uuid = lastItem.uuid, -- Use last item's UUID for actions
                myLot = "--",
                currentWinner = currentWinner,
                waitingFor = table.concat(allWaitingPlayers, ", "),
                timeToLive = shortestItem.timeToLive,
                dropTime = shortestItem.dropTime,
                consolidatedCount = notLottedCount,
                sourceItems = categories.notLotted
            };
            
            table.insert(consolidatedWinnable, consolidatedItem);
        end
        
        -- Create "winning" row if we have items we're winning
        if (winningCount > 0) then
            -- Sort by slot index (ascending for consistent ordering)
            table.sort(categories.winning, function(a, b) return a.slotIndex < b.slotIndex end);
            local firstItem = categories.winning[1]; -- For sorting position
            local lastItem = categories.winning[#categories.winning]; -- For actions
            -- Find item with shortest timer
            local shortestItem = categories.winning[1];
            for _, item in ipairs(categories.winning) do
                if item.timeToLive and shortestItem.timeToLive and item.timeToLive < shortestItem.timeToLive then
                    shortestItem = item;
                end
            end
            local displayName = itemName;
            if (winningCount > 1) then
                displayName = string.format("x%d %s", winningCount, itemName);
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
            
            -- Determine current winner display - show my name if I'm winning
            local currentWinner = "--";
            local amIWinning = false;
            for _, item in ipairs(categories.winning) do
                if (item.currentWinner and item.currentWinner ~= "--") then
                    -- Check if the winner string contains my name
                    if (string.find(item.currentWinner, myName or "Player")) then
                        amIWinning = true;
                        currentWinner = myName or "You";
                        break;
                    else
                        currentWinner = item.currentWinner;
                        break;
                    end
                end
            end
            
            local consolidatedItem = {
                item = displayName,
                itemId = lastItem.itemId,
                slotIndex = firstItem.slotIndex, -- Use first item's slot for sorting
                actionSlotIndex = lastItem.slotIndex, -- Use last item's slot for actions
                uuid = lastItem.uuid, -- Use last item's UUID for actions
                myLot = lotDisplay,
                currentWinner = currentWinner,
                waitingFor = table.concat(allWaitingPlayers, ", "),
                timeToLive = shortestItem.timeToLive,
                dropTime = shortestItem.dropTime,
                consolidatedCount = winningCount,
                sourceItems = categories.winning
            };
            
            table.insert(consolidatedWinnable, consolidatedItem);
        end
        
        -- Create consolidated lost entry if we have lost items
        if (lostCount > 0) then
            -- Sort by slot index (ascending for consistent ordering)
            table.sort(categories.lost, function(a, b) return a.slotIndex < b.slotIndex end);
            local firstItem = categories.lost[1]; -- For sorting position
            -- Find item with shortest timer
            local shortestItem = categories.lost[1];
            for _, item in ipairs(categories.lost) do
                if item.timeToLive and shortestItem.timeToLive and item.timeToLive < shortestItem.timeToLive then
                    shortestItem = item;
                end
            end
            local displayName = itemName;
            if (lostCount > 1) then
                displayName = string.format("x%d %s", lostCount, itemName);
            end
            
            -- Get winner info (use first lost item's winner)
            local winner = firstItem.winner or "Unknown";
            
            local consolidatedItem = {
                item = displayName,
                itemId = firstItem.itemId,
                slotIndex = firstItem.slotIndex,
                uuid = firstItem.uuid,
                winner = winner,
                timeToLive = shortestItem.timeToLive,
                dropTime = shortestItem.dropTime,
                consolidatedCount = lostCount,
                sourceItems = categories.lost
            };
            
            table.insert(consolidatedLost, consolidatedItem);
        end
    end
    
    -- Sort consolidated items by slot index (ascending)
    table.sort(consolidatedWinnable, function(a, b) return a.slotIndex < b.slotIndex end);
    table.sort(consolidatedLost, function(a, b) return a.slotIndex < b.slotIndex end);
    
    return consolidatedWinnable, consolidatedLost;
end

-- Process treasure pool data from internal packet-tracked state (pure packet approach)
local function ProcessTreasurePoolData()
    local winnableItems = {};
    local lostItems = {};
    
    -- Process each treasure pool slot from our internal tracking
    for i = 0, 9 do
        local slot = treasurePoolSlots[i];
        if (slot and slot.Id ~= 0) then
            -- Skip ignored items
            if (not ignoredItems[slot.UUID]) then
                local itemName = GetItemName(slot.Id);
                local displayName = itemName;
                
                -- Get lot information
                local myLotStatus, myLotValue = treasurePool.GetMyLotStatus(i);
                local currentWinner, highestLot = treasurePool.GetSlotWinner(i);
                local waitingPlayers = treasurePool.GetSlotWaitingPlayers(i);
                
                local itemData = {
                    item = displayName,
                    itemId = slot.Id,
                    slotIndex = i,
                    uuid = slot.UUID, -- Include UUID for ignore functionality
                    myLot = myLotStatus == "LOT" and tostring(myLotValue) or myLotStatus,
                    currentWinner = currentWinner and string.format("(%d) %s", highestLot, currentWinner) or "--",
                    waitingFor = table.concat(waitingPlayers, ", "),
                    timeToLive = 0, -- Not available from packet tracking
                    dropTime = slot.LastUpdateTime
                };
                
                -- Determine if item is winnable or lost
                if (myLotStatus == "PASS") then
                    -- We passed, so it's lost for us
                    itemData.winner = currentWinner or "Unknown";
                    table.insert(lostItems, itemData);
                elseif (myLotStatus == "--") then
                    -- We haven't acted yet, so it's winnable
                    table.insert(winnableItems, itemData);
                elseif (myLotStatus == "LOT") then
                    -- We lotted - check if we're still winning
                    if (not currentWinner or myLotValue >= highestLot) then
                        -- We're winning or tied for highest lot
                        table.insert(winnableItems, itemData);
                    else
                        -- Someone else has a higher lot, so it's lost
                        itemData.winner = currentWinner;
                        table.insert(lostItems, itemData);
                    end
                else
                    -- Fallback to old logic for edge cases
                    if (slot.Status == LotState.Untouched or slot.Status == LotState.Lotted) then
                        table.insert(winnableItems, itemData);
                    else
                        itemData.winner = "Unknown";
                        table.insert(lostItems, itemData);
                    end
                end
            end
        end
    end
    
    -- Sort items alphabetically for consistent display
    table.sort(winnableItems, function(a, b) return a.item < b.item end);
    table.sort(lostItems, function(a, b) return a.item < b.item end);
    
    return winnableItems, lostItems;
end

-- Packet handling functions (borrowed from Lootwhore logic)

-- Handle zone change packet (0x0A) - reset treasure pool state
local function HandleZonePacket(data)
    -- Get our ID/Name from packet data
    myServerId = struct.unpack('I', data, 0x04);
    local nameOffset = 0x84;
    local nameBytes = {};
    for i = 0, 15 do
        local byte = struct.unpack('B', data, nameOffset + i);
        if byte == 0 then break end
        table.insert(nameBytes, string.char(byte));
    end
    local newName = table.concat(nameBytes);
    
    if (newName ~= myName) then
        myName = newName;
    end
    
    -- Reset treasure pool state on zone change
    InitializeTreasurePoolSlots();
    
    if (onTreasurePoolUpdated) then
        onTreasurePoolUpdated();
    end
end

-- Handle item entering treasure pool (0xD2)
local function HandleItemEnterPacket(data)
    -- Extract pool index and item ID from confirmed offsets
    local poolIndex = struct.unpack('B', data, 0x14 + 1); -- Pool index at 0x14
    local itemId = struct.unpack('H', data, 0x10 + 1);    -- Item ID at 0x10 (little endian)
    
    if (poolIndex >= 0 and poolIndex <= 9) then
        -- Calculate random delay if configured
        local delay = 0;
        if (randomDelayMax > 0) then
            delay = math.random(randomDelayMin, randomDelayMax);
        end
        
        treasurePoolSlots[poolIndex] = CreateTreasurePoolSlot(itemId, delay);
                
        if (onItemEntered) then
            onItemEntered(poolIndex, itemId);
        end
        
        if (onTreasurePoolUpdated) then
            onTreasurePoolUpdated();
        end
    else
        -- LogMessage(string.format('Invalid pool index: %d', poolIndex));
    end
end

-- Handle lot update packet (0xD3)
local function HandleLotUpdatePacket(data)
    -- Determine packet type by checking the sort flag
    local sortFlag = struct.unpack('B', data, 0x15 + 1);  -- 0x15 determines packet type
    local poolIndex = struct.unpack('B', data, 0x14 + 1); -- Pool index at 0x14
    local serverId = 0;
    local winnerName = "";
    
    if (sortFlag == 2) then
        -- Failed distribution packet
        if (poolIndex >= 0 and poolIndex <= 9) then
            local itemId = treasurePoolSlots[poolIndex].Id;
            local itemName = GetItemName(itemId);
            ClearTreasurePoolSlot(poolIndex); -- Use helper to clean up ignored items
                        
            if (onItemRemoved) then
                onItemRemoved(poolIndex, itemId);
            end
        end
        
    elseif (sortFlag == 1) then
        -- Successful distribution packet
        serverId = struct.unpack('I', data, 0x04 + 1);  -- Winner server ID at 0x04
        
        -- Extract winner name starting at 0x17
        local nameBytes = {};
        for i = 0, 15 do
            local byte = struct.unpack('B', data, 0x17 + i + 1);
            if byte == 0 then break end
            table.insert(nameBytes, string.char(byte));
        end
        winnerName = table.concat(nameBytes);
        
        if (poolIndex >= 0 and poolIndex <= 9) then
            local itemId = treasurePoolSlots[poolIndex].Id;
            local itemName = GetItemName(itemId);
            ClearTreasurePoolSlot(poolIndex); -- Use helper to clean up ignored items
            
            if (onItemRemoved) then
                onItemRemoved(poolIndex, itemId);
            end
        end
        
    elseif (sortFlag == 0) then
        -- Lot/pass packet
        local lotValue = struct.unpack('H', data, 0x12 + 1);  -- Lot value at 0x12
        serverId = struct.unpack('I', data, 0x08 + 1);        -- Player server ID at 0x08
        
        if (poolIndex >= 0 and poolIndex <= 9) then
            -- Get player name from server ID
            local playerName = GetPartyMemberNameByServerId(serverId) or string.format("Player_%d", serverId);
            
            -- Initialize PlayerLots table if needed
            if (not treasurePoolSlots[poolIndex].PlayerLots) then
                treasurePoolSlots[poolIndex].PlayerLots = {};
            end
            
            -- Record the lot/pass
            treasurePoolSlots[poolIndex].PlayerLots[serverId] = {
                lot = lotValue,
                name = playerName
            };
            
            if (lotValue == 0xFFFF) then
                -- Pass packet
                if (serverId == myServerId) then
                    treasurePoolSlots[poolIndex].Status = LotState.Passed;
                    local itemName = GetItemName(treasurePoolSlots[poolIndex].Id);
                    -- LogMessage(string.format('You passed on: %s', itemName));
                end
            else
                -- Lot packet (1-999)
                if (serverId == myServerId) then
                    treasurePoolSlots[poolIndex].Status = LotState.Lotted;
                    local itemName = GetItemName(treasurePoolSlots[poolIndex].Id);
                    
                    -- Check if this item was previously ignored and remove from ignore list
                    local slot = treasurePoolSlots[poolIndex];
                    if (slot and slot.UUID and ignoredItems[slot.UUID]) then
                        ignoredItems[slot.UUID] = nil;
                        print(chat.header('[HXUI]') + chat.message(string.format('Removed "%s" from ignore list (you cast a lot on it)', itemName)));
                    end
                    
                    -- LogMessage(string.format('You lotted %d on: %s', lotValue, itemName));
                end
            end
        end
    end
    
    if (poolIndex and poolIndex >= 0 and poolIndex <= 9) then
        if (onTreasurePoolUpdated) then
            onTreasurePoolUpdated();
        end
    end
end

-- Handle inventory loading status
local function HandleInventoryPacket(packetId)
    if (packetId == 0x0B) then
        inventoryLoading = true;
    elseif (packetId == 0x1D) then
        inventoryLoading = false;
    end
end

-- Handle outgoing lot/pass packets to update local state
local function HandleOutgoingLotPacket(data)
    local poolIndex = struct.unpack('B', data, 0x04);
    if (poolIndex >= 0 and poolIndex <= 9) then
        treasurePoolSlots[poolIndex].Status = LotState.Lotted;
        treasurePoolSlots[poolIndex].PacketAttempts = treasurePoolSlots[poolIndex].PacketAttempts + 1;
        treasurePoolSlots[poolIndex].Lockout = os.clock() + retryDelay;
    end
end

local function HandleOutgoingPassPacket(data)
    local poolIndex = struct.unpack('B', data, 0x04);
    if (poolIndex >= 0 and poolIndex <= 9) then
        treasurePoolSlots[poolIndex].Status = LotState.Passed;
        treasurePoolSlots[poolIndex].PacketAttempts = treasurePoolSlots[poolIndex].PacketAttempts + 1;
        treasurePoolSlots[poolIndex].Lockout = os.clock() + retryDelay;
    end
end

-- Public API

-- Initialize the treasure pool system
function treasurePool.Initialize(ashitaCoreRef)
    ashitaCore = ashitaCoreRef;
    InitializeTreasurePoolSlots();
    
    -- Get initial player info
    if (ashitaCore) then
        local party = ashitaCore:GetMemoryManager():GetParty();
        if (party and party:GetMemberIsActive(0) ~= 0) then
            myServerId = party:GetMemberServerId(0);
            myName = party:GetMemberName(0);
        end
    end
end

-- Set callbacks for UI updates
function treasurePool.SetCallbacks(updateCallback, enterCallback, removeCallback)
    onTreasurePoolUpdated = updateCallback;
    onItemEntered = enterCallback;
    onItemRemoved = removeCallback;
end

-- Get processed treasure pool data for UI
function treasurePool.GetTreasurePoolData()
    if (inventoryLoading) then
        return {}, {};
    end
    
    return ProcessTreasurePoolData();
end

-- Get processed treasure pool data with forced consolidation (for testing/preview)
function treasurePool.GetConsolidatedTreasurePoolData()
    if (inventoryLoading) then
        return {}, {};
    end
    
    local winnableItems = {};
    local lostItems = {};
    
    -- Process each treasure pool slot from our internal tracking
    for i = 0, 9 do
        local slot = treasurePoolSlots[i];
        if (slot and slot.Id ~= 0) then
            -- Skip ignored items
            if (not ignoredItems[slot.UUID]) then
                local itemName = GetItemName(slot.Id);
                local displayName = itemName;
                
                -- Get lot information
                local myLotStatus, myLotValue = treasurePool.GetMyLotStatus(i);
                local currentWinner, highestLot = treasurePool.GetSlotWinner(i);
                local waitingPlayers = treasurePool.GetSlotWaitingPlayers(i);
                
                local itemData = {
                    item = displayName,
                    itemId = slot.Id,
                    slotIndex = i,
                    uuid = slot.UUID,
                    myLot = myLotStatus == "LOT" and tostring(myLotValue) or myLotStatus,
                    currentWinner = currentWinner and string.format("(%d) %s", highestLot, currentWinner) or "--",
                    waitingFor = table.concat(waitingPlayers, ", "),
                    timeToLive = 0,
                    dropTime = slot.LastUpdateTime
                };
                
                -- Determine if item is winnable or lost
                if (myLotStatus == "PASS") then
                    itemData.winner = currentWinner or "Unknown";
                    table.insert(lostItems, itemData);
                elseif (myLotStatus == "--") then
                    table.insert(winnableItems, itemData);
                elseif (myLotStatus == "LOT") then
                    if (not currentWinner or myLotValue >= highestLot) then
                        table.insert(winnableItems, itemData);
                    else
                        itemData.winner = currentWinner;
                        table.insert(lostItems, itemData);
                    end
                else
                    if (slot.Status == LotState.Untouched or slot.Status == LotState.Lotted) then
                        table.insert(winnableItems, itemData);
                    else
                        itemData.winner = "Unknown";
                        table.insert(lostItems, itemData);
                    end
                end
            end
        end
    end
    
    -- Sort items alphabetically for consistent display
    table.sort(winnableItems, function(a, b) return a.item < b.item end);
    table.sort(lostItems, function(a, b) return a.item < b.item end);
    
    -- Always apply consolidation for this function
    return ConsolidateTreasurePoolItems(winnableItems, lostItems);
end

-- Test function to manually add items for testing (remove this later)
function treasurePool.AddTestItems()
    treasurePoolSlots[0] = CreateTreasurePoolSlot(654); -- Damascus Ingot
    treasurePoolSlots[1] = CreateTreasurePoolSlot(1456); -- Example item 2
    treasurePoolSlots[1].Status = LotState.Passed; -- Mark as passed for testing
end

-- Check if player's inventory has space
local function HasInventorySpace()
    if (not ashitaCore) then
        return false; -- Assume no space if we can't check
    end
    
    local inventory = ashitaCore:GetMemoryManager():GetInventory();
    if (not inventory) then
        return false; -- Assume no space if we can't check
    end
    
    -- Check main inventory container (0)
    local containerMax = inventory:GetContainerCountMax(0);
    local containerCount = inventory:GetContainerCount(0);
    
    return containerCount < containerMax;
end

-- Lot on treasure pool item
function treasurePool.LotItem(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return false;
    end
    
    local slot = treasurePoolSlots[slotIndex];
    if (slot.Id == 0) then
        return false;
    end
    
    if (slot.Status ~= LotState.Untouched) then
        return false;
    end
    
    if (slot.PacketAttempts >= maxRetries) then
        return false;
    end
    
    if (os.clock() < slot.Lockout) then
        return false;
    end
    
    -- Check if inventory has space before lotting
    if (not HasInventorySpace()) then
        print(chat.header('[HotTub]') + chat.message('Cannot cast lots. Your inventory is full.'));
        return false;
    end
    
    -- Create and send lot packet
    local lot_packet = struct.pack('BBBBBBBB', 0x41, 0x04, 0x00, 0x00, slotIndex, 0x00, 0x00, 0x00):totable();
    
    if (ashitaCore) then
        ashitaCore:GetPacketManager():AddOutgoingPacket(0x41, lot_packet);
    end
    
    return true;
end

-- Pass on treasure pool item
function treasurePool.PassItem(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return false;
    end
    
    local slot = treasurePoolSlots[slotIndex];
    if (slot.Id == 0) then
        return false;
    end
    
    if (slot.Status ~= LotState.Untouched) then
        return false;
    end
    
    if (slot.PacketAttempts >= maxRetries) then
        return false;
    end
    
    if (os.clock() < slot.Lockout) then
        return false;
    end
    
    -- Create and send pass packet
    local pass_packet = struct.pack('BBBBBBBB', 0x42, 0x04, 0x00, 0x00, slotIndex, 0x00, 0x00, 0x00):totable();
    
    if (ashitaCore) then
        ashitaCore:GetPacketManager():AddOutgoingPacket(0x42, pass_packet);
    end
    
    return true;
end

-- Get slot status for external use
function treasurePool.GetSlotStatus(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return nil;
    end
    
    return treasurePoolSlots[slotIndex];
end

-- Get all lots/passes for a specific slot
function treasurePool.GetSlotLots(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return {};
    end
    
    return treasurePoolSlots[slotIndex].PlayerLots or {};
end

-- Get current highest lot and winner for a slot
function treasurePool.GetSlotWinner(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return nil, 0;
    end
    
    local playerLots = treasurePoolSlots[slotIndex].PlayerLots or {};
    local highestLot = 0;
    local winner = nil;
    
    for serverId, lotData in pairs(playerLots) do
        if (lotData.lot ~= 0xFFFF and lotData.lot > highestLot) then
            highestLot = lotData.lot;
            winner = lotData.name;
        end
    end
    
    return winner, highestLot;
end

-- Get list of players who have passed on a slot
function treasurePool.GetSlotPasses(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return {};
    end
    
    local playerLots = treasurePoolSlots[slotIndex].PlayerLots or {};
    local passes = {};
    
    for serverId, lotData in pairs(playerLots) do
        if (lotData.lot == 0xFFFF) then
            table.insert(passes, lotData.name);
        end
    end
    
    return passes;
end

-- Get list of players who haven't acted on a slot (useful for "waiting for" display)
function treasurePool.GetSlotWaitingPlayers(slotIndex)
    if (slotIndex < 0 or slotIndex > 9 or not ashitaCore) then
        return {};
    end
    
    local playerLots = treasurePoolSlots[slotIndex].PlayerLots or {};
    local waiting = {};
    local party = ashitaCore:GetMemoryManager():GetParty();
    
    if (not party) then
        return {};
    end
    
    -- Check all party members
    for i = 0, 17 do
        if (CanMemberLot(i)) then
            local serverId = party:GetMemberServerId(i);
            local playerName = party:GetMemberName(i);
            
            -- If this player hasn't lotted or passed yet, they're waiting
            if (not playerLots[serverId]) then
                table.insert(waiting, playerName);
            end
        end
    end
    
    return waiting;
end

-- Get my lot/pass status for a slot
function treasurePool.GetMyLotStatus(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return nil, 0;
    end
    
    local playerLots = treasurePoolSlots[slotIndex].PlayerLots or {};
    local myLotData = playerLots[myServerId];
    
    if (not myLotData) then
        return "--", 0;  -- Haven't acted yet
    elseif (myLotData.lot == 0xFFFF) then
        return "PASS", 0;     -- Passed
    else
        return "LOT", myLotData.lot;  -- Lotted with specific value
    end
end

-- Packet event handlers (to be registered by the main addon)
function treasurePool.HandleIncomingPacket(packetId, data)
    lastPacketTime = os.clock();
    
    if (packetId == 0x0A) then
        HandleZonePacket(data);
    elseif (packetId == 0xD2) then
        HandleItemEnterPacket(data);
    elseif (packetId == 0xD3) then
        HandleLotUpdatePacket(data);
    elseif (packetId == 0x0B or packetId == 0x1D) then
        HandleInventoryPacket(packetId);
    end
end

function treasurePool.HandleOutgoingPacket(packetId, data)
    if (packetId == 0x41) then
        HandleOutgoingLotPacket(data);
    elseif (packetId == 0x42) then
        HandleOutgoingPassPacket(data);
    end
end

-- Configuration setters
function treasurePool.SetMaxRetries(retries)
    maxRetries = retries;
end

function treasurePool.SetRetryDelay(delay)
    retryDelay = delay;
end

function treasurePool.SetRandomDelay(minMs, maxMs)
    randomDelayMin = minMs;
    randomDelayMax = maxMs;
end

-- Ignore item functionality
function treasurePool.IgnoreItem(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        print('[TreasurePool] Invalid slot index for ignore: ' .. tostring(slotIndex));
        return false;
    end
    
    local slot = treasurePoolSlots[slotIndex];
    if (not slot or slot.Id == 0) then
        print('[TreasurePool] No item at slot index: ' .. tostring(slotIndex));
        return false;
    end
    
    if (ignoredItems[slot.UUID]) then
        print('[TreasurePool] Item already ignored: ' .. GetItemName(slot.Id));
        return false;
    end
    
    -- Add to ignored list
    ignoredItems[slot.UUID] = true;
    
    print('[TreasurePool] Ignored item: ' .. GetItemName(slot.Id));
    
    -- Trigger UI update callback if set
    if (onTreasurePoolUpdated) then
        onTreasurePoolUpdated();
    end
    
    return true;
end

-- Get UUID for an item in a specific slot (for external ignore functionality)
function treasurePool.GetSlotUUID(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return nil;
    end
    
    local slot = treasurePoolSlots[slotIndex];
    if (not slot or slot.Id == 0) then
        return nil;
    end
    
    return slot.UUID;
end

-- Check if an item is ignored by UUID
function treasurePool.IsItemIgnored(uuid)
    return ignoredItems[uuid] == true;
end

-- Check if an item in a slot is ignored
function treasurePool.IsSlotIgnored(slotIndex)
    if (slotIndex < 0 or slotIndex > 9) then
        return false;
    end
    
    local slot = treasurePoolSlots[slotIndex];
    if (not slot or slot.Id == 0) then
        return false;
    end
    
    return ignoredItems[slot.UUID] == true;
end

-- Clear ignored items list (for testing or reset)
function treasurePool.ClearIgnoredItems()
    ignoredItems = {};
    
    -- Trigger UI update callback if set
    if (onTreasurePoolUpdated) then
        onTreasurePoolUpdated();
    end
    
    print('[TreasurePool] Cleared all ignored items');
end

-- Clear all state (for addon unload)
function treasurePool.Cleanup()
    InitializeTreasurePoolSlots();
    ignoredItems = {}; -- Clear ignored items on cleanup
    itemNameCache = {};
    onTreasurePoolUpdated = nil;
    onItemEntered = nil;
    onItemRemoved = nil;
end

return treasurePool;
