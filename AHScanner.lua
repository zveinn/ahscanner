--[[
	AH Scanner
	Opens with the auction house. When a profession window is open, Scan
	prices that profession's known recipes, one ingredient at a time.
	Profitable recipes are listed first. The full auction house is never downloaded.
]]

local ADDON = ...

local ALCHEMY_SKILL = 171
local SEARCH_GAP = 0.7
local SEARCH_TIMEOUT = 4

-- Unlimited vendor reagents. Buy price is the base price before reputation
-- discounts. An auction price is used instead when it is lower.
local VENDOR_BUY = {
	[3371] = 20,    -- Empty Vial
	[3372] = 200,   -- Leaded Vial
	[8925] = 2500,  -- Crystal Vial
	[18256] = 6000, -- Imbued Vial
}

local db
local frame
local eventFrame
local ahOpen = false
local placed = false
local cutPercent = 5
local marketKey = "Alliance"
local recipes = {}
local activeSkill = nil
local activeName = nil
local prices = {} -- [itemID] = copper, or false when confirmed unlisted
local names = {}
local icons = {}
local scanGeneration = 0
local scanMode = nil -- "search" | nil
local searchQueue = {} -- steps: one item of one recipe, in recipe order
local searchPending = nil
local searchPendingStep = nil
local searchAttempts = {}
local searchSeen = {} -- item IDs already priced in this scan
local nextSearchAt = 0
local refreshQueued = false
local scrollOffset = 0

local SORT_PRICE = {
	{ sortOrder = 0, reverseSort = false },
}

local function PriceSort()
	if Enum and Enum.AuctionHouseSortOrder and Enum.AuctionHouseSortOrder.Price then
		SORT_PRICE[1].sortOrder = Enum.AuctionHouseSortOrder.Price
	end
	return SORT_PRICE
end

local function InitDB()
	if type(AHScannerDB) ~= "table" then
		AHScannerDB = {}
	end
	db = AHScannerDB
	if type(db.characters) ~= "table" then db.characters = {} end
	if type(db.markets) ~= "table" then db.markets = {} end
	if type(db.lastReplicate) ~= "number" then db.lastReplicate = 0 end
	if type(db.minimapPos) ~= "number" then db.minimapPos = 225 end
end

local function CharacterKey()
	local name, realm = UnitFullName("player")
	if not name or name == "" then return nil end
	if not realm or realm == "" then
		realm = GetRealmName() or ""
	end
	return name .. "-" .. realm
end

local function CharacterRecord()
	local key = CharacterKey()
	if not key then return nil end
	local record = db.characters[key]
	if type(record) ~= "table" then
		record = {}
		db.characters[key] = record
	end
	if type(record.professions) ~= "table" then
		record.professions = {}
	end
	-- Older versions stored only alchemy on the character.
	if type(record.recipes) == "table" and #record.recipes > 0 and not record.professions[ALCHEMY_SKILL] then
		record.professions[ALCHEMY_SKILL] = { name = "Alchemy", recipes = record.recipes }
	end
	if type(record.activeSkill) ~= "number" and record.professions[ALCHEMY_SKILL] then
		record.activeSkill = ALCHEMY_SKILL
	end
	return record
end

local function CopyRecipe(recipe)
	local reagents = {}
	for i = 1, #recipe.reagents do
		local reagent = recipe.reagents[i]
		reagents[i] = { itemID = reagent.itemID, count = reagent.count }
	end
	return {
		recipeID = recipe.recipeID,
		outputItemID = recipe.outputItemID,
		outputCount = recipe.outputCount,
		outputMax = recipe.outputMax,
		reagents = reagents,
	}
end

local function ProfessionBucket(skillLine, name)
	local record = CharacterRecord()
	if not record or type(skillLine) ~= "number" then return nil end
	local bucket = record.professions[skillLine]
	if type(bucket) ~= "table" then
		bucket = { name = name or "Profession", recipes = {} }
		record.professions[skillLine] = bucket
	end
	if type(bucket.recipes) ~= "table" then
		bucket.recipes = {}
	end
	if type(name) == "string" and name ~= "" then
		bucket.name = name
	end
	return bucket
end

local function SaveRecipeList(list, replace)
	local bucket = ProfessionBucket(activeSkill, activeName)
	if not bucket then return end
	local record = CharacterRecord()
	if record then record.activeSkill = activeSkill end
	if replace then
		bucket.recipes = {}
		for i = 1, #list do
			bucket.recipes[i] = CopyRecipe(list[i])
		end
		return
	end
	local byID = {}
	for i = 1, #bucket.recipes do
		local recipe = bucket.recipes[i]
		if recipe and recipe.recipeID then
			byID[recipe.recipeID] = recipe
		end
	end
	for i = 1, #list do
		byID[list[i].recipeID] = CopyRecipe(list[i])
	end
	local merged = {}
	for _, recipe in pairs(byID) do
		merged[#merged + 1] = recipe
	end
	bucket.recipes = merged
end

local function LoadSavedRecipes()
	local record = CharacterRecord()
	if not record or type(activeSkill) ~= "number" then return {} end
	local bucket = record.professions[activeSkill]
	if type(bucket) ~= "table" or type(bucket.recipes) ~= "table" then return {} end
	if type(bucket.name) == "string" and bucket.name ~= "" then
		activeName = bucket.name
	end
	local list = {}
	for i = 1, #bucket.recipes do
		local recipe = bucket.recipes[i]
		if type(recipe) == "table" and recipe.recipeID and recipe.outputItemID and type(recipe.reagents) == "table" and #recipe.reagents > 0 then
			list[#list + 1] = CopyRecipe(recipe)
		end
	end
	return list
end

local function MarketPrices()
	local bucket = db.markets[marketKey]
	if type(bucket) ~= "table" then
		bucket = {}
		db.markets[marketKey] = bucket
	end
	return bucket
end

local function RememberPrice(itemID, price)
	prices[itemID] = price
	local bucket = MarketPrices()
	if price == nil then
		bucket[itemID] = nil
	else
		bucket[itemID] = price
	end
end

local function LoadMarketPrices()
	wipe(prices)
	local bucket = db.markets[marketKey]
	if type(bucket) ~= "table" then return end
	for itemID, price in pairs(bucket) do
		if type(itemID) == "number" and (type(price) == "number" or price == false) then
			prices[itemID] = price
		end
	end
end

local function DetectMarket()
	local faction = UnitFactionGroup("npc")
	local reaction = UnitReaction("npc", "player")
	local subzone = GetSubZoneText()
	-- Neutral auctioneers (Gadgetzan, Booty Bay, Everlook) keep 15%. A faction
	-- auctioneer is friendly, so a neutral reaction means the neutral house.
	if faction == "Neutral" or reaction == 4 or subzone == "Booty Bay" or subzone == "Gadgetzan" or subzone == "Everlook" then
		cutPercent = 15
		marketKey = "Neutral"
		return
	end
	cutPercent = 5
	local playerFaction = UnitFactionGroup("player")
	if playerFaction == "Horde" or playerFaction == "Alliance" then
		marketKey = playerFaction
	else
		marketKey = "Alliance"
	end
end

local function HouseCut(amount)
	return math.floor(amount * cutPercent / 100 + 1e-6)
end

-- Copper a vendor pays for one of this item. Nil until the client knows the item.
local function VendorSell(itemID)
	if not itemID then return nil end
	local sell
	if type(GetItemInfo) == "function" then
		local ok, _, _, _, _, _, _, _, _, _, _, price = pcall(GetItemInfo, itemID)
		if ok and type(price) == "number" then
			sell = price
		end
	end
	if sell == nil and C_Item and C_Item.GetItemInfo then
		local ok, a, _, _, _, _, _, _, _, _, _, price = pcall(C_Item.GetItemInfo, itemID)
		if ok then
			if type(a) == "table" and type(a.sellPrice) == "number" then
				sell = a.sellPrice
			elseif type(price) == "number" then
				sell = price
			end
		end
	end
	if sell == nil then
		return nil
	end
	return sell
end

local function PlainMoney(copper)
	local gold = math.floor(copper / 10000)
	local silver = math.floor((copper % 10000) / 100)
	local remainder = copper % 100
	local text = ""
	if gold > 0 then
		text = gold .. "g "
	end
	if silver > 0 or gold > 0 then
		text = text .. silver .. "s "
	end
	return text .. remainder .. "c"
end

local function MoneyText(copper)
	if type(copper) ~= "number" then
		return "|cff888888-|r"
	end
	local negative = copper < 0
	local amount = math.floor(math.abs(copper) + 0.5)
	local text
	if C_CurrencyInfo and C_CurrencyInfo.GetCoinTextureString then
		local ok, result = pcall(C_CurrencyInfo.GetCoinTextureString, amount)
		if ok and type(result) == "string" and result ~= "" then
			text = result
		end
	end
	if not text and type(GetCoinTextureString) == "function" then
		local ok, result = pcall(GetCoinTextureString, amount)
		if ok and type(result) == "string" and result ~= "" then
			text = result
		end
	end
	if not text then
		local ok, result = pcall(PlainMoney, amount)
		text = ok and result or (amount .. "c")
	end
	if negative then
		return "|cffff5555-|r" .. text
	end
	return text
end

local function RequestItem(itemID)
	if names[itemID] and icons[itemID] then return end
	if C_Item and C_Item.RequestLoadItemDataByID then
		C_Item.RequestLoadItemDataByID(itemID)
	elseif C_Item and C_Item.GetItemInfo then
		C_Item.GetItemInfo(itemID)
	elseif GetItemInfo then
		GetItemInfo(itemID)
	end
end

local function ItemName(itemID)
	local cached = names[itemID]
	if cached then return cached end
	local name
	if C_Item and C_Item.GetItemNameByID then
		name = C_Item.GetItemNameByID(itemID)
	end
	if not name and GetItemInfo then
		name = GetItemInfo(itemID)
	end
	if name and name ~= "" then
		names[itemID] = name
		return name
	end
	RequestItem(itemID)
	return "item " .. itemID
end

local function ItemIcon(itemID)
	local cached = icons[itemID]
	if cached then return cached end
	local icon
	if C_Item and C_Item.GetItemIconByID then
		icon = C_Item.GetItemIconByID(itemID)
	elseif GetItemIcon then
		icon = GetItemIcon(itemID)
	end
	if icon then
		icons[itemID] = icon
	end
	return icon or "Interface\\Icons\\INV_Misc_QuestionMark"
end

local function NoteItem(itemID)
	if itemID and itemID > 0 then
		RequestItem(itemID)
	end
end

local function ReadSchematic(recipeID)
	if not (C_TradeSkillUI and C_TradeSkillUI.GetRecipeSchematic) then
		return nil
	end
	local ok, schematic = pcall(C_TradeSkillUI.GetRecipeSchematic, recipeID, false)
	if not ok or type(schematic) ~= "table" then
		return nil
	end
	local outputID = schematic.outputItemID
	if type(outputID) ~= "number" or outputID <= 0 then
		return nil
	end
	local reagents = {}
	local slots = schematic.reagentSlotSchematics
	if type(slots) == "table" then
		for i = 1, #slots do
			local slot = slots[i]
			local reagent = slot and slot.reagents and slot.reagents[1]
			local itemID = reagent and reagent.itemID
			local count = slot and slot.quantityRequired
			if itemID and itemID > 0 and slot.required ~= false and type(count) == "number" and count > 0 then
				reagents[#reagents + 1] = { itemID = itemID, count = count }
			end
		end
	end
	if #reagents == 0 then
		return nil
	end
	local minCount = schematic.quantityMin
	local maxCount = schematic.quantityMax
	if type(minCount) ~= "number" or minCount < 1 then minCount = 1 end
	if type(maxCount) ~= "number" or maxCount < minCount then maxCount = minCount end
	return {
		recipeID = recipeID,
		outputItemID = outputID,
		outputCount = minCount,
		outputMax = maxCount,
		reagents = reagents,
	}
end

local function RecipeIsLearned(recipeID)
	if not (C_TradeSkillUI and C_TradeSkillUI.GetRecipeInfo) then
		return true
	end
	local ok, info = pcall(C_TradeSkillUI.GetRecipeInfo, recipeID)
	if not ok or type(info) ~= "table" then
		return false
	end
	return info.learned and true or false
end

-- The profession window that is open right now, if its recipe list is ready.
local function CurrentProfession()
	if not C_TradeSkillUI then return nil end
	if C_TradeSkillUI.IsTradeSkillReady and not C_TradeSkillUI.IsTradeSkillReady() then
		return nil
	end
	local skillLine, name
	if C_TradeSkillUI.GetTradeSkillLine then
		local ok, a, b = pcall(C_TradeSkillUI.GetTradeSkillLine)
		if ok then
			if type(a) == "table" then
				if type(a.professionID) == "number" and a.professionID > 0 then
					skillLine = a.professionID
				elseif type(a.parentProfessionID) == "number" and a.parentProfessionID > 0 then
					skillLine = a.parentProfessionID
				end
				if type(a.professionName) == "string" and a.professionName ~= "" then
					name = a.professionName
				elseif type(a.skillLineDisplayName) == "string" and a.skillLineDisplayName ~= "" then
					name = a.skillLineDisplayName
				end
			elseif type(a) == "number" and a > 0 then
				skillLine = a
				if type(b) == "string" and b ~= "" then
					name = b
				end
			end
		end
	end
	if C_TradeSkillUI.GetBaseProfessionInfo then
		local ok, info = pcall(C_TradeSkillUI.GetBaseProfessionInfo)
		if ok and type(info) == "table" then
			if not skillLine and type(info.professionID) == "number" and info.professionID > 0 then
				skillLine = info.professionID
			end
			if (not name or name == "") and type(info.professionName) == "string" then
				name = info.professionName
			end
		end
	end
	if not skillLine then return nil end
	if not name or name == "" then name = "Profession" end
	return skillLine, name
end

local function RecipeProfession(recipeID)
	if not (C_TradeSkillUI and C_TradeSkillUI.GetProfessionInfoByRecipeID) then
		return nil
	end
	local ok, info = pcall(C_TradeSkillUI.GetProfessionInfoByRecipeID, recipeID)
	if not ok or type(info) ~= "table" then return nil end
	local skill = info.professionID
	if type(skill) ~= "number" or skill <= 0 then
		skill = info.parentProfessionID
	end
	local name = info.professionName or info.parentProfessionName
	local parent = info.parentProfessionID
	if type(skill) ~= "number" or skill <= 0 then skill = nil end
	if type(parent) ~= "number" or parent <= 0 then parent = nil end
	if type(name) ~= "string" or name == "" then name = nil end
	if not skill and not parent and not name then return nil end
	return skill, parent, name
end

local function RecipeBelongs(recipeID, skillLine, name)
	local skill, parent, recipeName = RecipeProfession(recipeID)
	if not skill and not parent and not recipeName then
		return nil
	end
	if skill == skillLine or parent == skillLine then
		return true
	end
	if recipeName and name and recipeName:lower() == name:lower() then
		return true
	end
	return false
end

local function ReadOpenProfession()
	if not (C_TradeSkillUI and C_TradeSkillUI.GetAllRecipeIDs) then
		return nil
	end
	local skillLine, name = CurrentProfession()
	if not skillLine then
		return nil
	end
	local ok, ids = pcall(C_TradeSkillUI.GetAllRecipeIDs)
	if not ok or type(ids) ~= "table" then
		return nil
	end
	local list = {}
	local tagged = false
	local untagged = {}
	for i = 1, #ids do
		local recipeID = ids[i]
		if RecipeIsLearned(recipeID) then
			local belongs = RecipeBelongs(recipeID, skillLine, name)
			if belongs == nil then
				untagged[#untagged + 1] = recipeID
			else
				tagged = true
				if belongs then
					local recipe = ReadSchematic(recipeID)
					if recipe then
						list[#list + 1] = recipe
					end
				end
			end
		end
	end
	-- If the client never says which profession a recipe is, trust the open window.
	if not tagged then
		for i = 1, #untagged do
			local recipe = ReadSchematic(untagged[i])
			if recipe then
				list[#list + 1] = recipe
			end
		end
	end
	return list
end

local function UseRecipes(list, replace)
	if type(list) ~= "table" then return end
	SaveRecipeList(list, replace)
	recipes = LoadSavedRecipes()
	for i = 1, #recipes do
		local recipe = recipes[i]
		NoteItem(recipe.outputItemID)
		for n = 1, #recipe.reagents do
			NoteItem(recipe.reagents[n].itemID)
		end
	end
end

local function NeededItems()
	local needed = {}
	for i = 1, #recipes do
		local recipe = recipes[i]
		needed[recipe.outputItemID] = true
		for n = 1, #recipe.reagents do
			needed[recipe.reagents[n].itemID] = true
		end
	end
	return needed
end

local function NeededCount(needed)
	local count = 0
	for _ in pairs(needed) do
		count = count + 1
	end
	return count
end

local function PricedCount(needed)
	local count = 0
	for itemID in pairs(needed) do
		if prices[itemID] ~= nil then
			count = count + 1
		end
	end
	return count
end

-- Unit cost of one ingredient. Vendor vials are used when they are cheaper
-- than the auction house, or when the auction house has none listed.
local function IngredientUnit(itemID)
	local auction = prices[itemID]
	local vendor = VENDOR_BUY[itemID]
	if type(auction) == "number" then
		if vendor and vendor < auction then
			return vendor, "vendor"
		end
		return auction, "auction"
	end
	if auction == false and vendor then
		return vendor, "vendor"
	end
	if auction == false then
		return nil, "missing"
	end
	return nil, "pending"
end

local function Evaluate(recipe)
	local missing = false
	local cost = 0
	for i = 1, #recipe.reagents do
		local reagent = recipe.reagents[i]
		local unit, source = IngredientUnit(reagent.itemID)
		reagent.unit = unit
		reagent.source = source
		if unit then
			reagent.line = unit * reagent.count
			cost = cost + reagent.line
		else
			reagent.line = nil
			if source ~= "pending" then
				missing = true
			else
				missing = true
			end
		end
	end
	recipe.cost = cost
	recipe.missing = missing
	local count = recipe.outputCount or 1

	local sellUnit = prices[recipe.outputItemID]
	if type(sellUnit) ~= "number" then
		recipe.sale = nil
		recipe.profit = nil
		recipe.sellState = sellUnit == false and "missing" or "pending"
	else
		local gross = sellUnit * count
		recipe.sale = gross - HouseCut(gross)
		recipe.sellState = "auction"
		if missing then
			recipe.profit = nil
			recipe.sellState = "incomplete"
		else
			recipe.profit = recipe.sale - cost
		end
	end

	local vendorUnit = VendorSell(recipe.outputItemID)
	if vendorUnit == nil then
		RequestItem(recipe.outputItemID)
		recipe.vendorSale = nil
		recipe.vendorProfit = nil
		recipe.vendorState = "pending"
	elseif vendorUnit <= 0 then
		recipe.vendorSale = 0
		recipe.vendorProfit = nil
		recipe.vendorState = "none"
	else
		recipe.vendorSale = vendorUnit * count
		if missing then
			recipe.vendorProfit = nil
			recipe.vendorState = "incomplete"
		else
			recipe.vendorProfit = recipe.vendorSale - cost
			recipe.vendorState = "known"
		end
	end

	local best = nil
	if type(recipe.profit) == "number" then
		best = recipe.profit
	end
	if type(recipe.vendorProfit) == "number" and (best == nil or recipe.vendorProfit > best) then
		best = recipe.vendorProfit
	end
	recipe.best = best
	if best == nil then
		recipe.tier = 3
	elseif best > 0 then
		recipe.tier = 1
	else
		recipe.tier = 2
	end
end

local function SortedRecipes()
	local list = {}
	for i = 1, #recipes do
		Evaluate(recipes[i])
		list[i] = recipes[i]
	end
	table.sort(list, function(a, b)
		if a.tier ~= b.tier then
			return a.tier < b.tier
		end
		local pa, pb = a.best, b.best
		if pa ~= pb then
			if pa == nil then return false end
			if pb == nil then return true end
			return pa > pb
		end
		return ItemName(a.outputItemID) < ItemName(b.outputItemID)
	end)
	return list
end

local function ProfitCounts()
	local profitable, losing, incomplete = 0, 0, 0
	for i = 1, #recipes do
		Evaluate(recipes[i])
		if recipes[i].tier == 1 then
			profitable = profitable + 1
		elseif recipes[i].tier == 2 then
			losing = losing + 1
		else
			incomplete = incomplete + 1
		end
	end
	return profitable, losing, incomplete
end

local function StopScan()
	scanGeneration = scanGeneration + 1
	scanMode = nil
	searchPending = nil
	searchPendingStep = nil
	wipe(searchQueue)
	wipe(searchSeen)
end

local function NoteRecipes(list)
	for i = 1, #list do
		NoteItem(list[i].outputItemID)
		for n = 1, #list[i].reagents do
			NoteItem(list[i].reagents[n].itemID)
		end
	end
end

local function RestoreLastProfession()
	local record = CharacterRecord()
	if not record then return end
	local skill = record.activeSkill
	if type(skill) ~= "number" and type(record.professions) == "table" then
		for id in pairs(record.professions) do
			if type(id) == "number" then
				skill = id
				break
			end
		end
	end
	if type(skill) ~= "number" then return end
	activeSkill = skill
	local bucket = record.professions[skill]
	activeName = (bucket and bucket.name) or "Profession"
	recipes = LoadSavedRecipes()
	NoteRecipes(recipes)
end

-- Replace the window with only the profession that is open. Never keep
-- another profession's recipes on screen or fold them into this list.
local function AdoptOpenProfession()
	local skillLine, name = CurrentProfession()
	if not skillLine then return false end
	local list = ReadOpenProfession()
	if not list then return false end
	local switched = activeSkill ~= skillLine or activeName ~= name
	if switched and scanMode == "search" then
		StopScan()
	end
	if switched then
		recipes = {}
	end
	activeSkill = skillLine
	activeName = name
	if #list == 0 then
		return true
	end
	UseRecipes(list, true)
	return true
end

local function OnProfessionUpdate()
	if not AdoptOpenProfession() then return end
	if frame and frame:IsShown() then
		frame:Refresh()
	end
end

local function OnNewRecipe()
	OnProfessionUpdate()
end

local function ScheduleRefresh()
	if refreshQueued or not frame then return end
	refreshQueued = true
	C_Timer.After(0.12, function()
		refreshQueued = false
		if frame and frame:IsShown() then
			frame:Refresh()
		end
	end)
end

local function ScanFinished(generation)
	if generation ~= scanGeneration then return end
	scanMode = nil
	searchPending = nil
	ScheduleRefresh()
end

local function ItemKey(itemID)
	if C_AuctionHouse.MakeItemKey then
		local ok, key = pcall(C_AuctionHouse.MakeItemKey, itemID)
		if ok and type(key) == "table" then
			return key
		end
	end
	return { itemID = itemID, itemLevel = 0, itemSuffix = 0, battlePetSpeciesID = 0 }
end

-- One entry per item the scan still has to query. Recipes are walked in name
-- order. Each recipe contributes its ingredients first, then the crafted item.
-- An item used by an earlier recipe is not queried again.
local function BuildSearchQueue()
	local order = {}
	for i = 1, #recipes do
		order[i] = recipes[i]
	end
	table.sort(order, function(a, b)
		return ItemName(a.outputItemID) < ItemName(b.outputItemID)
	end)
	local queued = {}
	local total = #order
	for recipeNumber = 1, total do
		local recipe = order[recipeNumber]
		local stepCount = #recipe.reagents + 1
		for n = 1, #recipe.reagents do
			local itemID = recipe.reagents[n].itemID
			if not queued[itemID] then
				queued[itemID] = true
				searchQueue[#searchQueue + 1] = {
					itemID = itemID,
					outputItemID = recipe.outputItemID,
					recipeNumber = recipeNumber,
					recipeTotal = total,
					step = "ingredient",
					stepIndex = n,
					stepCount = stepCount,
				}
			end
		end
		if not queued[recipe.outputItemID] then
			queued[recipe.outputItemID] = true
			searchQueue[#searchQueue + 1] = {
				itemID = recipe.outputItemID,
				outputItemID = recipe.outputItemID,
				recipeNumber = recipeNumber,
				recipeTotal = total,
				step = "result",
				stepIndex = stepCount,
				stepCount = stepCount,
			}
		end
	end
end

local function StartSearch(generation)
	if generation ~= scanGeneration then return end
	scanMode = "search"
	searchPending = nil
	searchPendingStep = nil
	wipe(searchQueue)
	wipe(searchAttempts)
	wipe(searchSeen)
	BuildSearchQueue()
	if frame and frame.PumpSearch then
		frame:PumpSearch()
	end
end

local function BeginPriceScan()
	StopScan()
	local generation = scanGeneration
	if #recipes == 0 then
		ScheduleRefresh()
		return
	end
	if not ahOpen or not C_AuctionHouse or not C_AuctionHouse.SendSearchQuery then
		ScheduleRefresh()
		return
	end
	StartSearch(generation)
	ScheduleRefresh()
end

local function AcceptSearchPrice(itemID, price, generation)
	if generation ~= scanGeneration or scanMode ~= "search" then return end
	if price == nil then
		RememberPrice(itemID, false)
	else
		RememberPrice(itemID, price)
	end
	searchSeen[itemID] = true
	if searchPending == itemID then
		searchPending = nil
		searchPendingStep = nil
	end
	ScheduleRefresh()
	if frame and frame.PumpSearch then
		frame:PumpSearch()
	end
end

local function CheapestCommodity(itemID)
	local count = C_AuctionHouse.GetNumCommoditySearchResults(itemID) or 0
	local best
	local limit = count > 8 and 8 or count
	for i = 1, limit do
		local result = C_AuctionHouse.GetCommoditySearchResultInfo(itemID, i)
		local unit = result and result.unitPrice
		if type(unit) == "number" and unit > 0 and (not best or unit < best) then
			best = unit
		end
	end
	return best, count
end

local function CheapestItem(itemKey)
	local count = C_AuctionHouse.GetNumItemSearchResults(itemKey) or 0
	local best
	for i = 1, count do
		local result = C_AuctionHouse.GetItemSearchResultInfo(itemKey, i)
		local buyout = result and result.buyoutAmount
		local quantity = result and result.quantity
		if type(buyout) == "number" and buyout > 0 and type(quantity) == "number" and quantity > 0 then
			local unit = math.ceil(buyout / quantity)
			if not best or unit < best then
				best = unit
			end
		end
	end
	return best, count
end

local function OnCommodityResults(itemID)
	if scanMode ~= "search" or itemID ~= searchPending then return end
	local best, count = CheapestCommodity(itemID)
	if count == 0 then
		local itemBest, itemCount = CheapestItem(ItemKey(itemID))
		if itemCount > 0 then
			AcceptSearchPrice(itemID, itemBest, scanGeneration)
			return
		end
	end
	AcceptSearchPrice(itemID, best, scanGeneration)
end

local function OnItemResults(itemKey)
	if scanMode ~= "search" or type(itemKey) ~= "table" then return end
	local itemID = itemKey.itemID
	if itemID ~= searchPending then return end
	local best, count = CheapestItem(itemKey)
	if count == 0 then
		local commodityBest, commodityCount = CheapestCommodity(itemID)
		if commodityCount > 0 then
			AcceptSearchPrice(itemID, commodityBest, scanGeneration)
			return
		end
	end
	AcceptSearchPrice(itemID, best, scanGeneration)
end

local function PumpSearch()
	if scanMode ~= "search" or not ahOpen then return end
	if searchPending then return end
	if #searchQueue == 0 then
		ScanFinished(scanGeneration)
		return
	end
	if C_AuctionHouse.IsThrottledMessageSystemReady and not C_AuctionHouse.IsThrottledMessageSystemReady() then
		C_Timer.After(0.25, PumpSearch)
		return
	end
	local now = GetTime()
	if now < nextSearchAt then
		C_Timer.After(nextSearchAt - now, PumpSearch)
		return
	end
	while #searchQueue > 0 and searchSeen[searchQueue[1].itemID] do
		table.remove(searchQueue, 1)
	end
	if #searchQueue == 0 then
		ScanFinished(scanGeneration)
		return
	end
	local step = table.remove(searchQueue, 1)
	local itemID = step.itemID
	local generation = scanGeneration
	searchPending = itemID
	searchPendingStep = step
	nextSearchAt = now + SEARCH_GAP
	local ok = pcall(C_AuctionHouse.SendSearchQuery, ItemKey(itemID), PriceSort(), false)
	if not ok then
		searchPending = nil
		searchPendingStep = nil
		local attempts = (searchAttempts[itemID] or 0) + 1
		searchAttempts[itemID] = attempts
		if attempts < 3 then
			table.insert(searchQueue, 1, step)
		else
			RememberPrice(itemID, false)
			searchSeen[itemID] = true
			ScheduleRefresh()
		end
		C_Timer.After(SEARCH_GAP, PumpSearch)
		return
	end
	C_Timer.After(SEARCH_TIMEOUT, function()
		if scanGeneration ~= generation or searchPending ~= itemID then return end
		local attempts = (searchAttempts[itemID] or 0) + 1
		searchAttempts[itemID] = attempts
		searchPending = nil
		searchPendingStep = nil
		if attempts < 3 then
			table.insert(searchQueue, 1, step)
		else
			RememberPrice(itemID, false)
			searchSeen[itemID] = true
			ScheduleRefresh()
		end
		PumpSearch()
	end)
end

local function StatusText()
	if #recipes == 0 then
		local _, openName = CurrentProfession()
		if openName then
			return openName .. " is open, but it has no item recipes to price."
		end
		return "Open a profession window beside the auction house, then press Scan."
	end
	local profitable, losing, incomplete = ProfitCounts()
	local summary = (activeName or "Profession") .. ": " .. profitable .. " profitable, " .. losing .. " losing money"
	if incomplete > 0 then
		summary = summary .. ", " .. incomplete .. " missing a price"
	end
	summary = summary .. ". " .. #recipes .. " known recipes."
	if scanMode ~= "search" and incomplete == #recipes then
		summary = summary .. " Press Scan to price them."
	end
	if scanMode == "search" then
		local step = searchPendingStep or searchQueue[1]
		if step then
			local which
			if step.step == "result" then
				which = "sale price, " .. ItemName(step.itemID)
			else
				which = "ingredient " .. step.stepIndex .. " of " .. (step.stepCount - 1) .. ", " .. ItemName(step.itemID)
			end
			return "Recipe " .. step.recipeNumber .. " of " .. step.recipeTotal .. ": " .. ItemName(step.outputItemID) .. " — " .. which .. ". " .. summary
		end
		return "Pricing recipes one item at a time. " .. summary
	end
	return summary
end

local function NoteText()
	local house = cutPercent == 15 and "Neutral auction house keeps 15%." or "Faction auction house keeps 5%."
	return house .. " AH is the profit after that cut. Vendor is what a merchant pays for the crafted item. A recipe is listed first when either one makes money."
end

local function CreateRow(parent)
	local row = CreateFrame("Frame", nil, parent, "BackdropTemplate")
	row:SetHeight(72)
	row:SetBackdrop({
		bgFile = "Interface\\ChatFrame\\ChatFrameBackground",
		edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
		tile = true, tileSize = 16, edgeSize = 12,
		insets = { left = 3, right = 3, top = 3, bottom = 3 },
	})
	row:SetBackdropColor(0, 0, 0, 0.92)
	row:SetBackdropBorderColor(0.16, 0.16, 0.16, 1)
	row:EnableMouse(false)

	-- Text sits on a child frame so the row backdrop cannot cover it.
	row.content = CreateFrame("Frame", nil, row)
	row.content:SetAllPoints()
	row.content:SetFrameLevel(row:GetFrameLevel() + 2)

	row.bar = row.content:CreateTexture(nil, "ARTWORK")
	row.bar:SetTexture("Interface\\Buttons\\WHITE8X8")
	row.bar:SetPoint("TOPLEFT", 4, -4)
	row.bar:SetPoint("BOTTOMLEFT", 4, 4)
	row.bar:SetWidth(4)

	row.icon = CreateFrame("Button", nil, row.content)
	row.icon:SetSize(22, 22)
	row.icon:SetPoint("TOPLEFT", 12, -6)
	row.icon.texture = row.icon:CreateTexture(nil, "ARTWORK")
	row.icon.texture:SetAllPoints()
	row.icon:SetScript("OnEnter", function(self)
		if not self.itemID then return end
		GameTooltip:SetOwner(self, "ANCHOR_RIGHT")
		if GameTooltip.SetItemByID then
			GameTooltip:SetItemByID(self.itemID)
		else
			GameTooltip:SetHyperlink("item:" .. self.itemID)
		end
		GameTooltip:Show()
	end)
	row.icon:SetScript("OnLeave", function()
		GameTooltip:Hide()
	end)

	row.vendor = row.content:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
	row.vendor:SetPoint("TOPRIGHT", -8, -6)
	row.vendor:SetWidth(84)
	row.vendor:SetJustifyH("RIGHT")
	row.vendor:SetWordWrap(false)

	row.ah = row.content:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
	row.ah:SetPoint("TOPRIGHT", -98, -6)
	row.ah:SetWidth(84)
	row.ah:SetJustifyH("RIGHT")
	row.ah:SetWordWrap(false)

	row.name = row.content:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
	row.name:SetPoint("TOPLEFT", 40, -7)
	row.name:SetPoint("RIGHT", row.ah, "LEFT", -8, 0)
	row.name:SetJustifyH("LEFT")
	row.name:SetWordWrap(false)
	row.name:SetTextColor(1, 0.86, 0.55)

	row.reagents = row.content:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
	row.reagents:SetPoint("TOPLEFT", 40, -24)
	row.reagents:SetPoint("TOPRIGHT", -8, -24)
	row.reagents:SetJustifyH("LEFT")
	row.reagents:SetJustifyV("TOP")
	row.reagents:SetWordWrap(true)
	row.reagents:SetTextColor(0.62, 0.62, 0.62)

	return row
end

local function ProfitValue(amount, state)
	if state == "pending" or state == "incomplete" then
		return "|cff777777...|r"
	end
	if type(amount) ~= "number" then
		return "|cff555555—|r"
	end
	if amount > 0 then
		return "|cff3dcc66+" .. MoneyText(amount) .. "|r"
	end
	return "|cffff6666" .. MoneyText(amount) .. "|r"
end

local function ReagentBit(reagent)
	local price
	if reagent.source == "pending" then
		price = "|cff777777...|r"
	elseif not reagent.unit then
		price = "|cff555555—|r"
	else
		price = MoneyText(reagent.unit)
		if reagent.source == "vendor" then
			price = price .. "|cffddcc88v|r"
		end
	end
	return reagent.count .. " " .. ItemName(reagent.itemID) .. " " .. price
end

local function FillRow(row, recipe)
	Evaluate(recipe)
	local outputCount = recipe.outputCount or 1
	local outputMax = recipe.outputMax or outputCount
	row.icon.itemID = recipe.outputItemID
	row.icon.texture:SetTexture(ItemIcon(recipe.outputItemID))

	local name = ItemName(recipe.outputItemID)
	if outputMax > outputCount then
		name = name .. "  |cff777777" .. outputCount .. "–" .. outputMax .. "|r"
	elseif outputCount > 1 then
		name = name .. "  |cff777777x" .. outputCount .. "|r"
	end
	row.name:SetText(name)

	if recipe.tier == 1 then
		row.bar:SetVertexColor(0.25, 0.8, 0.35, 1)
	elseif recipe.tier == 2 then
		row.bar:SetVertexColor(0.85, 0.28, 0.22, 1)
	else
		row.bar:SetVertexColor(0.35, 0.35, 0.35, 1)
	end
	row.ah:SetText(ProfitValue(recipe.profit, recipe.sellState))
	row.vendor:SetText(ProfitValue(recipe.vendorProfit, recipe.vendorState))

	local bits = {}
	local cost = "|cff888888Cost "
	if recipe.missing and recipe.cost and recipe.cost > 0 then
		cost = cost .. MoneyText(recipe.cost) .. "+|r"
	elseif recipe.missing then
		cost = cost .. "—|r"
	else
		cost = cost .. MoneyText(recipe.cost or 0) .. "|r"
	end
	bits[1] = cost
	for i = 1, #recipe.reagents do
		bits[#bits + 1] = ReagentBit(recipe.reagents[i])
	end
	row.reagents:SetText(table.concat(bits, "   "))
	local textHeight = row.reagents:GetStringHeight() or 14
	if textHeight < 12 then textHeight = 14 end
	row.reagents:SetHeight(textHeight)
	local height = 28 + textHeight
	if height < 44 then height = 44 end
	row:SetHeight(height)
end

local listScroll
local syncingScroll = false

local function ScrollBarOf(scroll)
	if scroll.ScrollBar then return scroll.ScrollBar end
	local name = scroll:GetName()
	if name then return _G[name .. "ScrollBar"] end
end

local function SyncScrollBar(scroll)
	if syncingScroll or not scroll then return end
	local bar = ScrollBarOf(scroll)
	if not bar then return end
	syncingScroll = true
	local maxScroll = scroll:GetVerticalScrollRange() or 0
	if maxScroll < 0 then maxScroll = 0 end
	local offset = scroll:GetVerticalScroll() or 0
	if offset > maxScroll then offset = maxScroll end
	if offset < 0 then offset = 0 end
	bar:SetMinMaxValues(0, maxScroll)
	bar:SetValue(offset)
	scrollOffset = offset
	if math.abs((scroll:GetVerticalScroll() or 0) - offset) > 0.1 then
		scroll:SetVerticalScroll(offset)
	end
	if maxScroll > 1 then
		bar:Show()
		bar:SetAlpha(1)
	else
		bar:Hide()
	end
	syncingScroll = false
end

local function ScrollBy(delta)
	if not listScroll then return end
	local maxScroll = listScroll:GetVerticalScrollRange() or 0
	local offset = (listScroll:GetVerticalScroll() or 0) - (delta * 48)
	if offset < 0 then offset = 0 end
	if offset > maxScroll then offset = maxScroll end
	listScroll:SetVerticalScroll(offset)
end

local function HookWheel(target)
	target:EnableMouseWheel(true)
	target:SetScript("OnMouseWheel", function(_, delta)
		ScrollBy(delta)
	end)
end

local function BuildFrame()
	local main = CreateFrame("Frame", "AHScannerFrame", UIParent, "BackdropTemplate")
	main:SetSize(640, 640)
	main:SetFrameStrata("HIGH")
	main:SetToplevel(true)
	main:SetMovable(true)
	main:EnableMouse(true)
	main:SetClampedToScreen(true)
	main:SetBackdrop({
		bgFile = "Interface\\ChatFrame\\ChatFrameBackground",
		edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
		tile = true, tileSize = 16, edgeSize = 14,
		insets = { left = 4, right = 4, top = 4, bottom = 4 },
	})
	main:SetBackdropColor(0, 0, 0, 0.97)
	main:SetBackdropBorderColor(0.12, 0.12, 0.12, 1)
	main:RegisterForDrag("LeftButton")
	main:SetScript("OnDragStart", main.StartMoving)
	main:SetScript("OnDragStop", function(self)
		self:StopMovingOrSizing()
		local point, _, relativePoint, x, y = self:GetPoint(1)
		db.window = { point = point, relativePoint = relativePoint, x = x, y = y }
	end)
	table.insert(UISpecialFrames, "AHScannerFrame")

	main.title = main:CreateFontString(nil, "OVERLAY", "GameFontNormalLarge")
	main.title:SetPoint("TOPLEFT", 16, -12)
	main.title:SetText("AH Scanner")
	main.title:SetTextColor(0.92, 0.92, 0.92)

	main.close = CreateFrame("Button", nil, main, "UIPanelCloseButton")
	main.close:SetPoint("TOPRIGHT", 2, 2)
	main.close:SetScript("OnClick", function()
		main:Hide()
	end)

	main.status = main:CreateFontString(nil, "OVERLAY", "GameFontHighlight")
	main.status:SetPoint("TOPLEFT", 16, -38)
	main.status:SetPoint("TOPRIGHT", -16, -38)
	main.status:SetJustifyH("LEFT")
	main.status:SetWordWrap(true)
	main.status:SetHeight(32)
	main.status:SetTextColor(0.85, 0.85, 0.85)

	main.note = main:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
	main.note:SetPoint("TOPLEFT", main.status, "BOTTOMLEFT", 0, -2)
	main.note:SetPoint("RIGHT", main, "RIGHT", -16, 0)
	main.note:SetJustifyH("LEFT")
	main.note:SetWordWrap(true)
	main.note:SetHeight(32)
	main.note:SetTextColor(0.55, 0.55, 0.55)

	main.refresh = CreateFrame("Button", nil, main, "BackdropTemplate")
	main.refresh:SetSize(72, 22)
	main.refresh:SetPoint("TOPRIGHT", -40, -12)
	main.refresh:SetBackdrop({
		bgFile = "Interface\\ChatFrame\\ChatFrameBackground",
		edgeFile = "Interface\\Tooltips\\UI-Tooltip-Border",
		tile = true, tileSize = 16, edgeSize = 10,
		insets = { left = 2, right = 2, top = 2, bottom = 2 },
	})
	main.refresh:SetBackdropColor(0.05, 0.05, 0.05, 1)
	main.refresh:SetBackdropBorderColor(0.35, 0.35, 0.35, 1)
	main.refresh.label = main.refresh:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
	main.refresh.label:SetPoint("CENTER", 0, 0)
	main.refresh.label:SetText("Scan")
	main.refresh.label:SetTextColor(0.9, 0.9, 0.9)
	main.refresh:SetScript("OnClick", function()
		if not ahOpen then
			print("|cff33ccffAH Scanner:|r open the auction house, then open a profession and press Scan.")
			return
		end
		if not CurrentProfession() then
			print("|cff33ccffAH Scanner:|r open a profession window. Scan only prices that profession.")
			if frame then frame:Refresh() end
			return
		end
		AdoptOpenProfession()
		if #recipes == 0 then
			print("|cff33ccffAH Scanner:|r that profession has no item recipes to price.")
			if frame then frame:Refresh() end
			return
		end
		BeginPriceScan()
	end)
	main.refresh:SetScript("OnEnter", function(self)
		self:SetBackdropBorderColor(0.7, 0.7, 0.7, 1)
	end)
	main.refresh:SetScript("OnLeave", function(self)
		self:SetBackdropBorderColor(0.35, 0.35, 0.35, 1)
	end)

	main.scroll = CreateFrame("ScrollFrame", "AHScannerScrollFrame", main, "UIPanelScrollFrameTemplate")
	main.scroll:SetPoint("TOPLEFT", 10, -122)
	main.scroll:SetPoint("BOTTOMRIGHT", -28, 12)
	main.scroll:SetFrameLevel(main:GetFrameLevel() + 5)
	main.scroll:EnableMouse(true)
	main.scroll:EnableMouseWheel(true)
	-- Keep the template slider's range in sync. Replacing these scripts without
	-- updating the slider leaves the thumb stuck at the top.
	main.scroll:SetScript("OnScrollRangeChanged", function(self, xRange, yRange)
		if type(ScrollFrame_OnScrollRangeChanged) == "function" then
			pcall(ScrollFrame_OnScrollRangeChanged, self, xRange, yRange)
		end
		SyncScrollBar(self)
	end)
	main.scroll:SetScript("OnVerticalScroll", function(self, offset)
		scrollOffset = offset
		if not syncingScroll and type(ScrollFrame_OnVerticalScroll) == "function" then
			pcall(ScrollFrame_OnVerticalScroll, self, offset)
		end
		SyncScrollBar(self)
	end)
	main.scroll:SetScript("OnMouseWheel", function(_, delta)
		ScrollBy(delta)
	end)

	local bar = ScrollBarOf(main.scroll)
	if bar then
		bar:ClearAllPoints()
		bar:SetPoint("TOPLEFT", main.scroll, "TOPRIGHT", 4, -16)
		bar:SetPoint("BOTTOMLEFT", main.scroll, "BOTTOMRIGHT", 4, 16)
		bar:SetFrameLevel(main.scroll:GetFrameLevel() + 10)
		if not bar:GetScript("OnValueChanged") then
			bar:SetScript("OnValueChanged", function(self, value)
				if not syncingScroll then
					self:GetParent():SetVerticalScroll(value)
				end
			end)
		end
	end

	main.headVendor = main:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
	main.headVendor:SetPoint("BOTTOMRIGHT", main.scroll, "TOPRIGHT", -12, 4)
	main.headVendor:SetWidth(84)
	main.headVendor:SetJustifyH("RIGHT")
	main.headVendor:SetText("Vendor")
	main.headVendor:SetTextColor(0.65, 0.78, 0.9)

	main.headAH = main:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
	main.headAH:SetPoint("RIGHT", main.headVendor, "LEFT", -6, 0)
	main.headAH:SetWidth(84)
	main.headAH:SetJustifyH("RIGHT")
	main.headAH:SetText("AH")
	main.headAH:SetTextColor(0.9, 0.78, 0.45)

	main.headRecipe = main:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
	main.headRecipe:SetPoint("BOTTOMLEFT", main.scroll, "TOPLEFT", 40, 4)
	main.headRecipe:SetText("Recipe")
	main.headRecipe:SetTextColor(0.55, 0.55, 0.55)

	main.content = CreateFrame("Frame", nil, main.scroll)
	main.content:SetSize(480, 1)
	main.content:EnableMouse(false)
	main.scroll:SetScrollChild(main.content)
	listScroll = main.scroll
	HookWheel(main)
	HookWheel(main.content)
	main.rows = {}

	function main:Place()
		self:ClearAllPoints()
		local window = db.window
		if type(window) == "table" and window.point and window.relativePoint then
			self:SetPoint(window.point, UIParent, window.relativePoint, window.x or 0, window.y or 0)
			return
		end
		if AuctionHouseFrame and AuctionHouseFrame:IsShown() then
			self:SetPoint("TOPLEFT", AuctionHouseFrame, "TOPRIGHT", 8, 0)
		else
			self:SetPoint("TOPLEFT", UIParent, "TOPLEFT", 40, -80)
		end
	end

	function main:Refresh()
		if not self:IsShown() then return end
		if self.title then
			self.title:SetText(activeName and (activeName .. " Profit") or "AH Scanner")
		end
		self.status:SetText(StatusText())
		self.note:SetText(NoteText())
		local list = SortedRecipes()
		local width = self.scroll:GetWidth()
		if not width or width < 200 then width = self:GetWidth() - 40 end
		self.content:SetWidth(width)
		local y = -4
		for i = 1, #list do
			local row = self.rows[i]
			if not row then
				row = CreateRow(self.content)
				self.rows[i] = row
			end
			row:ClearAllPoints()
			row:SetPoint("TOPLEFT", 4, y)
			row:SetPoint("TOPRIGHT", -4, y)
			local ok, err = pcall(FillRow, row, list[i])
			if not ok then
				row.name:SetText("|cffff8080Could not draw this recipe|r")
				row.reagents:SetText(tostring(err))
				row:SetHeight(64)
			end
			row:Show()
			if not row.wheelHooked then
				HookWheel(row)
				if row.content then HookWheel(row.content) end
				if row.icon then HookWheel(row.icon) end
				row.wheelHooked = true
			end
			y = y - row:GetHeight() - 6
		end
		for i = #list + 1, #self.rows do
			self.rows[i]:Hide()
		end
		self.content:SetHeight(math.max(1, -y + 8))
		if self.scroll.UpdateScrollChildRect then
			self.scroll:UpdateScrollChildRect()
		end
		SyncScrollBar(self.scroll)
		C_Timer.After(0, function()
			if self.scroll then
				SyncScrollBar(self.scroll)
			end
		end)
	end

	main.PumpSearch = PumpSearch

	main:SetScript("OnShow", function(self)
		self:Refresh()
	end)
	main:SetScript("OnHide", function()
		-- A search in progress holds the auction house throttle, so closing
		-- the window stops it.
		if scanMode == "search" then
			StopScan()
		end
	end)
	main:Hide()
	return main
end

local function ShowWindow()
	if not frame then
		frame = BuildFrame()
	end
	if not placed then
		frame:Place()
		placed = true
	end
	frame:Show()
	frame:Raise()
	frame:Refresh()
end

local minimapButton

local MINIMAP_SHAPES = {
	["ROUND"] = { true, true, true, true },
	["SQUARE"] = { false, false, false, false },
	["CORNER-TOPLEFT"] = { false, false, false, true },
	["CORNER-TOPRIGHT"] = { false, false, true, false },
	["CORNER-BOTTOMLEFT"] = { false, true, false, false },
	["CORNER-BOTTOMRIGHT"] = { true, false, false, false },
	["SIDE-LEFT"] = { false, true, false, true },
	["SIDE-RIGHT"] = { true, false, true, false },
	["SIDE-TOP"] = { false, false, true, true },
	["SIDE-BOTTOM"] = { true, true, false, false },
	["TRICORNER-TOPLEFT"] = { false, true, true, true },
	["TRICORNER-TOPRIGHT"] = { true, false, true, true },
	["TRICORNER-BOTTOMLEFT"] = { true, true, false, true },
	["TRICORNER-BOTTOMRIGHT"] = { true, true, true, false },
}

local function UpdateMinimapButton()
	if not minimapButton or not Minimap then return end
	local angle = math.rad(db.minimapPos or 225)
	local x, y = math.cos(angle), math.sin(angle)
	local q = 1
	if x < 0 then q = q + 1 end
	if y > 0 then q = q + 2 end
	local shape = GetMinimapShape and GetMinimapShape() or "ROUND"
	local quad = MINIMAP_SHAPES[shape] or MINIMAP_SHAPES.ROUND
	local w = (Minimap:GetWidth() / 2) + 5
	local h = (Minimap:GetHeight() / 2) + 5
	if quad[q] then
		x, y = x * w, y * h
	else
		local diagW = math.sqrt(2 * w * w) - 10
		local diagH = math.sqrt(2 * h * h) - 10
		x = math.max(-w, math.min(x * diagW, w))
		y = math.max(-h, math.min(y * diagH, h))
	end
	minimapButton:ClearAllPoints()
	minimapButton:SetPoint("CENTER", Minimap, "CENTER", x, y)
end

local function ToggleWindow()
	if frame and frame:IsShown() then
		frame:Hide()
		return
	end
	DetectMarket()
	LoadMarketPrices()
	if not AdoptOpenProfession() and #recipes == 0 then
		RestoreLastProfession()
	end
	ShowWindow()
end

local function CreateMinimapButton()
	if minimapButton or not Minimap then return end
	local button = CreateFrame("Button", "AHScannerMinimapButton", Minimap)
	minimapButton = button
	button:SetSize(31, 31)
	button:SetFrameStrata("MEDIUM")
	button:SetFrameLevel(8)
	if button.SetFixedFrameStrata then button:SetFixedFrameStrata(true) end
	if button.SetFixedFrameLevel then button:SetFixedFrameLevel(true) end
	button:RegisterForClicks("LeftButtonUp", "RightButtonUp")
	button:RegisterForDrag("LeftButton")
	button:SetHighlightTexture(136477)

	button.border = button:CreateTexture(nil, "OVERLAY")
	button.border:SetTexture(136430)
	button.border:SetSize(53, 53)
	button.border:SetPoint("TOPLEFT")

	button.background = button:CreateTexture(nil, "BACKGROUND")
	button.background:SetTexture(136467)
	button.background:SetSize(20, 20)
	button.background:SetPoint("CENTER")

	button.icon = button:CreateTexture(nil, "ARTWORK")
	button.icon:SetTexture(136240) -- Trade_Alchemy
	button.icon:SetSize(17, 17)
	button.icon:SetPoint("CENTER")
	button.icon:SetTexCoord(0.05, 0.95, 0.05, 0.95)

	button:SetScript("OnClick", function()
		ToggleWindow()
	end)
	button:SetScript("OnEnter", function(self)
		GameTooltip:SetOwner(self, "ANCHOR_LEFT")
		GameTooltip:SetText("AH Scanner")
		GameTooltip:AddLine("Left-click to show or hide the profit window.", 1, 1, 1)
		GameTooltip:AddLine("Drag to move.", 0.8, 0.8, 0.8)
		GameTooltip:Show()
	end)
	button:SetScript("OnLeave", function()
		GameTooltip:Hide()
	end)
	button:SetScript("OnDragStart", function(self)
		GameTooltip:Hide()
		self:SetScript("OnUpdate", function()
			local mx, my = Minimap:GetCenter()
			local scale = Minimap:GetEffectiveScale()
			local px, py = GetCursorPosition()
			px, py = px / scale, py / scale
			local atan2 = math.atan2 or math.atan
			db.minimapPos = math.deg(atan2(py - my, px - mx)) % 360
			UpdateMinimapButton()
		end)
	end)
	button:SetScript("OnDragStop", function(self)
		self:SetScript("OnUpdate", nil)
	end)

	UpdateMinimapButton()
	button:Show()
end

local function PrepareAndScan()
	DetectMarket()
	LoadMarketPrices()
	if not AdoptOpenProfession() then
		RestoreLastProfession()
	end
	ShowWindow()
end

local function OnAuctionShow()
	ahOpen = true
	PrepareAndScan()
end

local function OnAuctionClosed()
	ahOpen = false
	StopScan()
	if frame then
		frame:Hide()
	end
end

local function Slash(message)
	message = message and message:lower():gsub("^%s+", ""):gsub("%s+$", "") or ""
	if message == "learn" or message == "recipes" then
		if not AdoptOpenProfession() then
			print("|cff33ccffAH Scanner:|r open a profession window first.")
			return
		end
		if frame and frame:IsShown() then
			frame:Refresh()
		end
		print("|cff33ccffAH Scanner:|r read " .. (activeName or "that profession") .. ". Press Scan at the auction house to price it.")
		return
	end
	ToggleWindow()
end

eventFrame = CreateFrame("Frame")
eventFrame:RegisterEvent("ADDON_LOADED")
eventFrame:RegisterEvent("PLAYER_ENTERING_WORLD")
eventFrame:RegisterEvent("AUCTION_HOUSE_SHOW")
eventFrame:RegisterEvent("AUCTION_HOUSE_CLOSED")
eventFrame:RegisterEvent("TRADE_SKILL_LIST_UPDATE")
eventFrame:RegisterEvent("TRADE_SKILL_SHOW")
eventFrame:RegisterEvent("NEW_RECIPE_LEARNED")
eventFrame:RegisterEvent("GET_ITEM_INFO_RECEIVED")
eventFrame:RegisterEvent("COMMODITY_SEARCH_RESULTS_UPDATED")
eventFrame:RegisterEvent("ITEM_SEARCH_RESULTS_UPDATED")
eventFrame:RegisterEvent("AUCTION_HOUSE_THROTTLED_SYSTEM_READY")
eventFrame:RegisterEvent("AUCTION_HOUSE_THROTTLED_MESSAGE_DROPPED")
eventFrame:RegisterEvent("AUCTION_HOUSE_SHOW_ERROR")

eventFrame:SetScript("OnEvent", function(self, event, arg1, arg2)
	if event == "ADDON_LOADED" then
		if arg1 ~= ADDON then return end
		InitDB()
		CreateMinimapButton()
		self:UnregisterEvent("ADDON_LOADED")
	elseif event == "PLAYER_ENTERING_WORLD" then
		if db then
			CreateMinimapButton()
			UpdateMinimapButton()
		end
	elseif event == "AUCTION_HOUSE_SHOW" then
		OnAuctionShow()
	elseif event == "AUCTION_HOUSE_CLOSED" then
		OnAuctionClosed()
	elseif event == "TRADE_SKILL_LIST_UPDATE" or event == "TRADE_SKILL_SHOW" then
		OnProfessionUpdate()
	elseif event == "NEW_RECIPE_LEARNED" then
		OnNewRecipe(arg1)
	elseif event == "GET_ITEM_INFO_RECEIVED" then
		if arg2 == false then return end
		names[arg1] = nil
		icons[arg1] = nil
		ItemName(arg1)
		ItemIcon(arg1)
		ScheduleRefresh()
	elseif event == "COMMODITY_SEARCH_RESULTS_UPDATED" then
		OnCommodityResults(arg1)
	elseif event == "ITEM_SEARCH_RESULTS_UPDATED" then
		OnItemResults(arg1)
	elseif event == "AUCTION_HOUSE_THROTTLED_SYSTEM_READY" then
		if scanMode == "search" then
			PumpSearch()
		end
	elseif event == "AUCTION_HOUSE_THROTTLED_MESSAGE_DROPPED" then
		if scanMode == "search" and searchPending then
			local itemID = searchPending
			local step = searchPendingStep
			searchPending = nil
			searchPendingStep = nil
			local attempts = (searchAttempts[itemID] or 0) + 1
			searchAttempts[itemID] = attempts
			if attempts >= 3 or not step then
				RememberPrice(itemID, false)
				searchSeen[itemID] = true
				ScheduleRefresh()
			else
				table.insert(searchQueue, 1, step)
			end
			C_Timer.After(SEARCH_GAP, PumpSearch)
		end
	end
end)

SLASH_AHSCANNER1 = "/ahscan"
SLASH_AHSCANNER2 = "/ahscanner"
SlashCmdList.AHSCANNER = Slash
