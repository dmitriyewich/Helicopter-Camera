script_name('Helicopter-Camera')
script_author('dmitriyewich, https://vk.com/dmitriyewichmods')
script_dependencies("mimgui", "sampfuncs")
script_properties('work-in-pause')
script_version("1.5")
script_version_number(150)

local script = thisScript()
require"lib.moonloader"
local ffi = require 'ffi'
local vkeys = require 'vkeys'
local Vector3D = require "vector3d"
local lmemory, memory = pcall(require, 'memory')
local limgui, imgui = pcall(require, 'mimgui') -- https://github.com/THE-FYP/mimgui
local new, str, sizeof = imgui.new, ffi.string, ffi.sizeof

local lencoding, encoding = pcall(require, 'encoding')
encoding.default = 'CP1251'
u8 = encoding.UTF8

-- AUTHOR main hooks lib: RTD/RutreD(https://www.blast.hk/members/126461/)
ffi.cdef[[
    int VirtualProtect(void* lpAddress, unsigned long dwSize, unsigned long flNewProtect, unsigned long* lpflOldProtect);
    void* VirtualAlloc(void* lpAddress, unsigned long dwSize, unsigned long  flAllocationType, unsigned long flProtect);
    int VirtualFree(void* lpAddress, unsigned long dwSize, unsigned long dwFreeType);
]]
local function copy(dst, src, len)
    return ffi.copy(ffi.cast('void*', dst), ffi.cast('const void*', src), len)
end
local buff = {free = {}}
local function VirtualProtect(lpAddress, dwSize, flNewProtect, lpflOldProtect)
    return ffi.C.VirtualProtect(ffi.cast('void*', lpAddress), dwSize, flNewProtect, lpflOldProtect)
end
local function VirtualAlloc(lpAddress, dwSize, flAllocationType, flProtect, blFree)
    local alloc = ffi.C.VirtualAlloc(lpAddress, dwSize, flAllocationType, flProtect)
    if blFree then
        table.insert(buff.free, function()
            ffi.C.VirtualFree(alloc, 0, 0x8000)
        end)
    end
    return ffi.cast('intptr_t', alloc)
end
--JMP HOOKS
local jmp_hook = {hooks = {}}
function jmp_hook.new(cast, callback, hook_addr, size, trampoline, org_bytes_tramp)
    jit.off(callback, true) --off jit compilation | thx FYP
    local size = size or 5
    local trampoline = trampoline or false
    local new_hook, mt = {}, {}
    local detour_addr = tonumber(ffi.cast('intptr_t', ffi.cast(cast, callback)))
    local old_prot = ffi.new('unsigned long[1]')
    local org_bytes = ffi.new('uint8_t[?]', size)
    copy(org_bytes, hook_addr, size)
    if trampoline then
        local alloc_addr = VirtualAlloc(nil, size + 5, 0x1000, 0x40, true)
        local trampoline_bytes = ffi.new('uint8_t[?]', size + 5, 0x90)
        if org_bytes_tramp then
            local i = 0
            for byte in org_bytes_tramp:gmatch('(%x%x)') do
                trampoline_bytes[i] = tonumber(byte, 16)
                i = i + 1
            end
        else
            copy(trampoline_bytes, org_bytes, size)
        end
        trampoline_bytes[size] = 0xE9
        ffi.cast('int32_t*', trampoline_bytes + size + 1)[0] = hook_addr - tonumber(alloc_addr) - size + (size - 5)
        copy(alloc_addr, trampoline_bytes, size + 5)
        new_hook.call = ffi.cast(cast, alloc_addr)
        mt = {__call = function(self, ...)
            return self.call(...)
        end}
    else
        new_hook.call = ffi.cast(cast, hook_addr)
        mt = {__call = function(self, ...)
            self.stop()
            local res = self.call(...)
            self.start()
            return res
        end}
    end
    local hook_bytes = ffi.new('uint8_t[?]', size, 0x90)
    hook_bytes[0] = 0xE9
    ffi.cast('int32_t*', hook_bytes + 1)[0] = detour_addr - hook_addr - 5
    new_hook.status = false
    local function set_status(bool)
        new_hook.status = bool
        VirtualProtect(hook_addr, size, 0x40, old_prot)
        copy(hook_addr, bool and hook_bytes or org_bytes, size)
        VirtualProtect(hook_addr, size, old_prot[0], old_prot)
    end
    new_hook.stop = function() set_status(false) end
    new_hook.start = function() set_status(true) end
    new_hook.start()
    if org_bytes[0] == 0xE9 or org_bytes[0] == 0xE8 then
        print('[WARNING] rewrote another hook'.. (trampoline and ' (old hook was disabled, through trampoline)' or ''))
    end
    table.insert(jmp_hook.hooks, new_hook)
    return setmetatable(new_hook, mt)
end
--JMP HOOKS
--DELETE HOOKS
addEventHandler('onScriptTerminate', function(scr)
    if scr == script.this then
        for i, hook in ipairs(jmp_hook.hooks) do
            if hook.status then
                hook.stop()
            end
        end
        for i, free in ipairs(buff.free) do
            free()
        end
    end
end)
--DELETE HOOKS

local function isarray(t, emptyIsObject) -- by Phrogz, сортировка
	if type(t)~='table' then return false end
	if not next(t) then return not emptyIsObject end
	local len = #t
	for k,_ in pairs(t) do
		if type(k)~='number' then
			return false
		else
			local _,frac = math.modf(k)
			if frac~=0 or k<1 or k>len then
				return false
			end
		end
	end
	return true
end

local function map(t,f)
	local r={}
	for i,v in ipairs(t) do r[i]=f(v) end
	return r
end

local keywords = {["and"]=1,["break"]=1,["do"]=1,["else"]=1,["elseif"]=1,["end"]=1,["false"]=1,["for"]=1,["function"]=1,["goto"]=1,["if"]=1,["in"]=1,["local"]=1,["nil"]=1,["not"]=1,["or"]=1,["repeat"]=1,["return"]=1,["then"]=1,["true"]=1,["until"]=1,["while"]=1}

local function neatJSON(value, opts) -- by Phrogz, сортировка
	opts = opts or {}
	if opts.wrap==nil  then opts.wrap = 80 end
	if opts.wrap==true then opts.wrap = -1 end
	opts.indent         = opts.indent         or "  "
	opts.arrayPadding  = opts.arrayPadding  or opts.padding      or 0
	opts.objectPadding = opts.objectPadding or opts.padding      or 0
	opts.afterComma    = opts.afterComma    or opts.aroundComma  or 0
	opts.beforeComma   = opts.beforeComma   or opts.aroundComma  or 0
	opts.beforeColon   = opts.beforeColon   or opts.aroundColon  or 0
	opts.afterColon    = opts.afterColon    or opts.aroundColon  or 0
	opts.beforeColon1  = opts.beforeColon1  or opts.aroundColon1 or opts.beforeColon or 0
	opts.afterColon1   = opts.afterColon1   or opts.aroundColon1 or opts.afterColon  or 0
	opts.beforeColonN  = opts.beforeColonN  or opts.aroundColonN or opts.beforeColon or 0
	opts.afterColonN   = opts.afterColonN   or opts.aroundColonN or opts.afterColon  or 0

	local colon  = opts.lua and '=' or ':'
	local array  = opts.lua and {'{','}'} or {'[',']'}
	local apad   = string.rep(' ', opts.arrayPadding)
	local opad   = string.rep(' ', opts.objectPadding)
	local comma  = string.rep(' ',opts.beforeComma)..','..string.rep(' ',opts.afterComma)
	local colon1 = string.rep(' ',opts.beforeColon1)..colon..string.rep(' ',opts.afterColon1)
	local colonN = string.rep(' ',opts.beforeColonN)..colon..string.rep(' ',opts.afterColonN)

	local build
	local function rawBuild(o,indent)
		if o==nil then
			return indent..'null'
		else
			local kind = type(o)
			if kind=='number' then
				local _,frac = math.modf(o)
				return indent .. string.format( frac~=0 and opts.decimals and ('%.'..opts.decimals..'f') or '%g', o)
			elseif kind=='boolean' or kind=='nil' then
				return indent..tostring(o)
			elseif kind=='string' then
				return indent..string.format('%q', o):gsub('\\\n','\\n')
			elseif isarray(o, opts.emptyTablesAreObjects) then
				if #o==0 then return indent..array[1]..array[2] end
				local pieces = map(o, function(v) return build(v,'') end)
				local oneLine = indent..array[1]..apad..table.concat(pieces,comma)..apad..array[2]
				if opts.wrap==false or #oneLine<=opts.wrap then return oneLine end
				if opts.short then
					local indent2 = indent..' '..apad;
					pieces = map(o, function(v) return build(v,indent2) end)
					pieces[1] = pieces[1]:gsub(indent2,indent..array[1]..apad, 1)
					pieces[#pieces] = pieces[#pieces]..apad..array[2]
					return table.concat(pieces, ',\n')
				else
					local indent2 = indent..opts.indent
					return indent..array[1]..'\n'..table.concat(map(o, function(v) return build(v,indent2) end), ',\n')..'\n'..(opts.indentLast and indent2 or indent)..array[2]
				end
			elseif kind=='table' then
				if not next(o) then return indent..'{}' end

				local sortedKV = {}
				local sort = opts.sort or opts.sorted
				for k,v in pairs(o) do
					local kind = type(k)
					if kind=='string' or kind=='number' then
						sortedKV[#sortedKV+1] = {k,v}
						if sort==true then
							sortedKV[#sortedKV][3] = tostring(k)
						elseif type(sort)=='function' then
							sortedKV[#sortedKV][3] = sort(k,v,o)
						end
					end
				end
				if sort then table.sort(sortedKV, function(a,b) return a[3]<b[3] end) end
				local keyvals
				if opts.lua then
					keyvals=map(sortedKV, function(kv)
						if type(kv[1])=='string' and not keywords[kv[1]] and string.match(kv[1],'^[%a_][%w_]*$') then
							return string.format('%s%s%s',kv[1],colon1,build(kv[2],''))
						else
							return string.format('[%q]%s%s',kv[1],colon1,build(kv[2],''))
						end
					end)
				else
					keyvals=map(sortedKV, function(kv) return string.format('%q%s%s',kv[1],colon1,build(kv[2],'')) end)
				end
				keyvals=table.concat(keyvals, comma)
				local oneLine = indent.."{"..opad..keyvals..opad.."}"
				if opts.wrap==false or #oneLine<opts.wrap then return oneLine end
				if opts.short then
					keyvals = map(sortedKV, function(kv) return {indent..' '..opad..string.format('%q',kv[1]), kv[2]} end)
					keyvals[1][1] = keyvals[1][1]:gsub(indent..' ', indent..'{', 1)
					if opts.aligned then
						local longest = math.max(table.unpack(map(keyvals, function(kv) return #kv[1] end)))
						local padrt   = '%-'..longest..'s'
						for _,kv in ipairs(keyvals) do kv[1] = padrt:format(kv[1]) end
					end
					for i,kv in ipairs(keyvals) do
						local k,v = kv[1], kv[2]
						local indent2 = string.rep(' ',#(k..colonN))
						local oneLine = k..colonN..build(v,'')
						if opts.wrap==false or #oneLine<=opts.wrap or not v or type(v)~='table' then
							keyvals[i] = oneLine
						else
							keyvals[i] = k..colonN..build(v,indent2):gsub('^%s+','',1)
						end
					end
					return table.concat(keyvals, ',\n')..opad..'}'
				else
					local keyvals
					if opts.lua then
						keyvals=map(sortedKV, function(kv)
							if type(kv[1])=='string' and not keywords[kv[1]] and string.match(kv[1],'^[%a_][%w_]*$') then
								return {table.concat{indent,opts.indent,kv[1]}, kv[2]}
							else
								return {string.format('%s%s[%q]',indent,opts.indent,kv[1]), kv[2]}
							end
						end)
					else
						keyvals = {}
						for i,kv in ipairs(sortedKV) do
							keyvals[i] = {indent..opts.indent..string.format('%q',kv[1]), kv[2]}
						end
					end
					if opts.aligned then
						local longest = math.max(table.unpack(map(keyvals, function(kv) return #kv[1] end)))
						local padrt   = '%-'..longest..'s'
						for _,kv in ipairs(keyvals) do kv[1] = padrt:format(kv[1]) end
					end
					local indent2 = indent..opts.indent
					for i,kv in ipairs(keyvals) do
						local k,v = kv[1], kv[2]
						local oneLine = k..colonN..build(v,'')
						if opts.wrap==false or #oneLine<=opts.wrap or not v or type(v)~='table' then
							keyvals[i] = oneLine
						else
							keyvals[i] = k..colonN..build(v,indent2):gsub('^%s+','',1)
						end
					end
					return indent..'{\n'..table.concat(keyvals, ',\n')..'\n'..(opts.indentLast and indent2 or indent)..'}'
				end
			end
		end
	end

	local function memoize()
		local memo = setmetatable({},{_mode='k'})
		return function(o,indent)
			if o==nil then
				return indent..(opts.lua and 'nil' or 'null')
			elseif o~=o then
				return indent..(opts.lua and '0/0' or '"NaN"')
			elseif o==math.huge then
				return indent..(opts.lua and '1/0' or '9e9999')
			elseif o==-math.huge then
				return indent..(opts.lua and '-1/0' or '-9e9999')
			end
			local byIndent = memo[o]
			if not byIndent then
				byIndent = setmetatable({},{_mode='k'})
				memo[o] = byIndent
			end
			if not byIndent[indent] then
				byIndent[indent] = rawBuild(o,indent)
			end
			return byIndent[indent]
		end
	end

	build = memoize()
	return build(value,'')
end

function savejson(table, path)
    local f = io.open(path, "w")
    f:write(table)
    f:close()
end

function convertTableToJsonString(config)
	return (neatJSON(config, { wrap = 157, short = true, sort = true, aligned = true, arrayPadding = 1, afterComma = 1, beforeColon1 = 1 }))
end

function zone()
	local zone = {{"Ависпа", "Avispa Country Club", -2667.810, -302.135, -28.831, -2646.400, -262.320, 71.169}, {"Международный Аэропорт Истер Бей", "Easter Bay Airport", -1315.420, -405.388, 15.406, -1264.400, -209.543, 25.406}, {"Ависпа", "Avispa Country Club", -2550.040, -355.493, 0.000, -2470.040, -318.493, 39.700},
	 {"Международный Аэропорт Истер Бей", "Easter Bay Airport", -1490.330, -209.543, 15.406, -1264.400, -148.388, 25.406}, {"Гарсия", "Garcia", -2395.140, -222.589, -5.3, -2354.090, -204.792, 200.000}, {"Сшэйди Кэйбин", "Shady Cabin", -1632.830, -2263.440, -3.0, -1601.330, -2231.790, 200.000},
	 {"Ист Лос Сантос", "East Los Santos", 2381.680, -1494.030, -89.084, 2421.030, -1454.350, 110.916}, {"Лва Фрейт Депо", "LVA Freight Depot", 1236.630, 1163.410, -89.084, 1277.050, 1203.280, 110.916}, {"Пилсон Интерсекшон", "Blackfield Intersection", 1277.050, 1044.690, -89.084, 1315.350, 1087.630, 110.916}, {"Ависпа", "Avispa Country Club", -2470.040, -355.493, 0.000, -2270.040, -318.493, 46.100}, {"Темпл", "Temple", 1252.330, -926.999, -89.084, 1357.000, -910.170, 110.916},
	 {"Юнити Стейшен", "Unity Station", 1692.620, -1971.800, -20.492, 1812.620, -1932.800, 79.508}, {"Лва Фрейт Депо", "LVA Freight Depot", 1315.350, 1044.690, -89.084, 1375.600, 1087.630, 110.916},
	 {"Лос Флорес", "Los Flores", 2581.730, -1454.350, -89.084, 2632.830, -1393.420, 110.916}, {"Старфиш", "Starfish Casino", 2437.390, 1858.100, -39.084, 2495.090, 1970.850, 60.916},
	 {"Истер Бэй Кемикалс", "Easter Bay Chemicals", -1132.820, -787.391, 0.000, -956.476, -768.027, 200.000}, {"Даунтаун Лос Сантос", "Downtown Los Santos", 1370.850, -1170.870, -89.084, 1463.900, -1130.850, 110.916}, {"Эсплэнейд Ист", "Esplanade East", -1620.300, 1176.520, -4.5, -1580.010, 1274.260, 200.000},
	 {"Маркет Стейшен", "Market Station", 787.461, -1410.930, -34.126, 866.009, -1310.210, 65.874}, {"Линден Стейшен", "Linden Station", 2811.250, 1229.590, -39.594, 2861.250, 1407.590, 60.406}, {"Монтгомери Интерсекшон", "Montgomery Intersection", 1582.440, 347.457, 0.000, 1664.620, 401.750, 200.000}, {"Мост Фредерик", "Frederick Bridge", 2759.250, 296.501, 0.000, 2774.250, 594.757, 200.000},
	 {"Иеллоу Белл Стейшен", "Yellow Bell Station", 1377.480, 2600.430, -21.926, 1492.450, 2687.360, 78.074}, {"Даунтаун Лос Сантос", "Downtown Los Santos", 1507.510, -1385.210, 110.916, 1582.550, -1325.310, 335.916}, {"Джефферсон", "Jefferson", 2185.330, -1210.740, -89.084, 2281.450, -1154.590, 110.916},
	 {"Малхолланд", "Mulholland", 1318.130, -910.170, -89.084, 1357.000, -768.027, 110.916}, {"Ависпа", "Avispa Country Club", -2361.510, -417.199, 0.000, -2270.040, -355.493, 200.000},
	 {"Джефферсон", "Jefferson", 1996.910, -1449.670, -89.084, 2056.860, -1350.720, 110.916}, {"Западный 226", "Julius Thruway West", 1236.630, 2142.860, -89.084, 1297.470, 2243.230, 110.916}, {"Джефферсон", "Jefferson", 2124.660, -1494.030, -89.084, 2266.210, -1449.670, 110.916},
	 {"Северный 226", "Julius Thruway North", 1848.400, 2478.490, -89.084, 1938.800, 2553.490, 110.916}, {"Родео", "Rodeo", 422.680, -1570.200, -89.084, 466.223, -1406.050, 110.916}, {"Станция Крэнберри", "Cranberry Station", -2007.830, 56.306, 0.000, -1922.000, 224.782, 100.000}, {"Даунтаун Лос Сантос", "Downtown Los Santos", 1391.050, -1026.330, -89.084, 1463.900, -926.999, 110.916},
	 {"Рэдсэндс Уэст", "Redsands West", 1704.590, 2243.230, -89.084, 1777.390, 2342.830, 110.916}, {"Литл Мехико", "Little Mexico", 1758.900, -1722.260, -89.084, 1812.620, -1577.590, 110.916}, {"Пилсон Интерсекшон", "Blackfield Intersection", 1375.600, 823.228, -89.084, 1457.390, 919.447, 110.916}, {"Лос Сантос Международный аэропорт", "Los Santos International", 1974.630, -2394.330, -39.084, 2089.000, -2256.590, 60.916},
	 {"Бекон Хилл", "Beacon Hill", -399.633, -1075.520, -1.489, -319.033, -977.516, 198.511}, {"Родео", "Rodeo", 334.503, -1501.950, -89.084, 422.680, -1406.050, 110.916}, {"Ричман", "Richman", 225.165, -1369.620, -89.084, 334.503, -1292.070, 110.916}, {"Даунтаун Лос Сантос", "Downtown Los Santos", 1724.760, -1250.900, -89.084, 1812.620, -1150.870, 110.916},
	 {"Стрип", "The Strip", 2027.400, 1703.230, -89.084, 2137.400, 1783.230, 110.916}, {"Даунтаун Лос Сантос", "Downtown Los Santos", 1378.330, -1130.850, -89.084, 1463.900, -1026.330, 110.916}, {"Пилсон Интерсекшон", "Blackfield Intersection", 1197.390, 1044.690, -89.084, 1277.050, 1163.390, 110.916},
	 {"Конференц центр", "Conference Center", 1073.220, -1842.270, -89.084, 1323.900, -1804.210, 110.916}, {"Монтгомери", "Montgomery", 1451.400, 347.457, -6.1, 1582.440, 420.802, 200.000}, {"Фостер Вэлли", "Foster Valley", -2270.040, -430.276, -1.2, -2178.690, -324.114, 200.000},
	 {"Блэкфилд Чапел", "Blackfield Chapel", 1325.600, 596.349, -89.084, 1375.600, 795.010, 110.916}, {"Международный аэропорт Лос Сантос", "Los Santos International", 2051.630, -2597.260, -39.084, 2152.450, -2394.330, 60.916}, {"Малхолланд", "Mulholland", 1096.470, -910.170, -89.084, 1169.130, -768.027, 110.916}, {"Ейллоу Белл", "Yellow Bell Gol Course", 1457.460, 2723.230, -89.084, 1534.560, 2863.230, 110.916},
	 {"Стрип", "The Strip", 2027.400, 1783.230, -89.084, 2162.390, 1863.230, 110.916}, {"Джефферсон", "Jefferson", 2056.860, -1210.740, -89.084, 2185.330, -1126.320, 110.916}, {"Малхолланд", "Mulholland", 952.604, -937.184, -89.084, 1096.470, -860.619, 110.916}, {"Алдеа Мальвада", "Aldea Malvada", -1372.140, 2498.520, 0.000, -1277.590, 2615.350, 200.000},
	 {"Лас Колинас", "Las Colinas", 2126.860, -1126.320, -89.084, 2185.330, -934.489, 110.916}, {"Лас Колинас", "Las Colinas", 1994.330, -1100.820, -89.084, 2056.860, -920.815, 110.916}, {"Ричман", "Richman", 647.557, -954.662, -89.084, 768.694, -860.619, 110.916}, {"Лва Фрейт Депо", "LVA Freight Depot", 1277.050, 1087.630, -89.084, 1375.600, 1203.280, 110.916},
	 {"Северный 226", "Julius Thruway North", 1377.390, 2433.230, -89.084, 1534.560, 2507.230, 110.916}, {"Уиллоуфилд", "Willowfield", 2201.820, -2095.000, -89.084, 2324.000, -1989.900, 110.916}, {"Северный 226", "Julius Thruway North", 1704.590, 2342.830, -89.084, 1848.400, 2433.230, 110.916},
	 {"Темпл", "Temple", 1252.330, -1130.850, -89.084, 1378.330, -1026.330, 110.916}, {"Литл Мехико", "Little Mexico", 1701.900, -1842.270, -89.084, 1812.620, -1722.260, 110.916},
	 {"Куинс", "Queens", -2411.220, 373.539, 0.000, -2253.540, 458.411, 200.000}, {"Лас Вентурас Аэропорт", "Las Venturas Airport", 1515.810, 1586.400, -12.500, 1729.950, 1714.560, 87.500}, {"Ричман", "Richman", 225.165, -1292.070, -89.084, 466.223, -1235.070, 110.916}, {"Темпл", "Temple", 1252.330, -1026.330, -89.084, 1391.050, -926.999, 110.916},
	 {"Ист Лос Сантос", "East Los Santos", 2266.260, -1494.030, -89.084, 2381.680, -1372.040, 110.916}, {"Восточный 226", "Julius Thruway East", 2623.180, 943.235, -89.084, 2749.900, 1055.960, 110.916}, {"Уиллоуфилд", "Willowfield", 2541.700, -1941.400, -89.084, 2703.580, -1852.870, 110.916}, {"Лас Колинас", "Las Colinas", 2056.860, -1126.320, -89.084, 2126.860, -920.815, 110.916},
	 {"Восточный 226", "Julius Thruway East", 2625.160, 2202.760, -89.084, 2685.160, 2442.550, 110.916}, {"Родео", "Rodeo", 225.165, -1501.950, -89.084, 334.503, -1369.620, 110.916}, {"Лас Брухас", "Las Brujas", -365.167, 2123.010, -3.0, -208.570, 2217.680, 200.000}, {"Восточный 226", "Julius Thruway East", 2536.430, 2442.550, -89.084, 2685.160, 2542.550, 110.916},
	 {"Родео", "Rodeo", 334.503, -1406.050, -89.084, 466.223, -1292.070, 110.916}, {"Вайнвуд", "Vinewood", 647.557, -1227.280, -89.084, 787.461, -1118.280, 110.916}, {"Родео", "Rodeo", 422.680, -1684.650, -89.084, 558.099, -1570.200, 110.916}, {"Северный 226", "Julius Thruway North", 2498.210, 2542.550, -89.084, 2685.160, 2626.550, 110.916},
	 {"Даунтаун Лос Сантос", "Downtown Los Santos", 1724.760, -1430.870, -89.084, 1812.620, -1250.900, 110.916}, {"Родео", "Rodeo", 225.165, -1684.650, -89.084, 312.803, -1501.950, 110.916}, {"Джефферсон", "Jefferson", 2056.860, -1449.670, -89.084, 2266.210, -1372.040, 110.916}, {"Хэмптон Барнс", "Hampton Barns", 603.035, 264.312, 0.000, 761.994, 366.572, 200.000},
	 {"Темпл", "Temple", 1096.470, -1130.840, -89.084, 1252.330, -1026.330, 110.916}, {"Мост Кинкейд", "Kincaid Bridge", -1087.930, 855.370, -89.084, -961.950, 986.281, 110.916}, {"Верона Бич", "Verona Beach", 1046.150, -1722.260, -89.084, 1161.520, -1577.590, 110.916}, {"Коммерс", "Commerce", 1323.900, -1722.260, -89.084, 1440.900, -1577.590, 110.916},
	 {"Малхолланд", "Mulholland", 1357.000, -926.999, -89.084, 1463.900, -768.027, 110.916}, {"Родео", "Rodeo", 466.223, -1570.200, -89.084, 558.099, -1385.070, 110.916}, {"Малхолланд", "Mulholland", 911.802, -860.619, -89.084, 1096.470, -768.027, 110.916}, {"Малхолланд", "Mulholland", 768.694, -954.662, -89.084, 952.604, -860.619, 110.916},
	 {"Южный 226", "Julius Thruway South", 2377.390, 788.894, -89.084, 2537.390, 897.901, 110.916}, {"Айдлвуд", "Idlewood", 1812.620, -1852.870, -89.084, 1971.660, -1742.310, 110.916}, {"Оушен Докс", "Ocean Docks", 2089.000, -2394.330, -89.084, 2201.820, -2235.840, 110.916}, {"Коммерс", "Commerce", 1370.850, -1577.590, -89.084, 1463.900, -1384.950, 110.916},
	 {"Северный 226", "Julius Thruway North", 2121.400, 2508.230, -89.084, 2237.400, 2663.170, 110.916}, {"Темпл", "Temple", 1096.470, -1026.330, -89.084, 1252.330, -910.170, 110.916}, {"Глен Парк", "Glen Park", 1812.620, -1449.670, -89.084, 1996.910, -1350.720, 110.916}, {"Международный Аэропорт Истер Бей", "Easter Bay Airport", -1242.980, -50.096, 0.000, -1213.910, 578.396, 200.000},
	 {"Мост Мартин", "Martin Bridge", -222.179, 293.324, 0.000, -122.126, 476.465, 200.000}, {"Стрип", "The Strip", 2106.700, 1863.230, -89.084, 2162.390, 2202.760, 110.916}, {"Уиллоуфилд", "Willowfield", 2541.700, -2059.230, -89.084, 2703.580, -1941.400, 110.916}, {"Мэйрина", "Marina", 807.922, -1577.590, -89.084, 926.922, -1416.250, 110.916},
	 {"Лас Вентурас Аэропорт", "Las Venturas Airport", 1457.370, 1143.210, -89.084, 1777.400, 1203.280, 110.916}, {"Айдлвуд", "Idlewood", 1812.620, -1742.310, -89.084, 1951.660, -1602.310, 110.916}, {"Эсплэнейд Ист", "Esplanade East", -1580.010, 1025.980, -6.1, -1499.890, 1274.260, 200.000}, {"Даунтаун Лос Сантос", "Downtown Los Santos", 1370.850, -1384.950, -89.084, 1463.900, -1170.870, 110.916},
	 {"Мост Мако Спан", "The Mako Span", 1664.620, 401.750, 0.000, 1785.140, 567.203, 200.000}, {"Родео", "Rodeo", 312.803, -1684.650, -89.084, 422.680, -1501.950, 110.916}, {"Першинг сквер", "Pershing Square", 1440.900, -1722.260, -89.084, 1583.500, -1577.590, 110.916}, {"Малхолланд", "Mulholland", 687.802, -860.619, -89.084, 911.802, -768.027, 110.916},
	 {"Мост Гант", "Gant Bridge", -2741.070, 1490.470, -6.1, -2616.400, 1659.680, 200.000}, {"Лас Колинас", "Las Colinas", 2185.330, -1154.590, -89.084, 2281.450, -934.489, 110.916}, {"Малхолланд", "Mulholland", 1169.130, -910.170, -89.084, 1318.130, -768.027, 110.916}, {"Северный 226", "Julius Thruway North", 1938.800, 2508.230, -89.084, 2121.400, 2624.230, 110.916},
	 {"Коммерс", "Commerce", 1667.960, -1577.590, -89.084, 1812.620, -1430.870, 110.916}, {"Родео", "Rodeo", 72.648, -1544.170, -89.084, 225.165, -1404.970, 110.916}, {"Рока Эскаланте", "Roca Escalante", 2536.430, 2202.760, -89.084, 2625.160, 2442.550, 110.916}, {"Родео", "Rodeo", 72.648, -1684.650, -89.084, 225.165, -1544.170, 110.916},
	 {"Маркет", "Market", 952.663, -1310.210, -89.084, 1072.660, -1130.850, 110.916}, {"Лас Колинас", "Las Colinas", 2632.740, -1135.040, -89.084, 2747.740, -945.035, 110.916}, {"Малхолланд", "Mulholland", 861.085, -674.885, -89.084, 1156.550, -600.896, 110.916}, {"Кингс", "King's", -2253.540, 373.539, -9.1, -1993.280, 458.411, 200.000},
	 {"Рэдсэндс Ист", "Redsands East", 1848.400, 2342.830, -89.084, 2011.940, 2478.490, 110.916}, {"Даунтаун", "Downtown", -1580.010, 744.267, -6.1, -1499.890, 1025.980, 200.000}, {"Конференц центр", "Conference Center", 1046.150, -1804.210, -89.084, 1323.900, -1722.260, 110.916}, {"Ричман", "Richman", 647.557, -1118.280, -89.084, 787.461, -954.662, 110.916},
	 {"Оушен Флэст", "Ocean Flats", -2994.490, 277.411, -9.1, -2867.850, 458.411, 200.000}, {"Грингласс", "Greenglass College", 964.391, 930.890, -89.084, 1166.530, 1044.690, 110.916}, {"Глен Парк", "Glen Park", 1812.620, -1100.820, -89.084, 1994.330, -973.380, 110.916}, {"Лва Фрейт Депо", "LVA Freight Depot", 1375.600, 919.447, -89.084, 1457.370, 1203.280, 110.916},
	 {"Регьюлар Том", "Regular Tom", -405.770, 1712.860, -3.0, -276.719, 1892.750, 200.000}, {"Верона Бич", "Verona Beach", 1161.520, -1722.260, -89.084, 1323.900, -1577.590, 110.916}, {"Ист Лос Сантос", "East Los Santos", 2281.450, -1372.040, -89.084, 2381.680, -1135.040, 110.916}, {"Калигула Палас", "Caligula's Palace", 2137.400, 1703.230, -89.084, 2437.390, 1783.230, 110.916}, {"Айдлвуд", "Idlewood", 1951.660, -1742.310, -89.084, 2124.660, -1602.310, 110.916},
	 {"Пилигрим", "Pilgrim", 2624.400, 1383.230, -89.084, 2685.160, 1783.230, 110.916}, {"Айдлвуд", "Idlewood", 2124.660, -1742.310, -89.084, 2222.560, -1494.030, 110.916}, {"Куинс", "Queens", -2533.040, 458.411, 0.000, -2329.310, 578.396, 200.000}, {"Даунтаун", "Downtown", -1871.720, 1176.420, -4.5, -1620.300, 1274.260, 200.000}, {"Коммерс", "Commerce", 1583.500, -1722.260, -89.084, 1758.900, -1577.590, 110.916},
	 {"Ист Лос Сантос", "East Los Santos", 2381.680, -1454.350, -89.084, 2462.130, -1135.040, 110.916}, {"Мэйрина", "Marina", 647.712, -1577.590, -89.084, 807.922, -1416.250, 110.916}, {"Ричман", "Richman", 72.648, -1404.970, -89.084, 225.165, -1235.070, 110.916}, {"Вайнвуд", "Vinewood", 647.712, -1416.250, -89.084, 787.461, -1227.280, 110.916}, {"Ист Лос Сантос", "East Los Santos", 2222.560, -1628.530, -89.084, 2421.030, -1494.030, 110.916},
	 {"Родео", "Rodeo", 558.099, -1684.650, -89.084, 647.522, -1384.930, 110.916}, {"Тунель Истер", "Easter Tunnel", -1709.710, -833.034, -1.5, -1446.010, -730.118, 200.000}, {"Родео", "Rodeo", 466.223, -1385.070, -89.084, 647.522, -1235.070, 110.916}, {"Рэдсэндс Ист", "Redsands East", 1817.390, 2202.760, -89.084, 2011.940, 2342.830, 110.916}, {"Клаун Покет", "The Clown's Pocket", 2162.390, 1783.230, -89.084, 2437.390, 1883.230, 110.916}, {"Айдлвуд", "Idlewood", 1971.660, -1852.870, -89.084, 2222.560, -1742.310, 110.916},
	 {"Монтгомери Интерсекшон", "Montgomery Intersection", 1546.650, 208.164, 0.000, 1745.830, 347.457, 200.000}, {"Уиллоуфилд", "Willowfield", 2089.000, -2235.840, -89.084, 2201.820, -1989.900, 110.916}, {"Темпл", "Temple", 952.663, -1130.840, -89.084, 1096.470, -937.184, 110.916}, {"Прикл Пайн", "Prickle Pine", 1848.400, 2553.490, -89.084, 1938.800, 2863.230, 110.916}, {"Международный аэропорт Лос Сантос", "Los Santos International", 1400.970, -2669.260, -39.084, 2189.820, -2597.260, 60.916},
	 {"Мост Гарвер", "Garver Bridge", -1213.910, 950.022, -89.084, -1087.930, 1178.930, 110.916}, {"Мост Гарвер", "Garver Bridge", -1339.890, 828.129, -89.084, -1213.910, 1057.040, 110.916}, {"Мост Кинкейд", "Kincaid Bridge", -1339.890, 599.218, -89.084, -1213.910, 828.129, 110.916}, {"Мост Кинкейд", "Kincaid Bridge", -1213.910, 721.111, -89.084, -1087.930, 950.022, 110.916}, {"Верона Бич", "Verona Beach", 930.221, -2006.780, -89.084, 1073.220, -1804.210, 110.916},
	 {"Вердант Блаффс", "Verdant Bluffs", 1073.220, -2006.780, -89.084, 1249.620, -1842.270, 110.916}, {"Вайнвуд", "Vinewood", 787.461, -1130.840, -89.084, 952.604, -954.662, 110.916}, {"Вайнвуд", "Vinewood", 787.461, -1310.210, -89.084, 952.663, -1130.840, 110.916}, {"Коммерс", "Commerce", 1463.900, -1577.590, -89.084, 1667.960, -1430.870, 110.916}, {"Маркет", "Market", 787.461, -1416.250, -89.084, 1072.660, -1310.210, 110.916},
	 {"Рокшор Уэст", "Rockshore West", 2377.390, 596.349, -89.084, 2537.390, 788.894, 110.916}, {"Северный 226", "Julius Thruway North", 2237.400, 2542.550, -89.084, 2498.210, 2663.170, 110.916}, {"Ист Бич", "East Beach", 2632.830, -1668.130, -89.084, 2747.740, -1393.420, 110.916}, {"Мост Фаллоу", "Fallow Bridge", 434.341, 366.572, 0.000, 603.035, 555.680, 200.000}, {"Уиллоуфилд", "Willowfield", 2089.000, -1989.900, -89.084, 2324.000, -1852.870, 110.916},
	 {"Чайнатаун", "Chinatown", -2274.170, 578.396, -7.6, -2078.670, 744.170, 200.000}, {"Эль Кастильо дель Дьябло", "El Castillo del Diablo", -208.570, 2337.180, 0.000, 8.430, 2487.180, 200.000}, {"Оушен Докс", "Ocean Docks", 2324.000, -2145.100, -89.084, 2703.580, -2059.230, 110.916}, {"Истер Бэй Кемикалс", "Easter Bay Chemicals", -1132.820, -768.027, 0.000, -956.476, -578.118, 200.000}, {"Визаж", "The Visage", 1817.390, 1703.230, -89.084, 2027.400, 1863.230, 110.916},
	 {"Оушен Флэст", "Ocean Flats", -2994.490, -430.276, -1.2, -2831.890, -222.589, 200.000}, {"Ричман", "Richman", 321.356, -860.619, -89.084, 687.802, -768.027, 110.916}, {"Грин Палмс", "Green Palms", 176.581, 1305.450, -3.0, 338.658, 1520.720, 200.000}, {"Ричман", "Richman", 321.356, -768.027, -89.084, 700.794, -674.885, 110.916}, {"Старфиш", "Starfish Casino", 2162.390, 1883.230, -89.084, 2437.390, 2012.180, 110.916}, {"Ист Бич", "East Beach", 2747.740, -1668.130, -89.084, 2959.350, -1498.620, 110.916},
	 {"Джефферсон", "Jefferson", 2056.860, -1372.040, -89.084, 2281.450, -1210.740, 110.916}, {"Даунтаун Лос Сантос", "Downtown Los Santos", 1463.900, -1290.870, -89.084, 1724.760, -1150.870, 110.916}, {"Даунтаун Лос Сантос", "Downtown Los Santos", 1463.900, -1430.870, -89.084, 1724.760, -1290.870, 110.916}, {"Мост Гарвер", "Garver Bridge", -1499.890, 696.442, -179.615, -1339.890, 925.353, 20.385}, {"Южный 226", "Julius Thruway South", 1457.390, 823.228, -89.084, 2377.390, 863.229, 110.916}, {"Ист Лос Сантос", "East Los Santos", 2421.030, -1628.530, -89.084, 2632.830, -1454.350, 110.916},
	 {"Грингласс", "Greenglass College", 964.391, 1044.690, -89.084, 1197.390, 1203.220, 110.916}, {"Лас Колинас", "Las Colinas", 2747.740, -1120.040, -89.084, 2959.350, -945.035, 110.916}, {"Малхолланд", "Mulholland", 737.573, -768.027, -89.084, 1142.290, -674.885, 110.916}, {"Оушен Докс", "Ocean Docks", 2201.820, -2730.880, -89.084, 2324.000, -2418.330, 110.916}, {"Ист Лос Сантос", "East Los Santos", 2462.130, -1454.350, -89.084, 2581.730, -1135.040, 110.916},
	 {"Гэнтон", "Ganton", 2222.560, -1722.330, -89.084, 2632.830, -1628.530, 110.916}, {"Ависпа", "Avispa Country Club", -2831.890, -430.276, -6.1, -2646.400, -222.589, 200.000}, {"Уиллоуфилд", "Willowfield", 1970.620, -2179.250, -89.084, 2089.000, -1852.870, 110.916}, {"Эсплэнейд Норт", "Esplanade North", -1982.320, 1274.260, -4.5, -1524.240, 1358.900, 200.000}, {"Хай Роллер", "The High Roller", 1817.390, 1283.230, -89.084, 2027.390, 1469.230, 110.916},
	 {"Оушен Докс", "Ocean Docks", 2201.820, -2418.330, -89.084, 2324.000, -2095.000, 110.916}, {"Ласт Дайм", "Last Dime Motel", 1823.080, 596.349, -89.084, 1997.220, 823.228, 110.916}, {"Бэйсайд Марина", "Bayside Marina", -2353.170, 2275.790, 0.000, -2153.170, 2475.790, 200.000}, {"Кингс", "King's", -2329.310, 458.411, -7.6, -1993.280, 578.396, 200.000}, {"Эль Корона", "El Corona", 1692.620, -2179.250, -89.084, 1812.620, -1842.270, 110.916},
	 {"Блэкфилд Чапел", "Blackfield Chapel", 1375.600, 596.349, -89.084, 1558.090, 823.228, 110.916}, {"Пинк Суон", "The Pink Swan", 1817.390, 1083.230, -89.084, 2027.390, 1283.230, 110.916}, {"Западный 226", "Julius Thruway West", 1197.390, 1163.390, -89.084, 1236.630, 2243.230, 110.916}, {"Лос Флорес", "Los Flores", 2581.730, -1393.420, -89.084, 2747.740, -1135.040, 110.916}, {"Визаж", "The Visage", 1817.390, 1863.230, -89.084, 2106.700, 2011.830, 110.916},
	 {"Прикл Пайн", "Prickle Pine", 1938.800, 2624.230, -89.084, 2121.400, 2861.550, 110.916}, {"Верона Бич", "Verona Beach", 851.449, -1804.210, -89.084, 1046.150, -1577.590, 110.916}, {"Робада Интерсекшон", "Robada Intersection", -1119.010, 1178.930, -89.084, -862.025, 1351.450, 110.916}, {"Линден Сайд", "Linden Side", 2749.900, 943.235, -89.084, 2923.390, 1198.990, 110.916}, {"Оушен Докс", "Ocean Docks", 2703.580, -2302.330, -89.084, 2959.350, -2126.900, 110.916},
	 {"Уиллоуфилд", "Willowfield", 2324.000, -2059.230, -89.084, 2541.700, -1852.870, 110.916}, {"Кингс", "King's", -2411.220, 265.243, -9.1, -1993.280, 373.539, 200.000}, {"Коммерс", "Commerce", 1323.900, -1842.270, -89.084, 1701.900, -1722.260, 110.916}, {"Малхолланд", "Mulholland", 1269.130, -768.027, -89.084, 1414.070, -452.425, 110.916}, {"Мэйрина", "Marina", 647.712, -1804.210, -89.084, 851.449, -1577.590, 110.916},
	 {"Бэттери Пойнт", "Battery Point", -2741.070, 1268.410, -4.5, -2533.040, 1490.470, 200.000}, {"Фор Драгонс", "The Four Dragons Casino", 1817.390, 863.232, -89.084, 2027.390, 1083.230, 110.916}, {"Блэкфилд", "Blackfield", 964.391, 1203.220, -89.084, 1197.390, 1403.220, 110.916}, {"Северный 226", "Julius Thruway North", 1534.560, 2433.230, -89.084, 1848.400, 2583.230, 110.916}, {"Ейллоу Белл", "Yellow Bell Gol Course", 1117.400, 2723.230, -89.084, 1457.460, 2863.230, 110.916},
	 {"Айдлвуд", "Idlewood", 1812.620, -1602.310, -89.084, 2124.660, -1449.670, 110.916}, {"Рэдсэндс Уэст", "Redsands West", 1297.470, 2142.860, -89.084, 1777.390, 2243.230, 110.916}, {"Доэрти", "Doherty", -2270.040, -324.114, -1.2, -1794.920, -222.589, 200.000}, {"Хилтоп", "Hilltop Farm", 967.383, -450.390, -3.0, 1176.780, -217.900, 200.000}, {"Лас Баранкас", "Las Barrancas", -926.130, 1398.730, -3.0, -719.234, 1634.690, 200.000}, {"Пирейтс ин мен Мэнтс", "Pirates in Men's Pants", 1817.390, 1469.230, -89.084, 2027.400, 1703.230, 110.916},
	 {"Сити Холл", "City Hall", -2867.850, 277.411, -9.1, -2593.440, 458.411, 200.000}, {"Ависпа", "Avispa Country Club", -2646.400, -355.493, 0.000, -2270.040, -222.589, 200.000}, {"Стрип", "The Strip", 2027.400, 863.229, -89.084, 2087.390, 1703.230, 110.916}, {"Хашбери", "Hashbury", -2593.440, -222.589, -1.0, -2411.220, 54.722, 200.000}, {"Международный аэропорт Лос Сантос", "Los Santos International", 1852.000, -2394.330, -89.084, 2089.000, -2179.250, 110.916},
	 {"Уайтвуд истейтс", "Whitewood Estates", 1098.310, 1726.220, -89.084, 1197.390, 2243.230, 110.916}, {"Шерманское водохранилище", "Sherman Reservoir", -789.737, 1659.680, -89.084, -599.505, 1929.410, 110.916}, {"Эль Корона", "El Corona", 1812.620, -2179.250, -89.084, 1970.620, -1852.870, 110.916}, {"Даунтаун", "Downtown", -1700.010, 744.267, -6.1, -1580.010, 1176.520, 200.000}, {"Фостер Вэлли", "Foster Valley", -2178.690, -1250.970, 0.000, -1794.920, -1115.580, 200.000},
	 {"Лас Паясдас", "Las Payasadas", -354.332, 2580.360, 2.0, -133.625, 2816.820, 200.000}, {"Валле Окультадо", "Valle Ocultado", -936.668, 2611.440, 2.0, -715.961, 2847.900, 200.000}, {"Пилсон Интерсекшон", "Blackfield Intersection", 1166.530, 795.010, -89.084, 1375.600, 1044.690, 110.916}, {"Гэнтон", "Ganton", 2222.560, -1852.870, -89.084, 2632.830, -1722.330, 110.916}, {"Аэропорт Истер-Бей", "Easter Bay Airport", -1213.910, -730.118, 0.000, -1132.820, -50.096, 200.000}, {"Рэдсэндс Ист", "Redsands East", 1817.390, 2011.830, -89.084, 2106.700, 2202.760, 110.916},
	 {"Эсплэнейд Ист", "Esplanade East", -1499.890, 578.396, -79.615, -1339.890, 1274.260, 20.385}, {"Калигула Палас", "Caligula's Palace", 2087.390, 1543.230, -89.084, 2437.390, 1703.230, 110.916}, {"Роял Казино", "Royal Casino", 2087.390, 1383.230, -89.084, 2437.390, 1543.230, 110.916}, {"Ричман", "Richman", 72.648, -1235.070, -89.084, 321.356, -1008.150, 110.916}, {"Старфиш", "Starfish Casino", 2437.390, 1783.230, -89.084, 2685.160, 2012.180, 110.916},
	 {"Малхолланд", "Mulholland", 1281.130, -452.425, -89.084, 1641.130, -290.913, 110.916}, {"Даунтаун", "Downtown", -1982.320, 744.170, -6.1, -1871.720, 1274.260, 200.000}, {"Ханкипанки Пойнт", "Hankypanky Point", 2576.920, 62.158, 0.000, 2759.250, 385.503, 200.000}, {"K.A.C.C. Милитари Фуэлс", "K.A.C.C. Military Fuels", 2498.210, 2626.550, -89.084, 2749.900, 2861.550, 110.916}, {"Гарри Голд Паркуэй", "Harry Gold Parkway", 1777.390, 863.232, -89.084, 1817.390, 2342.830, 110.916},
	 {"Тунель Бэйсайд", "Bayside Tunnel", -2290.190, 2548.290, -89.084, -1950.190, 2723.290, 110.916}, {"Оушен Докс", "Ocean Docks", 2324.000, -2302.330, -89.084, 2703.580, -2145.100, 110.916}, {"Ричман", "Richman", 321.356, -1044.070, -89.084, 647.557, -860.619, 110.916}, {"Рэндольф Индастриал Истейт", "Randolph Industrial Estate", 1558.090, 596.349, -89.084, 1823.080, 823.235, 110.916}, {"Ист Бич", "East Beach", 2632.830, -1852.870, -89.084, 2959.350, -1668.130, 110.916}, {"Флинт Уотер", "Flint Water", -314.426, -753.874, -89.084, -106.339, -463.073, 110.916},
	 {"Блуберри", "Blueberry", 19.607, -404.136, 3.8, 349.607, -220.137, 200.000}, {"Линден Стейшен", "Linden Station", 2749.900, 1198.990, -89.084, 2923.390, 1548.990, 110.916}, {"Глен Парк", "Glen Park", 1812.620, -1350.720, -89.084, 2056.860, -1100.820, 110.916}, {"Даунтаун", "Downtown", -1993.280, 265.243, -9.1, -1794.920, 578.396, 200.000}, {"Рэдсэндс Уэст", "Redsands West", 1377.390, 2243.230, -89.084, 1704.590, 2433.230, 110.916},
	 {"Ричман", "Richman", 321.356, -1235.070, -89.084, 647.522, -1044.070, 110.916}, {"Мост Гант", "Gant Bridge", -2741.450, 1659.680, -6.1, -2616.400, 2175.150, 200.000}, {"Лил Проуб", "Lil' Probe Inn", -90.218, 1286.850, -3.0, 153.859, 1554.120, 200.000}, {"Флинт Интерсекшон", "Flint Intersection", -187.700, -1596.760, -89.084, 17.063, -1276.600, 110.916}, {"Лас Колинас", "Las Colinas", 2281.450, -1135.040, -89.084, 2632.740, -945.035, 110.916}, {"Собелл Рейд Ярдс", "Sobell Rail Yards", 2749.900, 1548.990, -89.084, 2923.390, 1937.250, 110.916},
	 {"Эмералд Айл", "The Emerald Isle", 2011.940, 2202.760, -89.084, 2237.400, 2508.230, 110.916}, {"Эль Кастильо дель Дьябло", "El Castillo del Diablo", -208.570, 2123.010, -7.6, 114.033, 2337.180, 200.000}, {"Санта-Флора", "Santa Flora", -2741.070, 458.411, -7.6, -2533.040, 793.411, 200.000}, {"Плайя дель севиль", "Playa del Seville", 2703.580, -2126.900, -89.084, 2959.350, -1852.870, 110.916}, {"Маркет", "Market", 926.922, -1577.590, -89.084, 1370.850, -1416.250, 110.916}, {"Куинс", "Queens", -2593.440, 54.722, 0.000, -2411.220, 458.411, 200.000},
	 {"Плисон Интерсекшон", "Pilson Intersection", 1098.390, 2243.230, -89.084, 1377.390, 2507.230, 110.916}, {"Спинибед", "Spinybed", 2121.400, 2663.170, -89.084, 2498.210, 2861.550, 110.916}, {"Пилигрим", "Pilgrim", 2437.390, 1383.230, -89.084, 2624.400, 1783.230, 110.916}, {"Блэкфилд", "Blackfield", 964.391, 1403.220, -89.084, 1197.390, 1726.220, 110.916}, {"Большое ухо", "'The Big Ear'", -410.020, 1403.340, -3.0, -137.969, 1681.230, 200.000}, {"Диллимор", "Dillimore", 580.794, -674.885, -9.5, 861.085, -404.790, 200.000},
	 {"Эль Кебрадос", "El Quebrados", -1645.230, 2498.520, 0.000, -1372.140, 2777.850, 200.000}, {"Эсплэнейд Норт", "Esplanade North", -2533.040, 1358.900, -4.5, -1996.660, 1501.210, 200.000}, {"Международный Аэропорт Истер Бей", "Easter Bay Airport", -1499.890, -50.096, -1.0, -1242.980, 249.904, 200.000}, {"Фишер Лагун", "Fisher's Lagoon", 1916.990, -233.323, -100.000, 2131.720, 13.800, 200.000}, {"Малхолланд", "Mulholland", 1414.070, -768.027, -89.084, 1667.610, -452.425, 110.916},
	 {"Ист Бич", "East Beach", 2747.740, -1498.620, -89.084, 2959.350, -1120.040, 110.916}, {"Сан Андреас Саунд", "San Andreas Sound", 2450.390, 385.503, -100.000, 2759.250, 562.349, 200.000}, {"Шейди Крикс", "Shady Creeks", -2030.120, -2174.890, -6.1, -1820.640, -1771.660, 200.000}, {"Маркет", "Market", 1072.660, -1416.250, -89.084, 1370.850, -1130.850, 110.916}, {"Рокшор Уэст", "Rockshore West", 1997.220, 596.349, -89.084, 2377.390, 823.228, 110.916},
	 {"Прикл Пайн", "Prickle Pine", 1534.560, 2583.230, -89.084, 1848.400, 2863.230, 110.916}, {"Истер Бэйсин", "Easter Basin", -1794.920, -50.096, -1.04, -1499.890, 249.904, 200.000}, {"Лифи Холлоу", "Leafy Hollow", -1166.970, -1856.030, 0.000, -815.624, -1602.070, 200.000}, {"Лва Фрейт Депо", "LVA Freight Depot", 1457.390, 863.229, -89.084, 1777.400, 1143.210, 110.916}, {"Прикл Пайн", "Prickle Pine", 1117.400, 2507.230, -89.084, 1534.560, 2723.230, 110.916}, {"Блуберри", "Blueberry", 104.534, -220.137, 2.3, 349.607, 152.236, 200.000},
	 {"Эль Кастильо дель Дьябло", "El Castillo del Diablo", -464.515, 2217.680, 0.000, -208.570, 2580.360, 200.000}, {"Даунтаун", "Downtown", -2078.670, 578.396, -7.6, -1499.890, 744.267, 200.000}, {"Рокшор Ист", "Rockshore East", 2537.390, 676.549, -89.084, 2902.350, 943.235, 110.916}, {"Залив Сан Фиерро", "San Fierro Bay", -2616.400, 1501.210, -3.0, -1996.660, 1659.680, 200.000}, {"Парадизо", "Paradiso", -2741.070, 793.411, -6.1, -2533.040, 1268.410, 200.000}, {"Камелс Тоу", "The Camel's Toe", 2087.390, 1203.230, -89.084, 2640.400, 1383.230, 110.916},
	 {"Олд Вентурас Стрип", "Old Venturas Strip", 2162.390, 2012.180, -89.084, 2685.160, 2202.760, 110.916}, {"Джанипер Хилл", "Juniper Hill", -2533.040, 578.396, -7.6, -2274.170, 968.369, 200.000}, {"Джанипер Холлоу", "Juniper Hollow", -2533.040, 968.369, -6.1, -2274.170, 1358.900, 200.000}, {"Рока Эскаланте", "Roca Escalante", 2237.400, 2202.760, -89.084, 2536.430, 2542.550, 110.916}, {"Восточный 226", "Julius Thruway East", 2685.160, 1055.960, -89.084, 2749.900, 2626.550, 110.916},
	 {"Верона Бич", "Verona Beach", 647.712, -2173.290, -89.084, 930.221, -1804.210, 110.916}, {"Фостер Вэлли", "Foster Valley", -2178.690, -599.884, -1.2, -1794.920, -324.114, 200.000}, {"Арко Дель Оэсте", "Arco del Oeste", -901.129, 2221.860, 0.000, -592.090, 2571.970, 200.000}, {"Фоллен Три", "Fallen Tree", -792.254, -698.555, -5.3, -452.404, -380.043, 200.000}, {"Культ", "The Farm", -1209.670, -1317.100, 114.981, -908.161, -787.391, 251.981},
	 {"Плотина Шермана", "The Sherman Dam", -968.772, 1929.410, -3.0, -481.126, 2155.260, 200.000}, {"Эсплэнейд Норт", "Esplanade North", -1996.660, 1358.900, -4.5, -1524.240, 1592.510, 200.000}, {"Финаншиал", "Financial", -1871.720, 744.170, -6.1, -1701.300, 1176.420, 300.000}, {"Гарсия", "Garcia", -2411.220, -222.589, -1.14, -2173.040, 265.243, 200.000}, {"Монтгомери", "Montgomery", 1119.510, 119.526, -3.0, 1451.400, 493.323, 200.000}, {"Крик", "Creek", 2749.900, 1937.250, -89.084, 2921.620, 2669.790, 110.916},
	 {"Международный аэропорт Лос Сантос", "Los Santos International", 1249.620, -2394.330, -89.084, 1852.000, -2179.250, 110.916}, {"Санта Мария Бич", "Santa Maria Beach", 72.648, -2173.290, -89.084, 342.648, -1684.650, 110.916}, {"Малхолланд Интерсекшон", "Mulholland Intersection", 1463.900, -1150.870, -89.084, 1812.620, -768.027, 110.916}, {"Эйнджел Пайн", "Angel Pine", -2324.940, -2584.290, -6.1, -1964.220, -2212.110, 200.000}, {"Вёрдант Медоус", "Verdant Meadows", 37.032, 2337.180, -3.0, 435.988, 2677.900, 200.000}, {"Октан Спрингс", "Octane Springs", 338.658, 1228.510, 0.000, 664.308, 1655.050, 200.000},
	 {"Кам Э Лот", "Come-A-Lot", 2087.390, 943.235, -89.084, 2623.180, 1203.230, 110.916}, {"Рэдсэндс Уэст", "Redsands West", 1236.630, 1883.110, -89.084, 1777.390, 2142.860, 110.916}, {"Санта Мария Бич", "Santa Maria Beach", 342.648, -2173.290, -89.084, 647.712, -1684.650, 110.916}, {"Вердант Блаффс", "Verdant Bluffs", 1249.620, -2179.250, -89.084, 1692.620, -1842.270, 110.916}, {"Лас Вентурас Аэропорт", "Las Venturas Airport", 1236.630, 1203.280, -89.084, 1457.370, 1883.110, 110.916}, {"Флинт Рэндж", "Flint Range", -594.191, -1648.550, 0.000, -187.700, -1276.600, 200.000},
	 {"Вердант Блаффс", "Verdant Bluffs", 930.221, -2488.420, -89.084, 1249.620, -2006.780, 110.916}, {"Паломино Крик", "Palomino Creek", 2160.220, -149.004, 0.000, 2576.920, 228.322, 200.000}, {"Оушен Докс", "Ocean Docks", 2373.770, -2697.090, -89.084, 2809.220, -2330.460, 110.916}, {"Международный Аэропорт Истер Бей", "Easter Bay Airport", -1213.910, -50.096, -4.5, -947.980, 578.396, 200.000}, {"Уайтвуд истейтс", "Whitewood Estates", 883.308, 1726.220, -89.084, 1098.310, 2507.230, 110.916}, {"Кэлтон Хайтс", "Calton Heights", -2274.170, 744.170, -6.1, -1982.320, 1358.900, 200.000},
	 {"Истер Бэйсин", "Easter Basin", -1794.920, 249.904, -9.1, -1242.980, 578.396, 200.000}, {"Лос Сантос Inlet", "Los Santos Inlet", -321.744, -2224.430, -89.084, 44.615, -1724.430, 110.916}, {"Доэрти", "Doherty", -2173.040, -222.589, -1.0, -1794.920, 265.243, 200.000}, {"Гора Чилиад", "Mount Chiliad", -2178.690, -2189.910, -47.917, -2030.120, -1771.660, 576.083}, {"Форт Карсон", "Fort Carson", -376.233, 826.326, -3.0, 123.717, 1220.440, 200.000}, {"Фостер Вэлли", "Foster Valley", -2178.690, -1115.580, 0.000, -1794.920, -599.884, 200.000},
	 {"Оушен Флэст", "Ocean Flats", -2994.490, -222.589, -1.0, -2593.440, 277.411, 200.000}, {"Ферн Ридж", "Fern Ridge", 508.189, -139.259, 0.000, 1306.660, 119.526, 200.000}, {"Бэйсайд", "Bayside", -2741.070, 2175.150, 0.000, -2353.170, 2722.790, 200.000}, {"Лас Вентурас Аэропорт", "Las Venturas Airport", 1457.370, 1203.280, -89.084, 1777.390, 1883.110, 110.916}, {"Блуберри Эйкерс", "Blueberry Acres", -319.676, -220.137, 0.000, 104.534, 293.324, 200.000}, {"Пэлисейдс", "Palisades", -2994.490, 458.411, -6.1, -2741.070, 1339.610, 200.000},
	 {"Норт Рок", "North Rock", 2285.370, -768.027, 0.000, 2770.590, -269.740, 200.000}, {"Карьер Хантер", "Hunter Quarry", 337.244, 710.840, -115.239, 860.554, 1031.710, 203.761}, {"Международный аэропорт Лос Сантос", "Los Santos International", 1382.730, -2730.880, -89.084, 2201.820, -2394.330, 110.916}, {"Миссионер Хилл", "Missionary Hill", -2994.490, -811.276, 0.000, -2178.690, -430.276, 200.000}, {"Залив Сан Фиерро", "San Fierro Bay", -2616.400, 1659.680, -3.0, -1996.660, 2175.150, 200.000}, {"Запретная зона", "Restricted Area", -91.586, 1655.050, -50.000, 421.234, 2123.010, 250.000},
	 {"Гора Чилиад", "Mount Chiliad", -2997.470, -1115.580, -47.917, -2178.690, -971.913, 576.083}, {"Гора Чилиад","Mount Chiliad", -2178.690, -1771.660, -47.917, -1936.120, -1250.970, 576.083}, {"Международный Аэропорт Истер Бей", "Easter Bay Airport", -1794.920, -730.118, -3.0, -1213.910, -50.096, 200.000}, {"Паноптикум ", "The Panopticon", -947.980, -304.320, -1.1, -319.676, 327.071, 200.000}, {"Шейди Крикс", "Shady Creeks", -1820.640, -2643.680, -8.0, -1226.780, -1771.660, 200.000}, {"Бэк о Бейонд", "Back o Beyond", -1166.970, -2641.190, 0.000, -321.744, -1856.030, 200.000},
	 {"Гора Чилиад", "Mount Chiliad", -2994.490, -2189.910, -47.917, -2178.690, -1115.580, 576.083}, {"Тиерра Робада", "Tierra Robada", -1213.910, 596.349, -242.990, -480.539, 1659.680, 900.000}, {"Флинт Каунти", "Flint County", -1213.910, -2892.970, -242.990, 44.615, -768.027, 900.000}, {"Уэтстоун", "Whetstone", -2997.470, -2892.970, -242.990, -1213.910, -1115.580, 900.000}, {"Бон Каунти", "Bone County", -480.539, 596.349, -242.990, 869.461, 2993.870, 900.000}, {"Тиерра Робада", "Tierra Robada", -2997.470, 1659.680, -242.990, -480.539, 2993.870, 900.000}, {"Сан Фиерро", "San Fierro", -2997.470, -1115.580, -242.990, -1213.910, 1659.680, 900.000}, {"Лас Вентурас", "Las Venturas", 869.461, 596.349, -242.990, 2997.060, 2993.870, 900.000}, {"Рэд Каунти", "Red County", -1213.910, -768.027, -242.990, 2997.060, 596.349, 900.000}, {"Лос Сантос", "Los Santos", 44.615, -2892.970, -242.990, 2997.060, -768.027, 900.000}}
	return zone
end

local config = {}

function defalut_config()
	config = {
		["MAIN"] = {["heli_camera"] = {['z'] = 0.5}, ['cmd'] = 'BC', ["language"] = "RU",
				["zones"] = {['size'] = 0.0, ['dist'] = 1000},
				["light"] = {['multiplier'] = 4, ['auto'] = true, ['size'] = 5, ['intensity'] = 255},
				["vehicle"] = {[497] = 497}},
		["pos"] = {["info"] = {['x'] = 313, ['y'] = 310},
			["zoom"] = {['x'] = 67, ['y'] = 224},
			["compass_text"] = {['x'] = 320.5, ['y'] = 23},
			["heli"] = {['x'] = 46, ['y'] = 177},
			["camera"] = {['x'] = 87, ['y'] = 180},
			["arrow_compass"] = {['x'] = 87, ['y'] = 153}},
		['keybind'] = {['active_fixview'] = 'Right Button', ['hud'] = 'F9',
			['draw_noise'] = '1', ['nightvi'] = '2', ['infvi'] = '3',
			['sens_minus'] = '-', ['sens_plus'] = '=', ['zoom'] = 'Shift',
			['zones'] = 'Z', ['light'] = 'L', },
		['zones'] = {}
	}
	local zone = zone()
	for i = 1, #zone do
		local x, y, z = zone[i][3], zone[i][4], zone[i][5]
		local x1, y1, z1 = zone[i][6], zone[i][7], zone[i][8]
		local cx, cy, cz = (x+x1)/2, (y+y1)/2, (z+z1)/2
		config.zones[#config.zones+1] = {zone[i][1], zone[i][2], cx, cy, cz}
	end
    savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
end

if doesFileExist("moonloader/Helicopter-Camera/Helicopter-Camera.json") then
    local f = io.open("moonloader/Helicopter-Camera/Helicopter-Camera.json")
    config = decodeJson(f:read("*a"))
    f:close()
else
	defalut_config()
end

local blur = ffi.cast("void (*)(float)", 0x7030A0)

local active, angY = false, 0.0
local text_target = "NO TARGET"
local handle, name_model, id_model, sight_posX, sight_posY, sight_posZ, handle_fixview, who = -1, '', -1,  0, 0, 0, -1, 0
local light_active, zone_active, active_fixview = false, false, false
local test_fov = 70

function mod(a, b)
    return a - (math.floor(a/b)*b)
end

function DEC_HEX(IN)
    local B,K,OUT,I,D=16,"0123456789ABCDEF","",0
    while IN>0 do
        I=I+1
        IN,D=math.floor(IN/B), mod(IN,B)+1
        OUT=string.sub(K,D,D)..OUT
    end
    return tonumber(OUT, 16)
end

function onD3DPresent()
    if draw then
        callFunction(0x007037C0, 2, 2, 0x30 + DEC_HEX(test_fov), 1)
		-- blur(test_fov/100)
    end
end

function CarModel(x)
	local cars = {
	[400] = "Landstalker", [401] = "Bravura", [402] = "Buffalo", [403] = "Linerunner", [404] = "Perenniel", [405] = "Sentinel", [406] = "Dumper", [407] = "Firetruck", [408] = "Trashmaster", [409] = "Stretch", [410] = "Manana", [411] = "Infernus",
	[412] = "Voodoo", [413] = "Pony", [414] = "Mule", [415] = "Cheetah", [416] = "Ambulance", [417] = "Leviathan", [418] = "Moonbeam",
	[419] = "Esperanto", [420] = "Taxi", [421] = "Washington", [422] = "Bobcat", [423] = "Mr Whoopee", [424] = "BF Injection",
	[425] = "Hunter", [426] = "Premier", [427] = "Enforcer", [428] = "Securicar", [429] = "Banshee", [430] = "Predator", [431] = "Bus",
	[432] = "Rhino", [433] = "Barracks", [434] = "Hotknife", [435] = "Article Trailer", [436] = "Previon", [437] = "Coach", [438] = "Cabbie", [439] = "Stallion", [440] = "Rumpo", [441] = "RC Bandit", [442] = "Romero", [443] = "Packer", [444] = "Monster", [445] = "Admiral",
	[446] = "Squallo", [447] = "Seasparrow", [448] = "Pizzaboy", [449] = "Tram", [450] = "Article Trailer 2", [451] = "Turismo", [452] = "Speeder", [453] = "Reefer", [454] = "Tropic", [455] = "Flatbed", [456] = "Yankee", [457] = "Caddy", [458] = "Solair",
	[459] = "Topfun Van", [460] = "Skimmer", [461] = "PCJ-600", [462] = "Faggio", [463] = "Freeway", [464] = "RC Baron", [465] = "RC Raider", [466] = "Glendale", [467] = "Oceanic", [468] = "Sanchez", [469] = "Sparrow", [470] = "Patriot", [471] = "Quad", [472] = "Coastguard", [473] = "Dinghy", [474] = "Hermes", [475] = "Sabre", [476] = "Rustler", [477] = "ZR-350", [478] = "Walton", [479] = "Regina",
	[480] = "Comet", [481] = "BMX", [482] = "Burrito", [483] = "Camper", [484] = "Marquis", [485] = "Baggage", [486] = "Dozer", [487] = "Maverick", [488] = "SAN News Maverick", [489] = "Rancher", [490] = "FBI Rancher", [491] = "Virgo", [492] = "Greenwood",
	[493] = "Jetmax", [494] = "Hotring Racer C", [495] = "Sandking", [496] = "Blista Compact", [497] = "Police Maverick", [498] = "Boxville", [499] = "Benson", [500] = "Mesa", [501] = "RC Goblin", [502] = "Hotring Racer A", [503] = "Hotring Racer B",
	[504] = "Bloodring Banger", [505] = "Rancher", [506] = "Super GT", [507] = "Elegant", [508] = "Journey", [509] = "Bike", [510] = "Mountain Bike", [511] = "Beagle", [512] = "Cropduster", [513] = "Stuntplane", [514] = "Tanker", [515] = "Roadtrain",
	[516] = "Nebula", [517] = "Majestic", [518] = "Buccaneer", [519] = "Shamal", [520] = "Hydra", [521] = "FCR-900", [522] = "NRG-500", [523] = "HPV1000", [524] = "Cement Truck", [525] = "Towtruck", [526] = "Fortune", [527] = "Cadrona", [528] = "FBI Truck",
	[529] = "Willard", [530] = "Forklift", [531] = "Tractor", [532] = "Combine Harvester", [533] = "Feltzer", [534] = "Remington", [535] = "Slamvan", [536] = "Blade", [537] = "Freight (Train)", [538] = "Brownstreak (Train)", [539] = "Vortex", [540] = "Vincent",
	[541] = "Bullet", [542] = "Clover", [543] = "Sadler", [544] = "Firetruck LA", [545] = "Hustler", [546] = "Intruder", [547] = "Primo", [548] = "Cargobob", [549] = "Tampa", [550] = "Sunrise", [551] = "Merit", [552] = "Utility Van", [553] = "Nevada", [554] = "Yosemite",
	[555] = "Windsor", [556] = "Monster A", [557] = "Monster B", [558] = "Uranus", [559] = "Jester", [560] = "Sultan", [561] = "Stratum", [562] = "Elegy", [563] = "Raindance", [564] = "RC Tiger", [565] = "Flash",[566] = "Tahoma", [567] = "Savanna", [568] = "Bandito", [569] = "Freight Flat Trailer (Train)", [570] = "Streak Trailer (Train)",
	[571] = "Kart", [572] = "Mower", [573] = "Dune", [574] = "Sweeper", [575] = "Broadway", [576] = "Tornado", [577] = "AT400", [578] = "DFT-30", [579] = "Huntley", [580] = "Stafford", [581] = "BF-400", [582] = "Newsvan",
	[583] = "Tug", [584] = "Petrol Trailer", [585] = "Emperor", [586] = "Wayfarer", [587] = "Euros", [588] = "Hotdog", [589] = "Club", [590] = "Freight Box Trailer (Train)", [591] = "Article Trailer 3", [592] = "Andromada", [593] = "Dodo", [594] = "RC Cam",
	[595] = "Launch", [596] = "Police Car (LSPD)", [597] = "Police Car (SFPD)", [598] = "Police Car (LVPD)", [599] = "Police Ranger", [600] = "Picador", [601] = "S.W.A.T.", [602] = "Alpha", [603] = "Phoenix", [604] = "Glendale Shit", [605] = "Sadler Shit",
	[606] = "Baggage Trailer A", [607] = "Baggage Trailer B", [608] = "Tug Stairs Trailer", [609] = "Boxville", [610] = "Farm Trailer"
	}
	for i, v in pairs(cars) do
		if i == x then
			return v
		end
	end
	return 'None'
end

function NameModel(x)
	local testNameModel = {
		[0] = "cj", [1] = "truth", [2] = "maccer", [3] = "andre", [4] = "bbthin", [5] = "bb", [6] = "emmet", [7] = "male01", [8] = "janitor", [9] = "bfori",
		[10] = "bfost", [11] = "vbfycrp", [12] = "bfyri", [13] = "bfyst", [14] = "bmori", [15] = "bmost", [16] = "bmyap", [17] = "bmybu", [18] = "bmybe",
		[19] = "bmydj", [20] = "bmyri", [21] = "bmycr", [22] = "bmyst", [23] = "wmybmx", [24] = "wbdyg1", [25] = "wbdyg2", [26] = "wmybp", [27] = "wmycon",
		[28] = "bmydrug", [29] = "wmydrug", [30] = "hmydrug", [31] = "dwfolc", [32] = "dwmolc1", [33] = "dwmolc2", [34] = "dwmylc1", [35] = "hmogar", [36] = "wmygol1",
		[37] = "wmygol2", [38] = "hfori", [39] = "hfost", [40] = "hfyri", [41] = "hfyst", [42] = "jethro", [43] = "hmori", [44] = "hmost", [45] = "hmybe", [46] = "hmyri",
		[47] = "hmycr", [48] = "hmyst", [49] = "omokung", [50] = "wmymech", [51] = "bmymoun", [52] = "wmymoun", [53] = "ofori", [54] = "ofost", [55] = "ofyri", [56] = "ofyst",
		[57] = "omori", [58] = "omost", [59] = "omyri", [60] = "omyst", [61] = "wmyplt", [62] = "wmopj", [63] = "bfypro", [64] = "hfypro", [65] = "kendl", [66] = "bmypol1",
		[67] = "bmypol2", [68] = "wmoprea", [69] = "sbfyst", [70] = "wmosci", [71] = "wmysgrd", [72] = "swmyhp1", [73] = "swmyhp2", [74] = "-", [75] = "swfopro", [76] = "wfystew",
		[77] = "swmotr1", [78] = "wmotr1", [79] = "bmotr1", [80] = "vbmybox", [81] = "vwmybox", [82] = "vhmyelv", [83] = "vbmyelv", [84] = "vimyelv", [85] = "vwfypro",
		[86] = "ryder3", [87] = "vwfyst1", [88] = "wfori", [89] = "wfost", [90] = "wfyjg", [91] = "wfyri", [92] = "wfyro", [93] = "wfyst", [94] = "wmori", [95] = "wmost",
		[96] = "wmyjg", [97] = "wmylg", [98] = "wmyri", [99] = "wmyro", [100] = "wmycr", [101] = "wmyst", [102] = "ballas1", [103] = "ballas2", [104] = "ballas3", [105] = "fam1",
		[106] = "fam2", [107] = "fam3", [108] = "lsv1", [109] = "lsv2", [110] = "lsv3", [111] = "maffa", [112] = "maffb", [113] = "mafboss", [114] = "vla1", [115] = "vla2",
		[116] = "vla3", [117] = "triada", [118] = "triadb", [119] = "sindaco", [120] = "triboss", [121] = "dnb1", [122] = "dnb2", [123] = "dnb3", [124] = "vmaff1",
		[125] = "vmaff2", [126] = "vmaff3", [127] = "vmaff4", [128] = "dnmylc", [129] = "dnfolc1", [130] = "dnfolc2", [131] = "dnfylc", [132] = "dnmolc1", [133] = "dnmolc2",
		[134] = "sbmotr2", [135] = "swmotr2", [136] = "sbmytr3", [137] = "swmotr3", [138] = "wfybe", [139] = "bfybe", [140] = "hfybe", [141] = "sofybu", [142] = "sbmyst", [143] = "sbmycr",
		[144] = "bmycg", [145] = "wfycrk", [146] = "hmycm", [147] = "wmybu", [148] = "bfybu", [149] = "smokev", [150] = "wfybu", [151] = "dwfylc1", [152] = "wfypro", [153] = "wmyconb",
		[154] = "wmybe", [155] = "wmypizz", [156] = "bmobar", [157] = "cwfyhb", [158] = "cwmofr", [159] = "cwmohb1", [160] = "cwmohb2", [161] = "cwmyfr", [162] = "cwmyhb1",
		[163] = "bmyboun", [164] = "wmyboun", [165] = "wmomib", [166] = "bmymib", [167] = "wmybell", [168] = "bmochil", [169] = "sofyri", [170] = "somyst", [171] = "vwmybjd",
		[172] = "vwfycrp", [173] = "sfr1", [174] = "sfr2", [175] = "sfr3", [176] = "bmybar", [177] = "wmybar", [178] = "wfysex", [179] = "wmyammo", [180] = "bmytatt",
		[181] = "vwmycr", [182] = "vbmocd", [183] = "vbmycr", [184] = "vhmycr", [185] = "sbmyri", [186] = "somyri", [187] = "somybu", [188] = "swmyst", [189] = "wmyva",
		[190] = "copgrl3", [191] = "gungrl3", [192] = "mecgrl3", [193] = "nurgrl3", [194] = "crogrl3", [195] = "gangrl3", [196] = "cwfofr", [197] = "cwfohb",
		[198] = "cwfyfr1", [199] = "cwfyfr2", [200] = "cwmyhb2", [201] = "dwfylc2", [202] = "dwmylc2", [203] = "omykara", [204] = "wmykara", [205] = "wfyburg",
		[206] = "vwmycd", [207] = "vhfypro", [208] = "suzie", [209] = "omonood", [210] = "omoboat", [211] = "wfyclot", [212] = "vwmotr1", [213] = "vwmotr2",
		[214] = "vwfywai", [215] = "sbfori", [216] = "swfyri", [217] = "wmyclot", [218] = "sbfost", [219] = "sbfyri", [220] = "sbmocd", [221] = "sbmori",
		[222] = "sbmost", [223] = "shmycr", [224] = "sofori", [225] = "sofost", [226] = "sofyst", [227] = "somobu", [228] = "somori", [229] = "somost",
		[230] = "swmotr5", [231] = "swfori", [232] = "swfost", [233] = "swfyst", [234] = "swmocd", [235] = "swmori", [236] = "swmost", [237] = "shfypro",
		[238] = "sbfypro", [239] = "swmotr4", [240] = "swmyri", [241] = "smyst", [242] = "smyst2", [243] = "sfypro", [244] = "vbfyst2", [245] = "vbfypro",
		[246] = "vhfyst3", [247] = "bikera", [248] = "bikerb", [249] = "bmypimp", [250] = "swmycr", [251] = "wfylg", [252] = "wmyva2", [253] = "bmosec",
		[254] = "bikdrug", [255] = "wmych", [256] = "sbfystr", [257] = "swfystr", [258] = "heck1", [259] = "heck2", [260] = "bmycon", [261] = "wmycd1",
		[262] = "bmocd", [263] = "vwfywa2", [264] = "wmoice", [265] = "tenpen", [266] = "pulaski", [267] = "hern", [268] = "dwayne", [269] = "smoke", [270] = "sweet",
		[271] = "ryder", [272] = "forelli", [273] = "tbone", [274] = "laemt1", [275] = "lvemt1", [276] = "sfemt1", [277] = "lafd1", [278] = "lvfd1", [279] = "sffd1",
		[280] = "lapd1", [281] = "sfpd1", [282] = "lvpd1", [283] = "csher", [284] = "lapdm1", [285] = "swat", [286] = "fbi", [287] = "army", [288] = "dsher", [289] = "zero",
		[290] = "rose", [291] = "paul", [292] = "cesar", [293] = "ogloc", [294] = "wuzimu", [295] = "torino", [296] = "jizzy", [297] = "maddogg", [298] = "cat",
		[299] = "claude", [300] = "lapdna", [301] = "sfpdna", [302] = "lvpdna", [303] = "lapdpc", [304] = "lapdpd", [305] = "lvpdpc", [306] = "wfyclpd", [307] = "vbfycpd",
		[308] = "wfyclem", [309] = "wfycllv", [310] = "csherna", [311] = "dsherna";
	}
	for i = 0, #testNameModel do
		if x == i then
			return testNameModel[i]
		end
	end
    return 'None'
end

function setText(key, string, posX, posY, sX, sY, font, align, ARGB, sO, sARGB, wrapx, centresize, background, proportional, drawbeforefade)
	local a, sA = bit.band(bit.rshift(ARGB, 24), 0xFF), bit.band(bit.rshift(sARGB, 24), 0xFF)
	local r, sR = bit.band(bit.rshift(ARGB, 16), 0xFF), bit.band(bit.rshift(sARGB, 16), 0xFF)
	local g, sG = bit.band(bit.rshift(ARGB, 8), 0xFF), bit.band(bit.rshift(sARGB, 8), 0xFF)
	local b, sB = bit.band(ARGB, 0xFF), bit.band(sARGB, 0xFF)
	useRenderCommands(true)
	setTextScale(sX, sY) -- float
	setTextColour(r, g, b, a) -- int
	setTextEdge(sO, sR, sG, sB, sA) -- int
	setTextDropshadow(sO, sR, sG, sB, sA)
	setTextFont(font) -- int
	if align == 3 then
		setTextRightJustify(true) -- bool
	elseif align == 2 then
		setTextCentre(true) -- bool
	elseif align == 1 then
		setTextJustify(true) -- bool
	elseif align == 0 then
		setTextJustify(false)
		setTextCentre(false)
		setTextCentre(false)
	end
	setTextWrapx(wrapx) -- float
	setTextCentreSize(centresize) -- float
	setTextBackground(background) -- bool
	setTextProportional(proportional) -- bool
	setTextDrawBeforeFade(drawbeforefade) -- bool
	setGxtEntry(key, string)
	displayText(posX, posY, key)
end

function loadTextures(txd, names)
  if not loadTextureDictionary(txd) then return nil end

  local textures, count = {}, 0
  for _, name in ipairs(names) do
    local id = loadSprite(name)
    table.insert(textures, {weapon = name, sprite = id})
    count = count + 1
  end
  return textures
end

function drawIcon(int, id, x, y, sizex, sizey, color, angle)
	local a = bit.band(bit.rshift(color, 24), 0xFF)
	local r = bit.band(bit.rshift(color, 16), 0xFF)
	local g = bit.band(bit.rshift(color, 8), 0xFF)
	local b = bit.band(color, 0xFF)
	setSpritesDrawBeforeFade(true)
	if int == 1 then
		drawSprite(id, x, y, sizex, sizey, r, g, b, a)
	elseif int == 2 then
		drawSpriteWithRotation(id, x, y, sizex, sizey, angle, r, g, b, a)
	end
end

function loadTexturesTXD()
  if textureList == nil then
    textureList = loadTextures(getWorkingDirectory()..'\\Helicopter-Camera\\HeliCam', {'konus', 'crosshair_red', 'warning', 'compass_stat', 'arrow_compass', 'viewfinder', 'arrow', 'camera1', 'heli', 'zoom'})
    if textureList == nil then return false end
  end
  return true
end

if limgui then
	window = new.bool(false)
	cmdbuffer =  new.char[128](config.MAIN.cmd)
	sizeX, sizeY = getScreenResolution()


	local qweeqe = config.MAIN.language == "RU" and 1 or 2
	table.sort(config.zones, function(a,b) return a[qweeqe] < b[qweeqe] end)
	local texts_zones = {}
	for i = 1, #config.zones do
		texts_zones[i] = {}
		texts_zones[i][1] = new.char[256](config.zones[i][1])
		texts_zones[i][2] = new.char[256](config.zones[i][2])
		texts_zones[i][3] = new.float(config.zones[i][3])
		texts_zones[i][4] = new.float(config.zones[i][4])
		texts_zones[i][5] = new.float(config.zones[i][5])
	end

	local pos_new = {['z'] = new.float(config.MAIN.heli_camera.z)}
	for k, v in pairs(config.pos) do
		pos_new[k] = {new.float(config.pos[k].x), new.float(config.pos[k].y)}
	end

	local zones_size, zones_dist = new.float(config.MAIN.zones.size), new.float(config.MAIN.zones.dist)

	local checkbox_light_auto = new.bool(config.MAIN.light.auto)
	local light_size, light_intensity, light_multiplier = new.float(config.MAIN.light.size), new.float(config.MAIN.light.intensity), new.float(config.MAIN.light.multiplier)

	local add_veh = new.char[256]()

	function Standart()
		imgui.SwitchContext()
		local style = imgui.GetStyle()
		local colors = style.Colors
		local clr = imgui.Col
		local ImVec4 = imgui.ImVec4
		local ImVec2 = imgui.ImVec2

		style.WindowPadding = ImVec2(15, 15)
		style.WindowRounding = 4.7
		style.WindowBorderSize = 1.7
		style.WindowMinSize = ImVec2(1.5, 1.5)
		style.WindowTitleAlign = ImVec2(0.5, 0.5)
		style.ChildRounding = 4.7
		style.ChildBorderSize = 1
		style.PopupRounding = 4.7
		style.PopupBorderSize  = 1
		style.FramePadding = ImVec2(5, 5)
		style.FrameRounding = 4.7
		style.FrameBorderSize  = 1.0
		style.ItemSpacing = ImVec2(2, 7)
		style.ItemInnerSpacing = ImVec2(8, 6)
		style.ScrollbarSize = 9.0
		style.ScrollbarRounding = 4.7
		style.GrabMinSize = 15.0
		style.GrabRounding = 4.7
		style.IndentSpacing = 25.0
		style.ButtonTextAlign = ImVec2(0.5, 0.5)
		style.SelectableTextAlign = ImVec2(0.5, 0.5)
		style.TouchExtraPadding = ImVec2(0.00, 0.00)
		style.TabBorderSize = 1
		style.TabRounding = 4

		colors[clr.Text] = ImVec4(1.00, 1.00, 1.00, 1.00)
		colors[clr.TextDisabled] = ImVec4(0.50, 0.50, 0.50, 1.00)
		colors[clr.WindowBg] = ImVec4(0.15, 0.15, 0.15, 1.00)
		colors[clr.ChildBg] = ImVec4(0.00, 0.00, 0.00, 0.00)
		colors[clr.PopupBg] = ImVec4(0.19, 0.19, 0.19, 0.92)
		colors[clr.Border] = ImVec4(0.19, 0.19, 0.19, 1.0)
		colors[clr.BorderShadow] = ImVec4(0.00, 0.00, 0.00, 1.0)
		colors[clr.FrameBg] = ImVec4(0.05, 0.05, 0.05, 0.54)
		colors[clr.FrameBgHovered] = ImVec4(0.19, 0.19, 0.19, 0.54)
		colors[clr.FrameBgActive] = ImVec4(0.20, 0.22, 0.23, 1.00)
		colors[clr.TitleBg] = ImVec4(0.00, 0.00, 0.00, 1.00)
		colors[clr.TitleBgActive] = ImVec4(0.06, 0.06, 0.06, 1.00)
		colors[clr.TitleBgCollapsed] = ImVec4(0.00, 0.00, 0.00, 1.00)
		colors[clr.MenuBarBg] = ImVec4(0.14, 0.14, 0.14, 1.00)
		colors[clr.ScrollbarBg] = ImVec4(0.05, 0.05, 0.05, 0.54)
		colors[clr.ScrollbarGrab] = ImVec4(0.34, 0.34, 0.34, 0.54)
		colors[clr.ScrollbarGrabHovered] = ImVec4(0.40, 0.40, 0.40, 0.54)
		colors[clr.ScrollbarGrabActive] = ImVec4(0.56, 0.56, 0.56, 0.54)
		colors[clr.CheckMark] = ImVec4(0.33, 0.67, 0.86, 1.00)
		colors[clr.SliderGrab] = ImVec4(0.34, 0.34, 0.34, 0.54)
		colors[clr.SliderGrabActive] = ImVec4(0.56, 0.56, 0.56, 0.54)
		colors[clr.Button] = ImVec4(0.05, 0.05, 0.05, 0.54)
		colors[clr.ButtonHovered] = ImVec4(0.19, 0.19, 0.19, 0.54)
		colors[clr.ButtonActive] = ImVec4(0.20, 0.22, 0.23, 1.00)
		colors[clr.Header] = ImVec4(0.05, 0.05, 0.05, 0.52)
		colors[clr.HeaderHovered] = ImVec4(0.19, 0.19, 0.19, 0.36)
		colors[clr.HeaderActive] = ImVec4(0.20, 0.22, 0.23, 0.33)
		colors[clr.Separator] = ImVec4(0.28, 0.28, 0.28, 0.29)
		colors[clr.SeparatorHovered] = ImVec4(0.44, 0.44, 0.44, 0.29)
		colors[clr.SeparatorActive] = ImVec4(0.40, 0.44, 0.47, 1.00)
		colors[clr.ResizeGrip] = ImVec4(0.28, 0.28, 0.28, 0.29)
		colors[clr.ResizeGripHovered] = ImVec4(0.44, 0.44, 0.44, 0.29)
		colors[clr.ResizeGripActive] = ImVec4(0.40, 0.44, 0.47, 1.00)
		colors[clr.Tab]  = ImVec4(0.00, 0.00, 0.00, 0.52)
		colors[clr.TabHovered] = ImVec4(0.14, 0.14, 0.14, 1.00)
		colors[clr.TabActive] = ImVec4(0.20, 0.20, 0.20, 0.36)
		colors[clr.TabUnfocused] = ImVec4(0.00, 0.00, 0.00, 0.52)
		colors[clr.TabUnfocusedActive] = ImVec4(0.14, 0.14, 0.14, 1.00)
		colors[clr.PlotLines] = ImVec4(1.00, 0.00, 0.00, 1.00)
		colors[clr.PlotLinesHovered] = ImVec4(1.00, 0.00, 0.00, 1.00)
		colors[clr.PlotHistogram] = ImVec4(1.00, 0.00, 0.00, 1.00)
		colors[clr.PlotHistogramHovered] = ImVec4(1.00, 0.00, 0.00, 1.00)
		colors[clr.TextSelectedBg] = ImVec4(0.20, 0.22, 0.23, 1.00)
		colors[clr.DragDropTarget] = ImVec4(0.33, 0.67, 0.86, 1.00)
		colors[clr.NavHighlight] = ImVec4(1.00, 0.00, 0.00, 1.00)
		colors[clr.NavWindowingHighlight]  = ImVec4(1.00, 0.00, 0.00, 0.70)
		colors[clr.NavWindowingDimBg] = ImVec4(1.00, 0.00, 0.00, 0.20)
		colors[clr.ModalWindowDimBg] = ImVec4(1.00, 0.00, 0.00, 0.0)
	end

	imgui.OnInitialize(function()
		Standart()
		imgui.GetIO().IniFilename = nil
	end)

	newFrame = imgui.OnFrame(
		function() return window[0] end,
		function(helicam)
			helicam.HideCursor = false
			imgui.SetNextWindowPos(imgui.ImVec2(sizeX / 1.2, sizeY / 2), imgui.Cond.FirstUseEver, imgui.ImVec2(0.5, 0.5))
			imgui.SetNextWindowSize(imgui.ImVec2(374, 574), imgui.Cond.Always)
			imgui.Begin(script.name.." by dmitriyewich", window, imgui.WindowFlags.NoCollapse + imgui.WindowFlags.NoResize)

			if imgui.IsItemHovered() then
				if go_CMDserver == nil then go_CMDserver = os.clock() + (0.55 and 0.55 or 0.0) end
				local alpha = (os.clock() - go_CMDserver) * 3.5
				if os.clock() >= go_CMDserver then
					imgui.PushStyleVarFloat(imgui.StyleVar.Alpha, (alpha <= 1.0 and alpha or 1.0))
						imgui.BeginTooltip()
						imgui.PushTextWrapPos(450)
							imgui.TextUnformatted('©dmitriyewich aka Валерий Дмитриевич.\nРаспространение допускается только с указанием автора\nПКМ - Открыть группу в вк')
						if not imgui.IsItemVisible() and imgui.GetStyle().Alpha == 1.0 then go_CMDserver = nil end
						imgui.PopTextWrapPos()
						imgui.EndTooltip()
					imgui.PopStyleVar()
				end
			end
			if not imgui.IsItemHovered() then go_CMDserver = nil end
			if not imgui.IsAnyItemHovered() and imgui.GetStyle().Alpha == 1.0 then go_hint = nil end
			if imgui.IsItemClicked(1) then
				os.execute('explorer "https://vk.com/dmitriyewichmods"') -- открытие браузера с этой ссылкой
			end

			imgui.SetCursorPosY(imgui.GetCursorPosY() - 10)
			if imgui.CollapsingHeader('Районы') then
				if config.MAIN.language == "RU" then imgui.Text("RU") else imgui.TextDisabled("RU") end
				if imgui.IsItemClicked(0) then
					config.MAIN.language = "RU"
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
				imgui.SameLine(nil, 0)
				imgui.Text("|")
				imgui.SameLine(nil, 0)
				if config.MAIN.language == "EN" then imgui.Text("EN") else imgui.TextDisabled("EN") end
				if imgui.IsItemClicked(0) then
					config.MAIN.language = "EN"
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
				imgui.SameLine(nil, 0)
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 112) / 2)
				if imgui.Button('Добавить район##addbutton', imgui.ImVec2(112, 0)) then
					local positionX, positionY, positionZ = getCharCoordinates(PLAYER_PED)
					local positionX, positionY, positionZ = math.round(positionX, 2), math.round(positionY, 2), math.round(positionZ, 2)
					local i1, i2, i3 = #config.zones+1, #texts_zones+1, #zones_text+1
					rawset(config.zones, i1, {'Ваше местоположение'..i1, 'Your location'..i1, positionX, positionY, positionZ})

					rawset(texts_zones, i2, {new.char[256]('Ваше местоположение'..i2), new.char[256]('Your location'..i2), new.float(positionX), new.float(positionY), new.float(positionZ)})

					rawset(zones_text, i3, getFreeGxtKey())
					res_ru, res_en, res_x, res_y, res_z = 'Ваше местоположение'..i1, 'Your location'..i1, positionX, positionY, positionZ
					imgui.OpenPopup("##Popup"..i1)

				end

				imgui.Separator()
				for i = 1, #config.zones do
					if config.zones[i] == nil then goto continue end
					if config.zones[i][3] ~= nil and isPointOnScreen(config.zones[i][3], config.zones[i][4], config.zones[i][5], 0.5) then text_rar = ' !+! ' else text_rar = "" end

					if imgui.Button(text_rar..(config.MAIN.language == "RU" and config.zones[i][1] or config.zones[i][2]) .. '##mainbutton'..i, imgui.ImVec2(112, 0)) then
						imgui.OpenPopup("##Popup"..i)
						key_res, res_ru, res_en, res_x, res_y, res_z = i, config.zones[i][1], config.zones[i][2], config.zones[i][3], config.zones[i][4], config.zones[i][5]
					end

					if imgui.IsItemHovered() then
						if config.zones[i][3] ~= nil and isPointOnScreen(config.zones[i][3], config.zones[i][4], config.zones[i][5], 0.5) then
							local result, xx, yy, zz, _, _ = convert3DCoordsToScreenEx(config.zones[i][3], config.zones[i][4], config.zones[i][5], true, true)
							if result then
								setText(zones_text[i], RusToGame(u8:decode(config.zones[i][config.MAIN.language == "RU" and 1 or 2])), convertW(xx).x, convertW(yy).y, config.MAIN.zones.size+0.2, (config.MAIN.zones.size*4)+1.1, 2, 2, '0xFFFF0000', 0.5, 0x15FF0000, 500, 500, false, true, true)
							end
						end
					end
					if i % 3 ~= 0 and i ~= #config.zones then
						imgui.SameLine()
					end

					if imgui.BeginPopupModal("##Popup"..i, _, imgui.WindowFlags.NoCollapse + imgui.WindowFlags.NoScrollbar) then
						imgui.SetWindowSizeVec2(imgui.ImVec2(374, 274))

						if config.zones[i][3] ~= nil and isPointOnScreen(config.zones[i][3], config.zones[i][4], config.zones[i][5], 0.5) then
							local result, xx, yy, zz, _, _ = convert3DCoordsToScreenEx(config.zones[i][3], config.zones[i][4], config.zones[i][5], true, true)
							if result then
								setText(zones_text[i], RusToGame(u8:decode(config.zones[i][config.MAIN.language == "RU" and 1 or 2])), convertW(xx).x, convertW(yy).y, config.MAIN.zones.size+0.2, (config.MAIN.zones.size*4)+1.1, 2, 2, '0xFFFF0000', 0.5, 0x15FF0000, 500, 500, false, true, true)
							end
						end
						imgui.PushItemWidth(174)
						if imgui.InputText("Название на русском##InputTextRU"..i, texts_zones[i][1], sizeof(texts_zones[i][1])) then
							rawset(config.zones[i], 1, str(texts_zones[i][1]))
						end
						if imgui.InputText("Название на английском##InputTextEN"..i, texts_zones[i][2], sizeof(texts_zones[i][2])) then
							config.zones[i][2] = str(texts_zones[i][2])
						end
						imgui.PopItemWidth()

						imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize('CTRL+ЛКМ - ручной ввод координат').x) / 2)
						imgui.Text("CTRL+ЛКМ - ручной ввод координат")
						imgui.PushItemWidth(347)
						if imgui.SliderFloat("X  ##SliderFloat"..i, texts_zones[i][3], -3000.0, 3000.0) then
							config.zones[i][3] = texts_zones[i][3][0]
						end
						if imgui.SliderFloat("Y  ##SliderFloat"..i, texts_zones[i][4], -3000.0, 3000.0) then
							config.zones[i][4] = texts_zones[i][4][0]
						end
						if imgui.SliderFloat("Z##SliderFloat"..i, texts_zones[i][5], -100.0, 250.0) then
							config.zones[i][5] = texts_zones[i][5][0]
						end
						imgui.PopItemWidth()


						imgui.SetCursorPosX((imgui.GetWindowWidth() - 325) / 2)
						if imgui.Button('Сброс##Сброс'..i, imgui.ImVec2(75, 25)) then
							config.zones[i][1], config.zones[i][2], config.zones[i][3], config.zones[i][4], config.zones[i][5] = res_ru, res_en, res_x, res_y, res_z
							texts_zones[i][3][0], texts_zones[i][4][0], texts_zones[i][5][0] = res_x, res_y, res_z
							imgui.StrCopy(texts_zones[i][1], res_ru)
							imgui.StrCopy(texts_zones[i][2], res_en)

						end
						imgui.SameLine()
						if imgui.Button('Сохранить##Сохранить'..i, imgui.ImVec2(75, 25)) then
							savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
							imgui.CloseCurrentPopup()
						end
						imgui.SameLine()
						if imgui.Button('Закрыть##Закрыть'..i, imgui.ImVec2(75, 25)) then
							config.zones[i][1], config.zones[i][2], config.zones[i][3], config.zones[i][4], config.zones[i][5] = res_ru, res_en, res_x, res_y, res_z
							texts_zones[i][3][0], texts_zones[i][4][0], texts_zones[i][5][0] = res_x, res_y, res_z
							imgui.StrCopy(texts_zones[i][1], res_ru)
							imgui.StrCopy(texts_zones[i][2], res_en)
							imgui.CloseCurrentPopup()
						end
						imgui.SameLine()
						if imgui.Button('Удалить район##Удалить район'..i, imgui.ImVec2(100, 25)) then
							imgui.CloseCurrentPopup()
							table.remove(config.zones, key_res)
							table.remove(texts_zones, key_res)
							table.remove(zones_text, key_res)
							savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")

						end
						imgui.EndPopup()
					end
					::continue::
				end
				imgui.NewLine()
				imgui.Separator()
			end

			imgui.Separator()

			if imgui.CollapsingHeader('Настройки худа скрипта') then
				imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize('Координаты указаны игровые, не Вашего экрана').x) / 2)
				imgui.Text("Координаты указаны игровые, не Вашего экрана.")
				imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize('CTRL+ЛКМ - ручной ввод координат').x) / 2)
				imgui.Text("CTRL+ЛКМ - ручной ввод координат")

				imgui.Separator()
				imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize('Положение камеры').x) / 2)
				imgui.Text("Положение камеры")
				imgui.PushItemWidth(274)
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 276) / 2)
				if imgui.SliderFloat("Z  ##SliderFloatZ", pos_new.z, -4.0, 4.0) then
					config.MAIN.heli_camera.z = pos_new.z[0]
				end
				imgui.PopItemWidth()
				imgui.Separator()

				for k, v in pairs(config.pos) do
					imgui.Separator()
					local tbl_text_pos = {['compass_text'] = 'Позиция компаса', ['camera'] = 'Позиция икоки камеры', ['heli'] = 'Позиция икоки вертолета', ['arrow_compass'] = 'Позиция икоки направления на север', ['zoom'] = 'Позиция икоки зума', ['info'] = 'Позиция информации'}
					imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize(tbl_text_pos[''..k]).x) / 2)
					imgui.Text(tbl_text_pos[''..k])
					imgui.PushItemWidth(147)
					if imgui.SliderFloat("X  ##SliderFloat"..k, pos_new[k][1], 0.0, 640.0) then
						config.pos[k].x = pos_new[k][1][0]
					end
					imgui.SameLine()
					if imgui.SliderFloat("Y  ##SliderFloat"..k, pos_new[k][2], 0.0, 448.0) then
						config.pos[k].y = pos_new[k][2][0]
					end
					imgui.PopItemWidth()
					imgui.Separator()
				end
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 77) / 2)
				if imgui.Button('Сохранить##HUD2', imgui.ImVec2(75, 25)) then
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
			end
			imgui.Separator()


			if imgui.CollapsingHeader('Назначение клавиш') then
				imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize('Изменение чит-кода').x) / 2)
				imgui.Text("Изменение чит-кода")
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 210) / 2)
				imgui.PushItemWidth(210)
				if imgui.InputTextWithHint('##cmd', 'Введите чит-код', cmdbuffer, sizeof(cmdbuffer), imgui.InputTextFlags.AutoSelectAll) then
					config.MAIN.cmd = str(cmdbuffer)
				end
				imgui.PopItemWidth()
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 130) / 2)
				if imgui.Button('Сохранить чит-код', imgui.ImVec2(130, 0)) then
					config.MAIN.cmd = str(cmdbuffer)
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end

				tbl_button = {{'hud', '	Скрытие худа', 'F9'},
					{'sens_plus', '	Ув. чувствительности камеры', '='},
					{'sens_minus', '	Ум. чувствительности камеры', '-'},
					{'zoom', '	Ускорение зума', 'Shift'},
					{'infvi', '	Вкл/выкл тепловизора', '3'},
					{'active_fixview', '	Фиксация камеры', 'Right Button'},
					{'draw_noise', '	Вкл/выкл шума на экране', '1'},
					{'nightvi', '	Вкл/выкл прибор ночного видения', '2'},
					{'zones', '	Вкл/выкл отображение районов', 'Z'},
					{'light', '	Вкл/выкл пародию на луч света', 'L'},
				}
				table.sort(tbl_button, function(a,b) return a[2] > b[2] end)
				for i = 1, #tbl_button do
					imgui.HotKey(tbl_button[i][1]..'Скрытие худа##1', config.keybind, ''..tbl_button[i][1], ''..tbl_button[i][3], 90, 0)
					imgui.SameLine(nil, 0)
					imgui.SetCursorPosY(imgui.GetCursorPosY() - 1)
					imgui.Text(tbl_button[i][2])
					imgui.SetCursorPosY(imgui.GetCursorPosY() + 3)
				end

			end

			imgui.Separator()

			if imgui.CollapsingHeader('Прочее') then
				imgui.PushItemWidth(150)
				if imgui.SliderFloat("Размер шрифта районов##zones_size", zones_size, -0.2, 0.2) then
					config.MAIN.zones.size = zones_size[0]
				end
				if imgui.SliderFloat("Дистанция прорисовки районов##light_size", zones_dist, 0, 3600) then
					config.MAIN.zones.dist = zones_dist[0]
				end
				if imgui.Checkbox("Размер фонарика подбирается сам##light_sizeauto", checkbox_light_auto) then
					config.MAIN.light.auto = not config.MAIN.light.auto
				end
				if checkbox_light_auto[0] then
					if imgui.SliderFloat("Множитель для авторазмера##light_multiplier", light_multiplier, 0.5, 8) then
						config.MAIN.light.multiplier = light_multiplier[0]
					end
				else
					if imgui.SliderFloat("Размер фонарика##light_size", light_size, 0, 47) then
						config.MAIN.light.size = light_size[0]
					end
				end
				if imgui.SliderFloat("Интенсивность фонарика##light_intensity", light_intensity, 0, 255) then
					config.MAIN.light.intensity = light_intensity[0]
				end
				imgui.PopItemWidth()

				imgui.Separator()

				if imgui.TreeNodeStr('Список доступного камере транспорта') then
					imgui.PushItemWidth(74)
					imgui.InputText("Введите ID model  ##InputTextAddveh", add_veh, sizeof(add_veh)-1, imgui.InputTextFlags.CharsDecimal + imgui.InputTextFlags.AutoSelectAll)
					imgui.SameLine()
					if imgui.Button('Добавить##Addvehbutton', imgui.ImVec2(0, 0)) then
						config.MAIN.vehicle[tonumber(str(add_veh))] = tonumber(str(add_veh))
					end
					imgui.PopItemWidth()

					for k, v in pairs(config.MAIN.vehicle) do
						imgui.Text(string.format("%s(%s)", v, CarModel(v)))
						if imgui.IsItemClicked(1) then
							config.MAIN.vehicle[k] = nil
						end
					end
					imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize('ПКМ - удалить').x) / 2)
						imgui.Text("ПКМ - удалить")
					imgui.TreePop()
				end

				imgui.Separator()

				imgui.SetCursorPosX((imgui.GetWindowWidth() - 176) / 2)
				if imgui.Button('Сохранить##otherbutton4', imgui.ImVec2(174, 0)) then
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
			end

			imgui.Separator()

		imgui.End()
	end)

	local tHotKeyData = {edit = nil, save = {}, lasted = os.clock()}

	function getDownKeys()
		local curkeys, bool = '', false
		for k, v in pairs(vkeys) do
			if isKeyDown(v) then
				if string.len(tostring(curkeys)) == 0 then
					curkeys = v
					return curkeys,true
				end
				bool = false
			end
		end
		return curkeys, bool
	end

	function imgui.GetKeysName(keys)
		if type(keys) ~= 'table' then
			return false
		else
			local tKeysName = {}
			for k = 1, #keys do tKeysName[k] = vkeys.id_to_name(tonumber(keys[k]))end
			return tKeysName
		end
	end

	function imgui.HotKey(name, path, pointer, defaultKey, height, width) -- by DonHomka
		local width, height, cancel = height or 0, width or 90, isKeyDown(0x08)
		local tKeys, saveKeys = string.split(getDownKeys(), ' '),select(2,getDownKeys())
		local name, keys, bool = tostring(name), path[pointer] or defaultKey, false
		local sKeys = keys
		for i=0,2 do
			if imgui.IsMouseClicked(i) then
				tKeys = {i==2 and 4 or i+1}
				saveKeys = true
			end
		end

		if tHotKeyData.edit ~= nil and tostring(tHotKeyData.edit) == name then
			if not cancel then
				if not saveKeys then
					if #tKeys == 0 then
						sKeys = (math.ceil(imgui.GetTime()) % 2 == 0) and '______' or ' '
					end
				else
					path[pointer] = table.concat(imgui.GetKeysName(tKeys), ' + ')
					tHotKeyData.edit, tHotKeyData.lasted = nil, os.clock()
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
			else
				path[pointer], tHotKeyData.edit, tHotKeyData.lasted = defaultKey, nil, os.clock()
				savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
			end
		end

		imgui.PushStyleColor(imgui.Col.Button, imgui.GetStyle().Colors[imgui.Col.FrameBg])
		imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.GetStyle().Colors[imgui.Col.FrameBgHovered])
		imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.GetStyle().Colors[imgui.Col.FrameBgActive])
		if imgui.Button((sKeys ~= '' and sKeys or u8'Свободно') .. '## '..name, imgui.ImVec2(width, height)) then
			tHotKeyData.edit = name
		end
		imgui.PopStyleColor(3)
		return bool
	end

end

function AddHeliSearchLight(origin, target, targetRadius, power, coronaIndex, unknownFlag, drawShadow)
	if active and sx >= 0 and sy >= 0 and sx < sw and sy < sh then
	local px, py, pz = getActiveCameraPointAt()
	local posX1, posY1, posZ1 = convertScreenCoordsToWorld3D(sw/2, sh/2, 700.0)
	local result, colpoint = processLineOfSight(px, py, pz-1, posX1, posY1, posZ1, true, false, false, true, false, false, false)
	if result and colpoint.entity ~= 0 then
		local normal = colpoint.normal
		local pos = Vector3D(colpoint.pos[1], colpoint.pos[2], colpoint.pos[3]) - (Vector3D(normal[1], normal[2], normal[3]) * 0.1)
		local zOffset = 300
		if normal[3] >= 0.5 then zOffset = 1 end
		local result, colpoint2 = processLineOfSight(pos.x, pos.y, pos.z + zOffset, pos.x, pos.y, pos.z - 0.3,
		true, false, false, true, false, false, false)
		if result then
			pos = Vector3D(colpoint2.pos[1], colpoint2.pos[2], colpoint2.pos[3] + 1)
			target = ffi.new("float[3]", pos.x, pos.y, pos.z+1)
			end
		end
	end
	AddHeliSearchLight(origin, target, targetRadius, power, coronaIndex, unknownFlag, drawShadow)
end

function main()

	repeat wait(0) until memory.read(0xC8D4C0, 4, false) == 9
	if not isSampfuncsLoaded() or not isSampLoaded() then return end
	repeat wait(0) until isSampAvailable()
	repeat wait(0) until fixed_camera_to_skin()

	if not loadTexturesTXD() then return end

	standard_fov = getCameraFov()
	
	sw, sh = getScreenResolution()
	sx, sy = memory.getfloat(0xB6EC14) * sw, memory.getfloat(0xB6EC10) * sh

	AddHeliSearchLight = jmp_hook.new("void(__cdecl *)(const float*, const float*, float targetRadius, float power, unsigned int coronaIndex, unsigned char unknownFlag, unsigned char drawShadow)", AddHeliSearchLight, 0x6C45B0)

	sampRegisterChatCommand('helicam', function()
		if limgui then
		window[0] = not window[0]
		else
			printString("Library ~y~\'mimgui\' ~r~not found.~n~~w~Download: ~y~ https://github.com/THE-FYP/mimgui.~n~~r~Copy link in~y~ moonloader.log.", 5000)
			print('Download: https://github.com/THE-FYP/mimgui ')
		end
	end)

	lua_thread.create(compass)
	lua_thread.create(camhack)
	lua_thread.create(car)
	lua_thread.create(zones_thread)
	lua_thread.create(light_thread)
	lua_thread.create(draw_info)

	compassText = {[-180] = "S", [-135] = "SW", [-90] = "W", [-45] = "NW", [0] = "N", [45] = "NE", [90] = "E", [135] = "SE", [180] = "S",}
	test, test2, test_text3, zones_text = {}, {}, {}, {}
	for i = 0, 360 do
		test[i] = getFreeGxtKey()
		test2[i] = getFreeGxtKey()
		test_text3[i] = getFreeGxtKey()
	end
	for i = 0, #config.zones do
		zones_text[i] = getFreeGxtKey()
	end


	wait(-1)
    -- while true do wait(0)

    -- end
end

function light_thread()
	while true do wait(0)
		if active then
			if isKeyJustPressed(isKeys(config.keybind.light)) then
				light_active = not light_active
			end
			if light_active and sx >= 0 and sy >= 0 and sx < sw and sy < sh then
			local px, py, pz = getActiveCameraPointAt()
			local posX1, posY1, posZ1 = convertScreenCoordsToWorld3D(sw/2, sh/2, 700.0)
			local result, colpoint = processLineOfSight(px, py, pz-1, posX1, posY1, posZ1, true, false, false, true, false, false, false)
			if result and colpoint.entity ~= 0 then
				local normal = colpoint.normal
				local pos = Vector3D(colpoint.pos[1], colpoint.pos[2], colpoint.pos[3]) - (Vector3D(normal[1], normal[2], normal[3]) * 0.1)
				local zOffset = 300
				if normal[3] >= 0.5 then zOffset = 1 end
				local result, colpoint2 = processLineOfSight(pos.x, pos.y, pos.z + zOffset, pos.x, pos.y, pos.z - 0.3,
				true, false, false, true, false, false, false)
				if result then
					pos = Vector3D(colpoint2.pos[1], colpoint2.pos[2], colpoint2.pos[3] + 1)

					local GroundZ = getGroundZFor3dCoord(pos.x, pos.y, pos.z)
					drawShadow(3, pos.x, pos.y, pos.z, 0.0, config.MAIN.light.auto and ((pz - GroundZ) / config.MAIN.light.multiplier) or config.MAIN.light.size , 15, config.MAIN.light.intensity, config.MAIN.light.intensity, config.MAIN.light.intensity)

					drawLightWithRange(pos.x, pos.y, pos.z+5, 255, 255, 255, 15)
					end
				end
			end
		end
	end
end

function zones_thread()
	while true do wait(0)
		if active then
			if isKeyJustPressed(isKeys(config.keybind.zones)) then
				zone_active = not zone_active
			end
			if zone_active then
			local tbl_zone = config.zones
				for i = 1, #tbl_zone do
					local x, y, z = tbl_zone[i][3], tbl_zone[i][4], tbl_zone[i][5]
					local posX, posY, posZ = getCarModelCornersIn2d(getCarModel(storeCarCharIsInNoSave(PLAYER_PED)), storeCarCharIsInNoSave(PLAYER_PED))
					local dist = getDistanceBetweenCoords3d(posX, posY, posZ, x, y, z)
					if dist <= config.MAIN.zones.dist and isPointOnScreen(x, y, z, 0.5) then
						local result, xx, yy, zz, _, _ = convert3DCoordsToScreenEx(x, y, z, true, true)
						local GroundZ = getGroundZFor3dCoord(x, y, z)
						if result then
							setText(zones_text[i], RusToGame(u8:decode(tbl_zone[i][config.MAIN.language == "RU" and 1 or 2])), convertW(xx).x, convertW(yy).y, config.MAIN.zones.size+0.2, (config.MAIN.zones.size*4)+1.1, 2, 2, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)
						end
					end
				end
			end
		end
	end
end

function licenseplates(p)
    return memory.tostring(memory.getint32(memory.getint32(memory.getint32(memory.getint32(getModuleHandle('samp.dll') + 0x21A0F8, false) + 0x3CD, false) + 0x1C, false) + 0x1134 + p * 4, false) + 0x93, 32, false)
end

function car()
	while true do wait(0)
		if active then
			sight_posX, sight_posY, sight_posZ = 0, 0, 0
			local pos, cam = {convertScreenCoordsToWorld3D(sw / 2, sh / 2, 700.0)}, {getActiveCameraCoordinates()}
			local res, c = processLineOfSight(cam[1], cam[2], cam[3], pos[1], pos[2], pos[3], false, true, true, false, false, false, false, false)

			if res and (c.entityType == 2 or c.entityType == 3) and storeCarCharIsInNoSave(PLAYER_PED) ~= getVehiclePointerHandle(c.entity) and getCharPointerHandle(c.entity) ~= PLAYER_PED then

					sight_posX, sight_posY, sight_posZ = c.pos[1], c.pos[2], c.pos[3]

					handle = c.entityType == 2 and getVehiclePointerHandle(c.entity) or getCharPointerHandle(c.entity)

					id_model = c.entityType == 2 and getCarModel(handle) or getCharModel(handle)

					name_model = c.entityType == 2 and CarModel(id_model) or NameModel(id_model)

					local draw = c.entityType == 2 and {getCarCoordinates(handle)} or {getCharCoordinates(handle)}

					local wposX, wposY = convert3DCoordsToScreen(draw[1], draw[2], draw[3])
					drawIcon(1, 2, convertW(wposX).x, convertW(wposY).y, 42, 50, 0xDAFAFAFA)

					id_nickname = c.entityType == 2 and select(2, sampGetPlayerIdByCharHandle(getDriverOfCar(handle))) or select(2, sampGetPlayerIdByCharHandle(handle))

					id_car = c.entityType == 2 and select(2, sampGetVehicleIdByCarHandle(handle)) or -1

					text_target = c.entityType == 2 and "ON VEHICLE" or "ON HUMAN"
			else
				text_target = "NO TARGET"
			end

			if isKeyJustPressed(isKeys(config.keybind.active_fixview)) then
				if (text_target == "ON VEHICLE" or text_target == "ON HUMAN") then
					handle_fixview, who = handle, text_target == "ON VEHICLE" and 2 or 3
					active_fixview = not active_fixview
					if not active_fixview then handle_fixview = -1 end
				else
					active_fixview = false
				end
			end

			if active_fixview  then
				local positionX, positionY, positionZ
				if who == 2 then
					positionX, positionY, positionZ = getCarCoordinates(handle_fixview)
				elseif who == 3 then
					positionX, positionY, positionZ = getCharCoordinates(handle_fixview)
				end
				local cam = {getActiveCameraCoordinates()}
				local dist = getDistanceBetweenCoords3d(cam[1], cam[2], cam[3], positionX, positionY, positionZ)
				if dist <= (who == 2 and 400 or 200) then
					pointCameraAtPoint(positionX, positionY, positionZ, 2)
				else
					warring_thread = lua_thread.create(function()
						local timer = os.clock()
						active_fixview = false
						while true do wait(0)
							drawIcon(1, 3, 328, 338, 35, 40, 0xDAFAFAFA)
							setText(test_text3[1], RusToGame(u8:decode('~r~CONNECTION LOST')), 343, 334, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)
							if os.clock() - timer > 2 or active_fixview then break end
						end
					end)
				end
			end
		end
	end
end

function getHexFromU32(hex)
    return string.sub(hex:reverse(), 1, 6)
end

function getPlayerColorHex(id)
    return ''..getHexFromU32(bit.tohex(sampGetPlayerColor(id)))
end

function angleZ_test(x, y, z)
    local cx, cy, cz = getActiveCameraCoordinates()

    local vect = {fX = cx - x, fY = cy - y, fZ = cz - z}
    local ax = math.atan2(vect.fY, -vect.fX) - 3.14159265 / 2
    local az = math.atan2(math.sqrt(vect.fX * vect.fX + vect.fY * vect.fY), vect.fZ)
	local camDirection = math.round((az * 180 / math.pi), 0)
	return (90 - camDirection)
end

function camhack()
    local flymode, fov, radarHud, keyPressed, speed = 0, 70, 1, 0, 15.0
    while true do wait(0)
		test_fov = -(fov + 80 - (200))
		local pStSet = sampGetServerSettingsPtr()
		if isCharInAnyCar(PLAYER_PED) and config.MAIN.vehicle[tostring(getCarModel(storeCarCharIsInNoSave(PLAYER_PED)))] ~= nil then
			local posX, posY, posZ = getCarModelCornersIn2d(getCarModel(storeCarCharIsInNoSave(PLAYER_PED)), storeCarCharIsInNoSave(PLAYER_PED))
			posZ = posZ + config.MAIN.heli_camera.z
			if not active and testCheat(config.MAIN.cmd) then
				active, draw = true, true
				if flymode == 0 and active then
					angZ = getCharHeading(playerPed)
					angZ = angZ * -1.0
					setFixedCameraPosition(posX, posY, posZ, 0.0, 0.0, 0.0)
					angY = 0.0
					flymode = 1
				end
			end

			if flymode == 1 then
				setFixedCameraPosition(posX, posY, posZ, 0.0, 0.0, 0.0)
				if isKeyJustPressed(isKeys(config.keybind.draw_noise)) then
					draw = not draw
					infvi, nightvi = false, false
					setNightVision(false)
					setInfraredVision(false)
				end
				if isKeyJustPressed(isKeys(config.keybind.nightvi)) then
					nightvi = not nightvi
					infvi  = false
					setNightVision(nightvi)
					setInfraredVision(false)
				end
				if isKeyJustPressed(isKeys(config.keybind.infvi)) then
					infvi = not infvi
					nightvi = false
					setNightVision(false)
					setInfraredVision(infvi)
				end

				if isKeyDown(isKeys(config.keybind.sens_plus)) then
					speed = speed + 5.0
					printStringNow(speed, 1000)
				end

				if isKeyDown(isKeys(config.keybind.sens_minus)) then
					speed = speed - 5.0
					if speed <= 10.00 then
						speed = 10.00
					end
					printStringNow(speed, 1000)
				end

				local delta = getMousewheelDelta()
				if not isKeyDown(isKeys(config.keybind.zoom)) then delta = delta else delta = delta * 5 end
				fov = fov - delta

				if fov >= 100 then fov = 100 end
				if fov <= 20 then fov = 20 end
				cameraSetLerpFov( fov,  fov, 700, true)

				drawIcon(1, 10, config.pos.zoom.x, config.pos.zoom.y, 76, 10, 0xFAFAFAFA)
				drawIcon(1, 7, config.pos.zoom.x+49-((81 * fov) / 100), config.pos.zoom.y, 8, 8, 0xFAFAFAFA)
				setText(test_text3[2], RusToGame(u8:decode('Zoom: '..fov..' Sensitivity: '..speed)), config.pos.zoom.x, config.pos.zoom.y+3, 0.13, 1.0, 2, 2, '0xFFFFFFFF', 0.5, 0x15000000, 255, 500, false, true, true)


				if active_fixview then
					local cx, cy, _ = getActiveCameraCoordinates()
					local px, py, _ = getActiveCameraPointAt()
					angZ = math.atan2( (px-cx), (py-cy) ) * 180 / math.pi
					if angZ <= 0 then angZ = 360 + angZ elseif angZ >= 0 then angZ = angZ end

					local positionX, positionY, positionZ
					if who == 2 then
						positionX, positionY, positionZ = getCarCoordinates(handle_fixview)
					elseif who == 3 then
						positionX, positionY, positionZ = getCharCoordinates(handle_fixview)
					end
					angY = angleZ_test(positionX, positionY, positionZ)
					angY = -angY
				end

				if not active_fixview then
					offMouX, offMouY = getPcMouseMovement()

					offMouX = offMouX / speed
					offMouY = offMouY / speed
					angZ = angZ + offMouX
					angY = angY + offMouY

					if angZ > 360.0 then angZ = angZ - 360.0 end
					if angZ < 0.0 then angZ = angZ + 360.0 end

					if angY >= 4.7 then angY = 4.7 end
					if angY < -89.0 then angY = -89.0 end

					radZ = math.rad(angZ)
					radY = math.rad(angY)
					sinZ = math.sin(radZ)
					cosZ = math.cos(radZ)
					sinY = math.sin(radY)
					cosY = math.cos(radY)
					sinZ = sinZ * cosY
					cosZ = cosZ * cosY
					sinZ = sinZ * 1.0
					cosZ = cosZ * 1.0
					sinY = sinY * 1.0
					poiX = posX
					poiY = posY
					poiZ = posZ
					poiX = poiX + sinZ
					poiY = poiY + cosZ
					poiZ = poiZ + sinY
					pointCameraAtPoint(poiX, poiY, poiZ, 2)
				end

				if keyPressed == 0 and isKeyDown(isKeys(config.keybind.hud)) then
					keyPressed = 1
					if radarHud == 0 then
						displayHud(true)
						radarHud = 1
						memory.setint8(pStSet + 47, 1) -- показать хп
						memory.setint8(pStSet + 56, 1) -- показать ник
						sampSetChatDisplayMode(2)
						memory.setuint8(sampGetBase() + 0x71480, 0x74, true)
						memory.setint32(0xBA676C, 0) -- включить радар(для лаунчера аризоны)
					else
						displayHud(false)
						radarHud = 0
						memory.setint8(pStSet + 47, 0) -- скрыть хп
						memory.setint8(pStSet + 56, 0)	-- скрыть ник
						memory.setuint8(sampGetBase() + 0x71480, 0xEB, true)
						memory.setint32(0xBA676C, 2) -- выключить радар(для лаунчера аризоны)
						sampSetChatDisplayMode(0)
					end
				end

				if wasKeyReleased(isKeys(config.keybind.hud)) and keyPressed == 1 then
					keyPressed = 0
				end

				if active and testCheat(config.MAIN.cmd) then
					active, draw, active_fixview, light_active, zone_active = false, false, false, false, false
					if flymode == 1 and not active then
						angPlZ = angZ * -1.0
						restoreCameraJumpcut()
						setCameraBehindPlayer()
						setNightVision(false)
						setInfraredVision(false)
						cameraSetLerpFov( standard_fov,  standard_fov, 700, true)
						flymode = 0
						fov = standard_fov
					end
				end
			end
		else
			if active then
				active, draw, active_fixview, light_active, zone_active = false, false, false, false, false
				if flymode == 1 and not active then
					angPlZ = angZ * -1.0
					restoreCameraJumpcut()
					setCameraBehindPlayer()
					fov = standard_fov
					flymode = 0
					setNightVision(false)
					setInfraredVision(false)
					cameraSetLerpFov( standard_fov,  standard_fov, 700, true)
				end
			end
		end

    end
end

function compass()
	while true do wait(0)
		if active and isCharInAnyCar(PLAYER_PED) and config.MAIN.vehicle[tostring(getCarModel(storeCarCharIsInNoSave(PLAYER_PED)))] ~= nil then
			local cx, cy, _ = getActiveCameraCoordinates()
			local px, py, _ = getActiveCameraPointAt()
			local camDirection = math.round((math.atan2( (px-cx), (py-cy) ) * 180 / math.pi), 0)
			if camDirection <= 0 then camDirection = 360 + camDirection elseif camDirection >= 0 then camDirection = camDirection end

			local finalText, yaw = "", -camDirection

			for i = yaw - 120, yaw + 120 do
				local y = i if i >= 180 then y = -360 + i elseif i <= -180 then y = 360 + i end
				finalText = (compassText[y] and compassText[y]..finalText) or " "..finalText
			end
			local number = 0
			for k, v in ipairs(split(finalText, ' '), true) do
				if v ~= '' then
					number = number + 1
					test3 = number == 3 and 1 or number == 2 and 0.7 or number == 1 and 0.5 or number == 4 and 0.7 or number == 5 and 0.5 or number == 6 and 0.4
					setText(test[k], RusToGame(u8:decode(v)), config.pos.compass_text.x+((-119+k)/1.5), config.pos.compass_text.y, 0.25, 1.4, 2, 2, '0x'..dectohex(test3)..'FFFFFF', 0, 0xFF608453, 255, 500, false, true, true)
					setText(test2[k], "I", config.pos.compass_text.x+((-119+k)/1.5), config.pos.compass_text.y-10, 0.25, 1.4, 2, 2, '0x'..dectohex(test3)..'FFFFFF', 0, 0xFF608453, 255, 500, false, true, true)

					if number >= 2 then
						setText(test2[k], "I", config.pos.compass_text.x-43+((-119+k)/1.5), config.pos.compass_text.y-8, 0.15, 1.0, 2, 2, '0x'..dectohex(test3)..'FFFFFF', 0, 0xFF608453, 255, 500, false, true, true)
					end
					if number <= 4 then
						setText(test2[k], "I", config.pos.compass_text.x+45+((-119+k)/1.5), config.pos.compass_text.y-8, 0.15, 1.0, 2, 2, '0x'..dectohex(test3)..'FFFFFF', 0, 0xFF608453, 255, 500, false, true, true)
					end
				end
			end
			drawIcon(1, 7, config.pos.compass_text.x-0.6, config.pos.compass_text.y-5, 9, 9, 0xFaFFFFFF)

			local ang_vheli = getCarHeading(storeCarCharIsInNoSave(PLAYER_PED))
			drawIcon(1, 9, config.pos.heli.x, config.pos.heli.y, 40, 50, 0xFaFFFFFF)
			drawIcon(2, 1, config.pos.heli.x-0.7, config.pos.heli.y-19, -44, -58, 0xFaFFFFFF, ang_vheli + camDirection)
			setText(test_text3[3], math.round(ang_vheli, 0)..'~n~'..(tostring(-camDirection)):gsub('-', ''), config.pos.heli.x+0.5, config.pos.heli.y-22, 0.14, 0.95, 2, 2, '0xFFFFFFFF', 0, 0xFF608453, 255, 500, false, true, true)

			drawIcon(1, 8, config.pos.camera.x, config.pos.camera.y, 25, 32, 0xFaFFFFFF)
			drawIcon(2, 1, config.pos.camera.x, config.pos.camera.y+3, -26, -53, 0xFaFFFFFF, 90-angY)
			setText(test_text3[4], (tostring(math.round(angY, 0))):gsub('-', ''), config.pos.camera.x+7, config.pos.camera.y-5, 0.14, 0.95, 2, 2, '0xFFFFFFFF', 0, 0xFF608453, 255, 500, false, true, true)

			drawIcon(2, 5, config.pos.arrow_compass.x, config.pos.arrow_compass.y-2, -34, -38, 0xFAFAFAFA, ang_vheli)
			drawIcon(1, 4, config.pos.arrow_compass.x, config.pos.arrow_compass.y, 11, 14, 0xDAFFFFFF)

			drawIcon(1, 6, 320, 224, 133, 120, 0xFaFFFFFF)
		end
	end
end

function draw_info()
	while true do wait(0)
		if active then
			local posX, posY, posZ = getCarModelCornersIn2d(getCarModel(storeCarCharIsInNoSave(PLAYER_PED)), storeCarCharIsInNoSave(PLAYER_PED))

			local text1 = string.format("AIRCRAFT CAMERA %s", text_target, (active_fixview ~= nil and text_target ~= "NO TARGET" and (active_fixview and ' ~g~LOCK' or ' ~r~LOCK')  or ""))
			setText(test_text3[5], RusToGame(u8:decode(text1)), config.pos.info.x+7, config.pos.info.y-10, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

			local text2 = string.format("MY POS X: %s Y: %s Z: %s", math.round(posX, 1), math.round(posY, 1), math.round(posZ, 1))
			setText(test_text3[6], RusToGame(u8:decode(text2)), config.pos.info.x, config.pos.info.y, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

			if text_target ~= "NO TARGET" then
				local text3 = string.format("SIGHT POS X: %s Y: %s Z: %s", math.round(sight_posX, 1), math.round(sight_posY, 1), math.round(sight_posZ, 1))
				setText(test_text3[7], RusToGame(u8:decode(text3)), config.pos.info.x, config.pos.info.y+10, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

				local text4 = string.format("APPEARANCE: %s (%s)", name_model, id_model)
				setText(test_text3[8], RusToGame(u8:decode(text4)), config.pos.info.x, config.pos.info.y+20, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

				local dist = getDistanceBetweenCoords3d(posX, posY, posZ, sight_posX, sight_posY, sight_posZ)
				local text5 = string.format("DISTANCE: %sm", math.round(dist, 1))
				setText(test_text3[9], RusToGame(u8:decode(text5)), config.pos.info.x, config.pos.info.y+30, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

				local text6 = (text_target == "ON VEHICLE" and "LICENSE PLATE:" or "DATEBASE:")
				setText(test_text3[10], RusToGame(u8:decode(text6)), config.pos.info.x, config.pos.info.y+40, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

				local text7 = text_target == "ON VEHICLE" and string.format("%s", licenseplates(id_car)) or string.format("%s(%s)", id_nickname ~= -1 and sampGetPlayerNickname(id_nickname) or 'NO DATA', id_nickname)
				setText(test_text3[11], RusToGame(u8:decode(text7)), config.pos.info.x+(text_target == "ON VEHICLE" and 65 or 47), config.pos.info.y+40, 0.2, 1.1, 2, 1, id_nickname ~= -1 and '0xFF'..getPlayerColorHex(id_nickname) or '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

				if text_target == "ON VEHICLE" then
					local text8 = string.format("%s(%s)", id_nickname ~= -1 and sampGetPlayerNickname(id_nickname) or 'NO DATA', id_nickname)
					setText(test_text3[12], RusToGame(u8:decode("DRIVER:")), config.pos.info.x, config.pos.info.y+50, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)
					setText(test_text3[13], RusToGame(u8:decode(text8)), config.pos.info.x+33, config.pos.info.y+50, 0.2, 1.1, 2, 1, id_nickname ~= -1 and '0xFF'..getPlayerColorHex(id_nickname) or '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)
				end
			end
		end
	end
end

function isKeys(key)
	return vkeys.name_to_id(key, true)
end

function getCarModelCornersIn2d(id, handle)-- https://www.blast.hk/threads/13380/post-925354 by chapo
    local x1, y1, z1, x2, y2, z2 = getModelDimensions(id)
    local t = {
        [1] = {getOffsetFromCarInWorldCoords(handle, x1         , y1 * -1.1, z1)},
        [2] = {getOffsetFromCarInWorldCoords(handle, x1 * -1.0  , y1       , z1)},
    }
	local xc = (t[1][1] + t[2][1])/ 2
	local yc = (t[1][2] + t[2][2])/ 2
	local zc = (t[1][3] + t[2][3])/ 2
    return xc, yc, zc
end

function RusToGame(text)
    local convtbl = {[35]=35, [230]=155,[231]=159,[247]=164,[234]=107,[250]=144,[251]=168,[254]=171,[253]=170,[255]=172,[224]=97,[240]=112,[241]=99,[226]=162,[228]=154,[225]=151,[227]=153,[248]=165,[243]=121,[184]=101,[235]=158,[238]=111,[245]=120,[233]=157,[242]=166,[239]=163,[244]=152 ,[237]=174,[229]=101,[246]=160,[236]=175,[232]=156,[249]=161,[252]=169,[215]=141,[202]=75,[204]=77,[220]=146,[221]=147,[222]=148,[192]=65,[193]=128,[209]=67,[194]=139,[195]=130,[197]=69,[206]=79,[213]=88,[168]=69,[223]=149,[207]=140,[203]=135,[201]=133,[199]=136,[196]=131,[208]=80,[200]=133,[198]=132,[210]=143,[211]=89,[216]=142,[212]=129,[214]=137,[205]=72,[217]=138,[218]=167,[219]=145}
    local result = {}
    for i = 1, #text do
        local c = text:byte(i)
        result[i] = string.char(convtbl[c] or c)
    end
    return table.concat(result)
end

function fixed_camera_to_skin() -- проверка на приклепление камеры к скину
	return (memory.read(getModuleHandle('gta_sa.exe') + 0x76F053, 1, false) >= 1 and true or false)
end

function dectohex(input)
	return (string.format("%x", input * 255))
end

function split(str, delim, plain) -- https://www.blast.hk/threads/13380/post-231049
    local tokens, pos, plain = {}, 1, not (plain == false)
    repeat
        local npos, epos = string.find(str, delim, pos, plain)
        table.insert(tokens, string.sub(str, pos, npos and npos - 1))
        pos = epos and epos + 1
    until not pos
    return tokens
end

function string.split(inputstr, sep)
	if sep == nil then sep = '%s' end
	local t={} ; i=1
	for str in string.gmatch(inputstr, '([^'..sep..']+)') do
		t[i] = str
		i = i + 1
	end
	return t
end

function math.round(num, idp)
	local mult = 10^(idp or 0)
	return math.floor(num * mult + 0.5) / mult
end

function convertG(xy)
	local gposX, gposY = convertGameScreenCoordsToWindowScreenCoords(xy, xy)
	local cGtbl = {['x'] = gposX, ['y'] = gposY}
	return cGtbl
end

function convertW(xy)
	local wposX, wposY = convertWindowScreenCoordsToGameScreenCoords(xy, xy)
	local cWtbl = {['x'] = wposX, ['y'] = wposY}
	return cWtbl
end

function onScriptTerminate(LuaScript, quitGame)
    if LuaScript == thisScript() and not quitGame then
		if active then
			active = false
			setNightVision(false)
			setInfraredVision(false)
			restoreCameraJumpcut()
			setCameraBehindPlayer()
			cameraSetLerpFov( standard_fov,  standard_fov, 700, true)
		end
    end
end

-- Licensed under the MIT License
-- Copyright (c) 2022, dmitriyewich <https://github.com/dmitriyewich/Helicopter-Camera>
