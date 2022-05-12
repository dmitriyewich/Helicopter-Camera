script_name('Helicopter-Camera')
script_author('dmitriyewich, https://vk.com/dmitriyewichmods')
script_dependencies("mimgui", "sampfuncs")
script_properties('work-in-pause')
script_version("1.5.6")
script_version_number(156)

local script = thisScript()
require"lib.moonloader"
local ffi = require 'ffi'
local vkeys = require 'vkeys'
local Vector3D = require "vector3d"
local lmemory, memory = pcall(require, 'memory')
local limgui, imgui = pcall(require, 'mimgui') -- https://github.com/THE-FYP/mimgui
local new, str, sizeof = imgui.new, ffi.string, ffi.sizeof

local sw, sh = getScreenResolution()

local active, draw, active_fixview, light_active, zone_active = false, false, false, false, false
local samp, angY, test_fov = 0, 0.0, 70
local handle, id_model, sight_posX, sight_posY, sight_posZ, handle_fixview, who = -1, -1, 0, 0, 0, -1, 0
local text_target, name_model, samp_v = "NO TARGET", '', 'unknown'

local lencoding, encoding = pcall(require, 'encoding')
encoding.default = 'CP1251'
u8 = encoding.UTF8

-- Authors: Roberto Ierusalimschy and Andre Carregal
local performResume, handleReturnValue
local oldpcall, oldxpcall = pcall, xpcall
local pack = table.pack or function(...) return {n = select("#", ...), ...} end
local unpack = table.unpack or unpack
local running = coroutine.running
local coromap = setmetatable({}, { __mode = "k" })

function handleReturnValue(err, co, status, ...)
	if not status then
		return false, err(debug.traceback(co, (...)), ...)
	end
	if coroutine.status(co) == 'suspended' then
		return performResume(err, co, coroutine.yield(...))
	else
		return true, ...
	end
end

function performResume(err, co, ...)
	return handleReturnValue(err, co, coroutine.resume(co, ...))
end

function id(trace, ...)
	return trace
end

function coxpcall(f, err, ...)
	local current = running()
	if not current then
		if err == id then
			return oldpcall(f, ...)
		else
			if select("#", ...) > 0 then
				local oldf, params = f, pack(...)
				f = function() return oldf(unpack(params, 1, params.n)) end
			end
		return oldxpcall(f, err)
		end
	else
		local res, co = oldpcall(coroutine.create, f)
		if not res then
			local newf = function(...) return f(...) end
			co = coroutine.create(newf)
		end
		coromap[co] = current
		return performResume(err, co, ...)
	end
end

function copcall(f, ...)
	return coxpcall(f, id, ...)
end

-- AUTHOR main hooks lib: RTD/RutreD(https://www.blast.hk/members/126461/)
ffi.cdef[[
	int VirtualProtect(void* lpAddress, unsigned long dwSize, unsigned long flNewProtect, unsigned long* lpflOldProtect);
	void* VirtualAlloc(void* lpAddress, unsigned long dwSize, unsigned long	flAllocationType, unsigned long flProtect);
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
	local size, trampoline = size or 5, trampoline or false
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
	if opts.wrap==nil then opts.wrap = 80 end
	if opts.wrap==true then opts.wrap = -1 end
	opts.indent = opts.indent or " "
	opts.arrayPadding = opts.arrayPadding or opts.padding or 0
	opts.objectPadding = opts.objectPadding or opts.padding or 0
	opts.afterComma = opts.afterComma or opts.aroundComma or 0
	opts.beforeComma = opts.beforeComma or opts.aroundComma or 0
	opts.beforeColon = opts.beforeColon or opts.aroundColon or 0
	opts.afterColon = opts.afterColon or opts.aroundColon or 0
	opts.beforeColon1 = opts.beforeColon1 or opts.aroundColon1 or opts.beforeColon or 0
	opts.afterColon1 = opts.afterColon1 or opts.aroundColon1 or opts.afterColon or 0
	opts.beforeColonN = opts.beforeColonN or opts.aroundColonN or opts.beforeColon or 0
	opts.afterColonN = opts.afterColonN or opts.aroundColonN or opts.afterColon or 0

	local colon = opts.lua and '=' or ':'
	local array = opts.lua and {'{','}'} or {'[',']'}
	local apad = string.rep(' ', opts.arrayPadding)
	local opad = string.rep(' ', opts.objectPadding)
	local comma = string.rep(' ',opts.beforeComma)..','..string.rep(' ',opts.afterComma)
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
						local padrt = '%-'..longest..'s'
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
						local padrt = '%-'..longest..'s'
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

local config = {}

function defalut_config()
	config = {
		["MAIN"] = {["heli_camera"] = {['z'] = 0.5}, ['cmd'] = 'BC', ['cmd_samp'] = '/helicam',
			["language"] = {['main'] = "EN", ['compass'] = "EN", ['zones'] = "EN"},
			["zones"] = {['size'] = 0.0, ['dist'] = 1000},
			["light"] = {['multiplier'] = 4, ['auto'] = true, ['size'] = 5, ['intensity'] = 255},
			["vehicle"] = {['497'] = 497}},
		["pos"] = {["info"] = {['x'] = 313, ['y'] = 310},
			["zoom"] = {['x'] = 67, ['y'] = 224},
			["compass_text"] = {['x'] = 320.5, ['y'] = 23},
			["heli"] = {['x'] = 46, ['y'] = 177},
			["camera"] = {['x'] = 87, ['y'] = 180},
			["arrow_compass"] = {['x'] = 87, ['y'] = 153}},
		['keybind'] = {['active_fixview'] = 'Right Button', ['hud'] = 'F9',
			['draw_noise'] = '1', ['nightvi'] = '2', ['infvi'] = '3',
			['sens_minus'] = '-', ['sens_plus'] = '=', ['zoom'] = 'Shift',
			['zones'] = 'Z', ['light'] = 'L', ['menu'] = 'F12', },
		['zones'] = zone()
	}
	savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
end

if doesFileExist("moonloader/Helicopter-Camera/Helicopter-Camera.json") then
	local f = io.open("moonloader/Helicopter-Camera/Helicopter-Camera.json")
	config = decodeJson(f:read("*a"))
	f:close()
else
	defalut_config()
end

function CarModel(x)
	local cars = {[400] = "Landstalker", [401] = "Bravura", [402] = "Buffalo", [403] = "Linerunner", [404] = "Perenniel", [405] = "Sentinel", [406] = "Dumper", [407] = "Firetruck", [408] = "Trashmaster", [409] = "Stretch", [410] = "Manana", [411] = "Infernus", [412] = "Voodoo", [413] = "Pony", [414] = "Mule", [415] = "Cheetah", [416] = "Ambulance", [417] = "Leviathan", [418] = "Moonbeam", [419] = "Esperanto", [420] = "Taxi", [421] = "Washington", [422] = "Bobcat", [423] = "Mr Whoopee", [424] = "BF Injection", [425] = "Hunter", [426] = "Premier", [427] = "Enforcer", [428] = "Securicar", [429] = "Banshee", [430] = "Predator", [431] = "Bus", [432] = "Rhino", [433] = "Barracks", [434] = "Hotknife", [435] = "Article Trailer", [436] = "Previon", [437] = "Coach", [438] = "Cabbie", [439] = "Stallion", [440] = "Rumpo", [441] = "RC Bandit", [442] = "Romero", [443] = "Packer", [444] = "Monster", [445] = "Admiral", [446] = "Squallo", [447] = "Seasparrow", [448] = "Pizzaboy", [449] = "Tram", [450] = "Article Trailer 2", [451] = "Turismo", [452] = "Speeder", [453] = "Reefer", [454] = "Tropic", [455] = "Flatbed", [456] = "Yankee", [457] = "Caddy", [458] = "Solair", [459] = "Topfun Van", [460] = "Skimmer", [461] = "PCJ-600", [462] = "Faggio", [463] = "Freeway", [464] = "RC Baron", [465] = "RC Raider", [466] = "Glendale", [467] = "Oceanic", [468] = "Sanchez", [469] = "Sparrow", [470] = "Patriot", [471] = "Quad", [472] = "Coastguard", [473] = "Dinghy", [474] = "Hermes", [475] = "Sabre", [476] = "Rustler", [477] = "ZR-350", [478] = "Walton", [479] = "Regina", [480] = "Comet", [481] = "BMX", [482] = "Burrito", [483] = "Camper", [484] = "Marquis", [485] = "Baggage", [486] = "Dozer", [487] = "Maverick", [488] = "SAN News Maverick", [489] = "Rancher", [490] = "FBI Rancher", [491] = "Virgo", [492] = "Greenwood", [493] = "Jetmax", [494] = "Hotring Racer C", [495] = "Sandking", [496] = "Blista Compact", [497] = "Police Maverick", [498] = "Boxville", [499] = "Benson", [500] = "Mesa", [501] = "RC Goblin", [502] = "Hotring Racer A", [503] = "Hotring Racer B", [504] = "Bloodring Banger", [505] = "Rancher", [506] = "Super GT", [507] = "Elegant", [508] = "Journey", [509] = "Bike", [510] = "Mountain Bike", [511] = "Beagle", [512] = "Cropduster", [513] = "Stuntplane", [514] = "Tanker", [515] = "Roadtrain", [516] = "Nebula", [517] = "Majestic", [518] = "Buccaneer", [519] = "Shamal", [520] = "Hydra", [521] = "FCR-900", [522] = "NRG-500", [523] = "HPV1000", [524] = "Cement Truck", [525] = "Towtruck", [526] = "Fortune", [527] = "Cadrona", [528] = "FBI Truck", [529] = "Willard", [530] = "Forklift", [531] = "Tractor", [532] = "Combine Harvester", [533] = "Feltzer", [534] = "Remington", [535] = "Slamvan", [536] = "Blade", [537] = "Freight (Train)", [538] = "Brownstreak (Train)", [539] = "Vortex", [540] = "Vincent", [541] = "Bullet", [542] = "Clover", [543] = "Sadler", [544] = "Firetruck LA", [545] = "Hustler", [546] = "Intruder", [547] = "Primo", [548] = "Cargobob", [549] = "Tampa", [550] = "Sunrise", [551] = "Merit", [552] = "Utility Van", [553] = "Nevada", [554] = "Yosemite", [555] = "Windsor", [556] = "Monster A", [557] = "Monster B", [558] = "Uranus", [559] = "Jester", [560] = "Sultan", [561] = "Stratum", [562] = "Elegy", [563] = "Raindance", [564] = "RC Tiger", [565] = "Flash",[566] = "Tahoma", [567] = "Savanna", [568] = "Bandito", [569] = "Freight Flat Trailer (Train)", [570] = "Streak Trailer (Train)", [571] = "Kart", [572] = "Mower", [573] = "Dune", [574] = "Sweeper", [575] = "Broadway", [576] = "Tornado", [577] = "AT400", [578] = "DFT-30", [579] = "Huntley", [580] = "Stafford", [581] = "BF-400", [582] = "Newsvan", [583] = "Tug", [584] = "Petrol Trailer", [585] = "Emperor", [586] = "Wayfarer", [587] = "Euros", [588] = "Hotdog", [589] = "Club", [590] = "Freight Box Trailer (Train)", [591] = "Article Trailer 3", [592] = "Andromada", [593] = "Dodo", [594] = "RC Cam", [595] = "Launch", [596] = "Police Car (LSPD)", [597] = "Police Car (SFPD)", [598] = "Police Car (LVPD)", [599] = "Police Ranger", [600] = "Picador", [601] = "S.W.A.T.", [602] = "Alpha", [603] = "Phoenix", [604] = "Glendale Shit", [605] = "Sadler Shit", [606] = "Baggage Trailer A", [607] = "Baggage Trailer B", [608] = "Tug Stairs Trailer", [609] = "Boxville", [610] = "Farm Trailer";}
	for i, v in pairs(cars) do
		if i == x then
			return v
		end
	end
	return 'None'
end

function NameModel(x)
	local testNameModel = {[0] = "cj", [1] = "truth", [2] = "maccer", [3] = "andre", [4] = "bbthin", [5] = "bb", [6] = "emmet", [7] = "male01", [8] = "janitor", [9] = "bfori", [10] = "bfost", [11] = "vbfycrp", [12] = "bfyri", [13] = "bfyst", [14] = "bmori", [15] = "bmost", [16] = "bmyap", [17] = "bmybu", [18] = "bmybe", [19] = "bmydj", [20] = "bmyri", [21] = "bmycr", [22] = "bmyst", [23] = "wmybmx", [24] = "wbdyg1", [25] = "wbdyg2", [26] = "wmybp", [27] = "wmycon", [28] = "bmydrug", [29] = "wmydrug", [30] = "hmydrug", [31] = "dwfolc", [32] = "dwmolc1", [33] = "dwmolc2", [34] = "dwmylc1", [35] = "hmogar", [36] = "wmygol1", [37] = "wmygol2", [38] = "hfori", [39] = "hfost", [40] = "hfyri", [41] = "hfyst", [42] = "jethro", [43] = "hmori", [44] = "hmost", [45] = "hmybe", [46] = "hmyri", [47] = "hmycr", [48] = "hmyst", [49] = "omokung", [50] = "wmymech", [51] = "bmymoun", [52] = "wmymoun", [53] = "ofori", [54] = "ofost", [55] = "ofyri", [56] = "ofyst", [57] = "omori", [58] = "omost", [59] = "omyri", [60] = "omyst", [61] = "wmyplt", [62] = "wmopj", [63] = "bfypro", [64] = "hfypro", [65] = "kendl", [66] = "bmypol1", [67] = "bmypol2", [68] = "wmoprea", [69] = "sbfyst", [70] = "wmosci", [71] = "wmysgrd", [72] = "swmyhp1", [73] = "swmyhp2", [74] = "-", [75] = "swfopro", [76] = "wfystew", [77] = "swmotr1", [78] = "wmotr1", [79] = "bmotr1", [80] = "vbmybox", [81] = "vwmybox", [82] = "vhmyelv", [83] = "vbmyelv", [84] = "vimyelv", [85] = "vwfypro", [86] = "ryder3", [87] = "vwfyst1", [88] = "wfori", [89] = "wfost", [90] = "wfyjg", [91] = "wfyri", [92] = "wfyro", [93] = "wfyst", [94] = "wmori", [95] = "wmost", [96] = "wmyjg", [97] = "wmylg", [98] = "wmyri", [99] = "wmyro", [100] = "wmycr", [101] = "wmyst", [102] = "ballas1", [103] = "ballas2", [104] = "ballas3", [105] = "fam1", [106] = "fam2", [107] = "fam3", [108] = "lsv1", [109] = "lsv2", [110] = "lsv3", [111] = "maffa", [112] = "maffb", [113] = "mafboss", [114] = "vla1", [115] = "vla2", [116] = "vla3", [117] = "triada", [118] = "triadb", [119] = "sindaco", [120] = "triboss", [121] = "dnb1", [122] = "dnb2", [123] = "dnb3", [124] = "vmaff1", [125] = "vmaff2", [126] = "vmaff3", [127] = "vmaff4", [128] = "dnmylc", [129] = "dnfolc1", [130] = "dnfolc2", [131] = "dnfylc", [132] = "dnmolc1", [133] = "dnmolc2", [134] = "sbmotr2", [135] = "swmotr2", [136] = "sbmytr3", [137] = "swmotr3", [138] = "wfybe", [139] = "bfybe", [140] = "hfybe", [141] = "sofybu", [142] = "sbmyst", [143] = "sbmycr", [144] = "bmycg", [145] = "wfycrk", [146] = "hmycm", [147] = "wmybu", [148] = "bfybu", [149] = "smokev", [150] = "wfybu", [151] = "dwfylc1", [152] = "wfypro", [153] = "wmyconb", [154] = "wmybe", [155] = "wmypizz", [156] = "bmobar", [157] = "cwfyhb", [158] = "cwmofr", [159] = "cwmohb1", [160] = "cwmohb2", [161] = "cwmyfr", [162] = "cwmyhb1", [163] = "bmyboun", [164] = "wmyboun", [165] = "wmomib", [166] = "bmymib", [167] = "wmybell", [168] = "bmochil", [169] = "sofyri", [170] = "somyst", [171] = "vwmybjd", [172] = "vwfycrp", [173] = "sfr1", [174] = "sfr2", [175] = "sfr3", [176] = "bmybar", [177] = "wmybar", [178] = "wfysex", [179] = "wmyammo", [180] = "bmytatt", [181] = "vwmycr", [182] = "vbmocd", [183] = "vbmycr", [184] = "vhmycr", [185] = "sbmyri", [186] = "somyri", [187] = "somybu", [188] = "swmyst", [189] = "wmyva", [190] = "copgrl3", [191] = "gungrl3", [192] = "mecgrl3", [193] = "nurgrl3", [194] = "crogrl3", [195] = "gangrl3", [196] = "cwfofr", [197] = "cwfohb", [198] = "cwfyfr1", [199] = "cwfyfr2", [200] = "cwmyhb2", [201] = "dwfylc2", [202] = "dwmylc2", [203] = "omykara", [204] = "wmykara", [205] = "wfyburg", [206] = "vwmycd", [207] = "vhfypro", [208] = "suzie", [209] = "omonood", [210] = "omoboat", [211] = "wfyclot", [212] = "vwmotr1", [213] = "vwmotr2", [214] = "vwfywai", [215] = "sbfori", [216] = "swfyri", [217] = "wmyclot", [218] = "sbfost", [219] = "sbfyri", [220] = "sbmocd", [221] = "sbmori", [222] = "sbmost", [223] = "shmycr", [224] = "sofori", [225] = "sofost", [226] = "sofyst", [227] = "somobu", [228] = "somori", [229] = "somost", [230] = "swmotr5", [231] = "swfori", [232] = "swfost", [233] = "swfyst", [234] = "swmocd", [235] = "swmori", [236] = "swmost", [237] = "shfypro", [238] = "sbfypro", [239] = "swmotr4", [240] = "swmyri", [241] = "smyst", [242] = "smyst2", [243] = "sfypro", [244] = "vbfyst2", [245] = "vbfypro", [246] = "vhfyst3", [247] = "bikera", [248] = "bikerb", [249] = "bmypimp", [250] = "swmycr", [251] = "wfylg", [252] = "wmyva2", [253] = "bmosec", [254] = "bikdrug", [255] = "wmych", [256] = "sbfystr", [257] = "swfystr", [258] = "heck1", [259] = "heck2", [260] = "bmycon", [261] = "wmycd1", [262] = "bmocd", [263] = "vwfywa2", [264] = "wmoice", [265] = "tenpen", [266] = "pulaski", [267] = "hern", [268] = "dwayne", [269] = "smoke", [270] = "sweet", [271] = "ryder", [272] = "forelli", [273] = "tbone", [274] = "laemt1", [275] = "lvemt1", [276] = "sfemt1", [277] = "lafd1", [278] = "lvfd1", [279] = "sffd1", [280] = "lapd1", [281] = "sfpd1", [282] = "lvpd1", [283] = "csher", [284] = "lapdm1", [285] = "swat", [286] = "fbi", [287] = "army", [288] = "dsher", [289] = "zero", [290] = "rose", [291] = "paul", [292] = "cesar", [293] = "ogloc", [294] = "wuzimu", [295] = "torino", [296] = "jizzy", [297] = "maddogg", [298] = "cat", [299] = "claude", [300] = "lapdna", [301] = "sfpdna", [302] = "lvpdna", [303] = "lapdpc", [304] = "lapdpd", [305] = "lvpdpc", [306] = "wfyclpd", [307] = "vbfycpd", [308] = "wfyclem", [309] = "wfycllv", [310] = "csherna", [311] = "dsherna";}
	for i = 0, #testNameModel do
		if x == i then
			return testNameModel[i]
		end
	end
	return 'None'
end

if limgui then
	window, cmdbuffer = new.bool(false), new.char[128](config.MAIN.cmd)

	local qweeqe = config.MAIN.language.zones == "RU" and 1 or 2
	table.sort(config.zones, function(a,b) return a[qweeqe] < b[qweeqe] end)
	local texts_zones = {}
	for i = 1, #config.zones do
		texts_zones[i] = {new.char[256](config.zones[i][1]), new.char[256](config.zones[i][2]), new.float(config.zones[i][3]), new.float(config.zones[i][4]), new.float(config.zones[i][5])}
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
		style.PopupBorderSize = 1
		style.FramePadding = ImVec2(5, 5)
		style.FrameRounding = 4.7
		style.FrameBorderSize = 1.0
		style.ItemSpacing = ImVec2(2, 7)
		style.ItemInnerSpacing = ImVec2(8, 6)
		style.ScrollbarSize = 9.47
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
		colors[clr.Tab] = ImVec4(0.00, 0.00, 0.00, 0.52)
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
		colors[clr.NavWindowingHighlight] = ImVec4(1.00, 0.00, 0.00, 0.70)
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
			imgui.SetNextWindowPos(imgui.ImVec2(sw / 1.2, sh / 2), imgui.Cond.FirstUseEver, imgui.ImVec2(0.5, 0.5))
			imgui.SetNextWindowSize(imgui.ImVec2(374, 574), imgui.Cond.Always)
			imgui.Begin(script.name.." by dmitriyewich", window, imgui.WindowFlags.NoCollapse + imgui.WindowFlags.NoResize)

			if imgui.IsItemHovered() then
				if go_CMDserver == nil then go_CMDserver = os.clock() + (0.55 and 0.55 or 0.0) end
				local alpha = (os.clock() - go_CMDserver) * 3.5
				if os.clock() >= go_CMDserver then
					imgui.PushStyleVarFloat(imgui.StyleVar.Alpha, (alpha <= 1.0 and alpha or 1.0))
						imgui.BeginTooltip()
						imgui.PushTextWrapPos(450)
							imgui.TextUnformatted(config.MAIN.language.main == "RU" and '©dmitriyewich aka Валерий Дмитриевич.\nПКМ - Открыть группу в вк' or '©dmitriyewich aka Valeriy Dmitriyewich.\nRMB - Open a group in VK')
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

			imgui.BeginChild("MainChild", imgui.ImVec2(354, 495))
			imgui.Separator()
			if imgui.CollapsingHeader(config.MAIN.language.main == "RU" and 'Районы' or 'Zones') then
				if config.MAIN.language.zones == "RU" then imgui.Text("RU") else imgui.TextDisabled("RU") end
				if imgui.IsItemClicked(0) then
					config.MAIN.language.zones = "RU"
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
				imgui.SameLine(nil, 0)
				imgui.Text("|")
				imgui.SameLine(nil, 0)
				if config.MAIN.language.zones == "EN" then imgui.Text("EN") else imgui.TextDisabled("EN") end
				if imgui.IsItemClicked(0) then
					config.MAIN.language.zones = "EN"
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
				imgui.SameLine(nil, 0)
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 112) / 2)
				if imgui.Button(config.MAIN.language.main == "RU" and 'Добавить район' or 'Add zone'..'##addbutton', imgui.ImVec2(112, 0)) then
					local positionX, positionY, positionZ = get_char_oordinates(PLAYER_PED)
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

					if imgui.Button(text_rar..(config.MAIN.language.zones == "RU" and config.zones[i][1] or config.zones[i][2]) .. '##mainbutton'..i, imgui.ImVec2(112, 0)) then
						imgui.OpenPopup("##Popup"..i)
						key_res, res_ru, res_en, res_x, res_y, res_z = i, config.zones[i][1], config.zones[i][2], config.zones[i][3], config.zones[i][4], config.zones[i][5]
					end

					if imgui.IsItemHovered() then
						if config.zones[i][3] ~= nil and isPointOnScreen(config.zones[i][3], config.zones[i][4], config.zones[i][5], 0.5) then
							local result, xx, yy, zz, _, _ = convert3DCoordsToScreenEx(config.zones[i][3], config.zones[i][4], config.zones[i][5], true, true)
							if result then
								setText(zones_text[i], RusToGame(u8:decode(config.zones[i][config.MAIN.language.zones == "RU" and 1 or 2])), convertW(xx).x, convertW(yy).y, config.MAIN.zones.size+0.2, (config.MAIN.zones.size*4)+1.1, 2, 2, '0xFFFF0000', 0.5, 0x15FF0000, 500, 500, false, true, true)
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
								setText(zones_text[i], RusToGame(u8:decode(config.zones[i][config.MAIN.language.zones == "RU" and 1 or 2])), convertW(xx).x, convertW(yy).y, config.MAIN.zones.size+0.2, (config.MAIN.zones.size*4)+1.1, 2, 2, '0xFFFF0000', 0.5, 0x15FF0000, 500, 500, false, true, true)
							end
						end
						imgui.PushItemWidth(174)
						if imgui.InputText(config.MAIN.language.main == "RU" and 'Название на русском' or 'Name in your language'.."##InputTextRU"..i, texts_zones[i][1], sizeof(texts_zones[i][1])) then
							rawset(config.zones[i], 1, str(texts_zones[i][1]))
						end
						if imgui.InputText(config.MAIN.language.main == "RU" and 'Название на английском' or 'Name in english'.."##InputTextEN"..i, texts_zones[i][2], sizeof(texts_zones[i][2])) then
							config.zones[i][2] = str(texts_zones[i][2])
						end
						imgui.PopItemWidth()

						imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize(config.MAIN.language.main == "RU" and "CTRL+ЛКМ - ручной ввод координат" or "CTRL+LMB - manual input of coordinates").x) / 2)
						imgui.Text(config.MAIN.language.main == "RU" and "CTRL+ЛКМ - ручной ввод координат" or "CTRL+LMB - manual input of coordinates")
						imgui.PushItemWidth(347)
						if imgui.SliderFloat("X ##SliderFloat"..i, texts_zones[i][3], -3000.0, 3000.0) then
							config.zones[i][3] = texts_zones[i][3][0]
						end
						if imgui.SliderFloat("Y ##SliderFloat"..i, texts_zones[i][4], -3000.0, 3000.0) then
							config.zones[i][4] = texts_zones[i][4][0]
						end
						if imgui.SliderFloat("Z##SliderFloat"..i, texts_zones[i][5], -100.0, 250.0) then
							config.zones[i][5] = texts_zones[i][5][0]
						end
						imgui.PopItemWidth()

						imgui.SetCursorPosX((imgui.GetWindowWidth() - 325) / 2)
						if imgui.Button(config.MAIN.language.main == "RU" and 'Сброс' or 'Reset'..'##Сброс'..i, imgui.ImVec2(75, 25)) then
							config.zones[i][1], config.zones[i][2], config.zones[i][3], config.zones[i][4], config.zones[i][5] = res_ru, res_en, res_x, res_y, res_z
							texts_zones[i][3][0], texts_zones[i][4][0], texts_zones[i][5][0] = res_x, res_y, res_z
							imgui.StrCopy(texts_zones[i][1], res_ru)
							imgui.StrCopy(texts_zones[i][2], res_en)

						end
						imgui.SameLine()
						if imgui.Button(config.MAIN.language.main == "RU" and 'Сохранить' or 'Save'..'##Сохранить'..i, imgui.ImVec2(75, 25)) then
							savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
							imgui.CloseCurrentPopup()
						end
						imgui.SameLine()
						if imgui.Button(config.MAIN.language.main == "RU" and 'Закрыть' or 'Close'..'##Закрыть'..i, imgui.ImVec2(75, 25)) then
							config.zones[i][1], config.zones[i][2], config.zones[i][3], config.zones[i][4], config.zones[i][5] = res_ru, res_en, res_x, res_y, res_z
							texts_zones[i][3][0], texts_zones[i][4][0], texts_zones[i][5][0] = res_x, res_y, res_z
							imgui.StrCopy(texts_zones[i][1], res_ru)
							imgui.StrCopy(texts_zones[i][2], res_en)
							imgui.CloseCurrentPopup()
						end
						imgui.SameLine()
						if imgui.Button(config.MAIN.language.main == "RU" and 'Удалить район' or 'Delete an zone'..'##Удалить район'..i, imgui.ImVec2(100, 25)) then
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

			if imgui.CollapsingHeader(config.MAIN.language.main == "RU" and 'Настройки худа скрипта' or 'HUD Script Settings') then
				imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize(config.MAIN.language.main == "RU" and 'Координаты указаны игровые, не Вашего экрана' or 'The coordinates are game coordinates, not your screen').x) / 2)
				imgui.Text(config.MAIN.language.main == "RU" and 'Координаты указаны игровые, не Вашего экрана' or 'The coordinates are game coordinates, not your screen')
				imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize(config.MAIN.language.main == "RU" and "CTRL+ЛКМ - ручной ввод координат" or "CTRL+LMB - manual input of coordinates").x) / 2)
				imgui.Text(config.MAIN.language.main == "RU" and "CTRL+ЛКМ - ручной ввод координат" or "CTRL+LMB - manual input of coordinates")

				imgui.Separator()
				imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize(config.MAIN.language.main == "RU" and "Положение камеры" or "Camera position").x) / 2)
				imgui.Text(config.MAIN.language.main == "RU" and "Положение камеры" or "Camera position")
				imgui.PushItemWidth(274)
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 276) / 2)
				if imgui.SliderFloat("Z ##SliderFloatZ", pos_new.z, -4.0, 4.0) then
					config.MAIN.heli_camera.z = pos_new.z[0]
				end
				imgui.PopItemWidth()
				imgui.Separator()

				for k, v in pairs(config.pos) do
					imgui.Separator()
					local tbl_text_pos = {['compass_text'] = config.MAIN.language.main == "RU" and 'Позиция компаса' or 'Compass position', ['camera'] = config.MAIN.language.main == "RU" and 'Позиция иконки камеры' or 'Camera icon position', ['heli'] = config.MAIN.language.main == "RU" and 'Позиция иконки вертолета' or 'Helicopter icon position', ['arrow_compass'] = config.MAIN.language.main == "RU" and 'Позиция иконки направления на север' or 'Position of north icon', ['zoom'] = config.MAIN.language.main == "RU" and 'Позиция иконки зума' or 'Zoom icon position', ['info'] = config.MAIN.language.main == "RU" and 'Позиция информации' or 'Information position'}
					imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize(tbl_text_pos[''..k]).x) / 2)
					imgui.Text(tbl_text_pos[''..k])
					imgui.PushItemWidth(147)
					if imgui.SliderFloat("X ##SliderFloat"..k, pos_new[k][1], 0.0, 640.0) then
						config.pos[k].x = pos_new[k][1][0]
					end
					imgui.SameLine()
					if imgui.SliderFloat("Y ##SliderFloat"..k, pos_new[k][2], 0.0, 448.0) then
						config.pos[k].y = pos_new[k][2][0]
					end
					imgui.PopItemWidth()
					imgui.Separator()
				end
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 77) / 2)
				if imgui.Button(config.MAIN.language.main == "RU" and 'Сохранить' or 'Save'..'##HUD2', imgui.ImVec2(75, 25)) then
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
			end
			imgui.Separator()

			if imgui.CollapsingHeader(config.MAIN.language.main == "RU" and 'Назначение клавиш' or 'Keybind assignment') then
				imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize(config.MAIN.language.main == "RU" and "Изменение чит-кода" or 'Changing cheat code').x) / 2)
				imgui.Text(config.MAIN.language.main == "RU" and "Изменение чит-кода" or 'Changing cheat code')
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 210) / 2)
				imgui.PushItemWidth(210)
				if imgui.InputTextWithHint('##cmd', config.MAIN.language.main == "RU" and 'Введите чит-код' or 'Write cheat-code', cmdbuffer, sizeof(cmdbuffer), imgui.InputTextFlags.AutoSelectAll) then
					config.MAIN.cmd = str(cmdbuffer)
				end
				imgui.PopItemWidth()
				imgui.SetCursorPosX((imgui.GetWindowWidth() - 130) / 2)
				if imgui.Button(config.MAIN.language.main == "RU" and 'Сохранить чит-код' or 'Save cheat-code', imgui.ImVec2(130, 0)) then
					config.MAIN.cmd = str(cmdbuffer)
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end

				tbl_button = {{'hud', config.MAIN.language.main == "RU" and 'Скрытие худа' or 'Hiding HUD', 'F9'}, {'sens_plus', config.MAIN.language.main == "RU" and 'Ув. чувствительности камеры' or 'Increasing sensitivity of camera', '='},
					{'sens_minus', config.MAIN.language.main == "RU" and 'Ум. чувствительности камеры' or 'Reducing sensitivity of camera', '-'}, {'zoom', config.MAIN.language.main == "RU" and 'Ускорение зума' or 'Zoom acceleration', 'Shift'},
					{'infvi', config.MAIN.language.main == "RU" and 'Вкл/выкл тепловизора' or 'On/off thermal imager', '3'}, {'active_fixview', config.MAIN.language.main == "RU" and 'Фиксация камеры' or 'Fixing camera', 'Right Button'},
					{'draw_noise', config.MAIN.language.main == "RU" and 'Вкл/выкл шума на экране' or 'On/off screen noise', '1'}, {'nightvi', config.MAIN.language.main == "RU" and 'Вкл/выкл прибор ночного видения' or 'On/off night vision device', '2'},
					{'zones', config.MAIN.language.main == "RU" and 'Вкл/выкл отображение районов' or 'On/off display of zones', 'Z'}, {'light', config.MAIN.language.main == "RU" and 'Вкл/выкл пародию на луч света' or 'On/off parody of a ray of light', 'L'},
					{'menu', config.MAIN.language.main == "RU" and 'Вкл/выкл меню настроек(для сингла)' or 'On/off settings menu(for single)', 'F12'};}
				table.sort(tbl_button, function(a,b) return a[1] > b[1] end)
				for i = 1, #tbl_button do
					imgui.HotKey(tbl_button[i][1]..'##1'..i, config.keybind, ''..tbl_button[i][1], ''..tbl_button[i][3], 90, 0)
					imgui.SameLine(nil, 0)
					imgui.SetCursorPosY(imgui.GetCursorPosY() - 1)
					imgui.SetCursorPosX(imgui.GetCursorPosX() + 10)
					imgui.Text(tbl_button[i][2])
					imgui.SetCursorPosY(imgui.GetCursorPosY() + 3)
				end

			end

			imgui.Separator()

			if imgui.CollapsingHeader(config.MAIN.language.main == "RU" and 'Прочее' or 'Other') then
				if config.MAIN.language.compass == "RU" then imgui.Text("RU") else imgui.TextDisabled("RU") end
				if imgui.IsItemClicked(0) then
					config.MAIN.language.compass = "RU"
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
				imgui.SameLine(nil, 0)
				imgui.Text("|")
				imgui.SameLine(nil, 0)
				if config.MAIN.language.compass == "EN" then imgui.Text("EN") else imgui.TextDisabled("EN") end
				if imgui.IsItemClicked(0) then
					config.MAIN.language.compass = "EN"
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
				imgui.SameLine(nil, 0)
				imgui.Text(config.MAIN.language.main == "RU" and "	Изменение языка компаса" or '	Changing compass language')
				imgui.PushItemWidth(150)
				if imgui.SliderFloat(config.MAIN.language.main == "RU" and "Размер шрифта районов" or 'Font size of zones'..'##zones_size', zones_size, -0.2, 0.2) then
					config.MAIN.zones.size = zones_size[0]
				end
				if imgui.SliderFloat(config.MAIN.language.main == "RU" and "Дистанция прорисовки районов" or 'Drawing distance of zones'..'##light_size', zones_dist, 0, 3600) then
					config.MAIN.zones.dist = zones_dist[0]
				end
				if imgui.Checkbox(config.MAIN.language.main == "RU" and 'Размер фонарика '.. (checkbox_light_auto[0] and 'подбирается автоматически' or 'настраивается вручную') or 'Flashlight size '.. (checkbox_light_auto[0] and 'is selected automatically' or 'is adjusted manually')..'##light_sizeauto', checkbox_light_auto) then
					config.MAIN.light.auto = not config.MAIN.light.auto
				end
				if checkbox_light_auto[0] then
					if imgui.SliderFloat(config.MAIN.language.main == "RU" and "Множитель для авторазмера" or 'Multiplier for auto-size'..'##light_multiplier', light_multiplier, 0.5, 8) then
						config.MAIN.light.multiplier = light_multiplier[0]
					end
				else
					if imgui.SliderFloat(config.MAIN.language.main == "RU" and "Размер фонарика" or 'Flashlight size'..'##light_size', light_size, 0, 47) then
						config.MAIN.light.size = light_size[0]
					end
				end
				if imgui.SliderFloat(config.MAIN.language.main == "RU" and "Интенсивность фонарика" or 'Flashlight intensity'..'##light_intensity', light_intensity, 0, 255) then
					config.MAIN.light.intensity = light_intensity[0]
				end
				imgui.PopItemWidth()

				imgui.Separator()

				if imgui.TreeNodeStr(config.MAIN.language.main == "RU" and 'Список доступного камере транспорта' or 'List of transport available to camera') then
					imgui.PushItemWidth(74)
					imgui.InputText(config.MAIN.language.main == "RU" and "Введите ID model" or 'Enter model ID'..'##InputTextAddveh', add_veh, sizeof(add_veh)-1, imgui.InputTextFlags.CharsDecimal + imgui.InputTextFlags.AutoSelectAll)
					imgui.SameLine()
					if imgui.Button(config.MAIN.language.main == "RU" and "Добавить" or 'Add'..'##Addvehbutton', imgui.ImVec2(0, 0)) then
						config.MAIN.vehicle[str(add_veh)] = tonumber(str(add_veh))
					end
					imgui.PopItemWidth()

					for k, v in pairs(config.MAIN.vehicle) do
						imgui.Text(string.format("%s(%s)", v, CarModel(v)))
						if imgui.IsItemClicked(1) then
							config.MAIN.vehicle[k] = nil
						end
					end
					imgui.SetCursorPosX((imgui.GetWindowWidth() - imgui.CalcTextSize(config.MAIN.language.main == "RU" and "ПКМ - удалить" or 'RMB - delete').x) / 2)
						imgui.Text(config.MAIN.language.main == "RU" and "ПКМ - удалить" or 'RMB - delete')
					imgui.TreePop()
				end

				imgui.Separator()

				imgui.SetCursorPosX((imgui.GetWindowWidth() - 176) / 2)
				if imgui.Button(config.MAIN.language.main == "RU" and "Сохранить" or 'Save'..'##otherbutton4', imgui.ImVec2(174, 0)) then
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
			end
			imgui.Separator()
			imgui.EndChild()
				if config.MAIN.language.main == "RU" then imgui.Text("RU") else imgui.TextDisabled("RU") end
				if imgui.IsItemClicked(0) then
					config.MAIN.language.main = "RU"
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
				imgui.SameLine(nil, 0)
				imgui.Text("|")
				imgui.SameLine(nil, 0)
				if config.MAIN.language.main == "EN" then imgui.Text("EN") else imgui.TextDisabled("EN") end
				if imgui.IsItemClicked(0) then
					config.MAIN.language.main = "EN"
					savejson(convertTableToJsonString(config), "moonloader/Helicopter-Camera/Helicopter-Camera.json")
				end
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
		local tKeys, saveKeys = split(getDownKeys(), ' '),select(2,getDownKeys())
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
		local pa = getAC_PA()[2]
		local dist = getDistanceBetweenCoords3d(pa[1], pa[2], pa[3], origin[0], origin[1], origin[2])
		if dist <= (4.5 + config.MAIN.heli_camera.z) then
			local posX1, posY1, posZ1 = convertScreenCoordsToWorld3D(sw/2, sh/2, 700.0)
			local lres, result, colpoint = copcall(processLineOfSight, pa[1], pa[2], pa[3]-1, posX1, posY1, posZ1, true, false, false, true, false, false, false)
			if lres and result and colpoint.entity ~= 0 then
				local normal = colpoint.normal
				local pos = Vector3D(colpoint.pos[1], colpoint.pos[2], colpoint.pos[3]) - (Vector3D(normal[1], normal[2], normal[3]) * 0.1)
				local zOffset = 300
				if normal[3] >= 0.5 then zOffset = 1 end

				local lres2, result2, colpoint2 = copcall(processLineOfSight, pos.x, pos.y, pos.z + zOffset, pos.x, pos.y, pos.z - 0.3, true, false, false, true, false, false, false)
				if lres2 and result2 then
					local pos = Vector3D(colpoint2.pos[1], colpoint2.pos[2], colpoint2.pos[3] + 1)
					target = ffi.new("float[3]", pos.x, pos.y, pos.z+1)
				end
			end
		end
	end
	AddHeliSearchLight(origin, target, targetRadius, power, coronaIndex, unknownFlag, drawShadow)
end

function SendCMD(this, szString)
	if ffi.string(szString) == config.MAIN.cmd_samp then
		if limgui then
		window[0] = not window[0]
		else
			printString("Library ~y~\'mimgui\' ~r~not found.~n~~w~Download: ~y~ https://github.com/THE-FYP/mimgui.~n~~r~Copy link in~y~ moonloader.log.", 5000)
			print('Download: https://github.com/THE-FYP/mimgui ')
		end
		return false
	end
	SendCMD(this, szString)
end

function main()

	repeat wait(0) until memory.read(0xC8D4C0, 4, false) == 9
	repeat wait(0) until fixed_camera_to_skin()

	if isSampLoaded() then samp, samp_v = 1, samp_ver() end
	if samp == 1 and samp_v ~= 'unknown' then
		vehpool = memory.getint32(memory.getint32(memory.getint32(samp_handle() + (samp_v == 'R1' and 0x21A0F8 or 0x26E8DC), false) + (samp_v == 'R1' and 0x3CD or 0x3DE), false) + (samp_v == 'R1' and 0x1C or 0xC), false)
		pedpool = memory.getint32(memory.getint32(memory.getint32(samp_handle() + (samp_v == 'R1' and 0x21A0F8 or 0x26E8DC), false) + (samp_v == 'R1' and 0x3CD or 0x3DE), false) + (samp_v == 'R1' and 0x18 or 0x8), false)
		SendCMD = jmp_hook.new("void(__thiscall *)(uintptr_t*, const char*)", SendCMD, samp_handle() + (samp_v == 'R1' and 0x65C60 or 0x69190))
	end

	if not loadTexturesTXD() then return end

	standard_fov = getCameraFov()

	sx, sy = memory.getfloat(0xB6EC14) * sw, memory.getfloat(0xB6EC10) * sh

	AddHeliSearchLight = jmp_hook.new("void(__cdecl *)(const float*, const float*, float targetRadius, float power, unsigned int coronaIndex, unsigned char unknownFlag, unsigned char drawShadow)", AddHeliSearchLight, 0x6C45B0)

	lua_thread.create(camhack)
	lua_thread.create(car)
	lua_thread.create(compass)
	lua_thread.create(zones_thread)
	lua_thread.create(light_thread)
	lua_thread.create(draw_info)

	compassTextEN = {[-180] = "S", [-135] = "SE", [-90] = "E", [-45] = "NE", [0] = "N", [45] = "NW", [90] = "W", [135] = "SW", [180] = "S"}
	compassTextRU = {[-180] = "Ю", [-135] = "ЮВ", [-90] = "В", [-45] = "СВ", [0] = "С", [45] = "СЗ", [90] = "З", [135] = "ЮЗ", [180] = "Ю"}
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
end

function light_thread()
	while true do wait(0)
		if active then
			if isKeyJustPressed(isKeys(config.keybind.light)) then
				light_active = not light_active
			end
			if light_active and sx >= 0 and sy >= 0 and sx < sw and sy < sh then
			local pa = getAC_PA()[2]
			local posX1, posY1, posZ1 = convertScreenCoordsToWorld3D(sw/2, sh/2, 700.0)
			local lres, result, colpoint = copcall(processLineOfSight, pa[1], pa[2], pa[3]-1, posX1, posY1, posZ1, true, false, false, true, false, true, false)
			if lres and result and colpoint.entity ~= 0 then
				local normal = colpoint.normal
				local pos = Vector3D(colpoint.pos[1], colpoint.pos[2], colpoint.pos[3]) - (Vector3D(normal[1], normal[2], normal[3]) * 0.1)
				local zOffset = 300
				if normal[3] >= 0.5 then zOffset = 1 end
				local lres2, result2, colpoint2 = copcall(processLineOfSight, pos.x, pos.y, pos.z + zOffset, pos.x, pos.y, pos.z - 0.3, true, false, false, true, false, false, false)
				if lres2 and result2 then
					local pos = Vector3D(colpoint2.pos[1], colpoint2.pos[2], colpoint2.pos[3] + 1)
					local GroundZ = getGroundZFor3dCoord(pos.x, pos.y, pos.z)
					drawShadow(3, pos.x, pos.y, pos.z, 0.0, config.MAIN.light.auto and ((pa[3] - GroundZ) / config.MAIN.light.multiplier) or config.MAIN.light.size , 15, config.MAIN.light.intensity, config.MAIN.light.intensity, config.MAIN.light.intensity)

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
						if result then
							setText(zones_text[i], RusToGame(u8:decode(tbl_zone[i][config.MAIN.language.zones == "RU" and 1 or 2])), convertW(xx).x, convertW(yy).y, config.MAIN.zones.size+0.2, (config.MAIN.zones.size*4)+1.1, 2, 2, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)
						end
					end
				end
			end
		end
	end
end

function car()
	while true do wait(0)
		if active then
			sight_posX, sight_posY, sight_posZ = 0, 0, 0
			local pos, cam = {convertScreenCoordsToWorld3D(sw / 2, sh / 2, 700.0)}, getAC_PA()[1]
			local lres, res, c = copcall(processLineOfSight, cam[1], cam[2], cam[3], pos[1], pos[2], pos[3], true, true, true, true, true, true, true, true)

			if lres and res and (c.entityType == 2 or c.entityType == 3) then
				if c.entityType == 3 and getCharPointerHandle(c.entity) ~= PLAYER_PED or storeCarCharIsInNoSave(PLAYER_PED) ~= getVehiclePointerHandle(c.entity) then
					sight_posX, sight_posY, sight_posZ = c.pos[1], c.pos[2], c.pos[3]

					handle = c.entityType == 2 and getVehiclePointerHandle(c.entity) or getCharPointerHandle(c.entity)

					id_model = c.entityType == 2 and getCarModel(handle) or getCharModel(handle)

					name_model = c.entityType == 2 and CarModel(id_model) or NameModel(id_model)

					local draw = c.entityType == 2 and {get_car_oordinates(handle)} or {get_char_oordinates(handle)}

					local wposX, wposY = convert3DCoordsToScreen(draw[1], draw[2], draw[3])
					drawIcon(1, 2, convertW(wposX).x, convertW(wposY).y, 42, 50, 0xDAFAFAFA)
					if samp == 1 then
						id_nickname = c.entityType == 2 and getPedID(getDriverOfCar(handle)) or getPedID(handle)

						id_car = c.entityType == 2 and getCarID(handle) or -1
					end
					text_target = c.entityType == 2 and "ON VEHICLE" or "ON HUMAN"
				end
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

			if active_fixview then
				local position, cam = (who == 2 and {get_car_oordinates(handle_fixview)} or who == 3 and {get_char_oordinates(handle_fixview)}), getAC_PA()[1]
				local dist = getDistanceBetweenCoords3d(cam[1], cam[2], cam[3], position[1], position[2], position[3])
				if dist <= (who == 2 and 400 or 200) then
					pointCameraAtPoint(position[1], position[2], position[3], 2)
				else
					warring_thread = lua_thread.create(function()
						local timer = os.clock()
						active_fixview = false
						while true do wait(0)
							drawIcon(1, 3, config.pos.info.x+15, config.pos.info.y+28, 35, 40, 0xDAFAFAFA)
							setText(test_text3[1], RusToGame(u8:decode('~r~CONNECTION LOST')), config.pos.info.x+30, config.pos.info.y+24, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)
							if os.clock() - timer > 2 or active_fixview then break end
						end
					end)
				end
			end
		end
	end
end

function camhack()
	local flymode, fov, radarHud, keyPressed, speed = 0, 70, 1, 0, 15.0
	while true do wait(0)
		test_fov = -(fov + 80 - (200))
		if samp == 0 and isKeyJustPressed(isKeys(config.keybind.menu)) then
			if limgui then
			window[0] = not window[0]
			else
				printString("Library ~y~\'mimgui\' ~r~not found.~n~~w~Download: ~y~ https://github.com/THE-FYP/mimgui.~n~~r~Copy link in~y~ moonloader.log.", 5000)
				print('Download: https://github.com/THE-FYP/mimgui ')
			end
		end
		-- local pStSet = sampGetServerSettingsPtr()
		if isCharInAnyCar(PLAYER_PED) and config.MAIN.vehicle[tostring(getCarModel(storeCarCharIsInNoSave(PLAYER_PED)))] ~= nil then
			local posX, posY, posZ = getCarModelCornersIn2d(getCarModel(storeCarCharIsInNoSave(PLAYER_PED)), storeCarCharIsInNoSave(PLAYER_PED))
			local posZ = posZ + config.MAIN.heli_camera.z
			if not active and testCheat(config.MAIN.cmd) then
				active, draw = true, true
				if flymode == 0 and active then
					angZ = -getCharHeading(playerPed)
					angY, flymode = 0.0, 1
				end
			end

			if flymode == 1 then
				setFixedCameraPosition(posX, posY, posZ, 0.0, 0.0, 0.0)
				if isKeyJustPressed(isKeys(config.keybind.draw_noise)) then
					draw, infvi, nightvi = not draw, false, false
					setNightVision(false)
					setInfraredVision(false)
				end
				if isKeyJustPressed(isKeys(config.keybind.nightvi)) then
					nightvi, infvi = not nightvi, false
					setNightVision(nightvi)
					setInfraredVision(false)
				end
				if isKeyJustPressed(isKeys(config.keybind.infvi)) then
					infvi, nightvi = not infvi, false
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
				cameraSetLerpFov( fov, fov, 700, true)

				drawIcon(1, 10, config.pos.zoom.x, config.pos.zoom.y, 76, 10, 0xFAFAFAFA)
				drawIcon(1, 7, config.pos.zoom.x+49-((81 * fov) / 100), config.pos.zoom.y, 8, 8, 0xFAFAFAFA)
				setText(test_text3[2], RusToGame(u8:decode('Zoom: '..fov..' Sensitivity: '..speed)), config.pos.zoom.x, config.pos.zoom.y+3, 0.13, 1.0, 2, 2, '0xFFFFFFFF', 0.5, 0x15000000, 255, 500, false, true, true)

				if active_fixview then
					local ac_pa = getAC_PA()
					angZ = math.atan2( (ac_pa[2][1]-ac_pa[1][1]), (ac_pa[2][2]-ac_pa[1][2]) ) * 180 / math.pi
					if angZ <= 0 then angZ = 360 + angZ elseif angZ >= 0 then angZ = angZ end

					local position = (who == 2 and {get_car_oordinates(handle_fixview)} or who == 3 and {get_char_oordinates(handle_fixview)})
					angY = -(angleZ_test(position[1], position[2], position[3]))
				end

				if not active_fixview then
					offMouX, offMouY = getPcMouseMovement()
					offMouX, offMouY = offMouX / speed, offMouY / speed
					angZ, angY = angZ + offMouX, angY + offMouY

					if angZ > 360.0 then angZ = angZ - 360.0 end
					if angZ < 0.0 then angZ = angZ + 360.0 end

					if angY >= 4.7 then angY = 4.7 end
					if angY < -89.0 then angY = -89.0 end

					radZ, radY = math.rad(angZ), math.rad(angY)
					sinZ, cosZ = math.sin(radZ), math.cos(radZ)
					sinY, cosY = math.sin(radY), math.cos(radY)
					sinZ, cosZ = sinZ * cosY, cosZ * cosY
					sinZ, cosZ, sinY = sinZ * 1.0, cosZ * 1.0, sinY * 1.0
					poiX, poiY, poiZ = posX, posY, posZ
					poiX, poiY, poiZ = poiX + sinZ, poiY + cosZ, poiZ + sinY
					pointCameraAtPoint(poiX, poiY, poiZ, 2)
				end

				if keyPressed == 0 and isKeyDown(isKeys(config.keybind.hud)) then
					keyPressed = 1
					if radarHud == 0 then
						displayHud(true)
						radarHud = 1
						-- memory.setint8(pStSet + 47, 1) -- показать хп
						-- memory.setint8(pStSet + 56, 1) -- показать ник
						-- sampSetChatDisplayMode(2)
						-- memory.setuint8(sampGetBase() + 0x71480, 0x74, true)
						memory.setint32(0xBA676C, 0) -- включить радар(для лаунчера аризоны)
					else
						displayHud(false)
						radarHud = 0
						-- memory.setint8(pStSet + 47, 0) -- скрыть хп
						-- memory.setint8(pStSet + 56, 0)	-- скрыть ник
						-- memory.setuint8(sampGetBase() + 0x71480, 0xEB, true)
						memory.setint32(0xBA676C, 2) -- выключить радар(для лаунчера аризоны)
						-- sampSetChatDisplayMode(0)
					end
				end

				if wasKeyReleased(isKeys(config.keybind.hud)) and keyPressed == 1 then
					keyPressed = 0
				end

				if active and testCheat(config.MAIN.cmd) then
					active, draw, active_fixview, light_active, zone_active = false, false, false, false, false
					if flymode == 1 and not active then
						angPlZ, flymode, fov = -angZ, 0, standard_fov
						Reset()
					end
				end
			end
		else
			if active then
				active, draw, active_fixview, light_active, zone_active = false, false, false, false, false
				if flymode == 1 and not active then
					angPlZ, flymode, fov = -angZ, 0, standard_fov
					Reset()
				end
			end
		end
	end
end

function compass()
	while true do wait(0)
		if active and isCharInAnyCar(PLAYER_PED) and config.MAIN.vehicle[tostring(getCarModel(storeCarCharIsInNoSave(PLAYER_PED)))] ~= nil then
			local ac_pa = getAC_PA()
			local camDirection = math.round((math.atan2( (ac_pa[2][1]-ac_pa[1][1]), (ac_pa[2][2]-ac_pa[1][2]) ) * 180 / math.pi), 0)
			if camDirection <= 0 then camDirection = 360 + camDirection elseif camDirection >= 0 then camDirection = camDirection end

			local finalText, yaw = "", -camDirection

			for i = yaw - 120, yaw + 120 do
				local y = i if i >= 180 then y = -360 + i elseif i <= -180 then y = 360 + i end
				finalText = ((config.MAIN.language.compass == "RU" and compassTextRU[y] or compassTextEN[y]) and (config.MAIN.language.compass == "RU" and compassTextRU[y] or compassTextEN[y])..finalText) or " "..finalText
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

			local text1 = string.format("AIRCRAFT CAMERA %s %s", text_target, ((active_fixview ~= nil and text_target ~= "NO TARGET") and (active_fixview and ' ~g~LOCK' or ' ~r~LOCK') or "	"))
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

				if samp == 1 then
					local text6 = (text_target == "ON VEHICLE" and "LICENSE PLATE:" or "DATEBASE:")
					setText(test_text3[10], RusToGame(u8:decode(text6)), config.pos.info.x, config.pos.info.y+40, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

					local text7 = text_target == "ON VEHICLE" and string.format("%s", licenseplates(id_car)) or string.format("%s(%s)", id_nickname ~= -1 and GetName(id_nickname) or 'NO DATA', id_nickname)
					setText(test_text3[11], RusToGame(u8:decode(text7)), config.pos.info.x+(text_target == "ON VEHICLE" and 65 or 47), config.pos.info.y+40, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)

					if text_target == "ON VEHICLE" then
						local text8 = string.format("%s(%s)", id_nickname ~= -1 and GetName(id_nickname) or 'NO DATA', id_nickname)
						setText(test_text3[12], RusToGame(u8:decode("DRIVER:")), config.pos.info.x, config.pos.info.y+50, 0.2, 1.1, 2, 1, '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)
						setText(test_text3[13], RusToGame(u8:decode(text8)), config.pos.info.x+33, config.pos.info.y+50, 0.2, 1.1, 2, 1, id_nickname ~= -1 and '0xFF'..getPlayerColorHex(id_nickname) or '0xFFFFFFFF', 0.5, 0x15000000, 500, 500, false, true, true)
					end
				end
			end
		end
	end
end

function samp_handle()
	return getModuleHandle('samp.dll')
end

function samp_ver()
	local samp = samp_handle()
	local entry = samp ~= 0 and memory.getuint32((samp + memory.getint32(samp + 0x3C)) + 0x28)
	local samp_ver = (entry == 0x31DF13 and 'R1') or (entry == 0xCC4D0 and 'R3') or 'unknown'
	return samp_ver
end

function licenseplates(id)
	local plate
	if samp_handle() ~= 0 and samp_v ~= 'unknown' and id ~= -1 then
		plate = memory.tostring(memory.getint32(vehpool + 0x1134 + id * 4, false) + 0x93, 32, false)
	end
	return plate
end

function getCarID(handle)
	if samp_handle() ~= 0 and samp_v ~= 'unknown' then
		local id = ffi.cast('unsigned short (__thiscall *)(uintptr_t, uintptr_t)', samp_handle() + (samp_v == 'R1' and 0x1B0A0 or 0x1E440))(vehpool, getCarPointer(handle))
		if id ~= nil then
			return handle ~= -1 and id or -1
		end
	end
	return -1
end

function getPedID(handle)
	if samp_handle() ~= 0 and samp_v ~= 'unknown' then
		local id = ffi.cast('unsigned short (__thiscall *)(uintptr_t, uintptr_t)', samp_handle() + (samp_v == 'R1' and 0x10420 or 0x13570))(pedpool, getCharPointer(handle))
		if id ~= nil then
			return handle ~= -1 and id or -1
		end
	end
	return -1
end

function GetName(id)
	if samp_handle() ~= 0 and samp_v ~= 'unknown' then
		local nick = ffi.cast('const char*(__thiscall *)(uintptr_t, unsigned short)', samp_handle() + (samp_v == 'R1' and 0x13CE0 or 0x16F00))(pedpool, id)
		if nick ~= nil then
			return id ~= 65535 and ffi.string(nick) or -1
		end
	end
	return 'unknown'
end

function GetColorAsARGB(id)
	if samp_handle() ~= 0 and samp_v ~= 'unknown' then
		return memory.getint32(samp_handle() + (samp_v == 'R1' and 0x216378 or 0x151578) + id * 4)
	end
end

-- local blur = ffi.cast("void (*)(float)", 0x7030A0)

function mod(a, b)
	return a - (math.floor(a/b)*b)
end

function DEC_HEX(IN)
	local B, K, OUT, I, D= 16, "0123456789ABCDEF", "", 0
	while IN > 0 do
		I = I + 1
		IN, D = math.floor(IN / B), mod(IN, B) + 1
		OUT = string.sub(K, D, D)..OUT
	end
	return tonumber(OUT, 16)
end

function onD3DPresent()
	if draw then
		callFunction(0x007037C0, 2, 2, 0x30 + DEC_HEX(test_fov), 1)
		-- blur(test_fov/100)
	end
end

function getAC_PA()
	return {{getActiveCameraCoordinates()}, {getActiveCameraPointAt()}}
end

function getHexFromU32(hex)
	return string.sub(hex:reverse(), 3, 8)
end

function getPlayerColorHex(id)
	return ''..getHexFromU32(bit.tohex(GetColorAsARGB(id)))
end

function angleZ_test(x, y, z)
	local ac_pa = getAC_PA()
	local vect = {fX = ac_pa[1][1] - x, fY = ac_pa[1][2] - y, fZ = ac_pa[1][3] - z}
	local az = math.atan2(math.sqrt(vect.fX * vect.fX + vect.fY * vect.fY), vect.fZ)
	local camDirection = math.round((az * 180 / math.pi), 0)
	return (90 - camDirection)
end

function get_char_oordinates(hanlde)
	local res, x, y, z = copcall(getCharCoordinates, hanlde)
	return (res and x or 0), (res and y or 0), (res and z or 0)
end

function get_car_oordinates(hanlde)
	local res, x, y, z = copcall(getCarCoordinates, hanlde)
	return (res and x or 0), (res and y or 0), (res and z or 0)
end

function isKeys(key)
	return vkeys.name_to_id(key, true)
end

function getCarModelCornersIn2d(id, handle)-- https://www.blast.hk/threads/13380/post-925354 by chapo
	local x1, y1, z1, x2, y2, z2 = getModelDimensions(id)
	local t = {
	[1] = {getOffsetFromCarInWorldCoords(handle, x1 , y1 * -1.1, z1)},
	[2] = {getOffsetFromCarInWorldCoords(handle, x1 * -1.0 , y1 , z1)};}
	local xc = (t[1][1] + t[2][1])/ 2
	local yc = (t[1][2] + t[2][2])/ 2
	local zc = (t[1][3] + t[2][3])/ 2
	return xc, yc, zc
end

function setText(key, string, posX, posY, sX, sY, font, align, ARGB, sO, sARGB, wrapx, centresize, background, proportional, drawbeforefade)
	local a, sA = bit.band(bit.rshift(ARGB, 24), 0xFF), bit.band(bit.rshift(sARGB, 24), 0xFF)
	local r, sR = bit.band(bit.rshift(ARGB, 16), 0xFF), bit.band(bit.rshift(sARGB, 16), 0xFF)
	local g, sG = bit.band(bit.rshift(ARGB, 8), 0xFF), bit.band(bit.rshift(sARGB, 8), 0xFF)
	local b, sB = bit.band(ARGB, 0xFF), bit.band(sARGB, 0xFF)
	useRenderCommands(true)
	setTextScale(sX, sY)
	setTextColour(r, g, b, a)
	setTextEdge(sO, sR, sG, sB, sA)
	setTextDropshadow(sO, sR, sG, sB, sA)
	setTextFont(font)
	if align == 3 then
		setTextRightJustify(true)
	elseif align == 2 then
		setTextCentre(true)
	elseif align == 1 then
		setTextJustify(true)
	elseif align == 0 then
		setTextJustify(false)
		setTextCentre(false)
		setTextCentre(false)
	end
	setTextWrapx(wrapx)
	setTextCentreSize(centresize)
	setTextBackground(background)
	setTextProportional(proportional)
	setTextDrawBeforeFade(drawbeforefade)
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

function RusToGame(text)
	local convtbl = {[35]=35, [230]=155,[231]=159,[247]=164,[234]=107,[250]=144,[251]=168,[254]=171,[253]=170,[255]=172,[224]=97,[240]=112,[241]=99,[226]=162,[228]=154,[225]=151,[227]=153,[248]=165,[243]=121,[184]=101,[235]=158,[238]=111,[245]=120,[233]=157,[242]=166,[239]=163,[244]=152 ,[237]=174,[229]=101,[246]=160,[236]=175,[232]=156,[249]=161,[252]=169,[215]=141,[202]=75,[204]=77,[220]=146,[221]=147,[222]=148,[192]=65,[193]=128,[209]=67,[194]=139,[195]=130,[197]=69,[206]=79,[213]=88,[168]=69,[223]=149,[207]=140,[203]=135,[201]=133,[199]=136,[196]=131,[208]=80,[200]=133,[198]=132,[210]=143,[211]=89,[216]=142,[212]=129,[214]=137,[205]=72,[217]=138,[218]=167,[219]=145}
	local result = {}
	for i = 1, #text do
	local c = text:byte(i)
	result[i] = string.char(convtbl[c] or c)
	end
	return table.concat(result)
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

function fixed_camera_to_skin() -- проверка на приклепление камеры к скину
	return (memory.read(getModuleHandle('gta_sa.exe') + 0x76F053, 1, false) >= 1 and true or false)
end

function Reset()
	setNightVision(false)
	setInfraredVision(false)
	restoreCameraJumpcut()
	setCameraBehindPlayer()
	cameraSetLerpFov( standard_fov, standard_fov, 700, true)
end

addEventHandler('onScriptTerminate', function(scr, quitGame)
	if scr == script.this then
		for i, hook in ipairs(jmp_hook.hooks) do
			if hook.status then hook.stop() end
		end
		for i, free in ipairs(buff.free) do free() end
		if active then Reset() end
	end
end)

-- Licensed under the MIT License
-- Copyright (c) 2022, dmitriyewich <https://github.com/dmitriyewich/Helicopter-Camera>
