local realprint = print
local realpcall = pcall
local realxpcall = xpcall
local realtostring = tostring
local realtype = type
local realpairs = pairs
local realipairs = ipairs
local realselect = select
local realsetmetatable = setmetatable
local realrawequal = rawequal
local realconcat = table.concat
local realsort = table.sort

local function serialize(v, seen)
  seen = seen or {}
  local t = realtype(v)
  if t == "table" then
    if seen[v] then return "<cycle>" end
    seen[v] = true
    local keys = {}
    for k in realpairs(v) do keys[#keys + 1] = k end
    realsort(keys, function(a, b) return realtostring(a) < realtostring(b) end)
    local parts = {}
    for _, k in realipairs(keys) do
      parts[#parts + 1] = realtostring(k) .. "=" .. serialize(v[k], seen)
    end
    return "{" .. realconcat(parts, ", ") .. "}"
  else
    return realtostring(v)
  end
end

local function log(...)
  local parts = {}
  for i = 1, realselect("#", ...) do
    parts[i] = realtostring((realselect(i, ...)))
  end
  realprint("ORACLELOG\tpc=" .. realtostring(oraclepc) .. "\top=" .. realtostring(oracleopcode) .. "\t" .. realconcat(parts, "\t"))
end

local function mkproxy(path)
  local self
  self = realsetmetatable({}, {
    __index = function(_, k)
      log("GET", path .. "." .. realtostring(k))
      return mkproxy(path .. "." .. realtostring(k))
    end,
    __newindex = function(_, k, v)
      log("SET", path .. "." .. realtostring(k), serialize(v))
    end,
    __call = function(_, ...)
      local args = {}
      for i = 1, realselect("#", ...) do
        args[i] = serialize((realselect(i, ...)))
      end
      log("CALL", path, realconcat(args, ", "))
      return mkproxy(path .. "()")
    end,
    __tostring = function() return "<proxy:" .. path .. ">" end,
    __eq = function(a, b) return realrawequal(a, b) end,
  })
  return self
end

game = mkproxy("game")
Enum = mkproxy("Enum")
workspace = mkproxy("workspace")
script = mkproxy("script")
print = function(...)
  local parts = {}
  for i = 1, realselect("#", ...) do
    parts[i] = realtostring((realselect(i, ...)))
  end
  log("PRINT", realconcat(parts, " "))
end
setclipboard = function(t) log("SETCLIPBOARD", realtostring(t)) end
loadstring = function(src)
  log("LOADSTRING", realtostring(src))
  return function(...) log("LOADSTRING_RESULT_CALLED"); return mkproxy("loadedlib") end
end
wait = function(...) log("WAIT") end
spawn = function(f) log("SPAWN"); if f then f() end end
delay = function(t, f) log("DELAY", realtostring(t)); if f then f() end end
tick = function() log("TICK"); return 0 end
getgenv = function() log("GETGENV"); return {} end
oracletrace = log
