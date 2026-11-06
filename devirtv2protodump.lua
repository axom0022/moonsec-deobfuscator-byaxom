local function esc(s)
  local out = {}
  for i = 1, #s do
    local b = s:byte(i)
    if b == 34 then
      out[#out + 1] = '\\"'
    elseif b == 92 then
      out[#out + 1] = "\\\\"
    elseif b == 10 then
      out[#out + 1] = "\\n"
    elseif b == 13 then
      out[#out + 1] = "\\r"
    elseif b == 9 then
      out[#out + 1] = "\\t"
    elseif b < 32 or b > 126 then
      out[#out + 1] = string.format("\\u%04x", b)
    else
      out[#out + 1] = string.char(b)
    end
  end
  return table.concat(out)
end

local parts = {}

local function dump(v, seen)
  seen = seen or {}
  local t = type(v)
  if t == "table" then
    if seen[v] then
      parts[#parts + 1] = '"<cycle>"'
      return
    end
    seen[v] = true
    parts[#parts + 1] = "{"
    local first = true
    local keys = {}
    for k in pairs(v) do
      keys[#keys + 1] = k
    end
    table.sort(keys, function(x, y) return tostring(x) < tostring(y) end)
    for _, k in ipairs(keys) do
      if not first then parts[#parts + 1] = "," end
      first = false
      parts[#parts + 1] = '"' .. esc(tostring(k)) .. '":'
      dump(v[k], seen)
    end
    parts[#parts + 1] = "}"
  elseif t == "string" then
    parts[#parts + 1] = '"' .. esc(v) .. '"'
  elseif t == "number" then
    parts[#parts + 1] = tostring(v)
  elseif t == "boolean" then
    parts[#parts + 1] = tostring(v)
  elseif t == "function" then
    parts[#parts + 1] = '"<function>"'
  else
    parts[#parts + 1] = "null"
  end
end

moonsecv2dumpandstop = function(proto)
  dump(proto)
  print("---DEVIRTV2DUMPSTART---")
  print(table.concat(parts))
  print("---DEVIRTV2DUMPEND---")
  error("stoppedafterdump")
end
