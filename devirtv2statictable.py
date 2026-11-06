import subprocess
import json
import sys
import os

TOOLSDIR = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
LUAUAST = os.path.join(TOOLSDIR, "luau-ast")

class notfoldable(Exception):
    pass

def parseast(targetpath):
    r = subprocess.run([LUAUAST, targetpath], capture_output=True, timeout=30)
    text = r.stdout.decode("utf-8", errors="surrogateescape")
    return json.loads(text)

def findall(node, pred, acc=None):
    acc = acc if acc is not None else []
    if isinstance(node, dict):
        if pred(node):
            acc.append(node)
        for v in node.values():
            findall(v, pred, acc)
    elif isinstance(node, list):
        for v in node:
            findall(v, pred, acc)
    return acc

def localkey(localnode):
    return (localnode["name"], localnode["location"])

_rawsrccache = {}

def _loadrawsrc(path):
    cached = _rawsrccache.get(path)
    if cached is not None:
        return cached
    with open(path, "rb") as f:
        data = f.read()
    lines = data.split(b"\n")
    offsets = []
    acc = 0
    for l in lines:
        offsets.append(acc)
        acc += len(l) + 1
    cached = (data, offsets)
    _rawsrccache[path] = cached
    return cached

def _parseloc(loc):
    startpart, endpart = loc.split(" - ")
    sline, scol = (int(x) for x in startpart.split(","))
    eline, ecol = (int(x) for x in endpart.split(","))
    return sline, scol, eline, ecol

def rawtext(path, location):
    data, offsets = _loadrawsrc(path)
    sline, scol, eline, ecol = _parseloc(location)
    start = offsets[sline] + scol
    end = offsets[eline] + ecol
    return data[start:end].decode("utf-8", errors="surrogateescape")

class env:
    def __init__(self, parent=None):
        self.parent = parent
        self.vals = {}

    def get(self, key):
        e = self
        while e is not None:
            if key in e.vals:
                return e.vals[key]
            e = e.parent
        raise notfoldable("unbound " + str(key))

    def set(self, key, value):
        self.vals[key] = value

    def child(self):
        return env(self)

def truthy(v):
    return not (v is None or v is False)

def foldexpr(node, e):
    t = node["type"]
    if t == "AstExprConstantNumber":
        return node["value"]
    if t == "AstExprConstantString":
        return node["value"]
    if t == "AstExprConstantBool":
        return node["value"]
    if t == "AstExprConstantNil":
        return None
    if t == "AstExprGroup":
        return foldexpr(node["expr"], e)
    if t == "AstExprLocal":
        v = e.get(localkey(node["local"]))
        if v is UNRESOLVED:
            raise notfoldable("unresolved local")
        return v
    if t == "AstExprUnary":
        op = node["op"]
        if op == "Len" and node["expr"]["type"] == "AstExprTable":
            return sum(1 for it in node["expr"]["items"] if it["kind"] == "item")
        v = foldexpr(node["expr"], e)
        if op == "Minus":
            return -v
        if op == "Not":
            return not truthy(v)
        if op == "Len" and isinstance(v, str):
            return len(v)
        raise notfoldable("unaryop " + op)
    if t == "AstExprBinary":
        op = node["op"]
        if op == "And":
            lv = foldexpr(node["left"], e)
            if not truthy(lv):
                return lv
            return foldexpr(node["right"], e)
        if op == "Or":
            lv = foldexpr(node["left"], e)
            if truthy(lv):
                return lv
            return foldexpr(node["right"], e)
        lv = foldexpr(node["left"], e)
        rv = foldexpr(node["right"], e)
                                                                     
        if not (isinstance(lv, (int, float, str, bool))
                and isinstance(rv, (int, float, str, bool))):
            raise notfoldable("binopnonconstant " + str(op))
        if op == "Add":
            return lv + rv
        if op == "Sub":
            return lv - rv
        if op == "Mul":
            return lv * rv
        if op == "Div":
            return lv / rv
        if op == "FloorDiv":
            return lv // rv
        if op == "Mod":
            return lv - (lv // rv) * rv
        if op == "Pow":
            return lv ** rv
        if op == "Concat":
            return str(lv) + str(rv)
        if op == "CompareEq":
            return lv == rv
        if op == "CompareNe":
            return lv != rv
        if op == "CompareLt":
            return lv < rv
        if op == "CompareLe":
            return lv <= rv
        if op == "CompareGt":
            return lv > rv
        if op == "CompareGe":
            return lv >= rv
        raise notfoldable("binop " + op)
    if t == "AstExprIfElse":
        cv = foldexpr(node["condition"], e)
        if truthy(cv):
            return foldexpr(node["trueExpr"], e)
        return foldexpr(node["falseExpr"], e)
    if t == "AstExprTable":
        raise notfoldable("table literal")
    if t == "AstExprFunction":
        raise notfoldable("function literal")
    raise notfoldable("expr " + t)

def tryfold(node, e):
    try:
        return True, foldexpr(node, e)
    except notfoldable:
        return False, None

def processstat(node, e):
    t = node["type"]
    if t == "AstStatLocal":
        for var, val in zip(node["vars"], node.get("values", [])):
            ok, v = tryfold(val, e)
            e.set(localkey(var), v if ok else UNRESOLVED)
        for var in node["vars"][len(node.get("values", [])):]:
            e.set(localkey(var), UNRESOLVED)
        return
    if t == "AstStatAssign":
        for var, val in zip(node["vars"], node["values"]):
            if var["type"] == "AstExprLocal":
                ok, v = tryfold(val, e)
                e.set(localkey(var["local"]), v if ok else UNRESOLVED)
        return
    if t == "AstStatCompoundAssign":
        var = node["var"]
        if var["type"] == "AstExprLocal":
            synth = {"type": "AstExprBinary", "op": node["op"], "left": var, "right": node["value"]}
            ok, v = tryfold(synth, e)
            e.set(localkey(var["local"]), v if ok else UNRESOLVED)
        return

UNRESOLVED = object()

def scanforconsts(stmts, e):
    for s in stmts:
        processstat(s, e)

class dispatchmiss(Exception):
    pass

def resolvehandler(stmts, e):
    pending = []
    for s in stmts:
        t = s["type"]
        if t == "AstStatWhile":
            ok, cv = tryfold(s["condition"], e)
            if not ok:
                raise notfoldable("condition not foldable")
            if truthy(cv):
                pending.extend(resolvehandler(s["body"]["body"], e))
            continue
        if t == "AstStatBreak":
            continue
        processstat(s, e)
        pending.append(s)
    if pending:
        return pending
    raise dispatchmiss()

def bindaval(e, avalkey, avalue):
    e.set(avalkey, avalue)

def buildopcodetable(dispatchbody, avalkey, maxop, baseenv):
    table = {}
    for opval in range(0, maxop + 1):
        e = env(baseenv)
        e.set(avalkey, opval)
        try:
            handler = resolvehandler(dispatchbody, e)
            table[opval] = handler
        except (dispatchmiss, notfoldable):
            pass
    return table

def findenclosingblock(ast, funcname):
    found = []
    def walk(node):
        if isinstance(node, dict):
            if node.get("type") == "AstStatBlock":
                stmts = node["body"]
                for idx, s in enumerate(stmts):
                    if s["type"] == "AstStatLocalFunction" and s["name"]["name"] == funcname:
                        found.append((stmts, idx))
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)
    walk(ast)
    if not found:
        raise RuntimeError("enclosingblocknotfound " + funcname)
    return found[0]

def findenclosingscopes(ast, funcname):
    chain = []

    def walk(node):
        if isinstance(node, dict):
            if node.get("type") == "AstStatBlock":
                stmts = node["body"]
                for idx, s in enumerate(stmts):
                    if (s.get("type") == "AstStatLocalFunction"
                            and (s.get("name") or {}).get("name") == funcname):
                        chain.append((stmts, idx))
                        return True
            for v in node.values():
                if walk(v):
                    if node.get("type") == "AstStatBlock":
                        chain.append((node["body"], None))
                                                                         
                    return True
        elif isinstance(node, list):
            for v in node:
                if walk(v):
                    return True
        return False

    walk(ast)
    chain.reverse()
    return chain

def extractopcodetable(targetpath, pname, maxop=400):
    ast = parseast(targetpath)
    stmts, idx = findenclosingblock(ast, pname)
    baseenv = env()
                                                                          
    try:
        scopes = findenclosingscopes(ast, pname)
    except Exception:
        scopes = []
    for stmts2, idx2 in reversed(scopes):
        cand = stmts2 if idx2 is None else stmts2[:idx2]
        try:
            scanforconsts(cand, baseenv)
        except Exception:
            pass
    scanforconsts(stmts[:idx], baseenv)
    dispatchfunc = stmts[idx]["func"]
    dispatchargs = dispatchfunc["args"]
    einnerarg = dispatchargs[0]
    dispatchbody = dispatchfunc["body"]["body"]
    returnstmt = None
    for s in dispatchbody:
        if s["type"] == "AstStatReturn":
            returnstmt = s
    innerfunc = returnstmt["list"][0]
    while innerfunc["type"] == "AstExprGroup":
        innerfunc = innerfunc["expr"]
    innerbody = innerfunc["body"]["body"]
    mainwhile = None
    for s in innerbody:
        if s["type"] == "AstStatWhile" and s["condition"]["type"] == "AstExprConstantBool" and s["condition"]["value"] is True:
            mainwhile = s
    if mainwhile is None:
        raise RuntimeError("mainwhilenotfound")
    wbody = mainwhile["body"]["body"]
    denv = env(baseenv)
    scanforconsts(wbody[:3], denv)
    assignforopcode = wbody[1]
    opcodeexpr = assignforopcode["values"][0]
    opfieldidx = None
    if opcodeexpr["type"] == "AstExprIndexExpr":
        ok, v = tryfold(opcodeexpr["index"], denv)
        if ok:
            opfieldidx = v
    avar = wbody[1]["vars"][0]
    avalkey = localkey(avar["local"]) if avar["type"] == "AstExprLocal" else None
    dispatchwhiles = [s for s in wbody if s["type"] == "AstStatWhile"]
    table = buildopcodetable(wbody[3:], avalkey, maxop, denv)
    return {"table": table, "opfieldidx": opfieldidx, "numopslots": len(dispatchwhiles)}

def stmtkind(s):
    t = s["type"]
    if t == "AstStatAssign":
        return "assign"
    if t == "AstStatLocal":
        return "local"
    if t == "AstStatReturn":
        return "return"
    if t == "AstStatCompoundAssign":
        return "compound"
    if t == "AstStatExpr":
        return "exprstat"
    if t == "AstStatFor":
        return "for"
    if t == "AstStatForIn":
        return "forin"
    if t == "AstStatIf":
        return "if"
    if t == "AstStatDo":
        return "do"
    return t

LIBCANDIDATES = []
_LIBBASE = ["print", "type", "tostring", "tonumber", "pairs", "ipairs", "next", "select",
            "unpack", "rawget", "rawset", "rawequal", "rawlen", "setmetatable", "getmetatable",
            "pcall", "xpcall", "error", "assert", "loadstring", "load", "require",
            "collectgarbage", "newproxy", "gcinfo"]
for _b in _LIBBASE:
    LIBCANDIDATES.append(_b)
_LIBMODS = {
    "string": ["sub", "byte", "char", "format", "find", "gsub", "gmatch", "rep", "len",
               "upper", "lower", "reverse", "match", "split"],
    "table": ["insert", "remove", "concat", "sort", "unpack", "pack", "find", "create", "clear"],
    "math": ["floor", "ceil", "abs", "max", "min", "huge", "random", "randomseed", "sqrt",
             "fmod", "pow"],
    "os": ["time", "clock", "date"],
    "coroutine": ["create", "wrap", "resume", "yield", "status", "isyieldable"],
    "bit32": ["band", "bor", "bxor", "bnot", "lshift", "rshift", "arshift", "extract", "replace"],
}
for _lib, _fns in _LIBMODS.items():
    for _fn in _fns:
        LIBCANDIDATES.append(_lib + "." + _fn)

def identifylibraryfuncs(targetpath, pname, names, workdir="/tmp"):
    import devirtv2oracle as o
    src = open(targetpath, encoding="utf-8").read()
    pname2, lname, tname, protoarg, sigstart, sigend = o.findsignature(src) if False else (None,) * 6
                                                                                     
    import devirtv2extract as extr
    _, _, _, _, sigstart2, sigend2 = extr.findsignature(src)

    candnames = ",".join('"' + c + '"' for c in LIBCANDIDATES)
    candvals = ",".join(
        "(function() local ok,v=pcall(function() return " + c + " end) if ok then return v else return nil end end)()"
        for c in LIBCANDIDATES
    )
    localnames = ",".join('"' + n + '"' for n in names)
    localvals = ",".join(names)
    lines = []
    lines.append("local __candnames = {" + candnames + "}")
    lines.append("local __candvals = {" + candvals + "}")
    lines.append("local __localnames = {" + localnames + "}")
    lines.append("local __localvals = {" + localvals + "}")
    lines.append("""
local __result = {}
for li, lname2 in ipairs(__localnames) do
  local lv = __localvals[li]
  if type(lv) == "function" then
    for ci, cname in ipairs(__candnames) do
      local cv = __candvals[ci]
      if cv ~= nil and rawequal(lv, cv) then
        __result[lname2] = cname
        break
      end
    end
  end
end
print("---LIBMATCHSTART---")
local parts = {}
for k,v in pairs(__result) do parts[#parts+1] = '"'..k..'":"'..v..'"' end
print("{" .. table.concat(parts, ",") .. "}")
print("---LIBMATCHEND---")
error("stoppedafterlibmatch")
""")
    injected = "\n".join(lines)
    patched = src[:sigend2] + injected + src[sigend2:]
    combinedpath = os.path.join(workdir, "libmatch_runtime.lua")
    open(combinedpath, "w", encoding="utf-8").write(patched)
    r = subprocess.run([LUAUAST.replace("luau-ast", "luau"), combinedpath],
                        capture_output=True, text=True, timeout=30)
    out = r.stdout
    import re
    m = re.search(r"---LIBMATCHSTART---\n(.*?)\n---LIBMATCHEND---", out, re.S)
    if not m:
        return {}
    return json.loads(m.group(1))

if __name__ == "__main__":
    path = sys.argv[1]
    import devirtv2oracle as o
    src = open(path, encoding="utf-8").read()
    pname, lname, tname, sstart, send = o.findsignature(src)
    result = extractopcodetable(path, pname)
    table = result["table"]
    print("resolved", len(table), "opcodes, op field idx", result["opfieldidx"], "num top slots", result["numopslots"])
    for k in sorted(table.keys()):
        kinds = [stmtkind(s) for s in table[k]]
        print(k, kinds)
