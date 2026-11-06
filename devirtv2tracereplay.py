import re
import subprocess
import sys
import os
import json
import devirtv2oracle as o
import devirtv2extract as d
from astutil import load, findall, locoffset, locrange

def findloopinsertoffset(astpath, src):
    ast = load(astpath)
    funcs = findall(ast, "AstExprFunction")
    for cand in funcs:
        if len(cand.get("args", [])) == 3:
            main = cand
            break
    else:
        raise RuntimeError("mainfuncnotfound")
    body = main["body"]["body"]
    pfunc = None
    for st in body:
        if st["type"] == "AstStatLocalFunction":
            inner = findall(st, "AstExprFunction")
            if len(inner) >= 2 and len(inner[1].get("args", [])) == 0:
                retbody = inner[1]["body"]["body"]
                if retbody and retbody[-1]["type"] == "AstStatWhile":
                    pfunc = st
                    break
    if pfunc is None:
        raise RuntimeError("dispatchernotfound")
    fn = findall(pfunc, "AstExprFunction")
    inner = fn[1]
    innerbody = inner["body"]["body"]
    wh = innerbody[-1]
    loopbody = wh["body"]["body"]
    pcassignstmt = loopbody[0]
    opassignstmt = loopbody[1]
    pcname = pcassignstmt["values"][0]["index"]["local"]["name"]
    opname = opassignstmt["vars"][0]["local"]["name"]
    _, end = locrange(opassignstmt["location"])
    off = locoffset(src, end)
    return off, pcname, opname

def serialize(name, protodict, out):
    instrs = protodict["1"]
    n = len(instrs)
    lines = [name + "t={}"]
    for i in range(1, n + 1):
        instr = instrs[str(i)]
        fields = []
        for fi in range(1, 5):
            k = str(fi)
            if k in instr:
                fields.append("[%d]=%s" % (fi, o.luaval(instr[k])))
        lines.append(name + "t[%d]={%s}" % (i, ",".join(fields)))
    protos = protodict["2"]
    lines.append(name + "h={}")
    for k, v in protos.items():
        subname = name + "p" + str(k)
        serialize(subname, v, lines)
        lines.append(name + "h[%s]=%s" % (k, subname))
    lines.append(name + "n={}")
    numparams = protodict["3"]
    lines.append(name + "=" + "{" + name + "t," + name + "h," + str(numparams) + "," + name + "n}")
    out.extend(lines)
    return out

def tracereplay(targetpath, workdir):
    src = open(targetpath, encoding="utf-8").read()
    astpath = os.path.join(workdir, "trace_ast.json")
    luauast = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools", "luau-ast")
    luauast = os.path.abspath(luauast)
    r = subprocess.run([luauast, targetpath], capture_output=True, encoding="utf-8", errors="replace", timeout=30)
    open(astpath, "w", encoding="utf-8", errors="replace").write(r.stdout)

    off, pcname, opname = findloopinsertoffset(astpath, src)
    traced = src[:off] + ("oraclepc=%s;oracleopcode=%s;" % (pcname, opname)) + src[off:]

    pname, lname, tname, sigstart, sigend = o.findsignature(traced)
    replacement = "oracledispatch=" + pname + ";oracleenvfn=" + tname + ";"
    patched = traced[:sigstart] + replacement + traced[sigend:]

    info = d.extract(targetpath, workdir)
    proto = info["proto"]
    lines = []
    serialize("u", proto, lines)
    protocode = ";".join(lines)

    mockpath = os.path.join(os.path.dirname(os.path.abspath(__file__)), "devirtv2mock.lua")
    mock = open(mockpath, encoding="utf-8").read()

    combined = patched + "\n" + mock + "\n" + protocode + """
local ok, result = realpcall(function()
    return oracledispatch(u, {}, oracleenvfn())()
end)
oracletrace("DONE", realtostring(ok), realtostring(result))
"""
    combinedpath = os.path.join(workdir, "tracereplay.lua")
    open(combinedpath, "w", encoding="utf-8").write(combined)
    luaubin = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools", "luau")
    luaubin = os.path.abspath(luaubin)
    r = subprocess.run([luaubin, combinedpath], capture_output=True, text=True, timeout=30)
    return r.stdout, r.stderr, info

if __name__ == "__main__":
    target = sys.argv[1]
    workdir = sys.argv[2] if len(sys.argv) > 2 else "/tmp"
    out, err, info = tracereplay(target, workdir)
    print(out)
    print("STDERR:", err)
