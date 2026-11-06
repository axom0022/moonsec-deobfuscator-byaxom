import re
import subprocess
import os
import json

TOOLSDIR = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools"))
LUAU = os.path.join(TOOLSDIR, "luau")

def findsignature(src):
    m = re.search(r"return\s+(\w+)\((\w+)\(\),\{\},(\w+)\(\)\)\(\)", src)
    if not m:
        raise RuntimeError("tailpatternnotfound")
    pname, lname, tname = m.groups()
    return pname, lname, tname, m.start(), m.end()

def capturesource(targetpath):
    src = open(targetpath, encoding="utf-8").read()
    pname, lname, tname, sigstart, sigend = findsignature(src)
    replacement = "oracledispatch=" + pname + ";oracleenvfn=" + tname + ";"
    patched = src[:sigstart] + replacement + src[sigend:]
    return patched, pname, lname, tname

def luaquote(s):
    out = ['"']
    for ch in s:
        o = ord(ch)
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif o < 32 or o > 126:
            out.append("\\%d" % o)
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)

def luaval(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return repr(v)
    if isinstance(v, str):
        return luaquote(v)
    if v is None:
        return "nil"
    raise RuntimeError("unsupported value " + repr(v))

def buildinstrtable(varname, instrs):
    parts = [varname + "={}"]
    for idx, fields in enumerate(instrs, start=1):
        fieldparts = []
        for fi, fv in enumerate(fields, start=1):
            if fv is not None:
                fieldparts.append("[" + str(fi) + "]=" + luaval(fv))
        parts.append(varname + "[%d]={%s}" % (idx, ",".join(fieldparts)))
    return ";".join(parts)

def buildproto(varname, instrs, protos=None, numparams=0, upvalnames=None):
    protos = protos or {}
    upvalnames = upvalnames or {}
    lines = []
    lines.append(buildinstrtable(varname + "t", instrs))
    lines.append(varname + "h={}")
    for k, v in protos.items():
        lines.append(varname + "h[%d]=%s" % (k, v))
    lines.append(varname + "n={}")
    lines.append(varname + "=" + "{" + varname + "t," + varname + "h," + str(numparams) + "," + varname + "n}")
    return ";".join(lines)

def runtest(targetpath, testluacode, workdir, extraglobals=None, label=""):
    patched, pname, lname, tname = capturesource(targetpath)
    extraglobals = extraglobals or {}
    setupglobals = ";".join(k + "=" + luaval(v) for k, v in extraglobals.items())
    combined = patched + "\n" + setupglobals + "\n" + testluacode
    path = os.path.join(workdir, "oracletest_" + (label or "x") + ".lua")
    open(path, "w", encoding="utf-8").write(combined)
    result = subprocess.run([LUAU, path], capture_output=True, text=True, timeout=30)
    return result.stdout, result.stderr

if __name__ == "__main__":
    import sys
    target = sys.argv[1]
    workdir = sys.argv[2] if len(sys.argv) > 2 else "/tmp"
    patched, pname, lname, tname = capturesource(target)
    print("captured dispatcher:", pname, "decoder:", lname, "envfn:", tname)
