import re
import subprocess
import sys
import json
import os

def findsignature(src):
    m = re.search(r"return\s+(\w+)\((\w+)\(\),\{\},(\w+)\(\)\)\(\)", src)
    if not m:
        raise RuntimeError("tailpatternnotfound")
    pname, lname, tname = m.groups()
    m2 = re.search(r"local function " + re.escape(pname) + r"\((\w+),(\w+),(\w+)\)", src)
    if not m2:
        raise RuntimeError("dispatchernotfound")
    protoarg = m2.group(1)
    return pname, lname, tname, protoarg, m2.start(), m2.end()

def splice(src, protoarg, insertpos):
    injected = "moonsecv2dumpandstop(" + protoarg + ");"
    return src[:insertpos] + injected + src[insertpos:]

def extract(targetpath, workdir):
    src = open(targetpath, encoding="utf-8").read()
    pname, lname, tname, protoarg, sigstart, sigend = findsignature(src)
    patched = splice(src, protoarg, sigend)
    preamblepath = os.path.join(os.path.dirname(os.path.abspath(__file__)), "devirtv2probe.lua")
    preamble = open(preamblepath, encoding="utf-8").read()
    combined = preamble + "\n" + patched
    combinedpath = os.path.join(workdir, "combinedtarget.lua")
    open(combinedpath, "w", encoding="utf-8").write(combined)
    luaubin = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools", "luau")
    luaubin = os.path.abspath(luaubin)
    result = subprocess.run(
        [luaubin, combinedpath],
        capture_output=True, text=True, timeout=30
    )
    out = result.stdout
    m = re.search(r"---DEVIRTV2DUMPSTART---\n(.*)\n---DEVIRTV2DUMPEND---", out, re.S)
    if not m:
        raise RuntimeError("nodumpfound stdout=" + out[:2000] + " stderr=" + result.stderr[:2000])
    data = json.loads(m.group(1))
    return {"dispatcher": pname, "decoder": lname, "envfn": tname, "proto": data}

if __name__ == "__main__":
    targetpath = sys.argv[1]
    workdir = sys.argv[2] if len(sys.argv) > 2 else "/tmp"
    info = extract(targetpath, workdir)
    print("dispatcher", info["dispatcher"], "decoder", info["decoder"], "envfn", info["envfn"])
    proto = info["proto"]
    print("proto top-level keys/shape:")
    if isinstance(proto, dict):
        for k, v in sorted(proto.items(), key=lambda kv: kv[0]):
            if isinstance(v, dict):
                print(" key", k, "-> object with", len(v), "entries, keys sample", list(v.keys())[:8])
            else:
                print(" key", k, "->", type(v).__name__, v)
    else:
        print(proto)
