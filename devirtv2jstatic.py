import json
import os
import re
import subprocess
import sys
import threading

import luasubset as LS
import devirtv2jinterp as J

HERE = os.path.dirname(os.path.abspath(__file__))
LUAU_AST = os.path.abspath(os.path.join(HERE, "..", "tools", "luau-ast"))


def findsignature(src):
    m = re.search(r"return\s+(\w+)\((\w+)\(\),\{\},(\w+)\(\)\)\(\)", src)
    if not m:
        raise RuntimeError("tail pattern not found")
    pname, lname, tname = m.groups()
    m2 = re.search(r"local function " + re.escape(pname) + r"\((\w+),(\w+),(\w+)\)", src)
    if not m2:
        raise RuntimeError("dispatcher not found")
    return pname, lname, tname, m2.group(1)


def parse_ast(path):
    r = subprocess.run([LUAU_AST, path], capture_output=True, timeout=120)
    if r.returncode != 0:
        raise RuntimeError("luau-ast failed: %s" % r.stderr[:300])
    return json.loads(r.stdout.decode("utf-8", errors="surrogateescape"))


def _num(v):
    if isinstance(v, float) and v.is_integer():
        return int(v)
    return v


def to_json_value(v, depth=0):
    if depth > 200:
        return None
    if isinstance(v, LS.LuaTable):
        out = {}
        for k, x in v.hash.items():
            key = k[1] if isinstance(k, tuple) and k and k[0] == "__bool__" else k
            if isinstance(key, bool):
                skey = "true" if key else "false"
            elif isinstance(key, float):
                skey = str(_num(key))
            else:
                skey = str(key)
            out[skey] = to_json_value(x, depth + 1)
        return out
    if isinstance(v, bool) or v is None:
        return v
    if isinstance(v, (int, float)):
        return _num(float(v))
    if isinstance(v, str):
        return v
    return "<function>"


def extract(target_path, workdir=None):
    src = open(target_path, "rb").read().decode("latin-1")
    pname, lname, tname, _protoarg = findsignature(src)
    tree = parse_ast(target_path)
    result = {}

    def go():
        try:
            proto = J.dispatcher_result(tree, pname, max_steps=200_000_000)
            result["proto"] = to_json_value(proto)
        except Exception as e:
            result["error"] = "%s: %s" % (type(e).__name__, str(e)[:500])

    sys.setrecursionlimit(1_000_000)
    threading.stack_size(512 * 1024 * 1024)
    th = threading.Thread(target=go)
    th.start()
    th.join()
    if "error" in result:
        raise RuntimeError(result["error"])
    return {"dispatcher": pname, "decoder": lname, "envfn": tname, "proto": result["proto"]}


def library_matches(target_path, names):
    import devirtv2statictable as st
    src = open(target_path, "rb").read().decode("latin-1")
    pname, _, _, _ = findsignature(src)
    tree = parse_ast(target_path)
    result = {}

    def go():
        try:
            result["m"] = J.library_matches(tree, pname, list(names), st.LIBCANDIDATES)
        except Exception as e:
            result["error"] = "%s: %s" % (type(e).__name__, str(e)[:500])

    sys.setrecursionlimit(1_000_000)
    threading.stack_size(512 * 1024 * 1024)
    th = threading.Thread(target=go)
    th.start()
    th.join()
    if "error" in result:
        raise RuntimeError(result["error"])
    return result["m"]


if __name__ == "__main__":
    info = extract(sys.argv[1])
    p = info["proto"]
    print("dispatcher", info["dispatcher"], "decoder", info["decoder"], "envfn", info["envfn"])
    if isinstance(p, dict):
        for k in sorted(p.keys()):
            v = p[k]
            if isinstance(v, dict):
                print(" key", k, "-> object with", len(v), "entries")
            else:
                print(" key", k, "->", type(v).__name__, str(v)[:80])
