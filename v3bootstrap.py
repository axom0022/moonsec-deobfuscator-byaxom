import os
import sys

from luaparser import ast as L

import luasubset as LS


def find_first(node, typename):
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, list):
            stack.extend(reversed(n))
            continue
        if not hasattr(n, "__dict__") or type(n).__module__ != "luaparser.astnodes":
            continue
        if type(n).__name__ == typename:
            return n
        kids = []
        for k, v in vars(n).items():
            if k.startswith("_"):
                continue
            if isinstance(v, list) or type(v).__module__ == "luaparser.astnodes":
                kids.append(v)
        stack.extend(reversed(kids))
    return None


def find_all(node, typename):
    out = []
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, list):
            stack.extend(reversed(n))
            continue
        if type(n).__module__ != "luaparser.astnodes":
            continue
        if type(n).__name__ == typename:
            out.append(n)
        for k, v in vars(n).items():
            if k.startswith("_"):
                continue
            if isinstance(v, list) or type(v).__module__ == "luaparser.astnodes":
                stack.append(v)
    return out


def decode_blob(seed, text):
    alphabet = text[:16]
    index = {c: i for i, c in enumerate(alphabet)}
    data = text[16:]
    r = seed
    f = seed
    out = []
    for i in range(0, len(data) - 1, 2):
        v = index.get(data[i], 0) * 16 + index.get(data[i + 1], 0)
        out.append(chr(int((v + f) % 256)))
        f = r + f
    return "".join(out)


def _is_decode_call(call):
    if type(call.func).__name__ != "Name" or len(call.args) != 2:
        return False
    a0, a1 = call.args
    return (type(a0).__name__ == "Name" and type(a1).__name__ == "String"
            and len(a1.raw) > 200)


def bootstrap_scope(path):
    src = open(path, encoding="latin-1").read()
    import astcache
    tree = astcache.parse(src)
    ret = None
    for st in tree.body.body:
        if type(st).__name__ == "Return":
            ret = st
            break
    if ret is None:
        raise SystemExit("no top-level return found")
    anon = find_first(ret.values, "AnonymousFunction")
    if anon is None:
        raise SystemExit("no entry function in top-level return")
    stmts = anon.body.body
    site = None
    for i, st in enumerate(stmts):
        for call in find_all(st, "Call"):
            if _is_decode_call(call):
                site = (i, call)
                break
        if site:
            break
    if site is None:
        raise SystemExit("no decode call found in bootstrap")
    gi, decode = site

    it = LS.Interp()
    root = LS.Scope(None)
    root.vars["..."] = []
    root.vars["o"] = None
    fin = it.exec_block(stmts[:gi], root, new_scope=False)

    seedname = decode.args[0].id
    text = LS.unescape_raw(decode.args[1].raw)
    return it, fin, text, seedname, decode.func.id


def main(path):
    it, fin, text, seedname, decname = bootstrap_scope(path)
    seed = it.lookup_name(seedname, fin)
    if not isinstance(seed, float):
        raise SystemExit("seed is not a number: %r" % (seed,))
    seedint = int(seed)
    blob = decode_blob(seedint, text)
    return blob


def static_blob(path):
    import threading
    sys.setrecursionlimit(1000000)
    threading.stack_size(512 * 1024 * 1024)
    box = {}

    def target():
        try:
            box["out"] = main(path)
        except BaseException as e:
            box["err"] = e

    t = threading.Thread(target=target)
    t.start()
    t.join()
    if "err" in box:
        raise box["err"]
    return box["out"]


if __name__ == "__main__":
    out = static_blob(sys.argv[1])
    if len(sys.argv) > 2:
        open(sys.argv[2], "w", encoding="latin-1").write(out)
