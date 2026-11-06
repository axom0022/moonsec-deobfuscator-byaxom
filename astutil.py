import json

def load(path):
    data = open(path, encoding="utf-8", errors="replace").read()
    return json.loads(data)

def walk(node, cb, path=()):
    if isinstance(node, dict):
        if "type" in node:
            cb(node, path)
        for k, v in node.items():
            walk(v, cb, path + (k,))
    elif isinstance(node, list):
        for i, v in enumerate(node):
            walk(v, cb, path + (i,))

def findall(node, typename):
    out = []
    def cb(n, p):
        if n.get("type") == typename:
            out.append(n)
    walk(node, cb)
    return out

def bytecoltochar(line, bytecol):
    total = 0
    for i, ch in enumerate(line):
        if total >= bytecol:
            return i
        total += len(ch.encode("utf-8"))
    return len(line)

def locoffset(src, locstr):
    line, col = locstr.split(",")
    line = int(line)
    col = int(col)
    lines = src.split("\n")
    offset = sum(len(l) + 1 for l in lines[:line])
    offset += bytecoltochar(lines[line], col)
    return offset

def locrange(locstr):
    a, b = locstr.split(" - ")
    return a, b
