import re
import struct
import sys

opnames = [
    "MOVE", "LOADK", "LOADBOOL", "LOADNIL", "GETUPVAL", "GETGLOBAL", "GETTABLE",
    "SETGLOBAL", "SETUPVAL", "SETTABLE", "NEWTABLE", "SELF", "ADD", "SUB", "MUL",
    "DIV", "MOD", "POW", "UNM", "NOT", "LEN", "CONCAT", "JMP", "EQ", "LT", "LE",
    "TEST", "TESTSET", "CALL", "TAILCALL", "RETURN", "FORLOOP", "FORPREP",
    "TFORLOOP", "SETLIST", "CLOSE", "CLOSURE", "VARARG",
]


abxops = {"LOADK", "GETGLOBAL", "SETGLOBAL", "CLOSURE"}
asbxops = {"JMP", "FORLOOP", "FORPREP"}

maxargbx = (1 << 18) - 1
maxargsbx = maxargbx >> 1


class reader:
    def __init__(self, data):
        self.data = data
        self.pos = 0

    def bytes(self, n):
        b = self.data[self.pos:self.pos + n]
        self.pos += n
        return b

    def byte(self):
        b = self.data[self.pos]
        self.pos += 1
        return b

    def u32(self):
        v = struct.unpack_from("<I", self.data, self.pos)[0]
        self.pos += 4
        return v

    def i32(self):
        v = struct.unpack_from("<i", self.data, self.pos)[0]
        self.pos += 4
        return v

    def u64(self):
        v = struct.unpack_from("<Q", self.data, self.pos)[0]
        self.pos += 8
        return v

    def double(self):
        v = struct.unpack_from("<d", self.data, self.pos)[0]
        self.pos += 8
        return v

    def uint(self, width):
        fmt = {1: "<B", 2: "<H", 4: "<I", 8: "<Q"}[width]
        v = struct.unpack_from(fmt, self.data, self.pos)[0]
        self.pos += width
        return v

    def luastring(self, header):
        size = self.uint(header["szsizet"])
        if size == 0:
            return None
        s = self.bytes(size)
        return s[:-1]


class instr:
    __slots__ = ("op", "opname", "a", "b", "c", "bx", "sbx", "raw")

    def __repr__(self):
        if self.opname in abxops:
            return f"{self.opname} A={self.a} Bx={self.bx}"
        if self.opname in asbxops:
            return f"{self.opname} A={self.a} sBx={self.sbx}"
        return f"{self.opname} A={self.a} B={self.b} C={self.c}"


def decodeinstr(word):
    op = word & 0x3F
    a = (word >> 6) & 0xFF
    c = (word >> 14) & 0x1FF
    b = (word >> 23) & 0x1FF
    bx = (word >> 14) & 0x3FFFF
    sbx = bx - maxargsbx
    ins = instr()
    ins.op = op
    ins.opname = opnames[op] if op < len(opnames) else f"OP{op}"
    ins.a = a
    ins.b = b
    ins.c = c
    ins.bx = bx
    ins.sbx = sbx
    ins.raw = word
    return ins


class proto:
    def __init__(self):
        self.source = None
        self.linedefined = 0
        self.lastlinedefined = 0
        self.nups = 0
        self.numparams = 0
        self.is_vararg = 0
        self.maxstacksize = 0
        self.code = []
        self.consts = []
        self.protos = []
        self.lines = []
        self.locals = []
        self.upvalnames = []


def readheader(r):
    sig = r.bytes(4)
    assert sig == b"\x1bLua", f"bad signature {sig!r}"
    version = r.byte()
    fmt = r.byte()
    endian = r.byte()
    szint = r.byte()
    szsizet = r.byte()
    szinstr = r.byte()
    sznumber = r.byte()
    integral = r.byte()
    return dict(version=version, fmt=fmt, endian=endian, szint=szint,
                szsizet=szsizet, szinstr=szinstr, sznumber=sznumber,
                integral=integral)


def readconst(r, header):
    t = r.byte()
    if t == 0:
        return None
    if t == 1:
        return bool(r.byte())
    if t == 3:
        if header["integral"]:
            return r.u64() if header["sznumber"] == 8 else r.i32()
        return r.double()
    if t == 4:
        return r.luastring(header)
    raise ValueError(f"unknown const type {t}")


def readproto(r, header):
    szint = header["szint"]
    p = proto()
    p.source = r.luastring(header)
    p.linedefined = r.uint(szint)
    p.lastlinedefined = r.uint(szint)
    p.nups = r.byte()
    p.numparams = r.byte()
    p.is_vararg = r.byte()
    p.maxstacksize = r.byte()

    n = r.uint(szint)
    for round in range(n):
        word = r.u32()
        p.code.append(decodeinstr(word))

    n = r.uint(szint)
    for round in range(n):
        p.consts.append(readconst(r, header))

    n = r.uint(szint)
    for round in range(n):
        p.protos.append(readproto(r, header))

    n = r.uint(szint)
    for round in range(n):
        p.lines.append(r.uint(szint))

    n = r.uint(szint)
    for round in range(n):
        name = r.luastring(header)
        startpc = r.uint(szint)
        endpc = r.uint(szint)
        p.locals.append((name, startpc, endpc))

    n = r.uint(szint)
    for round in range(n):
        p.upvalnames.append(r.luastring(header))

    return p


def load(path):
    data = open(path, "rb").read()
    r = reader(data)
    header = readheader(r)
    proto = readproto(r, header)
    return header, proto


def walk(proto, depth=0, path=""):
    yield path, proto
    for i, child in enumerate(proto.protos):
        yield from walk(child, depth + 1, path + "." + str(i))


identre = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
globalops = {"GETGLOBAL", "SETGLOBAL"}


def findbadglobalnames(proto, acc=None):
    if acc is None:
        acc = set()
    for ins in proto.code:
        if ins.opname in globalops and ins.bx < len(proto.consts):
            name = proto.consts[ins.bx]
            if isinstance(name, bytes):
                text = name.decode("utf-8", "surrogateescape")
                if not identre.match(text):
                    acc.add(text)
    for child in proto.protos:
        findbadglobalnames(child, acc)
    return acc


if __name__ == "__main__":
    header, root = load(sys.argv[1])
    print("header", header)
    total = 0
    for path, p in walk(root):
        total += 1
    print("total protos:", total)

