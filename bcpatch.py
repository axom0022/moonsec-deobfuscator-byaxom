import struct
import sys
import bcread


def encodeinstr(op, a=0, b=0, c=0, bx=None, sbx=None):
    if bx is not None:
        return (op & 0x3F) | ((a & 0xFF) << 6) | ((bx & 0x3FFFF) << 14)
    if sbx is not None:
        bxv = sbx + bcread.maxargsbx
        return (op & 0x3F) | ((a & 0xFF) << 6) | ((bxv & 0x3FFFF) << 14)
    return (op & 0x3F) | ((a & 0xFF) << 6) | ((c & 0x1FF) << 14) | ((b & 0x1FF) << 23)


returnop = bcread.opnames.index("RETURN")

rkbothops = {"ADD", "SUB", "MUL", "DIV", "MOD", "POW", "EQ", "LT", "LE", "SETTABLE"}
rkconlyops = {"GETTABLE", "SELF"}
placeholdertext = b"<unrecoverable constant (upstream devirtualizer bug)>"


def fixbadconstrefs(proto):
    placeholderidx = None
    fields = []
    for ins in proto.code:
        if ins.opname in rkbothops:
            fields.append((ins, "b"))
            fields.append((ins, "c"))
        elif ins.opname in rkconlyops:
            fields.append((ins, "c"))
    for ins, field in fields:
        v = getattr(ins, field)
        if v < 256:
            continue
        k = v - 256
        if k < len(proto.consts):
            continue
        if placeholderidx is None:
            proto.consts.append(placeholdertext)
            placeholderidx = len(proto.consts) - 1
        setattr(ins, field, 256 + placeholderidx)
    for child in proto.protos:
        fixbadconstrefs(child)


class writer:
    def __init__(self):
        self.buf = bytearray()

    def bytes(self, b):
        self.buf += b

    def u8(self, v):
        self.buf += struct.pack("<B", v & 0xFF)

    def u32(self, v):
        self.buf += struct.pack("<I", v & 0xFFFFFFFF)

    def i32(self, v):
        self.buf += struct.pack("<i", v)

    def u64(self, v):
        self.buf += struct.pack("<Q", v & 0xFFFFFFFFFFFFFFFF)

    def double(self, v):
        self.buf += struct.pack("<d", v)

    def uint(self, width, v):
        fmt = {1: "<B", 2: "<H", 4: "<I", 8: "<Q"}[width]
        self.buf += struct.pack(fmt, v & ((1 << (width * 8)) - 1))

    def luastring(self, header, s):
        if s is None:
            self.uint(header["szsizet"], 0)
            return
        data = s + b"\x00"
        self.uint(header["szsizet"], len(data))
        self.bytes(data)


def writeheader(w, header):
    w.bytes(b"\x1bLua")
    w.u8(header["version"])
    w.u8(header["fmt"])
    w.u8(header["endian"])
    w.u8(header["szint"])
    w.u8(header["szsizet"])
    w.u8(header["szinstr"])
    w.u8(header["sznumber"])
    w.u8(header["integral"])


def writeconst(w, header, v):
    if v is None:
        w.u8(0)
    elif isinstance(v, bool):
        w.u8(1)
        w.u8(1 if v else 0)
    elif isinstance(v, (int, float)):
        w.u8(3)
        if header["integral"]:
            if header["sznumber"] == 8:
                w.u64(int(v))
            else:
                w.i32(int(v))
        else:
            w.double(float(v))
    elif isinstance(v, bytes):
        w.u8(4)
        w.luastring(header, v)
    else:
        raise ValueError(f"unknown const {v!r}")


def ensuretrailingreturn(proto):
    code = proto.code
    needs = True
    if code:
        last = code[-1]
        if last.opname == "RETURN" and last.b == 1:
            needs = False
    if needs:
        word = encodeinstr(returnop, a=0, b=1, c=0)
        ins = bcread.decodeinstr(word)
        proto.code.append(ins)
        if proto.lines:
            proto.lines.append(proto.lines[-1] if proto.lines else 0)


def writeproto(w, header, proto, fixup=True):
    if fixup:
        ensuretrailingreturn(proto)
        for child in proto.protos:
            pass

    szint = header["szint"]
    w.luastring(header, proto.source)
    w.uint(szint, proto.linedefined)
    w.uint(szint, proto.lastlinedefined)
    w.u8(proto.nups)
    w.u8(proto.numparams)
    w.u8(proto.is_vararg)
    w.u8(proto.maxstacksize)

    w.uint(szint, len(proto.code))
    for ins in proto.code:
        if ins.opname in bcread.abxops:
            word = encodeinstr(ins.op, a=ins.a, bx=ins.bx)
        elif ins.opname in bcread.asbxops:
            word = encodeinstr(ins.op, a=ins.a, sbx=ins.sbx)
        else:
            word = encodeinstr(ins.op, a=ins.a, b=ins.b, c=ins.c)
        w.u32(word)

    w.uint(szint, len(proto.consts))
    for c in proto.consts:
        writeconst(w, header, c)

    w.uint(szint, len(proto.protos))
    for child in proto.protos:
        writeproto(w, header, child, fixup=fixup)

    w.uint(szint, len(proto.lines))
    for ln in proto.lines:
        w.uint(szint, ln)

    w.uint(szint, len(proto.locals))
    for name, startpc, endpc in proto.locals:
        w.luastring(header, name)
        w.uint(szint, startpc)
        w.uint(szint, endpc)

    w.uint(szint, len(proto.upvalnames))
    for name in proto.upvalnames:
        w.luastring(header, name)


def fixwatermarkconst(root, truewatermark):
    underscoreidx = None
    for i, c in enumerate(root.consts):
        if c == b"_":
            underscoreidx = i
            break
    if underscoreidx is None:
        return
    targetreg = None
    for ins in root.code:
        if ins.opname == "GETGLOBAL" and ins.bx == underscoreidx:
            targetreg = ins.a
            break
    if targetreg is None:
        return
    for ins in root.code:
        if ins.opname == "EQ" and (ins.b == targetreg or ins.c == targetreg):
            for field in ("b", "c"):
                v = getattr(ins, field)
                if v >= 256:
                    k = v - 256
                    if k < len(root.consts) and isinstance(root.consts[k], bytes):
                        if root.consts[k] != truewatermark:
                            root.consts[k] = truewatermark
                    return


def patchfile(inpath, outpath, truewatermark=None):
    header, root = bcread.load(inpath)
    fixbadconstrefs(root)
    if truewatermark is not None:
        fixwatermarkconst(root, truewatermark)
    w = writer()
    writeheader(w, header)
    writeproto(w, header, root, fixup=True)
    open(outpath, "wb").write(bytes(w.buf))


if __name__ == "__main__":
    patchfile(sys.argv[1], sys.argv[2])
    print("wrote", sys.argv[2])

