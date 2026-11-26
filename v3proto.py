import re
import struct


class V3Error(Exception):
    pass


_NUMTAG_RE = re.compile(
    r"==\s*1\s*\)\s*then\s*\w+\s*=\s*\(\s*\w+\s*\(\s*\)\s*~=\s*#\{\}\s*\)\s*;"
    r"\s*elseif\s*\(\s*\w+\s*==\s*(\d+)\s*\)\s*then\s*local\s+\w+\s*=\s*\w+\s*\(\s*\)"
)


def detect_numtag(src):
    m = _NUMTAG_RE.search(src)
    if m:
        return int(m.group(1))
    return None


def _u8(b, i):
    if i + 1 > len(b):
        raise V3Error("u8 past end at %d" % i)
    return b[i], i + 1


def _u16(b, i):
    if i + 2 > len(b):
        raise V3Error("u16 past end at %d" % i)
    return struct.unpack_from("<H", b, i)[0], i + 2


def _u32(b, i):
    if i + 4 > len(b):
        raise V3Error("u32 past end at %d" % i)
    return struct.unpack_from("<I", b, i)[0], i + 4


def _double(b, i):
    if i + 8 > len(b):
        raise V3Error("double past end at %d" % i)
    lo = struct.unpack_from("<I", b, i)[0]
    hi = struct.unpack_from("<I", b, i + 4)[0]
    return struct.unpack("<d", struct.pack("<II", lo, hi))[0], i + 8


def _bit(x, i, j=None):
    if j is None:
        j = i
    return (x >> (i - 1)) % (1 << (j - i + 1))


class Proto(object):
    def __init__(self):
        self.consts = []
        self.protos = []
        self.field3 = None
        self.instrs = []
        self.start = 0
        self.end = 0

    def ninstr(self):
        return len(self.instrs)

    def summary(self, depth=0):
        pad = "  " * depth
        out = []
        out.append("%sproto  consts=%d protos=%d field3=%s instrs=%d" % (
            pad, len(self.consts), len(self.protos), self.field3, len(self.instrs)))
        for p in self.protos:
            out.append(p.summary(depth + 1))
        return "\n".join(out)


def parse_proto(b, i, numtag=3, layout='protos_first', depth=0, maxdepth=64):
    if depth > maxdepth:
        raise V3Error("proto nesting too deep")
    p = Proto()
    p.start = i

    nconsts, i = _u32(b, i)
    if nconsts > 100000:
        raise V3Error("implausible nconsts=%d at %d" % (nconsts, i - 4))

    for _ in range(nconsts):
        t, i = _u8(b, i)
        if t == 0:
            ln, i = _u32(b, i)
            if ln > len(b) - i:
                raise V3Error("string len %d overruns at %d" % (ln, i))
            try:
                p.consts.append(b[i:i + ln].decode("utf-8"))
            except UnicodeDecodeError:
                p.consts.append(b[i:i + ln].decode("latin-1"))
            i += ln
        elif t == 1:
            v, i = _u8(b, i)
            p.consts.append(v != 0)
        elif t == numtag:
            v, i = _double(b, i)
            p.consts.append(v)
        else:
            p.consts.append(None)

    def read_protos(ii):
        nprotos, ii = _u32(b, ii)
        if nprotos > 10000:
            raise V3Error("implausible nprotos=%d at %d" % (nprotos, ii - 4))
        subs = []
        for _ in range(nprotos):
            sub, ii = parse_proto(b, ii, numtag, layout, depth + 1, maxdepth)
            subs.append(sub)
        return subs, ii

    def read_instrs(ii):
        ninstr, ii = _u32(b, ii)
        if ninstr > 200000:
            raise V3Error("implausible ninstr=%d at %d" % (ninstr, ii - 4))
        out = []
        for k in range(1, ninstr + 1):
            desc, ii = _u8(b, ii)
            if _bit(desc, 1) != 0:
                continue
            mode_b = _bit(desc, 2, 3)
            mode_c = _bit(desc, 4, 6)

            op, ii = _u16(b, ii)
            a, ii = _u16(b, ii)
            bv, cv = None, None

            if mode_b == 0:
                bv, ii = _u16(b, ii)
                cv, ii = _u16(b, ii)
            elif mode_b == 1:
                bv, ii = _u32(b, ii)
            elif mode_b == 2:
                bv, ii = _u32(b, ii)
                bv -= 65536
            elif mode_b == 3:
                bv, ii = _u32(b, ii)
                bv -= 65536
                cv, ii = _u16(b, ii)

            raw = (a, bv, cv)
            refs = []
            if _bit(mode_c, 1) == 1:
                refs.append("A")
                a = _const(p.consts, a)
            if _bit(mode_c, 2) == 1:
                refs.append("B")
                bv = _const(p.consts, bv)
            if _bit(mode_c, 3) == 1:
                refs.append("C")
                cv = _const(p.consts, cv)

            out.append({
                "op": op, "A": a, "B": bv, "C": cv,
                "mode_b": mode_b, "mode_c": mode_c,
                "raw": raw, "refs": refs, "pc": k,
            })
        return out, ii

    if layout == 'protos_first':
        p.protos, i = read_protos(i)
        p.field3, i = _u8(b, i)
        p.instrs, i = read_instrs(i)
    else:
        p.instrs, i = read_instrs(i)
        p.protos, i = read_protos(i)
        p.field3, i = _u8(b, i)

    p.end = i
    return p, i


def _const(consts, idx):
    if idx is None:
        return None
    if 1 <= idx <= len(consts):
        return consts[idx - 1]
    return idx


def parse_blob(b, numtag=None, layout=None, exact=True):
    tags = [numtag] if numtag is not None else [t for t in range(256) if t not in (0, 1)]
    lays = [layout] if layout is not None else ['protos_first', 'instrs_first']

    best = None
    for tg in tags:
        for ly in lays:
            try:
                pr, i = parse_proto(b, 0, tg, ly)
            except (V3Error, struct.error, IndexError, RecursionError):
                continue
            if i == len(b):
                return pr, i, tg, ly
            if best is None or i > best[1]:
                best = (pr, i, tg, ly)

    if best is not None and not exact:
        return best
    raise V3Error("no numtag/layout consumed the blob exactly (best=%s of %d)"
                  % (best[1] if best else "none", len(b)))


def walk(p, depth=0):
    yield depth, p
    for s in p.protos:
        for x in walk(s, depth + 1):
            yield x
