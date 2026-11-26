import re

import luasubset as LS

_CLS = {
    "a": "A-Za-z", "d": "0-9", "l": "a-z", "s": " \\t\\n\\r\\f\\v", "u": "A-Z",
    "w": "A-Za-z0-9", "x": "0-9A-Fa-f", "p": re.escape("!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~"),
    "c": "\\x00-\\x1f\\x7f", "g": "\\x21-\\x7e",
}


def _cls(ch, negate_ok=True):
    lo = ch.lower()
    if lo in _CLS:
        body = _CLS[lo]
        if ch.isupper():
            return "[^%s]" % body
        return "[%s]" % body
    return re.escape(ch)


def lua_pattern_to_re(pat):
    if pat.startswith("%b") or "%f" in pat:
        raise LS.LuaError("unsupported pattern item in %r" % pat)
    out = []
    i = 0
    anchored = pat.startswith("^")
    if anchored:
        i = 1
    n = len(pat)
    while i < n:
        c = pat[i]
        if c == "%":
            if i + 1 >= n:
                raise LS.LuaError("malformed pattern")
            nx = pat[i + 1]
            if nx.isdigit():
                out.append("\\%s" % nx)
            else:
                out.append(_cls(nx))
            i += 2
        elif c == "[":
            j = i + 1
            if j < n and pat[j] == "^":
                j += 1
            if j < n and pat[j] == "]":
                j += 1
            while j < n and pat[j] != "]":
                if pat[j] == "%" and j + 1 < n:
                    j += 2
                else:
                    j += 1
            if j >= n:
                raise LS.LuaError("malformed pattern (missing ']')")
            body = pat[i + 1:j]
            parts = []
            k = 0
            neg = body.startswith("^")
            if neg:
                body = body[1:]
            while k < len(body):
                if body[k] == "%" and k + 1 < len(body):
                    ch = body[k + 1]
                    lo = ch.lower()
                    if lo in _CLS:
                        parts.append(_CLS[lo] if ch.islower() else "")
                        if ch.isupper():
                            parts.append("")
                    else:
                        parts.append(re.escape(ch))
                    k += 2
                else:
                    parts.append(re.escape(body[k]) if body[k] not in "-" else "-")
                    k += 1
            out.append("[%s%s]" % ("^" if neg else "", "".join(parts)))
            i = j + 1
        elif c == ".":
            out.append(".")
            i += 1
        elif c in "*+?":
            out.append(c)
            i += 1
        elif c == "-":
            out.append("*?")
            i += 1
        elif c == "(":
            out.append("(")
            i += 1
        elif c == ")":
            out.append(")")
            i += 1
        elif c == "$" and i == n - 1:
            out.append("\\Z")
            i += 1
        else:
            out.append(re.escape(c))
            i += 1
    return ("^" if anchored else "") + "".join(out)


def _tostr(v):
    if isinstance(v, float) and v.is_integer():
        return str(int(v))
    return str(v)


def _captures(m, whole_if_none=True):
    if m.re.groups == 0:
        return [m.group(0)] if whole_if_none else []
    return [g for g in m.groups()]


def install(G):
    S = G.get("string")
    if S is None:
        S = LS.LuaTable()
        G.set("string", S)

    def s_find(s=None, pat=None, init=1.0, plain=None, *_):
        s = _tostr(s)
        pat = _tostr(pat)
        start = int(init) - 1 if init and init > 0 else max(0, len(s) + int(init))
        if plain is not None and plain is not False and plain is not None:
            idx = s.find(pat, start)
            if idx < 0:
                return [None]
            return [float(idx + 1), float(idx + len(pat))]
        rx = re.compile(lua_pattern_to_re(pat), re.DOTALL)
        m = rx.search(s, start)
        if not m:
            return [None]
        caps = _captures(m, whole_if_none=False)
        return [float(m.start() + 1), float(m.end())] + caps

    def s_match(s=None, pat=None, init=1.0, *_):
        s = _tostr(s)
        pat = _tostr(pat)
        start = int(init) - 1 if init and init > 0 else max(0, len(s) + int(init))
        rx = re.compile(lua_pattern_to_re(pat), re.DOTALL)
        m = rx.search(s, start)
        if not m:
            return [None]
        return _captures(m)

    def s_gsub(s=None, pat=None, repl=None, maxn=None, *_):
        s = _tostr(s)
        pat = _tostr(pat)
        rx = re.compile(lua_pattern_to_re(pat), re.DOTALL)
        count = [0]
        limit = int(maxn) if maxn is not None else 0

        def rep(m):
            if limit and count[0] >= limit:
                return m.group(0)
            count[0] += 1
            if isinstance(repl, str):
                def sub_one(mm):
                    d = mm.group(1)
                    if d == "0":
                        return m.group(0)
                    if d.isdigit():
                        return m.group(int(d)) or ""
                    return d
                return re.sub(r"%(.)", sub_one, repl)
            return _tostr(m.group(0))

        res = rx.sub(rep, s)
        return [res, float(count[0])]

    def s_format(fmt=None, *args):
        fmt = _tostr(fmt)
        out = []
        ai = 0
        i = 0
        while i < len(fmt):
            c = fmt[i]
            if c != "%":
                out.append(c)
                i += 1
                continue
            j = i + 1
            while j < len(fmt) and fmt[j] in "-+ #0123456789.":
                j += 1
            if j >= len(fmt):
                raise LS.LuaError("bad format")
            conv = fmt[j]
            spec = fmt[i:j]
            if conv == "%":
                out.append("%")
            else:
                v = args[ai] if ai < len(args) else None
                ai += 1
                if conv in "di":
                    out.append((spec + "d") % int(v))
                elif conv in "xXo":
                    out.append((spec + conv) % int(v))
                elif conv in "fgeEG":
                    out.append((spec + conv) % float(v))
                elif conv == "s":
                    out.append((spec + "s") % _tostr(v))
                elif conv == "q":
                    out.append('"%s"' % _tostr(v).replace("\\", "\\\\").replace('"', '\\"'))
                elif conv == "c":
                    out.append(chr(int(v)))
                else:
                    raise LS.LuaError("unsupported format %%%s" % conv)
            i = j + 1
        return ["".join(out)]

    fns = {
        "find": s_find, "match": s_match, "gsub": s_gsub, "format": s_format,
        "len": lambda s=None, *_: [float(len(_tostr(s)))],
        "lower": lambda s=None, *_: [_tostr(s).lower()],
        "upper": lambda s=None, *_: [_tostr(s).upper()],
        "rep": lambda s=None, n=0.0, *_: [_tostr(s) * int(n)],
    }
    for name, fn in fns.items():
        S.set(name, LS.Builtin(name, fn))


def _u32(x):
    return int(x) & 0xFFFFFFFF


def install_bit_utf8(G):
    bit = LS.LuaTable()

    def b_band(*a):
        r = 0xFFFFFFFF
        for x in a:
            r &= _u32(x)
        return [float(r)]

    def b_bor(*a):
        r = 0
        for x in a:
            r |= _u32(x)
        return [float(r & 0xFFFFFFFF)]

    def b_bxor(*a):
        r = 0
        for x in a:
            r ^= _u32(x)
        return [float(r & 0xFFFFFFFF)]

    def b_bnot(x=0.0, *_):
        return [float((~_u32(x)) & 0xFFFFFFFF)]

    def b_lshift(x=0.0, n=0.0, *_):
        return [float((_u32(x) << (int(n) & 31)) & 0xFFFFFFFF)]

    def b_rshift(x=0.0, n=0.0, *_):
        return [float(_u32(x) >> (int(n) & 31))]

    def b_arshift(x=0.0, n=0.0, *_):
        v = _u32(x)
        if v & 0x80000000:
            v -= 0x100000000
        return [float((v >> (int(n) & 31)) & 0xFFFFFFFF)]

    def b_lrotate(x=0.0, n=0.0, *_):
        v = _u32(x)
        k = int(n) & 31
        return [float(((v << k) | (v >> (32 - k))) & 0xFFFFFFFF if k else v)]

    def b_rrotate(x=0.0, n=0.0, *_):
        v = _u32(x)
        k = int(n) & 31
        return [float(((v >> k) | (v << (32 - k))) & 0xFFFFFFFF if k else v)]

    def b_btest(*a):
        return [b_band(*a)[0] != 0]

    for name, fn in [("band", b_band), ("bor", b_bor), ("bxor", b_bxor),
                     ("bnot", b_bnot), ("lshift", b_lshift), ("rshift", b_rshift),
                     ("arshift", b_arshift), ("lrotate", b_lrotate),
                     ("rrotate", b_rrotate), ("btest", b_btest)]:
        bit.set(name, LS.Builtin(name, fn))
    G.set("bit32", bit)

    u = LS.LuaTable()

    def u_char(*cps):
        return ["".join(chr(int(c)) for c in cps)]

    def u_codepoint(s=None, i=1.0, j=None, *_):
        s = str(s)
        i = int(i)
        j = i if j is None else int(j)
        return [float(ord(ch)) for ch in s[i - 1:j]]

    def u_len(s=None, *_):
        return [float(len(str(s)))]

    for name, fn in [("char", u_char), ("codepoint", u_codepoint), ("len", u_len)]:
        u.set(name, LS.Builtin(name, fn))
    u.set("charpattern", "[\x00-\x7F\xC2-\xFD][\x80-\xBF]*")
    G.set("utf8", u)
