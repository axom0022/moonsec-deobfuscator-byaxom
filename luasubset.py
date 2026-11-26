import math

from luaparser import ast as L


LOCATE = [None]
LOCATE_CHUNK = ["[string]"]


class LuaError(Exception):
    pass


class BreakSig(Exception):
    pass


class ReturnSig(Exception):
    def __init__(self, values):
        self.values = values


class LuaTable:
    __slots__ = ("hash", "meta")

    def __init__(self):
        self.hash = {}
        self.meta = None

    def get(self, k):
        return self.hash.get(normkey(k))

    def set(self, k, v):
        if k is None:
            raise LuaError("table index is nil")
        if isinstance(k, float) and k != k:
            raise LuaError("table index is NaN")
        k = normkey(k)
        if v is None:
            self.hash.pop(k, None)
        else:
            self.hash[k] = v

    def length(self):
        n = 0
        while (n + 1) in self.hash:
            n += 1
        return n


def normkey(k):
    if isinstance(k, bool):
        return ("__bool__", k)
    if isinstance(k, float) and k.is_integer():
        return int(k)
    return k


class Scope:
    __slots__ = ("vars", "parent")

    def __init__(self, parent=None):
        self.vars = {}
        self.parent = parent


class LuaFunction:
    __slots__ = ("params", "isvararg", "body", "scope", "name")

    def __init__(self, params, isvararg, body, scope, name="?"):
        self.params = params
        self.isvararg = isvararg
        self.body = body
        self.scope = scope
        self.name = name


class Builtin:
    __slots__ = ("name", "fn")

    def __init__(self, name, fn):
        self.name = name
        self.fn = fn


_ESC = {
    "a": "\a", "b": "\b", "f": "\f", "n": "\n", "r": "\r", "t": "\t",
    "v": "\v", "\\": "\\", '"': '"', "'": "'", "\n": "\n",
}


def unescape_raw(raw):
    src = raw.replace("\\\\", "\\")
    out = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c != "\\":
            out.append(c)
            i += 1
            continue
        i += 1
        c = src[i]
        if c.isdigit():
            j = i
            while j < n and j < i + 3 and src[j].isdigit():
                j += 1
            out.append(chr(int(src[i:j]) & 0xFF))
            i = j
        elif c in _ESC:
            out.append(_ESC[c])
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def index_key(it, n, sc):
    if getattr(n.notation, "name", "") == "DOT":
        return n.idx.id
    return it.ev(n.idx, sc)


def _stmt_hint(st):
    t = type(st).__name__
    if t in ("LocalAssign", "Assign"):
        return ", ".join(describe(v) for v in st.values)[:160]
    if t == "LocalFunction":
        return st.name.id
    if t in ("Call", "Invoke"):
        return describe(st.func) if t == "Call" else st.func.id
    return ""


def describe(n):
    t = type(n).__name__
    if t == "Name":
        return n.id
    if t == "Index":
        key = n.idx
        if getattr(n.notation, "name", "") == "DOT":
            return describe(n.value) + "." + key.id
        return describe(n.value) + "[" + describe(key) + "]"
    if t == "Number":
        return tostr(float(n.n))
    if t == "Call":
        return describe(n.func) + "(...)"
    if t == "Invoke":
        return describe(n.source) + ":" + n.func.id + "(...)"
    if t == "String":
        return repr(unescape_raw(n.raw)[:24])
    return t


def truthy(v):
    return not (v is None or v is False)


def tonum(v):
    if isinstance(v, float):
        return v
    if isinstance(v, bool) or v is None:
        raise LuaError("arithmetic on %s" % ("nil" if v is None else "boolean"))
    if isinstance(v, str):
        try:
            return float(v.strip())
        except ValueError:
            raise LuaError("arithmetic on string %r" % v)
    if isinstance(v, int):
        return float(v)
    raise LuaError("arithmetic on %s" % type(v).__name__)


def tostr(v):
    if v is None:
        return "nil"
    if v is True:
        return "true"
    if v is False:
        return "false"
    if isinstance(v, float):
        if v.is_integer() and abs(v) < 1e15:
            return str(int(v))
        if v != v:
            return "nan"
        if v in (math.inf, -math.inf):
            return "inf" if v > 0 else "-inf"
        return "%.14g" % v
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return v
    if isinstance(v, LuaTable):
        return "table: 0x%x" % id(v)
    return "function: 0x%x" % id(v)


def lua_eq(a, b):
    if isinstance(a, bool) or isinstance(b, bool):
        return type(a) is type(b) and a == b
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return a == b
    if isinstance(a, str) and isinstance(b, str):
        return a == b
    return a is b


def _div(a, b):
    if b == 0:
        if a == 0 or a != a:
            return math.nan
        return math.copysign(math.inf, a) * math.copysign(1.0, b)
    return a / b


def _mod(a, b):
    if b == 0:
        return math.nan
    return a - math.floor(a / b) * b


def _pow(a, b):
    try:
        return math.pow(a, b)
    except (OverflowError, ValueError):
        return math.nan


def _lt(a, b):
    if isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool) and not isinstance(b, bool):
        return a < b
    if isinstance(a, str) and isinstance(b, str):
        return a < b
    raise LuaError("attempt to compare %s with %s" % (type(a).__name__, type(b).__name__))


def _le(a, b):
    if isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool) and not isinstance(b, bool):
        return a <= b
    if isinstance(a, str) and isinstance(b, str):
        return a <= b
    raise LuaError("attempt to compare %s with %s" % (type(a).__name__, type(b).__name__))


LAST_CALL_WHERE = [None]


class Interp:
    def __init__(self, max_steps=50_000_000):
        self.G = LuaTable()
        self.steps = 0
        self.max_steps = max_steps
        self._install_stdlib()

    def _install_stdlib(self):
        G = self.G
        B = lambda name, fn: Builtin(name, fn)

        def set_(tbl, k, v):
            tbl.set(k, v)

        def b_type(*a):
            v = a[0] if a else None
            if v is None:
                return ["nil"]
            if isinstance(v, bool):
                return ["boolean"]
            if isinstance(v, (int, float)):
                return ["number"]
            if isinstance(v, str):
                return ["string"]
            if isinstance(v, LuaTable):
                return ["table"]
            return ["function"]

        def b_tonumber(v=None, base=None):
            if base is not None:
                try:
                    return [float(int(str(v), int(base)))]
                except ValueError:
                    return [None]
            if isinstance(v, (int, float)) and not isinstance(v, bool):
                return [float(v)]
            if isinstance(v, str):
                try:
                    s = v.strip()
                    if s.lower().startswith(("0x", "-0x")):
                        return [float(int(s, 16))]
                    return [float(s)]
                except ValueError:
                    return [None]
            return [None]

        def b_select(n, *rest):
            if n == "#":
                return [float(len(rest))]
            n = int(n)
            if n < 0:
                n = len(rest) + n + 1
            return list(rest[n - 1:])

        def b_pairs(t=None, *_):
            if not isinstance(t, LuaTable):
                raise LuaError("pairs on non-table")
            keys = list(t.hash.keys())
            vals = [t.hash[k] for k in keys]
            state = {"i": 0}

            def it(_s=None, _c=None):
                i = state["i"]
                if i >= len(keys):
                    return [None]
                state["i"] = i + 1
                k = keys[i]
                if isinstance(k, tuple) and k and k[0] == "__bool__":
                    k = k[1]
                return [k, vals[i]]
            return [Builtin("next", it), t, None]

        def b_ipairs(t=None, *_):
            def it(tb, i):
                i = int(i) + 1
                v = tb.get(float(i))
                if v is None:
                    return [None]
                return [float(i), v]
            return [Builtin("ipairs_it", it), t, 0.0]

        def b_next(t, k=None):
            keys = list(t.hash.keys())
            if k is None:
                if not keys:
                    return [None]
                kk = keys[0]
            else:
                kn = normkey(k)
                try:
                    kk = keys[keys.index(kn) + 1]
                except (ValueError, IndexError):
                    return [None]
            return [kk, t.hash[kk]]

        def b_setmetatable(t, mt=None):
            t.meta = mt
            return [t]

        def b_getmetatable(t=None):
            return [t.meta if isinstance(t, LuaTable) else None]

        def b_error(msg=None, *_):
            raise LuaError(tostr(msg))

        def b_assert(v=None, msg=None, *_):
            if not truthy(v):
                raise LuaError(tostr(msg) if msg is not None else "assertion failed!")
            return [v]

        def b_pcall(f, *args):
            try:
                return [True] + self.call(f, list(args))
            except LuaError as e:
                return [False, str(e)]

        def b_unpack(t, i=1.0, j=None):
            i = int(i)
            j = int(j) if j is not None else t.length()
            return [t.get(float(k)) for k in range(i, j + 1)]

        def b_getfenv(*_):
            return [self.G]

        def b_rawget(t, k):
            return [t.get(k)]

        def b_rawset(t, k, v):
            t.set(k, v)
            return [t]

        for name, fn in [
            ("type", b_type), ("tonumber", b_tonumber), ("select", b_select),
            ("pairs", b_pairs), ("ipairs", b_ipairs), ("next", b_next),
            ("setmetatable", b_setmetatable), ("getmetatable", b_getmetatable),
            ("error", b_error), ("assert", b_assert), ("pcall", b_pcall),
            ("unpack", b_unpack), ("getfenv", b_getfenv), ("rawget", b_rawget),
            ("rawset", b_rawset),
        ]:
            G.set(name, B(name, fn))
        G.set("tostring", B("tostring", lambda v=None, *_: [tostr(v)]))
        G.set("print", B("print", lambda *a: []))
        G.set("setfenv", B("setfenv", lambda *a: []))
        G.set("_G", self.G)
        G.set("_ENV", self.G)

        S = LuaTable()
        G.set("string", S)

        def s_byte(s, i=1.0, j=None):
            n = len(s)
            i = int(i)
            j = i if j is None else int(j)
            if i < 0:
                i = max(n + i + 1, 1)
            if j < 0:
                j = n + j + 1
            i = max(i, 1)
            j = min(j, n)
            return [float(ord(c)) for c in s[i - 1:j]]

        def s_sub(s, i=1.0, j=-1.0):
            n = len(s)
            i = int(i)
            j = int(j)
            if i < 0:
                i = max(n + i + 1, 1)
            elif i == 0:
                i = 1
            if j < 0:
                j = n + j + 1
            elif j > n:
                j = n
            if i > j:
                return [""]
            return [s[i - 1:j]]

        def s_char(*codes):
            return ["".join(chr(int(c) & 0xFF) for c in codes)]

        S.set("byte", B("byte", s_byte))
        S.set("sub", B("sub", s_sub))
        S.set("char", B("char", s_char))
        S.set("len", B("len", lambda s: [float(len(s))]))
        S.set("lower", B("lower", lambda s: [s.lower()]))
        S.set("upper", B("upper", lambda s: [s.upper()]))
        S.set("rep", B("rep", lambda s, n: [s * int(n)]))
        S.set("reverse", B("reverse", lambda s: [s[::-1]]))

        T = LuaTable()
        G.set("table", T)

        def t_concat(t, sep="", i=1.0, j=None):
            j = t.length() if j is None else int(j)
            parts = []
            for k in range(int(i), j + 1):
                v = t.get(float(k))
                if not isinstance(v, (str, int, float)) or isinstance(v, bool):
                    raise LuaError("invalid value in table.concat")
                parts.append(tostr(v))
            return [sep.join(parts)]

        def t_insert(t, *a):
            if len(a) == 1:
                t.set(float(t.length() + 1), a[0])
            else:
                pos, v = int(a[0]), a[1]
                n = t.length()
                for k in range(n, pos - 1, -1):
                    t.set(float(k + 1), t.get(float(k)))
                t.set(float(pos), v)
            return []

        def t_remove(t, pos=None):
            n = t.length()
            pos = n if pos is None else int(pos)
            v = t.get(float(pos))
            for k in range(pos, n):
                t.set(float(k), t.get(float(k + 1)))
            if n:
                t.set(float(n), None)
            return [v]

        T.set("concat", B("concat", t_concat))
        T.set("insert", B("insert", t_insert))
        T.set("remove", B("remove", t_remove))
        T.set("unpack", G.get("unpack"))
        T.set("getn", B("getn", lambda t: [float(t.length())]))

        M = LuaTable()
        G.set("math", M)
        M.set("floor", B("floor", lambda x: [float(math.floor(x))]))
        M.set("ceil", B("ceil", lambda x: [float(math.ceil(x))]))
        M.set("abs", B("abs", lambda x: [abs(float(x))]))
        M.set("max", B("max", lambda *a: [max(a)]))
        M.set("min", B("min", lambda *a: [min(a)]))
        M.set("sqrt", B("sqrt", lambda x: [math.sqrt(x)]))
        M.set("pow", B("pow", lambda x, y: [_pow(x, y)]))
        M.set("fmod", B("fmod", lambda x, y: [math.fmod(x, y)]))
        M.set("huge", math.inf)
        M.set("pi", math.pi)

    def call(self, f, args):
        if isinstance(f, Builtin):
            r = f.fn(*args)
            return list(r) if r is not None else []
        if isinstance(f, LuaFunction):
            sc = Scope(f.scope)
            for i, p in enumerate(f.params):
                sc.vars[p] = args[i] if i < len(args) else None
            if f.isvararg:
                sc.vars["..."] = list(args[len(f.params):])
            try:
                self.exec_block(f.body, sc, new_scope=False)
            except ReturnSig as r:
                return r.values
            return []
        if isinstance(f, LuaTable) and f.meta is not None:
            h = f.meta.get("__call")
            if h is not None:
                return self.call(h, [f] + list(args))
        raise LuaError("attempt to call %s" % (type(f).__name__))

    def _tick(self):
        self.steps += 1
        if self.steps > self.max_steps:
            raise LuaError("step limit exceeded")

    def ev(self, n, sc):
        self._tick()
        t = type(n).__name__
        if t in ("Call", "Invoke", "Dots"):
            r = self.evm(n, sc)
            return r[0] if r else None
        h = _EXPR.get(t)
        if h is None:
            raise LuaError("unsupported expression %s" % t)
        return h(self, n, sc)

    def evm(self, n, sc):
        t = type(n).__name__
        if t == "Call":
            f = self.ev(n.func, sc)
            args = self.evlist(n.args, sc)
            if f is None:
                raise LuaError("attempt to call nil: %s" % describe(n.func))
            if isinstance(f, LuaTable) and (f.meta is None or f.meta.get("__call") is None):
                try:
                    where = describe(n.func)
                except Exception:
                    where = type(n.func).__name__
                LAST_CALL_WHERE[0] = where
                raise LuaError("attempt to call LuaTable")
            return self.call(f, args)
        if t == "Invoke":
            obj = self.ev(n.source, sc)
            meth = self.index(obj, n.func.id)
            args = self.evlist(n.args, sc)
            return self.call(meth, [obj] + args)
        if t == "Dots":
            return list(self._varargs(sc))
        return [self.ev(n, sc)]

    def _varargs(self, sc):
        s = sc
        while s is not None:
            if "..." in s.vars:
                return s.vars["..."]
            s = s.parent
        raise LuaError("no varargs here")

    def evlist(self, exprs, sc):
        out = []
        last = len(exprs) - 1
        for i, e in enumerate(exprs):
            if i == last and type(e).__name__ in ("Call", "Invoke", "Dots"):
                out.extend(self.evm(e, sc))
            else:
                out.append(self.ev(e, sc))
        return out

    def index(self, obj, key):
        if isinstance(obj, LuaTable):
            return obj.get(key)
        if isinstance(obj, str):
            return self.G.get("string").get(key)
        raise LuaError("attempt to index %s" % type(obj).__name__)

    def exec_block(self, stmts, sc, new_scope=True):
        s = Scope(sc) if new_scope else sc
        for st in stmts:
            self._tick()
            t = type(st).__name__
            try:
                if t == "LocalAssign":
                    vals = self.evlist(st.values, s)
                    s = Scope(s)
                    for i, tgt in enumerate(st.targets):
                        s.vars[tgt.id] = vals[i] if i < len(vals) else None
                elif t == "LocalFunction":
                    s = Scope(s)
                    s.vars[st.name.id] = _make_function(st, s, st.name.id)
                else:
                    h = _STMT.get(t)
                    if h is None:
                        raise LuaError("unsupported statement %s" % t)
                    h(self, st, s)
            except LuaError as e:
                if not getattr(e, "located", False) and LOCATE[0] is not None:
                    sc_ = getattr(st, "start_char", None)
                    if sc_ is not None:
                        line = LOCATE[0].count("\n", 0, sc_) + 1
                        e.args = ("%s:%d: %s" % (LOCATE_CHUNK[0], line, e.args[0] if e.args else ""),)
                    e.located = True
                if getattr(e, "ctx", None) is None:
                    e.ctx = "%s: %s" % (t, _stmt_hint(st))
                if getattr(e, "scope", None) is None:
                    e.scope = s
                if getattr(e, "stmt", None) is None:
                    e.stmt = st
                raise
        return s

    def assign_name(self, name, v, sc):
        s = sc
        while s is not None:
            if name in s.vars:
                s.vars[name] = v
                return
            s = s.parent
        self.G.set(name, v)

    def lookup_name(self, name, sc):
        s = sc
        while s is not None:
            if name in s.vars:
                return s.vars[name]
            s = s.parent
        return self.G.get(name)


def _e_number(it, n, sc):
    return float(n.n)


def _e_string(it, n, sc):
    return unescape_raw(n.raw)


def _e_nil(it, n, sc):
    return None


def _e_true(it, n, sc):
    return True


def _e_false(it, n, sc):
    return False


def _e_name(it, n, sc):
    return it.lookup_name(n.id, sc)


def _e_index(it, n, sc):
    obj = it.ev(n.value, sc)
    key = index_key(it, n, sc)
    return it.index(obj, key)


def _e_function(it, n, sc):
    params = []
    isvararg = False
    for a in n.args:
        if type(a).__name__ == "Varargs":
            isvararg = True
        else:
            params.append(a.id)
    return LuaFunction(params, isvararg, n.body.body, sc)


def _e_table(it, n, sc):
    t = LuaTable()
    pos = 1
    fields = n.fields
    last = len(fields) - 1
    for i, f in enumerate(fields):
        if f.key is None:
            if i == last and type(f.value).__name__ in ("Call", "Invoke", "Dots"):
                for v in it.evm(f.value, sc):
                    t.set(float(pos), v)
                    pos += 1
            else:
                t.set(float(pos), it.ev(f.value, sc))
                pos += 1
        else:
            if getattr(f, "between_brackets", False):
                k = it.ev(f.key, sc)
            else:
                k = f.key.id if hasattr(f.key, "id") else f.key
            t.set(k, it.ev(f.value, sc))
    return t


def _arith(fn):
    def h(it, n, sc):
        a = tonum(it.ev(n.left, sc))
        b = tonum(it.ev(n.right, sc))
        return fn(a, b)
    return h


def _cmp(fn, swap=False, neg=False):
    def h(it, n, sc):
        a = it.ev(n.left, sc)
        b = it.ev(n.right, sc)
        if swap:
            a, b = b, a
        r = fn(a, b)
        return (not r) if neg else r
    return h


def _e_eq(it, n, sc):
    return lua_eq(it.ev(n.left, sc), it.ev(n.right, sc))


def _e_neq(it, n, sc):
    return not lua_eq(it.ev(n.left, sc), it.ev(n.right, sc))


def _e_concat(it, n, sc):
    a = it.ev(n.left, sc)
    b = it.ev(n.right, sc)
    for v in (a, b):
        if not isinstance(v, (str, int, float)) or isinstance(v, bool):
            raise LuaError("attempt to concatenate %s" % type(v).__name__)
    return tostr(a) + tostr(b)


def _e_and(it, n, sc):
    a = it.ev(n.left, sc)
    if not truthy(a):
        return a
    return it.ev(n.right, sc)


def _e_or(it, n, sc):
    a = it.ev(n.left, sc)
    if truthy(a):
        return a
    return it.ev(n.right, sc)


def _e_not(it, n, sc):
    return not truthy(it.ev(n.operand, sc))


def _e_neg(it, n, sc):
    return -tonum(it.ev(n.operand, sc))


def _e_len(it, n, sc):
    v = it.ev(n.operand, sc)
    if isinstance(v, str):
        return float(len(v))
    if isinstance(v, LuaTable):
        return float(v.length())
    raise LuaError("attempt to get length of %s" % type(v).__name__)


_EXPR = {
    "Number": _e_number,
    "String": _e_string,
    "Nil": _e_nil,
    "TrueExpr": _e_true,
    "FalseExpr": _e_false,
    "Name": _e_name,
    "Index": _e_index,
    "AnonymousFunction": _e_function,
    "Table": _e_table,
    "AddOp": _arith(lambda a, b: a + b),
    "SubOp": _arith(lambda a, b: a - b),
    "MultOp": _arith(lambda a, b: a * b),
    "FloatDivOp": _arith(_div),
    "ModOp": _arith(_mod),
    "ExpoOp": _arith(_pow),
    "Concat": _e_concat,
    "EqToOp": _e_eq,
    "NotEqToOp": _e_neq,
    "LessThanOp": _cmp(_lt),
    "LessOrEqThanOp": _cmp(_le),
    "GreaterThanOp": _cmp(_lt, swap=True),
    "GreaterOrEqThanOp": _cmp(_le, swap=True),
    "AndLoOp": _e_and,
    "OrLoOp": _e_or,
    "ULNotOp": _e_not,
    "UMinusOp": _e_neg,
    "ULengthOP": _e_len,
}


def _s_assign(it, n, sc):
    vals = it.evlist(n.values, sc)
    for i, tgt in enumerate(n.targets):
        v = vals[i] if i < len(vals) else None
        tt = type(tgt).__name__
        if tt == "Name":
            it.assign_name(tgt.id, v, sc)
        elif tt == "Index":
            obj = it.ev(tgt.value, sc)
            key = index_key(it, tgt, sc)
            if not isinstance(obj, LuaTable):
                raise LuaError("attempt to index %s" % type(obj).__name__)
            obj.set(key, v)
        else:
            raise LuaError("bad assignment target %s" % tt)


def _make_function(n, sc, name):
    params = []
    isvararg = False
    for a in n.args:
        if type(a).__name__ == "Varargs":
            isvararg = True
        else:
            params.append(a.id)
    return LuaFunction(params, isvararg, n.body.body, sc, name)


def _s_if(it, n, sc):
    node = n
    while True:
        tn = type(node).__name__
        if tn == "If" or tn == "ElseIf":
            if truthy(it.ev(node.test, sc)):
                it.exec_block(node.body.body, sc)
                return
            orelse = node.orelse
            if orelse is None:
                return
            if type(orelse).__name__ in ("If", "ElseIf"):
                node = orelse
                continue
            it.exec_block(orelse.body, sc)
            return
        raise LuaError("bad if node %s" % tn)


def _s_while(it, n, sc):
    try:
        while truthy(it.ev(n.test, sc)):
            it.exec_block(n.body.body, sc)
    except BreakSig:
        pass


def _s_repeat(it, n, sc):
    s = Scope(sc)
    try:
        while True:
            fin = it.exec_block(n.body.body, s, new_scope=False)
            if truthy(it.ev(n.test, fin)):
                break
    except BreakSig:
        pass


def _s_fornum(it, n, sc):
    start = tonum(it.ev(n.start, sc))
    stop = tonum(it.ev(n.stop, sc))
    step = tonum(it.ev(n.step, sc)) if not isinstance(n.step, (int, float)) else float(n.step)
    name = n.target.id
    i = start
    try:
        while (step > 0 and i <= stop) or (step <= 0 and i >= stop):
            s = Scope(sc)
            s.vars[name] = i
            it.exec_block(n.body.body, s, new_scope=False)
            i += step
    except BreakSig:
        pass


def _s_forin(it, n, sc):
    vals = it.evlist(n.iter, sc) if isinstance(n.iter, list) else it.evm(n.iter, sc)
    f = vals[0] if vals else None
    state = vals[1] if len(vals) > 1 else None
    ctrl = vals[2] if len(vals) > 2 else None
    names = [t.id for t in n.targets]
    try:
        while True:
            rs = it.call(f, [state, ctrl])
            if not rs or rs[0] is None:
                break
            ctrl = rs[0]
            s = Scope(sc)
            for i, nm in enumerate(names):
                s.vars[nm] = rs[i] if i < len(rs) else None
            it.exec_block(n.body.body, s, new_scope=False)
    except BreakSig:
        pass


def _s_return(it, n, sc):
    raise ReturnSig(it.evlist(n.values, sc))


def _s_break(it, n, sc):
    raise BreakSig()


def _s_call(it, n, sc):
    it.evm(n, sc)


def _s_semicolon(it, n, sc):
    return None


def _s_do(it, n, sc):
    it.exec_block(n.body.body, sc)


_STMT = {
    "Assign": _s_assign,
    "If": _s_if,
    "While": _s_while,
    "Repeat": _s_repeat,
    "Fornum": _s_fornum,
    "Forin": _s_forin,
    "Return": _s_return,
    "Break": _s_break,
    "Call": _s_call,
    "Invoke": _s_call,
    "SemiColon": _s_semicolon,
    "Do": _s_do,
}
