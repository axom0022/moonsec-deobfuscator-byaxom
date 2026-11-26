import math
import sys

import luasubset as LS
from luasubset import LuaTable, Builtin, LuaError, BreakSig, ReturnSig, lua_eq, truthy, tonum, tostr


LS.LuaTable.length = lambda self: _border(self)


class Captured(Exception):
    def __init__(self, value, env=None):
        self.value = value
        self.env = env


class Unsupported(Exception):
    pass


class JFunc:
    __slots__ = ("node", "env", "capture", "name")

    def __init__(self, node, env, name="?"):
        self.node = node
        self.env = env
        self.capture = False
        self.name = name


class Env:
    __slots__ = ("vars", "parent")

    def __init__(self, parent=None):
        self.vars = {}
        self.parent = parent


def _border(tb):
    h = tb.hash
    if 1.0 not in h and 1 not in h:
        return 0
    lo, hi = 1, 2
    while (hi in h) or (float(hi) in h):
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if (mid in h) or (float(mid) in h):
            lo = mid
        else:
            hi = mid
    return lo


def _describe(e):
    t = e["type"]
    if t == "AstExprGlobal":
        return e["global"]
    if t == "AstExprIndexName":
        return _describe(e["expr"]) + "." + e["index"]
    if t == "AstExprLocal":
        return e["local"]["name"]
    if t == "AstExprIndexExpr":
        return _describe(e["expr"]) + "[...]"
    return t


def _install_math(G):
    M = G.get("math")
    if M is None:
        M = LuaTable()
        G.set("math", M)

    def one(fn):
        return lambda x=None, *_: [fn(tonum(x))]

    def ldexp(x=None, e=None, *_):
        return [math.ldexp(tonum(x), int(tonum(e)))]

    def frexp(x=None, *_):
        m, e = math.frexp(tonum(x))
        return [m, float(e)]

    def modf(x=None, *_):
        f, i = math.modf(tonum(x))
        return [i, f]

    def log(x=None, base=None, *_):
        v = tonum(x)
        if base is None:
            return [math.log(v) if v > 0 else (-math.inf if v == 0 else math.nan)]
        return [math.log(v, tonum(base))]

    def safe(fn):
        def g(*a):
            try:
                return [fn(*a)]
            except (ValueError, OverflowError):
                return [math.nan]
        return g

    entries = {
        "ldexp": ldexp, "frexp": frexp, "modf": modf, "log": log,
        "exp": safe(lambda x: math.exp(tonum(x))),
        "log10": safe(lambda x: math.log10(tonum(x))),
        "sin": safe(lambda x: math.sin(tonum(x))), "cos": safe(lambda x: math.cos(tonum(x))),
        "tan": safe(lambda x: math.tan(tonum(x))), "asin": safe(lambda x: math.asin(tonum(x))),
        "acos": safe(lambda x: math.acos(tonum(x))), "atan": safe(lambda x: math.atan(tonum(x))),
        "atan2": safe(lambda y, x: math.atan2(tonum(y), tonum(x))),
        "deg": safe(lambda x: math.degrees(tonum(x))), "rad": safe(lambda x: math.radians(tonum(x))),
    }
    for name, fn in entries.items():
        if M.get(name) is None:
            M.set(name, Builtin(name, fn))


def _lkey(local_node):
    return (local_node["name"], local_node["location"])


def _bytes_str(v):
    return v.encode("utf-8", "surrogateescape").decode("latin-1")


_FAST = {
    "Add": lambda a, b: a + b,
    "Sub": lambda a, b: a - b,
    "Mul": lambda a, b: a * b,
    "CompareEq": lambda a, b: a == b,
    "CompareNe": lambda a, b: a != b,
    "CompareLt": lambda a, b: a < b,
    "CompareLe": lambda a, b: a <= b,
    "CompareGt": lambda a, b: a > b,
    "CompareGe": lambda a, b: a >= b,
}


class Interp:
    def __init__(self, max_steps=50_000_000):
        base = LS.Interp(max_steps)
        self.G = base.G
        import v3strlib
        v3strlib.install(self.G)
        v3strlib.install_bit_utf8(self.G)
        _install_math(self.G)
        self.max_steps = max_steps
        self.steps = 0
        self.capture_name = None
        self.def_snapshot = None
        self._pure_memo = {}
        self._const_cache = {}
        base.call = self.call
        self._base = base

    def call(self, f, args):
        if isinstance(f, Builtin):
            r = f.fn(*args)
            return list(r) if r is not None else []
        if isinstance(f, JFunc):
            if f.capture:
                raise Captured(args[0] if args else None)
            fn = f.node
            env = Env(f.env)
            params = fn.get("args", [])
            for i, p in enumerate(params):
                env.vars[_lkey(p)] = args[i] if i < len(args) else None
            if fn.get("vararg"):
                env.vars["..."] = list(args[len(params):])
            try:
                self.block(fn["body"]["body"], env)
            except ReturnSig as r:
                return r.values
            return []
        if isinstance(f, LuaTable) and f.meta is not None:
            h = f.meta.get("__call")
            if h is not None:
                return self.call(h, [f] + list(args))
        raise LuaError("attempt to call %s" % type(f).__name__)

    def block(self, stmts, env):
        for st in stmts:
            self.stmt(st, env)

    def _tick(self):
        self.steps += 1
        if self.steps > self.max_steps:
            raise LuaError("step limit exceeded")

    def stmt(self, st, env):
        self._tick()
        t = st["type"]
        if t == "AstStatLocal":
            vals = self.evlist(st.get("values", []), env)
            for i, v in enumerate(st["vars"]):
                env.vars[_lkey(v)] = vals[i] if i < len(vals) else None
        elif t == "AstStatAssign":
            vals = self.evlist(st["values"], env)
            for i, target in enumerate(st["vars"]):
                self.assign(target, vals[i] if i < len(vals) else None, env)
        elif t == "AstStatCompoundAssign":
            cur = self.ev(st["var"], env)
            rhs = self.ev(st["value"], env)
            self.assign(st["var"], self.binop(st["op"], cur, rhs), env)
        elif t == "AstStatLocalFunction":
            key = _lkey(st["name"])
            f = JFunc(st["func"], env, name=st["name"]["name"])
            if self.capture_name is not None and st["name"]["name"] == self.capture_name:
                f.capture = True
                snap = []
                x = env
                while x is not None:
                    snap.append(dict(x.vars))
                    x = x.parent
                self.def_snapshot = snap
            env.vars[key] = f
        elif t == "AstStatIf":
            if truthy(self.ev(st["condition"], env)):
                self.block(st["thenbody"]["body"], Env(env))
            elif st.get("elsebody") is not None:
                eb = st["elsebody"]
                if eb["type"] == "AstStatIf":
                    self.stmt(eb, env)
                else:
                    self.block(eb["body"], Env(env))
        elif t == "AstStatWhile":
            while truthy(self.ev(st["condition"], env)):
                try:
                    self.block(st["body"]["body"], Env(env))
                except BreakSig:
                    break
        elif t == "AstStatFor":
            start = tonum(self.ev(st["from"], env))
            stop = tonum(self.ev(st["to"], env))
            if start is None or stop is None:
                raise LuaError("'for' initial/limit must be a number")
            i = start
            key = _lkey(st["var"])
            while i <= stop:
                inner = Env(env)
                inner.vars[key] = i
                try:
                    self.block(st["body"]["body"], inner)
                except BreakSig:
                    break
                i = i + 1.0
        elif t == "AstStatBreak":
            raise BreakSig()
        elif t == "AstStatReturn":
            raise ReturnSig(self.evlist(st.get("list", []), env))
        elif t == "AstStatExpr":
            self.ev_multi(st["expr"], env)
        elif t == "AstStatBlock":
            self.block(st["body"], Env(env))
        elif t == "AstStatFunction":
            self.assign(st["name"], JFunc(st["func"], env), env)
        elif t == "Comment":
            return
        else:
            raise Unsupported("statement %s" % t)

    def assign(self, target, value, env):
        t = target["type"]
        if t == "AstExprLocal":
            key = _lkey(target["local"])
            e = env
            while e is not None:
                if key in e.vars:
                    e.vars[key] = value
                    return
                e = e.parent
            env.vars[key] = value
        elif t == "AstExprGlobal":
            self.G.set(target["global"], value)
        elif t == "AstExprIndexName":
            obj = self.ev(target["expr"], env)
            self.setindex(obj, target["index"], value)
        elif t == "AstExprIndexExpr":
            obj = self.ev(target["expr"], env)
            self.setindex(obj, self.ev(target["index"], env), value)
        else:
            raise Unsupported("assignment target %s" % t)

    def setindex(self, obj, key, value):
        if not isinstance(obj, LuaTable):
            raise LuaError("attempt to index a %s value" % type(obj).__name__)
        obj.set(key, value)

    def index(self, obj, key):
        if isinstance(obj, LuaTable):
            v = obj.get(key)
            if v is None and obj.meta is not None:
                h = obj.meta.get("__index")
                if isinstance(h, LuaTable):
                    return self.index(h, key)
                if h is not None:
                    return (self.call(h, [obj, key]) or [None])[0]
            return v
        if isinstance(obj, str):
            return self.G.get("string").get(key)
        raise LuaError("attempt to index a %s value" % type(obj).__name__)

    def evlist(self, exprs, env):
        out = []
        for i, e in enumerate(exprs):
            if i == len(exprs) - 1 and e["type"] in ("AstExprCall", "AstExprVarargs"):
                out.extend(self.ev_multi(e, env))
            else:
                out.append(self.ev(e, env))
        return out

    def ev_multi(self, e, env):
        t = e["type"]
        if t == "AstExprCall":
            return self.call_expr(e, env)
        if t == "AstExprVarargs":
            key = "..."
            x = env
            while x is not None:
                if key in x.vars:
                    return list(x.vars[key])
                x = x.parent
            return []
        return [self.ev(e, env)]

    def call_expr(self, e, env):
        if e.get("self"):
            obj = self.ev(e["func"]["expr"], env)
            f = self.index(obj, e["func"]["index"])
            args = [obj] + self.evlist(e["args"], env)
        else:
            f = self.ev(e["func"], env)
            args = self.evlist(e["args"], env)
        if f is None:
            raise LuaError("attempt to call nil: %s" % _describe(e["func"]))
        if isinstance(f, JFunc) and f.capture:
            raise Captured(args[0] if args else None, env)
        return self.call(f, args)

    def _pure(self, e):
        k = id(e)
        r = self._pure_memo.get(k)
        if r is not None:
            return r
        t = e["type"]
        if t in ("AstExprConstantNumber", "AstExprConstantString", "AstExprConstantBool", "AstExprConstantNil"):
            r = True
        elif t == "AstExprGroup" or t == "AstExprUnary":
            r = self._pure(e["expr"])
        elif t == "AstExprBinary":
            r = self._pure(e["left"]) and self._pure(e["right"])
        else:
            r = False
        self._pure_memo[k] = r
        return r

    def ev(self, e, env):
        t = e["type"]
        if (t == "AstExprBinary" or t == "AstExprUnary" or t == "AstExprGroup") and self._pure(e):
            k = id(e)
            if k in self._const_cache:
                return self._const_cache[k]
            v = self._ev_raw(e, env)
            self._const_cache[k] = v
            return v
        return self._ev_raw(e, env)

    def _ev_raw(self, e, env):
        t = e["type"]
        if t == "AstExprConstantNumber":
            return float(e["value"])
        if t == "AstExprConstantString":
            return _bytes_str(e["value"])
        if t == "AstExprConstantBool":
            return bool(e["value"])
        if t == "AstExprConstantNil":
            return None
        if t == "AstExprLocal":
            key = _lkey(e["local"])
            x = env
            while x is not None:
                if key in x.vars:
                    return x.vars[key]
                x = x.parent
            return None
        if t == "AstExprGlobal":
            return self.G.get(e["global"])
        if t == "AstExprIndexName":
            return self.index(self.ev(e["expr"], env), e["index"])
        if t == "AstExprIndexExpr":
            obj = self.ev(e["expr"], env)
            return self.index(obj, self.ev(e["index"], env))
        if t == "AstExprCall":
            r = self.call_expr(e, env)
            return r[0] if r else None
        if t == "AstExprVarargs":
            r = self.ev_multi(e, env)
            return r[0] if r else None
        if t == "AstExprFunction":
            return JFunc(e, env)
        if t == "AstExprGroup":
            return self.ev(e["expr"], env)
        if t == "AstExprTable":
            return self.table(e, env)
        if t == "AstExprUnary":
            v = self.ev(e["expr"], env)
            op = e["op"]
            if op == "Not":
                return not truthy(v)
            if op == "Minus":
                n = tonum(v)
                if n is None:
                    raise LuaError("attempt to perform arithmetic on a %s value" % type(v).__name__)
                return -n
            if op == "Len":
                if isinstance(v, str):
                    return float(len(v))
                if isinstance(v, LuaTable):
                    return float(_border(v))
                raise LuaError("attempt to get length of a %s value" % type(v).__name__)
            raise Unsupported("unary %s" % op)
        if t == "AstExprBinary":
            op = e["op"]
            if op == "And":
                a = self.ev(e["left"], env)
                return self.ev(e["right"], env) if truthy(a) else a
            if op == "Or":
                a = self.ev(e["left"], env)
                return a if truthy(a) else self.ev(e["right"], env)
            return self.binop(op, self.ev(e["left"], env), self.ev(e["right"], env))
        raise Unsupported("expression %s" % t)

    def table(self, e, env):
        tb = LuaTable()
        n = 0
        items = e.get("items", [])
        for i, it in enumerate(items):
            kind = it.get("kind")
            if kind == "item":
                if i == len(items) - 1 and it["value"]["type"] in ("AstExprCall", "AstExprVarargs"):
                    for v in self.ev_multi(it["value"], env):
                        n += 1
                        tb.set(float(n), v)
                else:
                    n += 1
                    tb.set(float(n), self.ev(it["value"], env))
            elif kind in ("record", "general"):
                k = self.ev(it["key"], env)
                tb.set(k, self.ev(it["value"], env))
            else:
                raise Unsupported("table item kind %r" % kind)
        return tb

    def binop(self, op, a, b):
        f = _FAST.get(op)
        if f is not None:
            x, y = a, b
            if type(x) is float and type(y) is float:
                return f(x, y)
        if op == "Add" or op == "Sub" or op == "Mul" or op == "Div" or op == "Mod" or op == "Pow":
            x, y = tonum(a), tonum(b)
            if x is None or y is None:
                raise LuaError("attempt to perform arithmetic on a non-number value")
            if op == "Add":
                return x + y
            if op == "Sub":
                return x - y
            if op == "Mul":
                return x * y
            if op == "Div":
                return LS._div(x, y)
            if op == "Mod":
                return LS._mod(x, y)
            return LS._pow(x, y)
        if op == "Concat":
            if isinstance(a, (str, float, int)) and isinstance(b, (str, float, int)) \
                    and not isinstance(a, bool) and not isinstance(b, bool):
                return tostr(a) + tostr(b)
            raise LuaError("attempt to concatenate a non-string value")
        if op == "CompareEq":
            return lua_eq(a, b)
        if op == "CompareNe":
            return not lua_eq(a, b)
        if op == "CompareLt":
            return LS._lt(a, b)
        if op == "CompareLe":
            return LS._le(a, b)
        if op == "CompareGt":
            return LS._lt(b, a)
        if op == "CompareGe":
            return LS._le(b, a)
        raise Unsupported("binary %s" % op)


def _run_to_dispatcher(json_ast, dispatcher_name, max_steps):
    it = Interp(max_steps)
    it.capture_name = dispatcher_name
    env = Env(None)
    env.vars["..."] = []
    try:
        it.block(json_ast["root"]["body"], env)
    except Captured as c:
        return c.value, c.env, it
    raise LuaError("dispatcher %r was not reached" % dispatcher_name)


def dispatcher_result(json_ast, dispatcher_name, max_steps=50_000_000):
    value, _, _ = _run_to_dispatcher(json_ast, dispatcher_name, max_steps)
    return value


def library_matches(json_ast, dispatcher_name, names, candidates, max_steps=50_000_000):
    _, env, it = _run_to_dispatcher(json_ast, dispatcher_name, max_steps)
    G = it.G
    snaps = it.def_snapshot if it.def_snapshot is not None else []
    if not snaps:
        x = env
        while x is not None:
            snaps.append(x.vars)
            x = x.parent
    cand_obj = {}
    for c in candidates:
        if "." in c:
            lib, fn = c.split(".", 1)
            tb = G.get(lib)
            v = tb.get(fn) if isinstance(tb, LuaTable) else None
        else:
            v = G.get(c)
        if v is not None:
            cand_obj.setdefault(id(v), c)
    wanted = set(names)
    result = {}
    for varsdict in snaps:
        for key, v in varsdict.items():
            if not isinstance(key, tuple):
                continue
            name = key[0]
            if name in wanted and name not in result and id(v) in cand_obj:
                result[name] = cand_obj[id(v)]
    return result
