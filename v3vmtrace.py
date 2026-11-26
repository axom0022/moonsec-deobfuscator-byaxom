import sys

from luaparser import ast as L

import luasubset as LS
import v3bootstrap as B


class Proxy:
    __slots__ = ("path", "kids")

    def __init__(self, path):
        self.path = path
        self.kids = {}


def _math_lib(G):
    import math as M

    def ldexp(m=0.0, e=0.0, *_):
        return [float(m) * (2.0 ** int(e))]

    def floor(x=0.0, *_):
        return [float(M.floor(x))]

    def ceil(x=0.0, *_):
        return [float(M.ceil(x))]

    def fmod(a=0.0, b=1.0, *_):
        return [float(M.fmod(a, b))]

    def lmax(*a):
        return [max(float(x) for x in a)]

    def lmin(*a):
        return [min(float(x) for x in a)]

    lib = LS.LuaTable()
    for name, fn in [("ldexp", ldexp), ("floor", floor), ("ceil", ceil),
                     ("fmod", fmod), ("max", lmax), ("min", lmin),
                     ("abs", lambda x=0.0, *_: [abs(float(x))]),
                     ("sqrt", lambda x=0.0, *_: [M.sqrt(float(x))]),
                     ("exp", lambda x=0.0, *_: [M.exp(float(x))]),
                     ("log", lambda x=0.0, *_: [M.log(float(x))])]:
        lib.set(name, LS.Builtin(name, fn))
    lib.set("huge", float("inf"))
    lib.set("pi", M.pi)
    G.set("math", lib)


class VMInterp(LS.Interp):
    def __init__(self, log, max_steps):
        super().__init__(max_steps=max_steps)
        self.log = log
        self._stack = []
        self.deferred = []
        _math_lib(self.G)
        import v3strlib
        v3strlib.install(self.G)
        v3strlib.install_bit_utf8(self.G)

    def index(self, obj, key):
        if isinstance(obj, Proxy):
            if key not in obj.kids:
                obj.kids[key] = Proxy("%s.%s" % (obj.path, key))
                self.log.append("GET %s.%s" % (obj.path, key))
            return obj.kids[key]
        if obj is None:
            raise LS.LuaError("index nil with key %r" % (key,))
        if isinstance(obj, LS.LuaTable):
            v = obj.get(key)
            if obj is self.G and key == "Strength":
                EVENTS.append({"k": "global_read", "name": key, "value": _struct(v)})
            if v is None and obj.meta is not None:
                h = obj.meta.get("__index")
                if isinstance(h, (LS.LuaFunction, LS.Builtin)):
                    r = self.call(h, [obj, key])
                    return r[0] if r else None
                if isinstance(h, LS.LuaTable):
                    return self.index(h, key)
            return v
        return super().index(obj, key)

    def lookup_name(self, name, sc):
        if name != "Strength":
            return super().lookup_name(name, sc)
        s = sc
        while s is not None:
            if name in s.vars:
                return s.vars[name]
            s = s.parent
        v = self.G.get(name)
        if name == "Strength":
            EVENTS.append({"k": "global_read", "name": name, "value": _struct(v)})
        return v

    def call(self, f, args):
        if isinstance(f, LS.LuaFunction):
            self._stack.append(f.name)
            if TRACE_X and self._stack.count("?") and f is TRACE_X_FN[0]:
                pass
            try:
                out = super().call(f, args)
                if TRACE_X and f is TRACE_X_FN[0] and len(self.log) < 400:
                    self.log.append("X(%s) -> %d value(s) %s [depth %d]" % (
                        ", ".join(_show_any(a) for a in args[:5]), len(out),
                        [_show_any(v) for v in out[:4]], len(self._stack)))
                return out
            except LS.LuaError as e:
                if getattr(e, "stack", None) is None:
                    e.stack = list(self._stack)
                raise
            finally:
                self._stack.pop()
        if isinstance(f, Proxy):
            shown = ", ".join(_deep(a) for a in args)
            self.log.append("CALL %s(%s)" % (f.path, shown))
            EVENTS.append({"k": "call", "path": f.path, "args": [_struct(a) for a in args]})
            for a in args:
                is_toggle = (isinstance(a, LS.LuaTable)
                             and a.get("flag") == "toggle")
                for fn in _functions_in(a):
                    self.deferred.append((fn, [True] if is_toggle else []))
            return [Proxy(f.path + "()")]
        return super().call(f, args)


TRACE_X = True
TRACE_X_FN = [None]


def _show_any(v):
    if isinstance(v, LS.LuaTable):
        return "table(%d)" % len(v.hash)
    if isinstance(v, LS.LuaFunction):
        return "fn"
    if isinstance(v, Proxy):
        return v.path
    return _show(v)


def _functions_in(v, depth=0):
    if depth > 3:
        return []
    if isinstance(v, LS.LuaFunction):
        return [v]
    if isinstance(v, LS.LuaTable):
        out = []
        for val in v.hash.values():
            out.extend(_functions_in(val, depth + 1))
        return out
    return []


def _deep(v, depth=0):
    if isinstance(v, LS.LuaTable):
        if depth > 3:
            return "{...}"
        items = []
        for k_ in sorted(v.hash.keys(), key=lambda x: (str(type(x)), str(x))):
            items.append("%s = %s" % (_show(k_), _deep(v.hash[k_], depth + 1)))
        return "{" + ", ".join(items) + "}"
    if isinstance(v, LS.LuaFunction):
        return "function"
    return _show_any(v)


def _show(v):
    if isinstance(v, str):
        return repr(v)
    if isinstance(v, Proxy):
        return v.path
    if isinstance(v, float) and v.is_integer():
        return str(int(v))
    return str(v)


WATERMARK = "This file was protected with MoonSec V3"
WAIT_CLEAR_AT = 3
path_out_prefix = [None]

EVENTS = []
FN_NAMES = {}


def _fn_name(fn):
    k = id(fn)
    if k not in FN_NAMES:
        FN_NAMES[k] = "cb%d" % (len(FN_NAMES) + 1)
    return FN_NAMES[k]


def _struct(v, depth=0):
    if v is None or isinstance(v, bool) or isinstance(v, str):
        return v
    if isinstance(v, float) and v.is_integer():
        return int(v)
    if isinstance(v, (int, float)):
        return v
    if isinstance(v, Proxy):
        return {"proxy": v.path}
    if isinstance(v, (LS.LuaFunction, LS.Builtin)):
        return {"fn": _fn_name(v)}
    if isinstance(v, LS.LuaTable):
        if depth > 4:
            return {"table": "..."}
        items = sorted(v.hash.items(), key=lambda kv: (str(type(kv[0])), str(kv[0])))
        return {"table": [[_struct(k, depth + 1), _struct(x, depth + 1)] for k, x in items]}
    return {"other": type(v).__name__}


class _LogDict(dict):

    def __init__(self, base, log):
        super().__init__(base)
        self._log = log

    def get(self, k, default=None):
        if isinstance(k, str):
            self._log.append("GLOBAL_READ %s" % k)
        return super().get(k, default)


def run(path, max_steps=5_000_000, watermark_set=False, trace_globals=False):
    src = open(path, encoding="latin-1").read()
    import astcache
    tree = astcache.parse(src)
    ret = None
    for st in tree.body.body:
        if type(st).__name__ == "Return":
            ret = st
            break
    anon = B.find_first(ret.values, "AnonymousFunction")
    stmts = anon.body.body
    gi = None
    gname = None
    for i, st in enumerate(stmts):
        if type(st).__name__ == "LocalFunction" and any(
                B._is_decode_call(c) for c in B.find_all(st, "Call")):
            gi = i
            gname = st.name.id
            break
    if gi is None:
        raise SystemExit("no VM function (decode call inside a local function) found")

    log = []
    LS.LOCATE[0] = src
    trace_globals_ref = trace_globals
    LS.LOCATE_CHUNK[0] = "[string]"
    it = VMInterp(log, max_steps)
    G = it.G
    game = Proxy("game")
    G.set("game", game)
    for wm_name in ("_ZSWmDsaqpxPR", "_KRbtOqVmJMLG"):
        G.set(wm_name, WATERMARK if watermark_set else None)
    WAITS = [0]

    def _spawn(f=None, *_):
        WAITS[0] = 0
        log.append("BEGIN_SPAWN")
        EVENTS.append({"k": "spawn_begin"})
        try:
            it.call(f, [])
        except LS.LuaError as e:
            log.append("SPAWN_ERROR %s" % e)
            EVENTS.append({"k": "error", "msg": str(e)})
        log.append("END_SPAWN")
        EVENTS.append({"k": "spawn_end"})
        return []

    def _wait(*_):
        WAITS[0] += 1
        log.append("WAIT")
        EVENTS.append({"k": "wait"})
        if WAITS[0] == WAIT_CLEAR_AT:
            it.G.set("Strength", None)
        return []

    G.set("spawn", LS.Builtin("spawn", _spawn))
    G.set("wait", LS.Builtin("wait", _wait))
    def _print(*a):
        log.append("PRINT " + " ".join(_show(x) for x in a))
        EVENTS.append({"k": "print", "args": [_struct(x) for x in a]})
        return []

    G.set("print", LS.Builtin("print", _print))
    payloads = []

    def _loadstring(s=None, *_):
        log.append("LOADSTRING %s" % _show(s))
        EVENTS.append({"k": "loadstring"})
        if isinstance(s, str):
            payloads.append(s)
        return [Proxy("chunk()")]

    G.set("loadstring", LS.Builtin("loadstring", _loadstring))

    TRACE_X_FN[0] = None
    orig_pcall = it.G.get("pcall")

    def logged_pcall(f=None, *args):
        EVENTS.append({"k": "pcall_begin", "f": _struct(f),
                       "args": [_struct(x) for x in args][:4]})
        res = orig_pcall.fn(f, *args)
        msg = res[1] if len(res) > 1 else None
        log.append("PCALL ok=%s msg=%r" % (res[0], msg if not isinstance(msg, str) else msg[:160]))
        ev = {"k": "pcall", "ok": bool(res[0]),
              "msg": msg if isinstance(msg, str) else None}
        if not res[0] and LS.LAST_CALL_WHERE[0] is not None:
            ev["where"] = LS.LAST_CALL_WHERE[0]
            LS.LAST_CALL_WHERE[0] = None
        EVENTS.append(ev)
        return res

    it.G.set("pcall", LS.Builtin("pcall", logged_pcall))
    if trace_globals_ref:
        it.G.hash = _LogDict(it.G.hash, log)
    root = LS.Scope(None)
    root.vars["..."] = []
    outer_call = ret.values[0]
    interp_name = anon.args[0].id
    root.vars[interp_name] = it.ev(outer_call.args[0], root)
    TRACE_X_FN[0] = root.vars[interp_name]
    fin = it.exec_block(stmts[:gi + 1], root, new_scope=False)
    g = it.lookup_name(gname, fin)
    try:
        ytab = LS.LuaTable()
        ytab.set(1, 1.0)
        ytab.set(2, 2.0)
        ytab.set(3, 3.0)
        out = it.call(g, [ytab])
        log.append("RETURN %d value(s)" % len(out))
        EVENTS.append({"k": "return"})
        strength = it.G.get("Strength")
        if isinstance(strength, LS.LuaFunction):
            FN_NAMES[id(strength)] = "Strength"
            log.append("BEGIN_CB Strength()")
            EVENTS.append({"k": "cb_begin", "fn": "Strength", "args": []})
            try:
                it.call(strength, [])
            except LS.LuaError as e:
                log.append("CB_ERROR %s" % e)
                EVENTS.append({"k": "cb_error", "msg": str(e)})
            log.append("END_CB")
            EVENTS.append({"k": "cb_end"})
            it.G.set("Strength", strength)
        for fn, cargs in it.deferred:
            log.append("BEGIN_CB %s" % ("(true)" if cargs else "()"))
            EVENTS.append({"k": "cb_begin", "fn": _fn_name(fn),
                           "args": [_struct(c) for c in cargs]})
            try:
                it.call(fn, cargs)
            except LS.LuaError as e:
                log.append("CB_ERROR %s" % e)
                EVENTS.append({"k": "cb_error", "msg": str(e)})
            log.append("END_CB")
            EVENTS.append({"k": "cb_end"})
    except LS.LuaError as e:
        log.append("LUAERROR %s | ctx=%s" % (e, getattr(e, "ctx", None)))
        log.append("STACK %s" % " > ".join(getattr(e, "stack", None) or []))
        st_ = getattr(e, "stmt", None)
        if st_ is not None:
            try:
                txt = L.to_lua_source(st_)
            except Exception as ex:
                txt = "<render failed: %s>" % ex
            log.append("FAILING STMT: " + txt[:700].replace("\n", " "))
        sc = getattr(e, "scope", None)
        depth = 0
        while sc is not None and depth < 12:
            small = {}
            for k_, v_ in sc.vars.items():
                if isinstance(v_, (int, float, str, bool)) or v_ is None:
                    small[k_] = v_
                elif isinstance(v_, LS.Builtin):
                    small[k_] = "builtin:" + v_.name
                elif isinstance(v_, LS.LuaTable):
                    small[k_] = "table(%d)" % len(v_.hash)
                else:
                    small[k_] = type(v_).__name__
            log.append("SCOPE%d %s" % (depth, small))
            sc = sc.parent
            depth += 1
    except LS.ReturnSig as r:
        log.append("RETURN %d value(s)" % len(r.values))
    for n_, p_ in enumerate(payloads):
        out_path = "%s.payload%d.lua" % (path_out_prefix[0], n_) if path_out_prefix[0] else None
        if out_path:
            with open(out_path, "w", encoding="latin-1") as f_:
                f_.write(p_)
            log.append("PAYLOAD_WRITTEN %s (%d bytes)" % (out_path, len(p_)))
    return log, it.steps


if __name__ == "__main__":
    import threading

    sys.setrecursionlimit(1000000)
    threading.stack_size(512 * 1024 * 1024)
    box = {}
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 5_000_000
    events_path = None
    for a_ in sys.argv:
        if a_.startswith("--out="):
            path_out_prefix[0] = a_[len("--out="):]
        if a_.startswith("--events="):
            events_path = a_[len("--events="):]

    def target():
        try:
            box["out"] = run(sys.argv[1], steps, "--wm" in sys.argv,
                             "--globals" in sys.argv)
        except BaseException as e:
            box["err"] = e

    t = threading.Thread(target=target)
    t.start()
    t.join()
    if "err" in box:
        raise box["err"]
    log, nsteps = box["out"]
    if events_path:
        import json
        with open(events_path, "w", encoding="utf-8") as ef:
            json.dump({"steps": nsteps, "events": EVENTS}, ef, indent=1)
    print("steps:", nsteps)
    for line in log[:200]:
        print(line)
    print("total log lines:", len(log))
