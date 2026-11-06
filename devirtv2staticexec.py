import re
import devirtv2statictable as st
import devirtv2oracle as oracle

class luaexpr:
    def __init__(self, text, ismultival=False, isctor=False):
        self.text = text
        self.ismultival = ismultival
                                                                         
        self.isctor = isctor

class notstraightline(Exception):
    def __init__(self, kind, info):
        self.kind = kind
        self.info = info

class discoveredloophead(Exception):
                                                                           
    def __init__(self, pc):
        self.pc = pc

class marker:
    def __init__(self, name):
        self.name = name

INSTRMARK = marker("instr")
RAWMARK = marker("raw")
REGMARK = marker("reg")
ENVMARK = marker("env")
NESTEDMARK = marker("nested")
PROTOMARK = marker("proto")
DISPATCHMARK = marker("dispatch")
CALLARGSMARK = marker("callargs")
UPVALMARK = marker("upval")

def luaident(name):
    return isinstance(name, str) and name.isidentifier()

def isrenderable(v):
    try:
        rendertext(v)
        return True
    except RuntimeError:
        return False

def rendertext(v):
    if isinstance(v, luaexpr):
        return v.text
    if isinstance(v, bool):
        return "true" if v else "false"
    if v is None:
        return "nil"
    if isinstance(v, int):
        return repr(v)
    if isinstance(v, float):
        if v == int(v):
            return repr(int(v))
        return repr(v)
    if isinstance(v, str):
        return oracle.luaquote(v)
    raise RuntimeError("cannotrender " + repr(v))

class protoctx:
    def __init__(self, info, instrs, nestedprotos, numparams, protoid, upvalexprs=None):
        self.info = info
        self.instrs = instrs
        self.nestedprotos = nestedprotos
        self.numparams = numparams
        self.protoid = protoid
        self.upvalexprs = upvalexprs or {}
        self.pc = 1
        self.e = st.env(info["denv"])
        for i in range(numparams):
            self.e.set(("__reg__", i), luaexpr(self.varname(i)))
        self.e.set(info["evarkey"], INSTRMARK)
        self.e.set(info["rkey"], RAWMARK)
        self.e.set(info["lkey"], 1)
        self.e.set(info["okey"], REGMARK)
        self.e.set(info["wkey"], ENVMARK)
        self.e.set(info["mkey"], NESTEDMARK)
        self.e.set(info["pkey"], DISPATCHMARK)
        if info.get("ckey") is not None:
            self.e.set(info["ckey"], CALLARGSMARK)
        if info.get("upvalparamkey") is not None:
            self.e.set(info["upvalparamkey"], UPVALMARK)
        self.out = []
                                                                        
        self.protopre = []
        self.maxregseen = numparams
        self.returned = False
        self.loopheads = []
        self.loopbackseen = False
        self.regtable = None
        self.loopvarseq = 0
        self.knownloopheads = set()
        self.exitstoppc = None
        self.loopexitmode = False
        self.cfgprobe = False

    def varname(self, idx):
        return "v" + str(self.protoid) + "_" + str(idx)

    def setpc(self, v):
        v = int(v)
        self.pc = v
        self.e.set(self.info["lkey"], v)

    def materialize(self, idx):
                                                                             
        key = ("__reg__", idx)
        try:
            cur = self.e.get(key)
        except st.notfoldable:
            cur = None
        name = self.varname(idx)
        if isinstance(cur, luaexpr) and cur.text == name:
            return name
        self.out.append("local " + name + " = " + rendertext(cur))
        self.e.set(key, luaexpr(name))
        self.maxregseen = max(self.maxregseen, idx)
        return name

    def curinstr(self):
        return self.instrs[self.pc - 1]

def getfield(ctx, idx):
    instr = ctx.curinstr()
    key = str(int(idx))
    return instr.get(key)

def getfieldat(ctx, pc, idx):
    instr = ctx.instrs[pc - 1]
    key = str(int(idx))
    return instr.get(key)

def foldorreg(node, ctx):
    try:
        return st.foldexpr(node, ctx.e)
    except st.notfoldable:
        return evalexpr(node, ctx)

def parenctor(base):
                                                                          
    if getattr(base, "isctor", False):
        return "(" + base.text + ")"
    return base.text

def evalexpr(node, ctx):
    t = node["type"]
    if t == "AstExprConstantNumber":
        return node["value"]
    if t == "AstExprConstantString":
        return node["value"]
    if t == "AstExprConstantBool":
        return node["value"]
    if t == "AstExprConstantNil":
        return None
    if t == "AstExprGroup":
        return evalexpr(node["expr"], ctx)
    if t == "AstExprLocal":
        key = st.localkey(node["local"])
        try:
            v = ctx.e.get(key)
        except st.notfoldable:
            raise RuntimeError("trulyunbound " + str(key))
        if v is st.UNRESOLVED:
            return materializelocal(ctx, key)
        return v
    if t == "AstExprUnary":
        v = evalexpr(node["expr"], ctx)
        if isinstance(v, luaexpr):
            opmap = {"Minus": "-", "Not": "not ", "Len": "#"}
            return luaexpr("(" + opmap[node["op"]] + v.text + ")")
        if node["op"] == "Minus":
            return -v
        if node["op"] == "Not":
            return not st.truthy(v)
        if node["op"] == "Len":
            return len(v)
        raise RuntimeError("unaryop")
    if t == "AstExprBinary":
        op = node["op"]
        if op == "And":
            lv = evalexpr(node["left"], ctx)
            if isinstance(lv, luaexpr):
                rv = evalexpr(node["right"], ctx)
                return luaexpr("(" + lv.text + " and " + rendertext(rv) + ")")
            if not st.truthy(lv):
                return lv
            return evalexpr(node["right"], ctx)
        if op == "Or":
            lv = evalexpr(node["left"], ctx)
            if isinstance(lv, luaexpr):
                rv = evalexpr(node["right"], ctx)
                return luaexpr("(" + lv.text + " or " + rendertext(rv) + ")")
            if st.truthy(lv):
                return lv
            return evalexpr(node["right"], ctx)
        lv = evalexpr(node["left"], ctx)
        rv = evalexpr(node["right"], ctx)
                                                                          
        _plain = (int, float, str, bool)
        if not (isinstance(lv, _plain) and isinstance(rv, _plain)):
            symmap = {
                "Add": "+", "Sub": "-", "Mul": "*", "Div": "/", "Mod": "%", "Pow": "^",
                "Concat": "..", "CompareEq": "==", "CompareNe": "~=", "CompareLt": "<",
                "CompareLe": "<=", "CompareGt": ">", "CompareGe": ">="
            }
            if op in symmap:
                return luaexpr("(" + rendertext(lv) + symmap[op] + rendertext(rv) + ")")
            raise RuntimeError("binopsym " + op)
        if op == "Add":
            return lv + rv
        if op == "Sub":
            return lv - rv
        if op == "Mul":
            return lv * rv
        if op == "Div":
            return lv / rv
        if op == "Mod":
            return lv - (lv // rv) * rv
        if op == "Pow":
            return lv ** rv
        if op == "Concat":
            return str(lv) + str(rv)
        if op == "CompareEq":
            return lv == rv
        if op == "CompareNe":
            return lv != rv
        if op == "CompareLt":
            return lv < rv
        if op == "CompareLe":
            return lv <= rv
        if op == "CompareGt":
            return lv > rv
        if op == "CompareGe":
            return lv >= rv
        raise RuntimeError("binop " + op)
    if t == "AstExprIfElse":
        cv = evalexpr(node["condition"], ctx)
        if isinstance(cv, luaexpr):
            raise notstraightline("dynamicif", node)
        if st.truthy(cv):
            return evalexpr(node["trueExpr"], ctx)
        return evalexpr(node["falseExpr"], ctx)
    if t == "AstExprIndexExpr":
        base = evalexpr(node["expr"], ctx)
        if base is INSTRMARK:
            idx = evalexpr(node["index"], ctx)
            return getfield(ctx, idx)
        if base is RAWMARK:
            idx = evalexpr(node["index"], ctx)
            if idx == ctx.pc:
                return INSTRMARK
            raise notstraightline("rawindexother", idx)
        if base is REGMARK:
            idx = evalexpr(node["index"], ctx)
            if ctx.regtable is not None:
                return luaexpr(ctx.regtable + "[" + rendertext(idx) + "]")
            if isinstance(idx, luaexpr):
                name = ensureregtable(ctx)
                return luaexpr(name + "[" + idx.text + "]")
            if idx is None:
                raise notstraightline("nilregindex", node)
            try:
                idx = int(idx)
            except (TypeError, ValueError):
                                                                          
                name = ensureregtable(ctx)
                return luaexpr(name + "[" + rendertext(idx) + "]")
            ctx.maxregseen = max(ctx.maxregseen, idx)
            try:
                return ctx.e.get(("__reg__", idx))
            except st.notfoldable:
                return luaexpr(ctx.varname(idx))
        if base is UPVALMARK:
            idx = evalexpr(node["index"], ctx)
            if isinstance(idx, luaexpr):
                raise notstraightline("dynamicupvalread", idx)
            idx = int(idx)
            target = ctx.upvalexprs.get(idx)
            if target is None:
                raise notstraightline("unknownupvalread", idx)
            return target
        if base is ENVMARK:
            idx = evalexpr(node["index"], ctx)
            if isinstance(idx, luaexpr):
                raise notstraightline("dynamicenvindex", idx)
            return luaexpr(str(idx) if luaident(idx) else "_G[" + oracle.luaquote(str(idx)) + "]")
        if base is PROTOMARK:
            idx = evalexpr(node["index"], ctx)
            if isinstance(idx, luaexpr):
                raise notstraightline("dynamicprotoindex", idx)
            idx = int(idx)
            if idx == 3:
                return ctx.numparams
                                                                         
            raise notstraightline("protofieldnotstatic", idx)
        if base is NESTEDMARK:
            idx = evalexpr(node["index"], ctx)
            return ("subproto", idx)
        if isinstance(base, tuple) and base[0] == "subproto":
            raise RuntimeError("indexintosubproto")
        if isinstance(base, tuple) and base[0] == "vtable":
            idx = foldorreg(node["index"], ctx)
            if isinstance(idx, luaexpr):
                raise notstraightline("dynamicvtableindex", idx)
            return base[1][int(idx) - 1]
        if isinstance(base, luaexpr):
            idx = evalexpr(node["index"], ctx)
            return luaexpr(parenctor(base) + "[" + rendertext(idx) + "]")
        raise RuntimeError("indexunknownbase " + repr(base))
    if t == "AstExprIndexName":
        base = evalexpr(node["expr"], ctx)
        if isinstance(base, luaexpr):
            return luaexpr(parenctor(base) + "." + node["index"])
        raise RuntimeError("indexnameunknownbase")
    if t == "AstExprTable":
        if all(it["kind"] == "item" for it in node["items"]):
            vals = [evalexpr(it["value"], ctx) for it in node["items"]]
            if any(not isrenderable(v) for v in vals):
                                                                          
                return ("vtable", vals)
        parts = []
        for it in node["items"]:
            kind = it["kind"]
            if kind == "item":
                v = evalexpr(it["value"], ctx)
                parts.append(rendertext(v))
            elif kind == "record":
                keyname = it["key"]["value"]
                v = evalexpr(it["value"], ctx)
                if luaident(keyname):
                    parts.append(keyname + " = " + rendertext(v))
                else:
                    parts.append("[" + oracle.luaquote(str(keyname)) + "] = " + rendertext(v))
            elif kind == "general":
                kv = evalexpr(it["key"], ctx)
                v = evalexpr(it["value"], ctx)
                parts.append("[" + rendertext(kv) + "] = " + rendertext(v))
            else:
                raise notstraightline("tableitemkind", it)
        return luaexpr("{" + ", ".join(parts) + "}", isctor=True)
    if t == "AstExprCall":
        func = node["func"]
        fval = evalexpr(func, ctx)
        if fval is DISPATCHMARK:
            args = node["args"]
            subprotoval = evalexpr(args[0], ctx)
            upvalval = evalexpr(args[1], ctx) if len(args) > 1 else None
            return makeclosurecall(ctx, subprotoval, upvalval)
        if fval is CALLARGSMARK:
            args = node["args"]
            start = foldorreg(args[1], ctx)
            end = foldorreg(args[2], ctx)
            return buildregrange(ctx, start, end)
        if isinstance(fval, luaexpr):
            argtext = renderarglist(node["args"], ctx)
            return luaexpr(fval.text + "(" + argtext + ")")
        raise notstraightline("call", node)
    raise notstraightline("expr", node)

def buildregrange(ctx, start, end):
                                                                        
    if isinstance(start, luaexpr) or isinstance(end, luaexpr) or ctx.regtable is not None:
                                                                           
        name = ensureregtable(ctx)
        return luaexpr("table.unpack(" + name + ", " + rendertext(start) + ", " + rendertext(end) + ")", ismultival=True)
    start = int(start)
    end = int(end)
    if start > end:
        return luaexpr("", ismultival=True)
    parts = []
    for i in range(start, end + 1):
        try:
            v = ctx.e.get(("__reg__", i))
        except st.notfoldable:
            v = None
        parts.append(rendertext(v))
    return luaexpr(", ".join(parts), ismultival=True)

def renderarglist(args, ctx):
    parts = []
    n = len(args)
    for i, a in enumerate(args):
        v = evalexpr(a, ctx)
        if getattr(v, "ismultival", False):
            if i != n - 1:
                raise notstraightline("multivalnotlast", a)
            if v.text != "":
                parts.append(v.text)
            continue
        parts.append(rendertext(v))
    return ", ".join(parts)

def makeclosurecall(ctx, subprotoval, upvalval):
    if getattr(ctx, "cfgprobe", False):
                                                                       
        return luaexpr("nil")
    if not (isinstance(subprotoval, tuple) and subprotoval[0] == "subproto"):
        raise notstraightline("closurenonconstproto", subprotoval)
    idx = subprotoval[1]
    subproto = ctx.nestedprotos[str(idx)]
    code = compileprotobody(ctx.info, subproto)
    return luaexpr(code)

def _opensblock(s):
    return bool(
        re.match(r"^if\b.*\bthen$", s)
        or re.match(r"^elseif\b.*\bthen$", s)
        or re.match(r"^while\b.*\bdo$", s)
        or re.match(r"^for\b.*\bdo$", s)
        or re.match(r"^do$", s)
        or re.match(r"^(local\s+)?function\b.*\)$", s)
        or re.search(r"=\s*function\s*\(.*\)$", s)
    )

def _iscloser(s):
    return s == "end" or s == "end)"

def deadcodeafterreturn(text):
    lines = text.split("\n")
    out = []
    i = 0
    n = len(lines)
    while i < n:
        s = lines[i].strip()
        if s.startswith("return"):
            out.append(lines[i])
            i += 1
            pending = 0
            while i < n:
                s2 = lines[i].strip()
                if pending == 0 and (_iscloser(s2) or s2.startswith("else")
                                     or s2.startswith("elseif")):
                    break
                if _opensblock(s2):
                    pending += 1
                elif _iscloser(s2):
                    pending -= 1
                i += 1
            continue
        out.append(lines[i])
        i += 1
    return "\n".join(out)

def compileprotobody(info, proto, upvalexprs=None):
    instrs = proto["1"]
    n = len(instrs)
    instrlist = [instrs[str(i)] for i in range(1, n + 1)]
    nested = proto["2"]
    numparams = proto["3"]
    protokey = id(proto)
    knownheads = info.setdefault("loopheadsbyproto", {}).setdefault(protokey, set())
                                                                      
    preheads = None
    droppedpreheads = False
                                                                         
    protoid = next(info["protoidgen"])
    primaryerror = None
    stmts = None
    subctx = None
    while True:
        subctx = protoctx(info, instrlist, nested, numparams, protoid, upvalexprs)
        subctx.knownloopheads = knownheads
        try:
            stmts = compilerange(subctx, 1, n + 1)
            break
        except discoveredloophead as e:
            if e.pc in knownheads:
                primaryerror = RuntimeError("loopheaddetectionloop " + str(e.pc))
                break
            knownheads.add(e.pc)
            continue
        except notstraightline as e:
            if preheads and not droppedpreheads:
                knownheads.difference_update(preheads)
                droppedpreheads = True
                continue
            primaryerror = e
            break
        except RecursionError as e:
                                                                           
            primaryerror = e
            break
    if stmts is None:
                                                                          
        info.setdefault("cfgfallbacks", []).append(
            {"protoid": protoid,
             "reason": "%s: %s" % (type(primaryerror).__name__,
                                   str(primaryerror)[:120])})
        return compileprotobodycfg(info, proto, upvalexprs)
    paramparts = [subctx.varname(i) for i in range(numparams)] + ["..."]
    params = ", ".join(paramparts)
                                                                         
    body = "\n".join(list(subctx.protopre) + stmts)
    return "function(" + params + ")\n" + body + "\nend"

def _scanstmt(stmt, ctx, targets):
                                                                       
    t = stmt["type"]
    lkey = ctx.info["lkey"]
    if t == "AstStatAssign":
        for var, val in zip(stmt["vars"], stmt["values"]):
            if var["type"] == "AstExprLocal" and st.localkey(var["local"]) == lkey:
                try:
                    v = foldorreg(val, ctx)
                except Exception:
                    v = None
                targets.add(None if (v is None or isinstance(v, luaexpr)) else int(v))
        return
    if t == "AstStatCompoundAssign":
        var = stmt["var"]
        if var["type"] == "AstExprLocal" and st.localkey(var["local"]) == lkey:
            synth = {"type": "AstExprBinary", "op": stmt["op"],
                     "left": var, "right": stmt["value"]}
            try:
                v = foldorreg(synth, ctx)
            except Exception:
                v = None
            targets.add(None if (v is None or isinstance(v, luaexpr)) else int(v))
        return
    if t == "AstStatIf":
        for b in (stmt.get("thenbody"), stmt.get("elsebody")):
            if b is not None:
                _scanstmt(b, ctx, targets)
        return
    if t == "AstStatBlock":
        _scanstmts(stmt["body"], ctx, targets)
        return
    if t == "AstStatWhile":
        _scanstmt(stmt["body"], ctx, targets)
        return

def _scanstmts(stmts, ctx, targets):
    i = 0
    n = len(stmts)
    while i < n:
        s = stmts[i]
        if s["type"] == "AstStatIf" and i + 1 < n:
            d = _pcepiloguedelta(stmts[i + 1], ctx)
            if d is not None:
                sub = set()
                _scanstmt(s, ctx, sub)
                for v in sub:
                    targets.add(None if v is None else v + d)
                i += 2
                continue
        _scanstmt(s, ctx, targets)
        i += 1

def _pcsuccessors(info, instrs, nested, numparams, p):
    ctx = protoctx(info, instrs, nested, numparams, 0)
    ctx.cfgprobe = True
    ctx.pc = p
    ctx.e.set(info["lkey"], p)
    try:
        opval = getfield(ctx, info["opfieldidx"])
    except Exception:
        return {p + 1}
    uvinfo = info["uvclosureops"].get(opval)
    if uvinfo is not None:
        try:
            k = int(getfield(ctx, uvinfo.numupvalsfield))
        except Exception:
            return {p + 1}
        return {p + k + 1}
    handler = info["table"].get(opval)
    if handler is None:
        return {p + 1}
    targets = set()
    try:
        _scanstmts(handler, ctx, targets)
    except Exception:
        return {p + 1}
    if None in targets or not targets:
        return {p + 1}
    return set(int(v) for v in targets)

def _loopheaders(n, succs):
                                                                        
    reach = set()
    stack = [1]
    while stack:
        u = stack.pop()
        if u in reach:
            continue
        reach.add(u)
        for v in succs.get(u, ()):
            if 1 <= v <= n and v not in reach:
                stack.append(v)
    preds = dict((i, set()) for i in range(1, n + 1))
    for u in reach:
        for v in succs.get(u, ()):
            if 1 <= v <= n:
                preds[v].add(u)
    dom = dict((i, set(reach)) for i in reach)
    dom[1] = {1}
    changed = True
    while changed:
        changed = False
        for i in sorted(reach):
            if i == 1:
                continue
            ps = [q for q in preds[i] if q in reach]
            new = set.intersection(*[dom[q] for q in ps]) if ps else set()
            new.add(i)
            if new != dom[i]:
                dom[i] = new
                changed = True
    heads = set()
    for u in reach:
        for v in succs.get(u, ()):
            if 1 <= v <= n and v in dom.get(u, ()):
                heads.add(v)
    return heads

def discoverloopheads(info, instrs, nested, numparams):
                                                                      
    n = len(instrs)
    succs = {}
    for p in range(1, n + 1):
        succs[p] = _pcsuccessors(info, instrs, nested, numparams, p)
    return _loopheaders(n, succs)

def _cfgdominators(adj, start):
    nodes = set()
    for u in adj:
        nodes.add(u)
        for v in adj[u]:
            nodes.add(v)
    reach = set()
    stack = [start]
    while stack:
        u = stack.pop()
        if u in reach:
            continue
        reach.add(u)
        for v in adj.get(u, ()):
            if v not in reach:
                stack.append(v)
    preds = dict((x, set()) for x in nodes)
    for u in reach:
        for v in adj.get(u, ()):
            preds.setdefault(v, set()).add(u)
    dom = dict((x, set(reach)) for x in reach)
    if start in dom:
        dom[start] = {start}
    changed = True
    while changed:
        changed = False
        for x in sorted(reach):
            if x == start:
                continue
            ps = [q for q in preds.get(x, ()) if q in reach]
            new = set.intersection(*[dom[q] for q in ps]) if ps else set()
            new.add(x)
            if new != dom[x]:
                dom[x] = new
                changed = True
    return dom, reach

def _cfgnaturalloop(preds, header, backsources):
    body = {header}
    stack = list(backsources)
    while stack:
        x = stack.pop()
        if x in body:
            continue
        body.add(x)
        for q in preds.get(x, ()):
            if q not in body:
                stack.append(q)
    return body

def _cfgpostdoms(n, succs):
                                                                        
    exitnode = n + 1
    adj = dict((i, set()) for i in range(1, n + 2))
    for u in range(1, n + 1):
        s = [v for v in succs.get(u, ()) if 1 <= v <= n]
        if s:
            for v in s:
                adj[u].add(v)
        else:
            adj[u].add(exitnode)
    rev = dict((i, set()) for i in range(1, n + 2))
    for u in adj:
        for v in adj[u]:
            rev[v].add(u)
    dom, reach = _cfgdominators(rev, exitnode)
    ipdom = {}
    for u in range(1, n + 1):
        cands = [q for q in dom.get(u, ()) if q != u and q <= n]
        if cands:
            ipdom[u] = max(cands, key=lambda q: len(dom.get(q, ())))
    return dom, ipdom

def _assignspc(stmt, ctx):
    lkey = ctx.info["lkey"]
    if stmt["type"] == "AstStatAssign":
        return any(v["type"] == "AstExprLocal" and st.localkey(v["local"]) == lkey
                   for v in stmt["vars"])
    if stmt["type"] == "AstStatCompoundAssign":
        v = stmt["var"]
        return v["type"] == "AstExprLocal" and st.localkey(v["local"]) == lkey
    return False

def cfgemiteffects(ctx, p):
                                                                           
    opval = getfield(ctx, ctx.info["opfieldidx"])
    handler = ctx.info["table"].get(opval)
    if handler is None:
        raise notstraightline("cfgnohandler", opval)
    cond = None
    i = 0
    n = len(handler)
    while i < n:
        s = handler[i]
        if s["type"] == "AstStatIf":
            targets = set()
            _scanstmt(s, ctx, targets)
            if targets:
                cond = evalexpr(s["condition"], ctx)
                i += 2 if (i + 1 < n and _pcepiloguedelta(handler[i + 1], ctx) is not None) else 1
                continue
        if _assignspc(s, ctx):
            i += 1
            continue
        execstmt(s, ctx)
        i += 1
    return cond

def _cfgemitnode(ctx, p, env, out, loopstack):
    n = env["n"]
                                                                        
    savedout = ctx.out
    ctx.out = out
    try:
        cond = cfgemiteffects(ctx, p)
    finally:
        ctx.out = savedout
    succ = [s for s in env["succs"][p] if 1 <= s <= n]
    if loopstack:
        succ = [s for s in succ if s != loopstack[-1]]
    if not succ:
        return None
    if len(succ) == 1:
        return succ[0]
    a, b = succ[0], succ[1]
    m = env["ipdom"].get(p)
    stop = {m} if (m is not None and m != p) else set()
    condtext = cond.text if cond is not None else "true"
    aout = []
    _cfgemitpath(ctx, a, env, aout, loopstack, stop, 0)
    bout = []
    _cfgemitpath(ctx, b, env, bout, loopstack, stop, 0)
    out.append("if " + condtext + " then")
    out.extend(indentlines(aout))
    out.append("else")
    out.extend(indentlines(bout))
    out.append("end")
    return m

def _cfglastisreturn(lst):
                                                                       
    for x in reversed(lst):
        s = x.strip()
        if s:
            return s.startswith("return")
    return False

def _cfgemitpath(ctx, p, env, out, loopstack, stop, depth):
    n = env["n"]
    if depth > 64:
        raise notstraightline("cfgdepth", p)
    while p is not None and 1 <= p <= n:
        if _cfglastisreturn(out):
            return None
        if p in stop:
            return p
        if loopstack and p == loopstack[-1]:
            return p
        if loopstack:
            header = loopstack[-1]
            if p not in env["loopbody"].get(header, {p}):
                out.append("break")
                return None
        if p in env["heads"] and p not in loopstack:
            bodyout = []
            _cfgemitpath(ctx, p, env, bodyout, loopstack + [p], set(), depth + 1)
            out.append("while true do")
            out.extend(indentlines(bodyout))
            out.append("end")
            region = env["loopbody"].get(p, set())
            exits = set()
            for x in region:
                for s in env["succs"][x]:
                    if s not in region:
                        exits.add(s)
            if len(exits) == 1:
                p = exits.pop()
                continue
            return None
        p = _cfgemitnode(ctx, p, env, out, loopstack)
    return None

def compileprotobodycfg(info, proto, upvalexprs=None):
    instrs = proto["1"]
    n = len(instrs)
    instrlist = [instrs[str(i)] for i in range(1, n + 1)]
    nested = proto["2"]
    numparams = proto["3"]
    protoid = next(info["protoidgen"])
    succs = {}
    for p in range(1, n + 1):
        succs[p] = sorted(v for v in _pcsuccessors(info, instrlist, nested, numparams, p)
                          if 1 <= v <= n)
    preds = dict((i, set()) for i in range(1, n + 1))
    for u in range(1, n + 1):
        for v in succs[u]:
            preds[v].add(u)
    dom, reach = _cfgdominators(succs, 1)
    heads = set()
    for u in range(1, n + 1):
        for v in succs[u]:
            if v in dom.get(u, ()):
                heads.add(v)
    loopbody = {}
    for h in heads:
        srcs = [u for u in range(1, n + 1) if h in succs[u] and u != h and h in dom.get(u, ())]
        loopbody[h] = _cfgnaturalloop(preds, h, srcs)
    _, ipdom = _cfgpostdoms(n, succs)
    env = {"n": n, "succs": succs, "heads": heads, "loopbody": loopbody, "ipdom": ipdom}
    ctx = protoctx(info, instrlist, nested, numparams, protoid, upvalexprs)
    out = []
    _cfgemitpath(ctx, 1, env, out, [], set(), 0)
    paramparts = [ctx.varname(i) for i in range(numparams)] + ["..."]
    return "function(" + ", ".join(paramparts) + ")\n" + "\n".join(out) + "\nend"

def writereg(ctx, idx, val):
    name = ctx.varname(idx)
    key = ("__reg__", idx)
    try:
        cur = ctx.e.get(key)
        alreadyreal = isinstance(cur, luaexpr) and cur.text == name
    except st.notfoldable:
        alreadyreal = False
    ctx.e.set(key, luaexpr(name))
    ctx.maxregseen = max(ctx.maxregseen, idx)
    if alreadyreal:
        ctx.out.append(name + " = " + rendertext(val))
    else:
        ctx.out.append("local " + name + " = " + rendertext(val))

def assigntarget(var, val, ctx):
    if var["type"] == "AstExprLocal":
        key = st.localkey(var["local"])
        ctx.e.set(key, val)
        return
    if var["type"] == "AstExprIndexExpr":
        base = evalexpr(var["expr"], ctx)
        if base is REGMARK:
            idx = evalexpr(var["index"], ctx)
            if ctx.regtable is not None:
                ctx.out.append(ctx.regtable + "[" + rendertext(idx) + "] = " + rendertext(val))
                return
            if isinstance(idx, luaexpr):
                name = ensureregtable(ctx)
                ctx.out.append(name + "[" + idx.text + "] = " + rendertext(val))
                return
            idx = int(idx)
            writereg(ctx, idx, val)
            return
        if base is UPVALMARK:
            idx = evalexpr(var["index"], ctx)
            if isinstance(idx, luaexpr):
                raise notstraightline("dynamicupvalwrite", idx)
            idx = int(idx)
            target = ctx.upvalexprs.get(idx)
            if target is None:
                raise notstraightline("unknownupvalwrite", idx)
            ctx.out.append(target.text + " = " + rendertext(val))
            return
        if base is ENVMARK:
            idx = evalexpr(var["index"], ctx)
            if isinstance(idx, luaexpr):
                raise notstraightline("dynamicenvwrite", idx)
            name = str(idx) if luaident(idx) else "_G[" + oracle.luaquote(str(idx)) + "]"
            ctx.out.append(name + " = " + rendertext(val))
            return
        if isinstance(base, luaexpr):
            idx = evalexpr(var["index"], ctx)
            ctx.out.append(base.text + "[" + rendertext(idx) + "] = " + rendertext(val))
            return
    raise notstraightline("assigntarget", var)

def _localsdeclaredin(node):
    out = set()

    def rec(n):
        if isinstance(n, dict):
            t = n.get("type")
            if t == "AstStatLocal":
                for v in n.get("vars", []) or []:
                    out.add(st.localkey(v))
            elif t == "AstStatLocalFunction":
                nm = n.get("name")
                if nm:
                    out.add(st.localkey(nm))
            elif t == "AstExprFunction":
                for p in n.get("args", []) or []:
                    if isinstance(p, dict) and p.get("type") == "AstLocal":
                        out.add(st.localkey(p))
            for k, v in n.items():
                if k in ("type", "location", "name"):
                    continue
                rec(v)
        elif isinstance(n, list):
            for x in n:
                rec(x)

    rec(node)
    return out

def findfreelocalrefs(node, acc=None, bound=frozenset()):
    acc = acc if acc is not None else []
    if isinstance(node, dict):
        t = node.get("type")
        if t in ("AstExprFunction", "AstStatLocalFunction"):
            inner = bound | _localsdeclaredin(node)
            for k, v in node.items():
                if k in ("type", "location", "name"):
                    continue
                findfreelocalrefs(v, acc, inner)
            return acc
        if t == "AstExprLocal":
            key = st.localkey(node["local"])
            if key not in bound:
                acc.append(key)
            return acc
        for k, v in node.items():
            if k in ("type", "location", "name"):
                continue
            findfreelocalrefs(v, acc, bound)
    elif isinstance(node, list):
        for v in node:
            findfreelocalrefs(v, acc, bound)
    return acc

def declvarkeys(decl):
    if decl["type"] == "AstStatLocalFunction":
        return [st.localkey(decl["name"])]
    return [st.localkey(v) for v in decl["vars"]]

def declvaluefor(decl, key, varkeys):
    if decl["type"] == "AstStatLocalFunction":
        return None
    values = decl.get("values", [])
    i = varkeys.index(key)
    return values[i] if i < len(values) else None

def _folddeclvalue(decl, ctx, varkeys):
    if len(varkeys) != 1:
        return None
    try:
        val = declvaluefor(decl, varkeys[0], varkeys)
    except Exception:
        return None
    if val is None:
        return None
    try:
        r = evalexpr(val, ctx)
    except Exception:
        return None
    if isinstance(r, (bool, int, float, str)):
        return r
    return None

def ensurebound(ctx, key, seen=None):
                                                                           
    seen = seen if seen is not None else set()
    if key in seen:
        raise RuntimeError("materializecycle " + str(key))
    seen = seen | {key}
    info = ctx.info
    name = key[0]
    isinner = key in info["innerdecls"]
    ismodule = ((not isinner)
                and (key in info["moduledecls"] or key in info["outerdecls"]))
    if not isinner and not ismodule:
        try:
            cur = ctx.e.get(key)
        except st.notfoldable:
            raise RuntimeError("trulyunbound " + str(key))
        if cur is st.UNRESOLVED:
            raise RuntimeError("trulyunbound " + str(key))
        return cur
    if isinner:
        try:
            cur = ctx.e.get(key)
        except st.notfoldable:
            cur = st.UNRESOLVED
                                                                              
        if cur is not st.UNRESOLVED and not isinstance(cur, luaexpr):
            return cur
        if isinstance(cur, luaexpr) and cur.text == name:
            return cur
        decl = info["innerdecls"][key]
        if isinstance(decl, dict) and decl.get("__protoobj__"):
            ctx.e.set(key, PROTOMARK)
            return PROTOMARK
        varkeys = declvarkeys(decl)
        if cur is st.UNRESOLVED:
            for vk in varkeys:
                val = declvaluefor(decl, vk, varkeys)
                if val is not None:
                    for dep in findfreelocalrefs(val):
                        ensurebound(ctx, dep, seen)
            folded = _folddeclvalue(decl, ctx, varkeys)
            if folded is not None:
                ctx.e.set(varkeys[0], folded)
                return folded
            text = st.rawtext(info["path"], decl["location"])
            ctx.out.append(text)
            for vk in varkeys:
                ctx.e.set(vk, luaexpr(vk[0]))
            return ctx.e.get(key)
        rendered = rendertext(cur)
        ctx.out.append("local " + name + " = " + rendered)
        ctx.e.set(key, luaexpr(name))
        return luaexpr(name)
                  
    if key not in info["denv"].vals:
        cur = st.UNRESOLVED
    else:
        cur = info["denv"].vals[key]
    if cur is not st.UNRESOLVED and not isinstance(cur, luaexpr):
        return cur
    if isinstance(cur, luaexpr) and cur.text == name:
        return cur
    decl = info["moduledecls"].get(key) or info["outerdecls"][key]
    if isinstance(decl, dict) and decl.get("__protoobj__"):
        info["denv"].vals[key] = PROTOMARK
        ctx.e.set(key, PROTOMARK)
        return PROTOMARK
    varkeys = declvarkeys(decl)
    if cur is st.UNRESOLVED:
        for vk in varkeys:
            val = declvaluefor(decl, vk, varkeys)
            if val is not None:
                for dep in findfreelocalrefs(val):
                    ensurebound(ctx, dep, seen)
        folded = _folddeclvalue(decl, ctx, varkeys)
        if folded is not None:
            info["denv"].vals[varkeys[0]] = folded
            return folded
        text = st.rawtext(info["path"], decl["location"])
        info["modulepreamble"].append(text)
        for vk in varkeys:
            info["denv"].vals[vk] = luaexpr(vk[0])
        return info["denv"].vals[key]
    rendered = rendertext(cur)
    info["modulepreamble"].append("local " + name + " = " + rendered)
    info["denv"].vals[key] = luaexpr(name)
    return info["denv"].vals[key]

def materializelocal(ctx, key, seen=None):
    return ensurebound(ctx, key, seen)

def allocreg(ctx):
    idx = ctx.maxregseen + 1
    ctx.maxregseen = idx
    return ctx.varname(idx)

def ensureregtable(ctx):
                                                                         
    if ctx.regtable is not None:
        return ctx.regtable
    name = "vreg" + str(ctx.protoid)
                                                                           
    ctx.protopre.append("local " + name + " = {}")
    for i in range(0, ctx.maxregseen + 1):
        try:
            v = ctx.e.get(("__reg__", i))
        except st.notfoldable:
            continue
        if isinstance(v, luaexpr) and v.text == ctx.varname(i):
                                                                      
            pass
        ctx.out.append(name + "[" + str(i) + "] = " + rendertext(v))
    ctx.regtable = name
    return name

def execassign(stmt, ctx):
    var = stmt["vars"][0]
    val = evalexpr(stmt["values"][0], ctx)
    assigntarget(var, val, ctx)

def execmultiassign(stmt, ctx):
                                                                       
    rhs = stmt["values"][0]
    val = evalexpr(rhs, ctx)
    if not isinstance(val, luaexpr):
        raise notstraightline("multiassignvalue", stmt)
    names = [allocreg(ctx) for _ in stmt["vars"]]
    ctx.out.append("local " + ", ".join(names) + " = " + val.text)
    for var, name in zip(stmt["vars"], names):
        assigntarget(var, luaexpr(name), ctx)

def execstmt(stmt, ctx):
    t = stmt["type"]
    if t == "AstStatCompoundAssign":
        var = stmt["var"]
        if var["type"] == "AstExprLocal" and st.localkey(var["local"]) == ctx.info["lkey"]:
            synth = {"type": "AstExprBinary", "op": stmt["op"], "left": var, "right": stmt["value"]}
            handlepcassign(synth, ctx)
        return
    if t == "AstStatLocal":
        for var, val in zip(stmt["vars"], stmt.get("values", [])):
            v = evalexpr(val, ctx)
            ctx.e.set(st.localkey(var), v)
        for var in stmt["vars"][len(stmt.get("values", [])):]:
            ctx.e.set(st.localkey(var), None)
        return
    if t == "AstStatAssign":
        if len(stmt["vars"]) != 1:
            if len(stmt["values"]) == 1 and stmt["values"][0]["type"] == "AstExprCall":
                execmultiassign(stmt, ctx)
                return
            raise notstraightline("multiassign", stmt)
        lhs = stmt["vars"][0]
        if lhs["type"] == "AstExprLocal":
            key = st.localkey(lhs["local"])
            if key == ctx.info["lkey"]:
                handlepcassign(stmt["values"][0], ctx)
                return
            if key == ctx.info["evarkey"]:
                handleinstrassign(stmt["values"][0], ctx)
                return
        execassign(stmt, ctx)
        return
    if t == "AstStatReturn":
        parts = [rendertext(evalexpr(v, ctx)) for v in stmt["list"]]
        ctx.out.append(("return " + ", ".join(parts)).rstrip())
        ctx.returned = True
        return
    if t == "AstStatBreak":
        return
    if t == "AstStatExpr":
        v = evalexpr(stmt["expr"], ctx)
        ctx.out.append(rendertext(v))
        return
    if t == "AstStatBlock":
        for s in stmt["body"]:
            execstmt(s, ctx)
            if ctx.returned:
                break
        return
    if t == "AstStatIf":
        handleifstmt(stmt, ctx)
        return
    if t == "AstStatFor":
                                                                     
        fromv = foldorreg(stmt["from"], ctx)
        tov = foldorreg(stmt["to"], ctx)
        stepnode = stmt.get("step")
        stepv = foldorreg(stepnode, ctx) if stepnode is not None else 1
        if isinstance(fromv, luaexpr) or isinstance(tov, luaexpr) or isinstance(stepv, luaexpr):
                                                                        
            loopvarname = "vfl" + str(ctx.protoid) + "_" + str(ctx.loopvarseq)
            ctx.loopvarseq += 1
            varkey = st.localkey(stmt["var"])
            savedreturned = ctx.returned
            savede = ctx.e
            ctx.e = ctx.e.child()
            ctx.e.set(varkey, luaexpr(loopvarname))
            savedout = ctx.out
            ctx.out = []
            for s in stmt["body"]["body"]:
                execstmt(s, ctx)
                if ctx.returned:
                    break
            body = ctx.out
            ctx.out = savedout
            ctx.e = savede
            ctx.returned = savedreturned
            header = "for " + loopvarname + " = " + rendertext(fromv) + ", " + rendertext(tov)
            if stepnode is not None:
                header += ", " + rendertext(stepv)
            header += " do"
            ctx.out.append(header)
            ctx.out.extend(indentlines(body))
            ctx.out.append("end")
            return
        fromv = int(fromv)
        tov = int(tov)
        stepv = int(stepv)
        varkey = st.localkey(stmt["var"])
        i = fromv
        while (stepv > 0 and i <= tov) or (stepv < 0 and i >= tov):
            ctx.e.set(varkey, i)
            for s in stmt["body"]["body"]:
                execstmt(s, ctx)
                if ctx.returned:
                    break
            if ctx.returned:
                break
            i += stepv
        return
    raise notstraightline("stmt", stmt)

def checkbackward(ctx, target):
                                                                     
    if target < 1:
        return
    if target <= ctx.pc and target not in ctx.loopheads and target not in ctx.knownloopheads:
        raise discoveredloophead(target)

def handlepcassign(valnode, ctx):
    v = foldorreg(valnode, ctx)
    if isinstance(v, luaexpr):
        raise notstraightline("dynamicpc", valnode)
    v = int(v)
    checkbackward(ctx, v)
    ctx.setpc(v)

def handleinstrassign(valnode, ctx):
    v = evalexpr(valnode, ctx)
    if v is not INSTRMARK:
        raise notstraightline("instrassignother", valnode)

def _pcepiloguedelta(stmt, ctx):
                                                                      
    if stmt["type"] != "AstStatCompoundAssign":
        return None
    var = stmt["var"]
    if var["type"] != "AstExprLocal" or st.localkey(var["local"]) != ctx.info["lkey"]:
        return None
    synth = {"type": "AstExprBinary", "op": stmt["op"], "left": var, "right": stmt["value"]}
    try:
        before = ctx.e.get(ctx.info["lkey"])
        newval = st.foldexpr(synth, ctx.e)
    except st.notfoldable:
        return None
    if isinstance(before, luaexpr) or isinstance(newval, luaexpr):
        return None
    return newval - before

def exechandler(stmts, ctx):
    i = 0
    n = len(stmts)
    while i < n:
        s = stmts[i]
        if s["type"] == "AstStatIf" and i + 1 < n:
            delta = _pcepiloguedelta(stmts[i + 1], ctx)
            if delta is not None:
                handleifstmt(s, ctx, postdelta=delta)
                i += 2
                if ctx.returned:
                    break
                continue
        execstmt(s, ctx)
        i += 1
        if ctx.returned:
            break

def steponepc(ctx):
                                                                            
    if ctx.returned:
                                                                        
        return False
    if ctx.pc in ctx.knownloopheads and ctx.pc not in ctx.loopheads:
        compilegenericloopbody(ctx)
        return True
    opval = getfield(ctx, ctx.info["opfieldidx"])
    uvinfo = ctx.info["uvclosureops"].get(opval)
    if uvinfo is not None:
        exec_uvclosure(ctx, uvinfo)
        return True
    handler = ctx.info["table"].get(opval)
    if handler is None:
        raise RuntimeError("unknownopcode " + str(opval) + " at pc " + str(ctx.pc))
    beforepc = ctx.pc
    exechandler(handler, ctx)
    if not ctx.returned and ctx.pc == beforepc:
        ctx.setpc(ctx.pc + 1)
    return True

def compilerange(ctx, startpc, endpc, stoponloopback=False):
    while startpc <= ctx.pc < endpc:
                                                                         
        if ctx.returned:
            break
        steponepc(ctx)
        if ctx.returned:
            break
        if stoponloopback and ctx.loopbackseen:
            break
        if ctx.exitstoppc is not None and ctx.pc == ctx.exitstoppc:
            break
    return ctx.out

def compilecaptured(ctx, startpc, endpc):
    saved = ctx.out
    ctx.out = []
    try:
        compilerange(ctx, startpc, endpc)
    finally:
        captured = ctx.out
        ctx.out = saved
    return captured

def indentlines(lines):
    return ["    " + l for l in lines]

def extractlassign(block, ctx):
    if block is None or block["type"] != "AstStatBlock" or len(block["body"]) != 1:
        return None
    inner = block["body"][0]
    if inner["type"] != "AstStatAssign" or len(inner["vars"]) != 1:
        return None
    var = inner["vars"][0]
    if var["type"] != "AstExprLocal" or st.localkey(var["local"]) != ctx.info["lkey"]:
        return None
    return inner["values"][0]

def _matchjumporassign(block, ctx):
                                                              
    if block is None or block["type"] != "AstStatBlock" or len(block["body"]) != 1:
        return None
    inner = block["body"][0]
    if inner["type"] != "AstStatAssign" or len(inner["vars"]) != 1:
        return None
    var = inner["vars"][0]
    if var["type"] == "AstExprLocal" and st.localkey(var["local"]) == ctx.info["lkey"]:
        pc = foldorreg(inner["values"][0], ctx)
        if isinstance(pc, luaexpr):
            return None
        return ("jump", int(pc))
    return ("assign", inner)

def _tryparseforloop(stmt, ctx):
                                                                      
    thenblock = stmt.get("thenbody")
    if thenblock is None or thenblock["type"] != "AstStatBlock" or len(thenblock["body"]) != 1:
        return None
    nestedif1 = thenblock["body"][0]
    if nestedif1["type"] != "AstStatIf":
        return None
    nestedif2 = stmt.get("elsebody")
    if nestedif2 is None or nestedif2["type"] != "AstStatIf":
        return None
    m1then = _matchjumporassign(nestedif1.get("thenbody"), ctx)
    m1else = _matchjumporassign(nestedif1.get("elsebody"), ctx)
    m2then = _matchjumporassign(nestedif2.get("thenbody"), ctx)
    m2else = _matchjumporassign(nestedif2.get("elsebody"), ctx)
    if not (m1then and m1else and m2then and m2else):
        return None
    if m1then[0] != "jump" or m2then[0] != "jump":
        return None
    if m1else[0] != "assign" or m2else[0] != "assign":
        return None
    if m1then[1] != m2then[1]:
        return None
    return {
        "outercond": stmt["condition"],
        "innercond1": nestedif1["condition"],
        "innercond2": nestedif2["condition"],
        "exitpc": m1then[1],
        "continueassign": m1else[1],
    }

def compileloopbody(ctx, startpc, loophead):
    saved = ctx.out
    ctx.out = []
    ctx.loopheads.append(loophead)
    savedflag = ctx.loopbackseen
    ctx.loopbackseen = False
    ctx.setpc(startpc)
    try:
        compilerange(ctx, startpc, len(ctx.instrs) + 1, stoponloopback=True)
        if not ctx.loopbackseen:
            raise notstraightline("loopneverrepeats", (startpc, loophead))
        return ctx.out
    finally:
        ctx.out = saved
        ctx.loopheads.pop()
        ctx.loopbackseen = savedflag

def compilegenericloopbody(ctx):
                                                                   
    loophead = ctx.pc
    saved = ctx.out
    ctx.out = []
    ctx.loopheads.append(loophead)
    savedflag = ctx.loopbackseen
    ctx.loopbackseen = False
    try:
        compilerange(ctx, loophead, len(ctx.instrs) + 1, stoponloopback=True)
        if not ctx.loopbackseen:
            raise notstraightline("genericloopneverrepeats", loophead)
        body = ctx.out
    finally:
        ctx.out = saved
        ctx.loopheads.pop()
        ctx.loopbackseen = savedflag
    ctx.out.append("while true do")
    ctx.out.extend(indentlines(body))
    ctx.out.append("end")
                                                                          
    limit = len(ctx.instrs) + 1
    exitctx = forkctx(ctx)
    exitctx.loopheads.append(loophead)
    exitctx.exitstoppc = loophead
    exitctx.loopexitmode = True
    exitctx.setpc(loophead)
    try:
        compilerange(exitctx, loophead, limit)
        landed = exitctx.pc
        allreturned = exitctx.returned
    except notstraightline:
        landed = loophead
        allreturned = False
    if allreturned:
        ctx.returned = True
    elif landed == loophead:
                                                                
        ctx.pc = limit
    else:
        ctx.pc = landed

def handleforloop(stmt, ctx, parsed, postdelta):
    loophead = ctx.pc
    outercond = evalexpr(parsed["outercond"], ctx)
    innercond1 = evalexpr(parsed["innercond1"], ctx)
    innercond2 = evalexpr(parsed["innercond2"], ctx)
    for c in (outercond, innercond1, innercond2):
        if not isinstance(c, luaexpr):
            raise notstraightline("forloopcondnotdynamic", stmt)
    exitpc = parsed["exitpc"] + postdelta
    continuepc = loophead + postdelta
    saved = ctx.out
    ctx.out = []
    execstmt(parsed["continueassign"], ctx)
    assignstmts = ctx.out
    ctx.out = saved
    bodystmts = compileloopbody(ctx, continuepc, loophead)
    inner = []
    inner.append("if " + outercond.text + " then")
    inner.append("    if " + innercond1.text + " then")
    inner.append("        break")
    inner.append("    end")
    inner.append("elseif " + innercond2.text + " then")
    inner.append("    break")
    inner.append("end")
    inner.extend(assignstmts)
    inner.extend(bodystmts)
    ctx.out.append("while true do")
    ctx.out.extend(indentlines(inner))
    ctx.out.append("end")
    ctx.setpc(exitpc)

def forkctx(ctx):
    new = protoctx.__new__(protoctx)
    new.info = ctx.info
    new.instrs = ctx.instrs
    new.nestedprotos = ctx.nestedprotos
    new.numparams = ctx.numparams
    new.protoid = ctx.protoid
    new.upvalexprs = ctx.upvalexprs
    new.pc = ctx.pc
    new.e = ctx.e.child()
    new.out = []
    new.protopre = ctx.protopre
    new.maxregseen = ctx.maxregseen
    new.returned = False
    new.loopheads = list(ctx.loopheads)
    new.loopbackseen = ctx.loopbackseen
    new.regtable = ctx.regtable
    new.loopvarseq = ctx.loopvarseq
    new.knownloopheads = ctx.knownloopheads
    new.exitstoppc = ctx.exitstoppc
    new.loopexitmode = ctx.loopexitmode
    new.cfgprobe = ctx.cfgprobe
    return new

def tryconverge(tctx, fctx, limit, stoponloopback):
    def done(c):
        if c.returned or c.pc >= limit:
            return True
        if stoponloopback and c.loopheads and c.pc == c.loopheads[-1]:
            return True
        return False
    steps = 0
    maxsteps = 4 * limit + 16
                                                                     
    tseen = set()
    fseen = set()
    while steps < maxsteps:
        if done(tctx) or done(fctx) or tctx.pc == fctx.pc:
            return True
        which = tctx if tctx.pc <= fctx.pc else fctx
        seen = tseen if which is tctx else fseen
        if which.pc in seen:
            raise discoveredloophead(which.pc)
        if which.pc in which.knownloopheads and which.pc not in which.loopheads:
                                                                         
            return False
        seen.add(which.pc)
        steponepc(which)
        steps += 1
    return False

def structureiffork(ctx, condtext, truepc, falsepc):
                                                                      
    tctx = forkctx(ctx)
    tctx.setpc(truepc)
    fctx = forkctx(ctx)
    fctx.setpc(falsepc)
    mergeforkedbranches(ctx, condtext, tctx, False, fctx, False)

def structureif(ctx, cond, truepc, falsepc):
    if truepc < falsepc:
        a, b = truepc, falsepc
        negate = False
    else:
        a, b = falsepc, truepc
        negate = True
    condtext = cond.text if not negate else "not (" + cond.text + ")"
    savedpc = ctx.pc
    savede = ctx.e
    ctx.setpc(a)
    try:
        bodystmts = compilecaptured(ctx, a, b)
    except notstraightline:
        ctx.pc = savedpc
        ctx.e = savede
        structureiffork(ctx, cond.text, truepc, falsepc)
        return
    if ctx.returned:
        ctx.returned = False
        ctx.setpc(b)
        landed = b
    else:
        landed = ctx.pc
    if landed < a:
        raise notstraightline("backwardjumpinifbody", (landed, a, b))
    if landed == b:
        if bodystmts:
            ctx.out.append("if " + condtext + " then")
            ctx.out.extend(indentlines(bodystmts))
            ctx.out.append("end")
        ctx.setpc(b)
        return
                                                                          
    ctx.pc = savedpc
    ctx.e = savede
    structureiffork(ctx, cond.text, truepc, falsepc)

def rundynbranch(block, fctx, postdelta):
                                                                         
    if block is not None:
        execstmt(block, fctx)
    if fctx.returned:
        return True
    if fctx.loopheads and fctx.pc == fctx.loopheads[-1]:
        if fctx.loopexitmode:
                                                         
            fctx.returned = True
            return True
        fctx.loopbackseen = True
        return True
    if fctx.pc in fctx.knownloopheads:
                                                                   
        return True
    fctx.setpc(fctx.pc + postdelta)
    return False

def mergeforkedbranches(ctx, condtext, tctx, tdone, fctx, fdone):
    ctx.loopbackseen = ctx.loopbackseen or tctx.loopbackseen or fctx.loopbackseen
    if tdone and fdone:
        ctx.out.append("if " + condtext + " then")
        ctx.out.extend(indentlines(tctx.out))
        ctx.out.append("else")
        ctx.out.extend(indentlines(fctx.out))
        ctx.out.append("end")
        ctx.returned = tctx.returned and fctx.returned
        if not ctx.returned:
                                                                          
            ctx.pc = len(ctx.instrs) + 1
        return
    if tdone and not fdone:
        ctx.out.append("if " + condtext + " then")
        ctx.out.extend(indentlines(tctx.out))
        ctx.out.append("end")
        ctx.out.extend(fctx.out)
        ctx.e = fctx.e
        ctx.pc = fctx.pc
        ctx.maxregseen = max(ctx.maxregseen, fctx.maxregseen)
        ctx.regtable = ctx.regtable or fctx.regtable
        ctx.returned = False
        return
    if fdone and not tdone:
        ctx.out.append("if not (" + condtext + ") then")
        ctx.out.extend(indentlines(fctx.out))
        ctx.out.append("end")
        ctx.out.extend(tctx.out)
        ctx.e = tctx.e
        ctx.pc = tctx.pc
        ctx.maxregseen = max(ctx.maxregseen, tctx.maxregseen)
        ctx.regtable = ctx.regtable or tctx.regtable
        ctx.returned = False
        return
    if tctx.pc == fctx.pc:
        ctx.out.append("if " + condtext + " then")
        ctx.out.extend(indentlines(tctx.out))
        ctx.out.append("else")
        ctx.out.extend(indentlines(fctx.out))
        ctx.out.append("end")
        ctx.pc = tctx.pc
        ctx.e = tctx.e
        ctx.maxregseen = max(ctx.maxregseen, tctx.maxregseen, fctx.maxregseen)
        ctx.regtable = ctx.regtable or tctx.regtable or fctx.regtable
        ctx.returned = False
        return
                                                                           
    limit = len(ctx.instrs) + 1
    stop = bool(ctx.loopheads)
                                                                        
    if tryconverge(tctx, fctx, limit, stop):
        earlytdone = tctx.returned or tctx.pc >= limit or (stop and tctx.loopheads and tctx.pc == tctx.loopheads[-1])
        earlyfdone = fctx.returned or fctx.pc >= limit or (stop and fctx.loopheads and fctx.pc == fctx.loopheads[-1])
        if not earlytdone and not earlyfdone and tctx.pc == fctx.pc:
            ctx.out.append("if " + condtext + " then")
            ctx.out.extend(indentlines(tctx.out))
            ctx.out.append("else")
            ctx.out.extend(indentlines(fctx.out))
            ctx.out.append("end")
            ctx.pc = tctx.pc
            ctx.e = tctx.e
            ctx.maxregseen = max(ctx.maxregseen, tctx.maxregseen, fctx.maxregseen)
            ctx.regtable = ctx.regtable or tctx.regtable or fctx.regtable
            ctx.returned = False
            ctx.loopbackseen = ctx.loopbackseen or tctx.loopbackseen or fctx.loopbackseen
            return
    tctx.out.extend(compilerange(tctx, tctx.pc, limit, stoponloopback=stop))
    fctx.out.extend(compilerange(fctx, fctx.pc, limit, stoponloopback=stop))
    ctx.loopbackseen = ctx.loopbackseen or tctx.loopbackseen or fctx.loopbackseen
    tdone = tctx.returned or (tctx.loopheads and tctx.pc == tctx.loopheads[-1])
    fdone = fctx.returned or (fctx.loopheads and fctx.pc == fctx.loopheads[-1])
    if tdone and fdone:
        ctx.out.append("if " + condtext + " then")
        ctx.out.extend(indentlines(tctx.out))
        ctx.out.append("else")
        ctx.out.extend(indentlines(fctx.out))
        ctx.out.append("end")
        ctx.returned = tctx.returned and fctx.returned
        if not ctx.returned:
            ctx.pc = len(ctx.instrs) + 1
        return
    if tdone and not fdone:
        ctx.out.append("if " + condtext + " then")
        ctx.out.extend(indentlines(tctx.out))
        ctx.out.append("end")
        ctx.out.extend(fctx.out)
        ctx.e = fctx.e
        ctx.pc = fctx.pc
        ctx.maxregseen = max(ctx.maxregseen, fctx.maxregseen)
        ctx.regtable = ctx.regtable or fctx.regtable
        ctx.returned = False
        return
    if fdone and not tdone:
        ctx.out.append("if not (" + condtext + ") then")
        ctx.out.extend(indentlines(fctx.out))
        ctx.out.append("end")
        ctx.out.extend(tctx.out)
        ctx.e = tctx.e
        ctx.pc = tctx.pc
        ctx.maxregseen = max(ctx.maxregseen, tctx.maxregseen)
        ctx.regtable = ctx.regtable or tctx.regtable
        ctx.returned = False
        return
                                                                         
    ctx.out.append("if " + condtext + " then")
    ctx.out.extend(indentlines(tctx.out))
    ctx.out.append("else")
    ctx.out.extend(indentlines(fctx.out))
    ctx.out.append("end")
    ctx.pc = limit
    ctx.returned = False

def handledynamicif(stmt, ctx, cond, postdelta):
    tctx = forkctx(ctx)
    tdone = rundynbranch(stmt.get("thenbody"), tctx, postdelta)
    fctx = forkctx(ctx)
    fdone = rundynbranch(stmt.get("elsebody"), fctx, postdelta)
    mergeforkedbranches(ctx, cond.text, tctx, tdone, fctx, fdone)

def handleifstmt(stmt, ctx, postdelta=0):
    thenval = extractlassign(stmt.get("thenbody"), ctx)
    elseval = extractlassign(stmt.get("elsebody"), ctx)
    if thenval is None or elseval is None:
        parsed = _tryparseforloop(stmt, ctx)
        if parsed is not None:
            handleforloop(stmt, ctx, parsed, postdelta)
            return
        cond = evalexpr(stmt["condition"], ctx)
        if not isinstance(cond, luaexpr):
            branch = stmt.get("thenbody") if st.truthy(cond) else stmt.get("elsebody")
            if branch is not None:
                execstmt(branch, ctx)
            if not ctx.returned:
                ctx.setpc(ctx.pc + postdelta)
            return
        handledynamicif(stmt, ctx, cond, postdelta)
        return
    cond = evalexpr(stmt["condition"], ctx)
    truepc = foldorreg(thenval, ctx)
    falsepc = foldorreg(elseval, ctx)
    if isinstance(truepc, luaexpr) or isinstance(falsepc, luaexpr):
        raise notstraightline("dynamicbranchtarget", stmt)
    truepc = int(truepc) + postdelta
    falsepc = int(falsepc) + postdelta
                                                                      
    checkbackward(ctx, truepc)
    checkbackward(ctx, falsepc)
    if not isinstance(cond, luaexpr):
        ctx.setpc(truepc if cond else falsepc)
        return
    if truepc in ctx.loopheads or falsepc in ctx.loopheads:
        handledynamicif(stmt, ctx, cond, postdelta)
        return
    structureif(ctx, cond, truepc, falsepc)

def exec_uvclosure(ctx, uvinfo):
    p0 = ctx.pc
    subprotoidx = int(getfield(ctx, uvinfo.subprotofield))
    numupvals = int(getfield(ctx, uvinfo.numupvalsfield))
    newupvalexprs = {}
    for d in range(1, numupvals + 1):
        descpc = p0 + d
        sentinel = getfieldat(ctx, descpc, uvinfo.sentinelfield)
        if sentinel == uvinfo.sentinelvalue:
            regidx = int(getfieldat(ctx, descpc, uvinfo.regfield))
            name = ctx.materialize(regidx)
            newupvalexprs[d - 1] = luaexpr(name)
        else:
            upvalidx = int(getfieldat(ctx, descpc, uvinfo.upvalfield))
            target = ctx.upvalexprs.get(upvalidx)
            if target is None:
                raise notstraightline("unknownupvalforward", upvalidx)
            newupvalexprs[d - 1] = target
    subproto = ctx.nestedprotos[str(subprotoidx)]
    code = compileprotobody(ctx.info, subproto, newupvalexprs)
    destidx = int(getfield(ctx, uvinfo.destfield))
    writereg(ctx, destidx, luaexpr(code))
    ctx.setpc(p0 + numupvals + 1)

def compileproto(path, pname, protodata):
    info = extractinfo(path, pname)
    return compileprotobody(info, protodata)

def _contains(node, target):
    if node is target:
        return True
    if isinstance(node, dict):
        return any(_contains(v, target) for k, v in node.items()
                   if k not in ("type", "location", "name"))
    if isinstance(node, list):
        return any(_contains(v, target) for v in node)
    return False

def extractinfo(path, pname):
    ast = st.parseast(path)
    stmts, idx = st.findenclosingblock(ast, pname)
    baseenv = st.env()
    st.scanforconsts(stmts[:idx], baseenv)
    applylibraryfuncs(path, pname, stmts, idx, baseenv)
    dispatchfunc = stmts[idx]["func"]
    dispatchbody = dispatchfunc["body"]["body"]
    returnstmt = None
    for s in dispatchbody:
        if s["type"] == "AstStatReturn":
            returnstmt = s
    innerfunc = returnstmt["list"][0]
    while innerfunc["type"] == "AstExprGroup":
        innerfunc = innerfunc["expr"]
    innerbody = innerfunc["body"]["body"]
    mainwhile = None
    for s in innerbody:
        if s["type"] == "AstStatWhile" and s["condition"]["type"] == "AstExprConstantBool" and s["condition"]["value"] is True:
            mainwhile = s
    preamblestmts = []
    for s in innerbody:
        if s is mainwhile:
            break
        preamblestmts.append(s)
    st.scanforconsts(preamblestmts, baseenv)
    wbody = mainwhile["body"]["body"]
    denv = st.env(baseenv)
    st.scanforconsts(wbody[:3], denv)
    modulepreamble = []
    moduledecls = {}
    for s in stmts[:idx]:
        if s["type"] == "AstStatLocal":
            for v in s["vars"]:
                moduledecls[st.localkey(v)] = s
        elif s["type"] == "AstStatLocalFunction":
            moduledecls[st.localkey(s["name"])] = s
    innerdecls = {}
    for s in preamblestmts:
        if s["type"] == "AstStatLocal":
            for v in s["vars"]:
                innerdecls[st.localkey(v)] = s
        elif s["type"] == "AstStatLocalFunction":
            innerdecls[st.localkey(s["name"])] = s
                                                                          
    outerdecls = {}
    try:
        scopes = st.findenclosingscopes(ast, pname) if ast is not None else []
    except Exception:
        scopes = []
    for stmts2, idx2 in scopes:
        if idx2 is None:
            cand = stmts2
        else:
            cand = stmts2[:idx2]
        for s2 in cand:
            if s2.get("type") == "AstStatLocal":
                for v in s2["vars"]:
                    outerdecls.setdefault(st.localkey(v), s2)
            elif s2.get("type") == "AstStatLocalFunction":
                outerdecls.setdefault(st.localkey(s2["name"]), s2)
                                                                       
    dispfunc = stmts[idx].get("func") if stmts[idx].get("type") == "AstStatLocalFunction" else None
    if isinstance(dispfunc, dict):
                                                                       
        dargs = dispfunc.get("args") or []
        if dargs and isinstance(dargs[0], dict) and dargs[0].get("name"):
            outerdecls[st.localkey(dargs[0])] = {
                "__protoobj__": True, "name": dargs[0]["name"]}
        dbody = (dispfunc.get("body") or {}).get("body") or []
        for s2 in dbody:
            if _contains([s2], mainwhile):
                continue                                                  
            if s2.get("type") == "AstStatLocal":
                for v in s2["vars"]:
                    outerdecls.setdefault(st.localkey(v), s2)
            elif s2.get("type") == "AstStatLocalFunction":
                outerdecls.setdefault(st.localkey(s2["name"]), s2)
    for k in list(outerdecls):
        if k in innerdecls or k in moduledecls:
            outerdecls.pop(k, None)

    def _globalsread(n, acc):
        if isinstance(n, dict):
            if n.get("type") == "AstExprGlobal":
                acc.add(n["global"])
            for k, v in n.items():
                if k in ("type", "location", "name"):
                    continue
                _globalsread(v, acc)
        elif isinstance(n, list):
            for v in n:
                _globalsread(v, acc)
        return acc

    vmglobals = _globalsread(stmts[idx], set())
                                                                      
    def _modulestmts():
        seen = []
        for blk in (ast.get("root", {}).get("body", []) or [], stmts[:idx]):
            for st2 in blk:
                if st2 not in seen:
                    seen.append(st2)
        return seen

    for s in _modulestmts():
        if s.get("type") in ("AstStatLocal", "AstStatLocalFunction"):
            continue
        targets = set()
        for v in s.get("vars", []) or []:
            if v.get("type") == "AstExprGlobal":
                targets.add(v["global"])
                                                                
        if not targets:
            continue
        try:
            _t = st.rawtext(path, s["location"])
        except Exception:
            continue
        if len(_t) > 400:
            continue
        try:
            text = st.rawtext(path, s["location"])
        except Exception:
            continue
        if text:
            modulepreamble.append(text)

    fetchstmt = wbody[0]
    opassignstmt = wbody[1]
    opcodeexpr = opassignstmt["values"][0]
    opfieldidx = st.foldexpr(opcodeexpr["index"], denv)
    evarkey = st.localkey(fetchstmt["vars"][0]["local"])
    rkey = st.localkey(fetchstmt["values"][0]["expr"]["local"])
    lkey = st.localkey(fetchstmt["values"][0]["index"]["local"])
    avalkey = st.localkey(opassignstmt["vars"][0]["local"])
    table = st.buildopcodetable(wbody[3:], avalkey, 400, denv)
    wkey = st.localkey(stmts[idx]["func"]["args"][2])
    upvalparamkey = st.localkey(stmts[idx]["func"]["args"][1])
    okey, mkey, pkey = findvmkeys(table, wkey, {evarkey, rkey, lkey, wkey})
    dkey = finddkey(wbody, denv)
    ckey = findckey(table, okey, {evarkey, rkey, lkey, wkey, okey, mkey, pkey})
    uvclosureops = finduvclosureops(table, denv, okey, pkey, wkey, upvalparamkey, evarkey)
    import itertools
    return {
        "evarkey": evarkey, "rkey": rkey, "lkey": lkey, "dkey": dkey,
        "okey": okey, "wkey": wkey, "mkey": mkey, "pkey": pkey,
        "ckey": ckey, "upvalparamkey": upvalparamkey,
        "opfieldidx": opfieldidx, "table": table, "denv": baseenv,
        "uvclosureops": uvclosureops, "protoidgen": itertools.count(1),
        "path": path, "moduledecls": moduledecls, "innerdecls": innerdecls,
        "outerdecls": outerdecls,
        "moduleresolved": {}, "modulepreamble": modulepreamble,
    }

class uvclosureinfo:
    def __init__(self, subprotofield, numupvalsfield, sentinelfield, sentinelvalue,
                 regfield, upvalfield, destfield):
        self.subprotofield = subprotofield
        self.numupvalsfield = numupvalsfield
        self.sentinelfield = sentinelfield
        self.sentinelvalue = sentinelvalue
        self.regfield = regfield
        self.upvalfield = upvalfield
        self.destfield = destfield

def _foldfieldidx(node, denv, evarkey):
                                                                          
    if node["type"] != "AstExprIndexExpr":
        return None
    if node["expr"]["type"] != "AstExprLocal" or st.localkey(node["expr"]["local"]) != evarkey:
        return None
    try:
        return int(st.foldexpr(node["index"], denv))
    except (st.notfoldable, ValueError, TypeError):
        return None

def _islocalkey(node, key):
    return node["type"] == "AstExprLocal" and st.localkey(node["local"]) == key

def _isplainlocalassign(s):
    if s["type"] not in ("AstStatAssign", "AstStatCompoundAssign"):
        return False
    var = s["var"] if s["type"] == "AstStatCompoundAssign" else s["vars"][0]
    return var["type"] == "AstExprLocal"

def _stripdeadaffixes(stmts):
    start = 0
    end = len(stmts)
    while start < end and _isplainlocalassign(stmts[start]):
        start += 1
    while end > start and _isplainlocalassign(stmts[end - 1]):
        end -= 1
    return stmts[start:end]

def _tryparseuvclosure(stmts, denv, okey, pkey, wkey, upvalparamkey, evarkey):
    stmts = _stripdeadaffixes(stmts)
    if len(stmts) != 6:
        return None
    s0, s1, s2, s3, s4, s5 = stmts
    if s0["type"] != "AstStatLocal" or len(s0["vars"]) != 1 or len(s0.get("values", [])) != 1:
        return None
    s0val = s0["values"][0]
    if s0val["type"] != "AstExprIndexExpr":
        return None
    subprotofield = _foldfieldidx(s0val["index"], denv, evarkey)
    if subprotofield is None:
        return None
    subprotolocalkey = st.localkey(s0["vars"][0])

    if s1["type"] != "AstStatLocal" or len(s1["vars"]) != 1 or len(s1.get("values", [])) != 0:
        return None
    alocalkey = st.localkey(s1["vars"][0])

    if s2["type"] != "AstStatLocal" or len(s2["vars"]) != 1:
        return None
    if len(s2.get("values", [])) != 1 or s2["values"][0]["type"] != "AstExprTable" or s2["values"][0]["items"]:
        return None
    nlocalkey = st.localkey(s2["vars"][0])

    if s3["type"] != "AstStatAssign" or len(s3["vars"]) != 1:
        return None
    if not _islocalkey(s3["vars"][0], alocalkey):
        return None
    callexpr = s3["values"][0]
    if callexpr["type"] != "AstExprCall" or len(callexpr["args"]) != 2:
        return None
    if callexpr["args"][0]["type"] != "AstExprTable" or callexpr["args"][0]["items"]:
        return None
    mtitems = callexpr["args"][1]["items"] if callexpr["args"][1]["type"] == "AstExprTable" else None
    if mtitems is None or len(mtitems) != 2:
        return None
    keys = set()
    for it in mtitems:
        if it["kind"] != "record" or it["value"]["type"] != "AstExprFunction":
            return None
        keys.add(it["key"]["value"])
    if keys != {"__index", "__newindex"}:
        return None

    if s4["type"] != "AstStatFor":
        return None
    numupvalsfield = _foldfieldidx(s4["to"], denv, evarkey)
    if numupvalsfield is None:
        return None
    forbody = s4["body"]["body"]
    ifstmt = None
    for fs in forbody:
        if fs["type"] == "AstStatIf":
            ifstmt = fs
    descriptorlocalkey = None
    for fs in forbody:
        if fs["type"] == "AstStatLocal" and len(fs.get("values", [])) == 1:
            v = fs["values"][0]
            if v["type"] == "AstExprIndexExpr" and v["expr"]["type"] == "AstExprLocal":
                descriptorlocalkey = st.localkey(fs["vars"][0])
    if ifstmt is None or descriptorlocalkey is None:
        return None
    cond = ifstmt["condition"]
    if cond["type"] != "AstExprBinary" or cond["op"] != "CompareEq":
        return None
    sentinelfield = _foldfieldidx(cond["left"], denv, descriptorlocalkey)
    if sentinelfield is None:
        return None
    if cond["right"]["type"] != "AstExprConstantNumber":
        return None
    sentinelvalue = cond["right"]["value"]

    def parsebranch(body, basekey):
        bstmts = body["body"]
        if len(bstmts) != 1 or bstmts[0]["type"] != "AstStatAssign":
            return None
        a = bstmts[0]
        if a["vars"][0]["type"] != "AstExprIndexExpr":
            return None
        if a["vars"][0]["expr"]["type"] != "AstExprLocal" or st.localkey(a["vars"][0]["expr"]["local"]) != nlocalkey:
            return None
        val = a["values"][0]
        if val["type"] != "AstExprTable" or len(val["items"]) != 2:
            return None
        it0, it1 = val["items"]
        if it0["kind"] != "item" or not _islocalkey(it0["value"], basekey):
            return None
        if it1["kind"] != "item":
            return None
        return _foldfieldidx(it1["value"], denv, descriptorlocalkey)

    regfield = parsebranch(ifstmt["thenbody"], okey)
    if regfield is None:
        return None
    upvalfield = parsebranch(ifstmt["elsebody"], upvalparamkey)
    if upvalfield is None:
        return None

    if s5["type"] != "AstStatAssign" or len(s5["vars"]) != 1:
        return None
    destvar = s5["vars"][0]
    if destvar["type"] != "AstExprIndexExpr" or destvar["expr"]["type"] != "AstExprLocal":
        return None
    if st.localkey(destvar["expr"]["local"]) != okey:
        return None
    destfield = _foldfieldidx(destvar["index"], denv, evarkey)
    if destfield is None:
        return None
    callv = s5["values"][0]
    if callv["type"] != "AstExprCall" or callv["func"]["type"] != "AstExprLocal":
        return None
    if st.localkey(callv["func"]["local"]) != pkey:
        return None
    if len(callv["args"]) != 3:
        return None
    if not _islocalkey(callv["args"][0], subprotolocalkey):
        return None
    if not _islocalkey(callv["args"][1], alocalkey):
        return None
    if not _islocalkey(callv["args"][2], wkey):
        return None

    return uvclosureinfo(subprotofield, numupvalsfield, sentinelfield, sentinelvalue,
                          regfield, upvalfield, destfield)

def finduvclosureops(table, denv, okey, pkey, wkey, upvalparamkey, evarkey):
    result = {}
    for op, stmts in table.items():
        try:
            info = _tryparseuvclosure(stmts, denv, okey, pkey, wkey, upvalparamkey, evarkey)
        except (KeyError, IndexError, TypeError):
            info = None
        if info is not None:
            result[op] = info
    return result

def applylibraryfuncs(path, pname, stmts, idx, baseenv):
    names = []
    for s in stmts[:idx]:
        if s["type"] == "AstStatLocal":
            for v in s["vars"]:
                names.append(v["name"])
    names = sorted(set(names))
    try:
        matches = st.identifylibraryfuncs(path, pname, names)
    except Exception:
        return
    if not matches:
        return
    byname = {}
    for k in baseenv.vals.keys():
        byname.setdefault(k[0], []).append(k)
    for name, realname in matches.items():
        for key in byname.get(name, []):
            baseenv.vals[key] = luaexpr(realname)

def findckey(table, okey, excludekeys):
    callcounts = {}

    def scan(node):
        if isinstance(node, dict):
            if (node.get("type") == "AstExprCall" and node["func"]["type"] == "AstExprLocal"
                    and len(node["args"]) == 3):
                fkey = st.localkey(node["func"]["local"])
                a0 = node["args"][0]
                if (fkey not in excludekeys and a0["type"] == "AstExprLocal"
                        and st.localkey(a0["local"]) == okey):
                    callcounts[fkey] = callcounts.get(fkey, 0) + 1
            for v in node.values():
                scan(v)
        elif isinstance(node, list):
            for v in node:
                scan(v)

    for op, stmts in table.items():
        for s in stmts:
            scan(s)
    if not callcounts:
        return None
    return max(callcounts, key=lambda k: callcounts[k])

def finddkey(wbody, denv):
    compoundstmt = wbody[5] if len(wbody) > 5 else None
    if compoundstmt and compoundstmt["type"] == "AstStatCompoundAssign":
        try:
            v = st.foldexpr(compoundstmt["value"], denv)
            return v
        except st.notfoldable:
            pass
    return 1

def findvmkeys(table, wkey, excludekeys):
    indexbasecounts = {}
    closurecalls = []

    def scan(node):
        if isinstance(node, dict):
            if node.get("type") == "AstExprIndexExpr" and node["expr"]["type"] == "AstExprLocal":
                k = st.localkey(node["expr"]["local"])
                indexbasecounts[k] = indexbasecounts.get(k, 0) + 1
            if node.get("type") == "AstExprCall":
                args = node["args"]
                if len(args) == 3 and args[1]["type"] == "AstExprConstantNil" and args[2]["type"] == "AstExprLocal":
                    if st.localkey(args[2]["local"]) == wkey and node["func"]["type"] == "AstExprLocal":
                        if args[0]["type"] == "AstExprIndexExpr" and args[0]["expr"]["type"] == "AstExprLocal":
                            closurecalls.append((st.localkey(node["func"]["local"]), st.localkey(args[0]["expr"]["local"])))
            for v in node.values():
                scan(v)
        elif isinstance(node, list):
            for v in node:
                scan(v)

    for op, stmts in table.items():
        for s in stmts:
            scan(s)
    for k in excludekeys:
        indexbasecounts.pop(k, None)
    okey = max(indexbasecounts, key=lambda k: indexbasecounts[k]) if indexbasecounts else None
    pkey = mkey = None
    if closurecalls:
        from collections import Counter
        cnt = Counter(closurecalls)
        pkey, mkey = cnt.most_common(1)[0][0]
    return okey, mkey, pkey

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    print("placeholder")
