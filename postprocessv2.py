import copy
import sys
from luaparser import ast, astnodes as A

SKIP = ("comments", "wrapped")

def flds(node):
    try:
        return [k for k in vars(node)
                if not k.startswith("_") and k not in SKIP]
    except TypeError:
        return []

def walk(node):
    if node is None or isinstance(node, (str, bytes, int, float, bool)):
        return
    yield node
    if isinstance(node, list):
        for c in node:
            yield from walk(c)
        return
    for k in flds(node):
        yield from walk(getattr(node, k, None))

def isname(x, n):
    return isinstance(x, A.Name) and x.id == n

def constnum(x):
    return x.n if isinstance(x, A.Number) else None

def iscall(x):
    return isinstance(x, (A.Call, A.Invoke))

def issimple(x):
    if isinstance(x, (A.Number, A.String, A.Nil, A.TrueExpr, A.FalseExpr, A.Name)):
        return True
    if isinstance(x, A.Index):
        return issimple(x.value) and issimple(x.idx)
    return False

def dup(x):
    try:
        return copy.deepcopy(x)
    except Exception:
        return x

def unpack_of(x, name):
    if not (isinstance(x, A.Call) and len(x.args) == 3):
        return None
    f = x.func
    if not (isinstance(f, A.Index) and isname(f.value, "table")
            and isname(f.idx, "unpack")):
        return None
    if not isname(x.args[0], name):
        return None
    lo, hi = constnum(x.args[1]), constnum(x.args[2])
    if lo is None or hi is None:
        return None
    return lo, hi

def scalarizeregtable(tree):
    total = 0
                                                                       
    for body in [n for n in walk(tree) if isinstance(n, A.Block)]:
        for i, st in enumerate(list(body.body)):
            if not isinstance(st, A.LocalAssign) or len(st.targets) != 1 \
               or len(st.values) != 1:
                continue
            tgt = st.targets[0]
            if not isinstance(tgt, A.Name) or not tgt.id.startswith("vreg"):
                continue
            if not (isinstance(st.values[0], A.Table) and not st.values[0].fields):
                continue
            total += _scalarize(body, i, tgt.id)
    return total

def regtabletolocals(tree):
    total = 0
    for block in [n for n in walk(tree) if isinstance(n, A.Block)]:
        for i, st in enumerate(list(block.body)):
            if not (isinstance(st, A.LocalAssign) and len(st.targets) == 1
                    and len(st.values) == 1):
                continue
            tgt = st.targets[0]
            if not (isinstance(tgt, A.Name) and tgt.id.startswith("vreg")):
                continue
            if not (isinstance(st.values[0], A.Table) and not st.values[0].fields):
                continue
            region = block.body[i + 1:]
            info = _regioninfo(region, tgt.id)
            if info is None:
                continue
            idxs, bare_unpacks = info
            for lo, hi in bare_unpacks:
                idxs.update(range(lo, hi + 1))
            if not idxs:
                continue
            mapping = {k: "%s_%d" % (tgt.id, k) for k in sorted(idxs)}
            if _collides(tree, mapping.values()):
                continue
            for s in region:
                _rewrite_region(s, tgt.id, mapping)
            decl = A.LocalAssign(
                targets=[A.Name(n) for n in mapping.values()], values=[])
            block.body[i] = decl
            total += 1
    return total

def _regioninfo(region, name):
    idxs = set()
    unpacks = []
    covered = set()                                                     
    for s in region:
        for w in walk(s):
            if isinstance(w, A.Index) and isinstance(w.value, A.Name) \
               and w.value.id == name:
                covered.add(id(w.value))
                k = constnum(w.idx)
                if k is None:
                    return None
                idxs.add(k)
    unpackargs = set()                                                    
    for s in region:
        for w in walk(s):
            if _is_unpack_call(w, name):
                unpackargs.add(id(w.args[0]))
                lo, hi = constnum(w.args[1]), constnum(w.args[2])
                if lo is None or hi is None:
                    return None
                unpacks.append((lo, hi))
    for s in region:
        for w in walk(s):
            if isinstance(w, A.Name) and w.id == name \
               and id(w) not in covered and id(w) not in unpackargs:
                return None                                       
    return idxs, unpacks

def _is_unpack_call(x, name):
    return (isinstance(x, A.Call) and len(x.args) == 3
            and isinstance(x.func, A.Index)
            and isname(x.func.value, "table")
            and isname(x.func.idx, "unpack")
            and isname(x.args[0], name))

def _unpackpos(namenode, region):
    for s in region:
        for w in walk(s):
            if _is_unpack_call(w, namenode.id) and w.args[0] is namenode:
                lo, hi = constnum(w.args[1]), constnum(w.args[2])
                if lo is not None and hi is not None:
                    return (lo, hi)
    return None

def _collides(tree, names):
    used = set()
    for w in walk(tree):
        if isinstance(w, A.Name):
            used.add(w.id)
    return any(n in used for n in names)

def _rewrite_region(stmt, name, mapping):
                                                                 
    for parent in list(walk(stmt)):
        if isinstance(parent, A.Call):
            _splice_unpack(parent, name, mapping)
                                                            
    while True:
        hit = None
        for w in walk(stmt):
            if isinstance(w, A.Index) and isinstance(w.value, A.Name) \
               and w.value.id == name:
                k = constnum(w.idx)
                if k is not None and k in mapping:
                    hit = w
                    break
        if hit is None:
            break
        _replacenode(stmt, hit, A.Name(mapping[constnum(hit.idx)]))

def _splice_unpack(call, name, mapping):
    args = getattr(call, "args", None)
    if not args:
        return
    new = []
    hit = False
    for a in args:
        if isinstance(a, A.Call) and len(a.args) == 3 \
           and isinstance(a.func, A.Index) and isname(a.func.value, "table") \
           and isname(a.func.idx, "unpack") and isname(a.args[0], name):
            lo, hi = constnum(a.args[1]), constnum(a.args[2])
            if lo is not None and hi is not None \
               and all(k in mapping for k in range(lo, hi + 1)):
                new.extend(A.Name(mapping[k]) for k in range(lo, hi + 1))
                hit = True
                continue
        new.append(a)
    if hit:
        call.args = new

def _mentions(stmts, start, name):
    last = start - 1
    for i in range(start, len(stmts)):
        for w in walk(stmts[i]):
            if isinstance(w, A.Name) and w.id == name:
                last = i
                break
    return last

def _scalarize(block, decl, name):
    stmts = block.body
    end = _mentions(stmts, decl + 1, name)
    if end < decl + 1:
        return 0

    cur = {}
    changed = 0

    def subst(x):
        if isinstance(x, A.Index) and isname(x.value, name):
            k = constnum(x.idx)
            if k is not None and k in cur:
                return dup(cur[k])
        if isinstance(x, A.Call):
            _rewriteargs(x)
        if isinstance(x, A.Invoke):
            _rewriteargs(x)
        for k in flds(x):
            v = getattr(x, k, None)
            if isinstance(v, list):
                for j, it in enumerate(v):
                    if hasattr(it, "__dict__"):
                        v[j] = subst(it)
            elif hasattr(v, "__dict__"):
                setattr(x, k, subst(v))
        return x

    def _rewriteargs(call):
        args = getattr(call, "args", None)
        if not args:
            return
        new = []
        for a in args:
            u = unpack_of(a, name)
            if u and all(k in cur for k in range(u[0], u[1] + 1)):
                new.extend(dup(cur[k]) for k in range(u[0], u[1] + 1))
                changed_outer.append(1)
            else:
                new.append(subst(a))
        call.args = new

    changed_outer = []

    out = []
    drop_decl = False
    for i in range(decl + 1, end + 1):
        st = stmts[i]

        if isinstance(st, A.Assign) and len(st.targets) == 1 and len(st.values) == 1:
            t, v = st.targets[0], st.values[0]
            v = subst(v)
            if isinstance(t, A.Index) and isname(t.value, name):
                k = constnum(t.idx)
                if k is not None:
                    if issimple(v):
                        cur[k] = v
                        changed += 1
                        drop_decl = True
                        continue                                     
                    cur.pop(k, None)
                    st.values[0] = v
                    out.append(st)
                    cur.clear()                                            
                    continue

        elif isinstance(st, A.LocalAssign):
            for j in range(len(st.values)):
                st.values[j] = subst(st.values[j])
            out.append(st)
        else:
            _substmt(st)
            out.append(st)

        if any(iscall(w) for w in walk(st)):
            cur.clear()

    def _substmt(st):
        for k in flds(st):
            v = getattr(st, k, None)
            if isinstance(v, list):
                for j, it in enumerate(v):
                    if hasattr(it, "__dict__"):
                        v[j] = subst(it)
            elif hasattr(v, "__dict__"):
                setattr(st, k, subst(v))

    if drop_decl:
                                                                   
        still = any(isinstance(w, A.Name) and w.id == name
                    for st in out for w in walk(st))
        newbody = stmts[:decl] + ([] if not still else [stmts[decl]]) + out
        block.body = newbody + stmts[end + 1:]
        return changed + len(changed_outer)
    return len(changed_outer)

def foldunpackgroups(tree):
    n = 0
    for block in [b for b in walk(tree) if isinstance(b, A.Block)]:
        i = 0
        while i < len(block.body):
            st = block.body[i]
                                                                         
            for call in _topcalls(st):
                if _splice_straightline(call, block.body, i):
                    n += 1
            i += 1
    return n

def _topcalls(stmt):
    out = []

    def rec(n):
        if n is None or isinstance(n, (str, bytes, int, float, bool)):
            return
        if isinstance(n, A.Block):
            return
        if isinstance(n, (A.Function,)):
            return
        if isinstance(n, list):
            for c in n:
                rec(c)
            return
        if isinstance(n, A.Call):
            out.append(n)
        for k in flds(n):
            rec(getattr(n, k, None))

    rec(stmt)
    return out

def _splice_straightline(call, stmts, sidx):
    args = getattr(call, "args", None)
    if not args:
        return False
    for pos, a in enumerate(args):
        if not _is_unpack_call_generic(a):
            continue
        name = a.args[0].id
        lo, hi = constnum(a.args[1]), constnum(a.args[2])
        if lo is None or hi is None:
            continue
                                                                          
        vals = {}
        j = sidx - 1
        while j >= 0 and len(vals) < (hi - lo + 1):
            s = stmts[j]
            if isinstance(s, A.Assign) and len(s.targets) == 1 and len(s.values) == 1:
                t = s.targets[0]
                if isinstance(t, A.Index) and isname(t.value, name):
                    k = constnum(t.idx)
                    if k is not None and lo <= k <= hi:
                        if k in vals:
                                                                           
                            j -= 1
                            continue
                        if issimple(s.values[0]):
                            vals[k] = s.values[0]
                            j -= 1
                            continue
                        break                                       
                    if k is not None:
                                                                        
                        j -= 1
                        continue
                    break                                                   
                if any(iscall(w) for w in walk(s.values[0])):
                    break                                          
            elif isinstance(s, (A.If, A.While, A.Repeat, A.Fornum, A.Forin,
                                A.Do, A.Function, A.LocalFunction, A.Return)):
                break                                                       
            j -= 1
        if len(vals) != (hi - lo + 1):
            continue
        newargs = list(args[:pos])
        newargs.extend(dup(vals[k]) for k in range(lo, hi + 1))
        newargs.extend(args[pos + 1:])
        call.args = newargs
                                                                    
        if isinstance(call.func, A.Index) and isname(call.func.value, name):
            fk = constnum(call.func.idx)
            if fk is not None:
                fv = _resolve_prior(stmts, sidx, name, fk)
                                                                          
                if fv is not None and issimple(fv):
                    call.func = dup(fv)
        return True
    return False

def _resolve_prior(stmts, sidx, name, k, limit=40):
    j = sidx - 1
    steps = 0
    while j >= 0 and steps < limit:
        steps += 1
        s = stmts[j]
        if isinstance(s, A.Assign) and len(s.targets) == 1 and len(s.values) == 1:
            t = s.targets[0]
            if isinstance(t, A.Index) and isname(t.value, name):
                kk = constnum(t.idx)
                if kk == k:
                    return s.values[0] if issimple(s.values[0]) else None
                if kk is not None:
                    j -= 1
                    continue
                return None
                                                                   
            if not issimple(s.values[0]):
                return None
        elif isinstance(s, (A.If, A.While, A.Repeat, A.Fornum, A.Forin,
                            A.Do, A.Function, A.LocalFunction, A.Return)):
            return None
        j -= 1
    return None

def _is_unpack_call_generic(x):
    return (isinstance(x, A.Call) and len(x.args) == 3
            and isinstance(x.func, A.Index)
            and isname(x.func.value, "table")
            and isname(x.func.idx, "unpack")
            and isinstance(x.args[0], A.Name))

def oluks_decrypt(data, step):
    out = bytearray()
    acc = 1
    for b in data:
        out.append((acc + b) % 256)
        acc = (step + acc) % 256
    return bytes(out)

def _rawbytes(snode):
    d = getattr(snode, "s", b"")
    if isinstance(d, str):
        d = d.encode("utf-8")
    if not d:
        return d
    try:
        return d.decode("utf-8").encode("latin1")
    except (UnicodeDecodeError, UnicodeEncodeError):
        return d

def printable(b):
    if not b:
        return False
    good = sum(1 for c in b if 32 <= c < 127 or c in (9, 10, 13))
    return good / len(b) >= 0.9

def luastringlit(rawbytes):
    out = ['"']
    for c in rawbytes:
        ch = chr(c)
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\r":
            out.append("\\r")
        elif ch == "\t":
            out.append("\\t")
        elif 32 <= c < 127:
            out.append(ch)
        else:
            out.append("\\%d" % c)
    out.append('"')
    return "".join(out)

def find_decoders(tree):
    names = set()
    for fn in [n for n in walk(tree)
               if isinstance(n, (A.Function, A.LocalFunction))]:
        nm = getattr(fn, "name", None)
        nm = getattr(nm, "id", None) if nm is not None else None
        if not nm:
            continue
        has = {type(w).__name__ for w in walk(fn)}
        txt = " ".join(sorted(has))
                                                                      
        body = _src(fn)
        if "%" in body and "char" in body and ("sub" in body or "byte" in body):
            names.add(nm)
    return names

def _src(node):
    try:
        return ast.to_lua_source(node)
    except Exception:
        return ""

def decryptstrings(tree, decoders):
    if not decoders:
        return 0
    n = 0
    for parent in list(walk(tree)):
        for k in flds(parent):
            v = getattr(parent, k, None)
            cands = v if isinstance(v, list) else [v]
            for j, item in enumerate(cands):
                if not isinstance(item, A.Call):
                    continue
                if not (isinstance(item.func, A.Name) and item.func.id in decoders):
                    continue
                if len(item.args) != 3 or not isinstance(item.args[0], A.String):
                    continue
                step = constnum(item.args[2])
                if step is None:
                    continue
                data = _rawbytes(item.args[0])
                if not data:
                    continue
                plain = oluks_decrypt(data, step)
                if not printable(plain):
                    continue
                lit = luastringlit(plain)
                new = ast.parse("local _x = " + lit).body.body[0].values[0]
                if isinstance(v, list):
                    v[j] = new
                else:
                    setattr(parent, k, new)
                n += 1
    return n

def deadstoreelim(tree, maxscan=80):
    n = 0
    for block in [b for b in walk(tree) if isinstance(b, A.Block)]:
        stmts = block.body
        i = 0
        while i < len(stmts):
            st = stmts[i]
            if not (isinstance(st, A.Assign) and len(st.targets) == 1
                    and len(st.values) == 1):
                i += 1
                continue
            t = st.targets[0]
            if not (isinstance(t, A.Index) and isinstance(t.value, A.Name)
                    and t.value.id.startswith("vreg")):
                i += 1
                continue
            name, k = t.value.id, constnum(t.idx)
            if k is None or not issimple(st.values[0]):
                i += 1
                continue
                                                               
            dead = False
            for j in range(i + 1, min(i + 1 + maxscan, len(stmts))):
                s2 = stmts[j]
                if _writes(s2, name, k):
                    if not any(_reads(x, name, k) for x in stmts[i + 1:j]):
                        dead = True
                    break
                if _reads(s2, name, k):
                    break
                                                                         
                if _leaks_table(s2, name):
                    break
            if dead:
                stmts.pop(i)
                n += 1
                continue
            i += 1
    return n

def resolvepackhelper(tree):
    n = 0
    for fn in [x for x in walk(tree)
               if isinstance(x, (A.Function, A.LocalFunction))]:
        body = getattr(fn, "body", None)
        if not isinstance(body, A.Block):
                                                           
            body = getattr(getattr(fn, "func", None), "body", None)
        if not isinstance(body, A.Block):
            continue
        stmts = body.body
        if len(stmts) != 1 or not isinstance(stmts[0], A.Return):
            continue
        ret = stmts[0]
        vals = getattr(ret, "values", None) or []
        if len(vals) != 2:
            continue
                                                 
        second = vals[1]
        if not (isinstance(second, A.Call) and isinstance(second.func, A.Name)):
            continue
        args = second.args
        if not args or not isinstance(args[0], A.String):
            continue
        try:
            txt = args[0].s.decode("utf-8") if isinstance(args[0].s, bytes) else str(args[0].s)
        except Exception:
            continue
        if txt != "#":
            continue
                                                               
        if not isinstance(vals[0], A.Table):
            continue
        target = second.func
        for parent in list(walk(tree)):
            for k in flds(parent):
                v = getattr(parent, k, None)
                items = v if isinstance(v, list) else [v]
                for j, item in enumerate(items):
                    if isinstance(item, A.Name) and item.id == target.id \
                       and item is not target:
                        if isinstance(v, list):
                            v[j] = A.Name("select")
                        else:
                            setattr(parent, k, A.Name("select"))
                        n += 1
                                                                    
        second.func = A.Name("select")
        n += 1
    return n

LOOPST = (A.While, A.Repeat, A.Fornum, A.Forin)
CTRLST = (A.If,) + LOOPST + (A.Do,)

def _walknoclosure(node):
    if node is None or isinstance(node, (str, bytes, int, float, bool)):
        return
    yield node
    if isinstance(node, A.Function):
        return
    if isinstance(node, list):
        for c in node:
            yield from _walknoclosure(c)
        return
    for k in flds(node):
        yield from _walknoclosure(getattr(node, k, None))

def _assignednames(node):
    out = set()
    for w in walk(node):
        if isinstance(w, A.Assign):
            for t in w.targets:
                if isinstance(t, A.Name):
                    out.add(t.id)
        elif isinstance(w, A.LocalAssign):
            for t in w.targets:
                if isinstance(t, A.Name):
                    out.add(t.id)
        elif isinstance(w, A.LocalFunction):
            out.add(w.name)
        elif isinstance(w, A.Function):
            nm = getattr(w, "name", None)
            if isinstance(nm, A.Name):
                out.add(nm.id)
        elif isinstance(w, A.Fornum):
            t = getattr(w, "target", None)
            if isinstance(t, A.Name):
                out.add(t.id)
        elif isinstance(w, A.Forin):
            for t in getattr(w, "targets", None) or []:
                if isinstance(t, A.Name):
                    out.add(t.id)
    return out

def _hascall_now(st):
    for x in _walknoclosure(st):
        if isinstance(x, (A.Call, A.Invoke)):
            return True
    return False

def _subblocks(st):
    out = []

    def rec(x):
        if x is None or isinstance(x, (str, bytes, int, float, bool)):
            return
        if isinstance(x, A.Function):
            return
        if isinstance(x, A.Block):
            out.append(x)
            return
        if isinstance(x, list):
            for c in x:
                rec(c)
            return
        for k in flds(x):
            rec(getattr(x, k, None))

    rec(st)
    return out

def _subst_slot(setfn, node, env):
    if isinstance(node, A.Name) and node.id in env:
        setfn(copy.deepcopy(env[node.id]))
        return 1
    return _subst_in(node, env)

def _subst_in(node, env):
    if node is None or isinstance(node, (str, bytes, int, float, bool)):
        return 0
    if isinstance(node, A.Function):
        return 0
    n = 0
    if isinstance(node, list):
        for i, v in enumerate(node):
            n += _subst_slot(lambda nv, i=i: node.__setitem__(i, nv), v, env)
        return n
    for k in flds(node):
        v = getattr(node, k, None)
        n += _subst_slot(lambda nv, k=k: setattr(node, k, nv), v, env)
    return n

def _subst_stmt(st, env):
    if isinstance(st, A.Assign):
        n = 0
        for t in st.targets:
            if isinstance(t, A.Index):
                n += _subst_slot(lambda nv: setattr(t, "value", nv),
                                 t.value, env)
                n += _subst_slot(lambda nv: setattr(t, "idx", nv), t.idx, env)
        for i, v in enumerate(st.values):
            n += _subst_slot(lambda nv, i=i: st.values.__setitem__(i, nv),
                             v, env)
        return n
    if isinstance(st, A.LocalAssign):
        n = 0
        for i, v in enumerate(st.values):
            n += _subst_slot(lambda nv, i=i: st.values.__setitem__(i, nv),
                             v, env)
        return n
    return _subst_in(st, env)

def _propagable(name, value):
    if not issimple(value):
        return False
    for w in walk(value):
        if isname(w, name):
            return False
    return True

def _propblock(block, closureassigned, alllocals, seen, env=None,
               funcnested=None):
    if not isinstance(seen, tuple):
        seen = (set(), [])
    if env is None:
        env = {}
    if id(block) in seen[0]:
        return 0
    seen[0].add(id(block))
    seen[1].append(block)                                                   
    n = 0
    for st in block.body:
        n += _propsonestmt(st, env, closureassigned, alllocals, seen,
                           funcnested)
    return n

def _eagerslots(st):
    out = []

    def add(g, f):
        out.append((g, f))

    if isinstance(st, A.If):
        add(lambda: st.test, lambda v: setattr(st, "test", v))
    elif isinstance(st, A.While):
        add(lambda: st.test, lambda v: setattr(st, "test", v))
    elif isinstance(st, A.Repeat):
        pass                                                     
    elif isinstance(st, A.Fornum):
        add(lambda: st.start, lambda v: setattr(st, "start", v))
        add(lambda: st.stop, lambda v: setattr(st, "stop", v))
        if getattr(st, "step", None) is not None:
            add(lambda: st.step, lambda v: setattr(st, "step", v))
    elif isinstance(st, A.Forin):
        it = getattr(st, "iterators", None) or []
        for i in range(len(it)):
            add(lambda i=i: st.iterators[i],
                lambda v, i=i: st.iterators.__setitem__(i, v))
    elif isinstance(st, A.Return):
        vals = getattr(st, "values", None) or []
        for i in range(len(vals)):
            add(lambda i=i: st.values[i],
                lambda v, i=i: st.values.__setitem__(i, v))
    else:
        return None
    return out

def _propsonestmt(st, env, closureassigned, alllocals, seen, funcnested=None):
                                                                      
    n = 0
    for fnb in [x for x in walk(st) if isinstance(x, A.Function)]:
        n += _propblock(fnb.body,
                        (funcnested or {}).get(id(fnb), set()),
                        alllocals, seen, env={}, funcnested=funcnested)
                                                                          
    view = env
    if isinstance(st, LOOPST):
        bad = _assignednames(st) | set(closureassigned)
        view = {k: v for k, v in env.items() if k not in bad}
    slots = _eagerslots(st)
    if slots is None:
        n += _subst_stmt(st, view)
    else:
        for get, setf in slots:
            n += _subst_slot(setf, get(), view)

    defs = None
    if isinstance(st, A.Assign) and len(st.targets) == 1 and len(st.values) == 1:
        defs = (st.targets[0], st.values[0])
    elif isinstance(st, A.LocalAssign) and len(st.targets) == 1 \
            and len(st.values) == 1:
        defs = (st.targets[0], st.values[0])
    if defs:
        t, v = defs
        if isinstance(t, A.Name):
            if _propagable(t.id, v):
                env[t.id] = copy.deepcopy(v)
            else:
                env.pop(t.id, None)
                                                                        
    if _hascall_now(st):
        for nm in list(env):
            if nm not in alllocals or nm in closureassigned:
                env.pop(nm)
    for b in _subblocks(st):
        n += _propblock(b, closureassigned, alllocals, seen, env=env,
                        funcnested=funcnested)
    if isinstance(st, CTRLST):
        for nm in _assignednames(st):
            env.pop(nm, None)
    if isinstance(st, (A.Return, A.Break)):
        env.clear()
    return n

def propagatesimple(tree):
                                                                        
    funcnested = {}
    for fnb in [x for x in walk(tree) if isinstance(x, A.Function)]:
        ns = set()
        for w in walk(fnb.body):
            if isinstance(w, A.Function):
                ns |= _assignednames(w.body)
        funcnested[id(fnb)] = ns
    closureassigned = set()
    for w in walk(tree):
        if isinstance(w, A.Function):
            closureassigned |= _assignednames(w.body)
    alllocals = set()
    for w in walk(tree):
        if isinstance(w, A.LocalAssign):
            for t in w.targets:
                if isinstance(t, A.Name):
                    alllocals.add(t.id)
        elif isinstance(w, A.LocalFunction):
            alllocals.add(w.name)
    seen = (set(), [])
    return _propblock(tree.body, closureassigned, alllocals, seen,
                      funcnested=funcnested)

def dropdeadsimple(tree, alllocals, maxscan=80):
    n = 0
    for block in [b for b in walk(tree) if isinstance(b, A.Block)]:
        stmts = block.body
        i = 0
        while i < len(stmts):
            st = stmts[i]
            if not (isinstance(st, A.Assign) and len(st.targets) == 1
                    and len(st.values) == 1
                    and isinstance(st.targets[0], A.Name)
                    and issimple(st.values[0])):
                i += 1
                continue
            nm = st.targets[0].id
            dead = False
            for j in range(i + 1, min(i + 1 + maxscan, len(stmts))):
                s2 = stmts[j]
                if _readsname(s2, nm):
                    break
                if (isinstance(s2, A.Assign) and len(s2.targets) == 1
                        and isinstance(s2.targets[0], A.Name)
                        and s2.targets[0].id == nm):
                    dead = True
                    break
                if isinstance(s2, (A.If,) + LOOPST):
                    break
                if _hascall_now(s2) and nm not in alllocals:
                    break
            if dead:
                stmts.pop(i)
                n += 1
                continue
            i += 1
    return n

def _readsname(node, name):
    if isinstance(node, (A.Assign, A.LocalAssign)):
        for t in getattr(node, "targets", None) or []:
            if isinstance(t, A.Index):
                if _readsname(t.value, name) or _readsname(t.idx, name):
                    return True
        for v in getattr(node, "values", None) or []:
            if _readsname(v, name):
                return True
        return False
    for w in _walknoclosure(node):
        if isname(w, name):
            return True
    return False

def normalizeunpack(tree):
    n = 0
    for parent in list(walk(tree)):
        for k in flds(parent):
            v = getattr(parent, k, None)
            if isinstance(v, A.Name) and v.id == "unpack":
                setattr(parent, k,
                        A.Index(idx=A.Name("unpack"), value=A.Name("table")))
                n += 1
            elif isinstance(v, list):
                for i, item in enumerate(v):
                    if isinstance(item, A.Name) and item.id == "unpack":
                        v[i] = A.Index(idx=A.Name("unpack"), value=A.Name("table"))
                        n += 1
    return n

def _leaks_table(stmt, name):
    covered = set()
    for w in walk(stmt):
        if isinstance(w, A.Index) and isname(w.value, name):
            covered.add(id(w.value))
    for w in walk(stmt):
        if isinstance(w, A.Name) and w.id == name and id(w) not in covered:
            if not _is_unpack_call_generic(getattr(w, "_dummy", None)):
                                                                      
                if not _is_unpack_arg(w, stmt, name):
                    return True
    return False

def _is_unpack_arg(namenode, stmt, name):
    for w in walk(stmt):
        if _is_unpack_call_generic(w) and w.args[0] is namenode:
            return True
    return False

def _writes(stmt, name, k):
    if isinstance(stmt, A.Assign) and len(stmt.targets) == 1:
        t = stmt.targets[0]
        return (isinstance(t, A.Index) and isname(t.value, name)
                and constnum(t.idx) == k)
    return False

def _reads(stmt, name, k):
    for w in walk(stmt):
        if isinstance(w, A.Index) and isname(w.value, name) \
           and constnum(w.idx) == k:
            return True
        if _is_unpack_call_generic(w) and isname(w.args[0], name):
            lo, hi = constnum(w.args[1]), constnum(w.args[2])
            if lo is not None and hi is not None and lo <= k <= hi:
                return True
    return False

def removesecureeq(tree):
    target = None
    for fn in [n for n in walk(tree)
               if isinstance(n, (A.Function, A.LocalFunction))]:
        nm = getattr(fn, "name", None)
        nm = getattr(nm, "id", None) if nm is not None else None
        if nm == "__secureeq":
            target = fn
            break
    if target is None:
        return 0
    if "pcall" not in _src(target):
        return 0
    n = 0
    for parent in list(walk(tree)):
        for k in flds(parent):
            v = getattr(parent, k, None)
            cands = v if isinstance(v, list) else [v]
            for j, item in enumerate(cands):
                if isinstance(item, A.Call) and isinstance(item.func, A.Name) \
                   and item.func.id == "__secureeq" and len(item.args) == 2:
                    rel = A.EqToOp(left=item.args[0], right=item.args[1])
                    if isinstance(v, list):
                        v[j] = rel
                    else:
                        setattr(parent, k, rel)
                    n += 1
                                                                       
    if n or True:
        _removestmt(tree, target)
    return n

def _removestmt(tree, stmt):
    for parent in walk(tree):
        for k in flds(parent):
            v = getattr(parent, k, None)
            if isinstance(v, list) and stmt in v:
                v.remove(stmt)
                return True
    return False

def run(inpath, outpath, rounds=4):
    src = open(inpath).read()
    tree = ast.parse(src)
    decoders = find_decoders(tree)

    c0 = 0
    c2 = 0
    for _ in range(rounds):
        a = foldunpackgroups(tree)
        b = decryptstrings(tree, decoders)
        c0 += a
        c2 += b
        if not a and not b:
            break
    c1 = regtabletolocals(tree)
    c3 = removesecureeq(tree)
    c5 = deadstoreelim(tree)
    c6 = resolvepackhelper(tree)
    c7 = propagatesimple(tree)
    _alllocals = set()
    for _w in walk(tree):
        if isinstance(_w, A.LocalAssign):
            for _t in _w.targets:
                if isinstance(_t, A.Name):
                    _alllocals.add(_t.id)
        elif isinstance(_w, A.LocalFunction):
            _alllocals.add(_w.name)
    c8 = dropdeadsimple(tree, _alllocals)
    c9 = normalizeunpack(tree)
                                                                           
    c4 = 0

    out = ast.to_lua_source(tree)
    open(outpath, "w").write(out.rstrip("\n") + "\n")
    print("decoders   :", sorted(decoders))
    print("unpackfold :", c0)
    print("regtable   :", c1)
    print("decrypted  :", c2)
    print("secureeq   :", c3)
    print("deadstores :", c5)
    print("packhelper :", c6)
    print("propagated :", c7)
    print("deaddrops  :", c8)
    print("unpackfix  :", c9)
    print("wrote", outpath, len(out), "bytes")

if __name__ == "__main__":
    run(sys.argv[1], sys.argv[2])
