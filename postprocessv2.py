import copy
import math
import re
import sys
from luaparser import ast, astnodes as A
import optimizeast as opt

SKIP = ("comments", "wrapped")

IMMUTABLE_LIBS = frozenset({
    "string", "table", "math", "coroutine", "bit", "bit32", "utf8",
    "os", "debug", "task", "Enum", "Color3", "Vector2", "Vector3",
    "CFrame", "UDim", "UDim2", "Instance", "Ray", "BrickColor",
    "TweenInfo", "NumberRange", "NumberSequence", "ColorSequence",
})

VM_REG_RE = re.compile(r"^(?:v\d+_\d+|p\d+_\d+|vtbl\d+(?:_\d+)?|vreg\d+(?:_\d+)?|vfl\d+_\d+|_ssa_\d+)$")

LOOPST = (A.While, A.Repeat, A.Fornum, A.Forin)
CTRLST = (A.If,) + LOOPST + (A.Do,)
FN_NODES = (A.Function, A.LocalFunction, A.AnonymousFunction)


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
    if isinstance(x, A.Number):
        return x.n
    if isinstance(x, A.UMinusOp) and isinstance(x.operand, A.Number):
        return -x.operand.n
    return None


def iscall(x):
    return isinstance(x, (A.Call, A.Invoke))


def isconstlit(x):
    if isinstance(x, (A.Number, A.String, A.Nil, A.TrueExpr, A.FalseExpr)):
        return True
    if isinstance(x, A.UMinusOp) and isinstance(x.operand, A.Number):
        return True
    return False


def isimmindex(x):
    if not isinstance(x, A.Index):
        return False
    if x.notation != A.IndexNotation.DOT and not isconstlit(x.idx):
        return False
    if isinstance(x.value, A.Name):
        return x.value.id in IMMUTABLE_LIBS
    return isimmindex(x.value)


def issimple(x):
    if isconstlit(x) or isinstance(x, A.Name):
        return True
    if isinstance(x, A.Index):
        if x.notation == A.IndexNotation.DOT:
            return issimple(x.value)
        return issimple(x.value) and issimple(x.idx)
    return False


def ispropagatable(x):
    return isconstlit(x) or isinstance(x, A.Name) or isimmindex(x)


def dup(x):
    try:
        return copy.deepcopy(x)
    except Exception:
        return x


def _isregtable(name):
    return isinstance(name, str) and (name.startswith("vreg") or name.startswith("vtbl"))


def unpack_of(x, name):
    if not (isinstance(x, A.Call) and len(x.args) == 3):
        return None
    f = x.func
    is_tu = (isinstance(f, A.Index) and isname(f.value, "table") and isname(f.idx, "unpack"))
    is_u = isname(f, "unpack")
    if not (is_tu or is_u):
        return None
    if not isname(x.args[0], name):
        return None
    lo, hi = constnum(x.args[1]), constnum(x.args[2])
    if lo is None or hi is None:
        return None
    return int(lo), int(hi)


def regtabletolocals(tree):
    total = 0
    for block in [n for n in walk(tree) if isinstance(n, A.Block)]:
        i = 0
        while i < len(block.body):
            st = block.body[i]
            if not (isinstance(st, A.LocalAssign) and len(st.targets) == 1
                    and len(st.values) == 1):
                i += 1
                continue
            tgt = st.targets[0]
            if not (isinstance(tgt, A.Name) and _isregtable(tgt.id)):
                i += 1
                continue
            if not (isinstance(st.values[0], A.Table) and not st.values[0].fields):
                i += 1
                continue
            region = block.body[i + 1:]
            info = _regioninfo(region, tgt.id)
            if info is None:
                i += 1
                continue
            idxs, bare_unpacks = info
            for lo, hi in bare_unpacks:
                idxs.update(range(lo, hi + 1))
            if not idxs:
                block.body.pop(i)
                total += 1
                continue
            mapping = {k: "%s_%d" % (tgt.id, k) for k in sorted(idxs)}
            if _collides(tree, mapping.values()):
                i += 1
                continue
            for s in region:
                _rewrite_region(s, tgt.id, mapping)
            decls = [A.LocalAssign(targets=[A.Name(n)], values=[]) for n in mapping.values()]
            block.body[i:i + 1] = decls
            total += 1
            i += len(decls)
    return total


def _regioninfo(region, name):
    idxs = set()
    unpacks = []
    covered = set()
    for s in region:
        for w in walk(s):
            if isinstance(w, A.Index) and isinstance(w.value, A.Name) \
               and w.value.id == name and w.notation != A.IndexNotation.DOT:
                covered.add(id(w.value))
                k = constnum(w.idx)
                if k is None:
                    return None
                idxs.add(int(k))
    unpackargs = set()
    for s in region:
        for w in walk(s):
            u = unpack_of(w, name)
            if u is not None:
                unpackargs.add(id(w.args[0]))
                unpacks.append(u)
    for s in region:
        for w in walk(s):
            if isinstance(w, A.Name) and w.id == name \
               and id(w) not in covered and id(w) not in unpackargs:
                return None
    return idxs, unpacks


def _collides(tree, names):
    used = set()
    for w in walk(tree):
        if isinstance(w, A.Name):
            used.add(w.id)
    return any(n in used for n in names)


def _replacenode(root, old, new):
    for parent in walk(root):
        for k in flds(parent):
            v = getattr(parent, k, None)
            if v is old:
                setattr(parent, k, new)
                return True
            if isinstance(v, list):
                for j, it in enumerate(v):
                    if it is old:
                        v[j] = new
                        return True
    return False


def _rewrite_region(stmt, name, mapping):
    for parent in list(walk(stmt)):
        if isinstance(parent, (A.Call, A.Invoke)):
            _splice_unpack(parent, name, mapping)
    while True:
        hit = None
        for w in walk(stmt):
            if isinstance(w, A.Index) and isinstance(w.value, A.Name) \
               and w.value.id == name and w.notation != A.IndexNotation.DOT:
                k = constnum(w.idx)
                if k is not None and int(k) in mapping:
                    hit = (w, int(k))
                    break
        if hit is None:
            break
        _replacenode(stmt, hit[0], A.Name(mapping[hit[1]]))


def _splice_unpack(call, name, mapping):
    args = getattr(call, "args", None)
    if not args:
        return
    new = []
    hit = False
    for a in args:
        u = unpack_of(a, name)
        if u is not None and all(k in mapping for k in range(u[0], u[1] + 1)):
            new.extend(A.Name(mapping[k]) for k in range(u[0], u[1] + 1))
            hit = True
            continue
        new.append(a)
    if hit:
        call.args = new


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
        if isinstance(n, A.Block) or isinstance(n, FN_NODES):
            return
        if isinstance(n, list):
            for c in n:
                rec(c)
            return
        if isinstance(n, (A.Call, A.Invoke)):
            out.append(n)
        for k in flds(n):
            rec(getattr(n, k, None))

    rec(stmt)
    return out


def _is_unpack_call_generic(x):
    if not (isinstance(x, A.Call) and len(x.args) == 3 and isinstance(x.args[0], A.Name)):
        return False
    f = x.func
    return (isinstance(f, A.Index) and isname(f.value, "table") and isname(f.idx, "unpack")) or isname(f, "unpack")


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
        lo, hi = int(lo), int(hi)
        vals = {}
        j = sidx - 1
        while j >= 0 and len(vals) < (hi - lo + 1):
            s = stmts[j]
            if isinstance(s, A.Assign) and len(s.targets) == 1 and len(s.values) == 1:
                t = s.targets[0]
                if isinstance(t, A.Index) and isname(t.value, name) and t.notation != A.IndexNotation.DOT:
                    k = constnum(t.idx)
                    if k is not None and lo <= int(k) <= hi:
                        k = int(k)
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
            elif isinstance(s, CTRLST + FN_NODES + (A.Return, A.Break)):
                break
            j -= 1
        if len(vals) != (hi - lo + 1):
            continue
        newargs = list(args[:pos])
        newargs.extend(dup(vals[k]) for k in range(lo, hi + 1))
        newargs.extend(args[pos + 1:])
        call.args = newargs
        if isinstance(call, A.Call) and isinstance(call.func, A.Index) and isname(call.func.value, name):
            fk = constnum(call.func.idx)
            if fk is not None:
                fv = _resolve_prior(stmts, sidx, name, int(fk))
                if fv is not None and issimple(fv):
                    call.func = _as_prefix(dup(fv))
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
            if isinstance(t, A.Index) and isname(t.value, name) and t.notation != A.IndexNotation.DOT:
                kk = constnum(t.idx)
                if kk is not None and int(kk) == k:
                    return s.values[0] if issimple(s.values[0]) else None
                if kk is not None:
                    j -= 1
                    continue
                return None
            if not issimple(s.values[0]):
                return None
        elif isinstance(s, CTRLST + FN_NODES + (A.Return, A.Break)):
            return None
        j -= 1
    return None


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
        raw = getattr(snode, "raw", "")
        if raw:
            return _unescape_lua_raw(raw)
        return b""
    try:
        return d.decode("utf-8").encode("latin1")
    except (UnicodeDecodeError, UnicodeEncodeError):
        return d


def _unescape_lua_raw(raw):
    out = bytearray()
    i = 0
    n = len(raw)
    while i < n:
        ch = raw[i]
        if ch != "\\":
            out.append(ord(ch) & 0xFF)
            i += 1
            continue
        i += 1
        if i >= n:
            break
        esc = raw[i]
        if esc.isdigit():
            j = i
            while j < min(i + 3, n) and raw[j].isdigit():
                j += 1
            out.append(int(raw[i:j]) & 0xFF)
            i = j
        elif esc == "n":
            out.append(10)
            i += 1
        elif esc == "r":
            out.append(13)
            i += 1
        elif esc == "t":
            out.append(9)
            i += 1
        elif esc == "a":
            out.append(7)
            i += 1
        elif esc == "b":
            out.append(8)
            i += 1
        elif esc == "f":
            out.append(12)
            i += 1
        elif esc == "v":
            out.append(11)
            i += 1
        else:
            out.append(ord(esc) & 0xFF)
            i += 1
    return bytes(out)


def printable(b):
    if not b:
        return True
    good = sum(1 for c in b if 32 <= c < 127 or c in (9, 10, 13))
    return good / len(b) >= 0.85


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


def mkstringnode(rawbytes):
    lit = luastringlit(rawbytes)
    return ast.parse("local _x = " + lit).body.body[0].values[0]


def mknumbernode(val):
    if isinstance(val, float) and val.is_integer() and abs(val) < 2 ** 53:
        val = int(val)
    if val < 0:
        return A.UMinusOp(operand=A.Number(abs(val)))
    return A.Number(val)


def find_decoders(tree):
    names = set()
    cachetables = set()
    for fn in [n for n in walk(tree)
               if isinstance(n, (A.Function, A.LocalFunction))]:
        nm = getattr(fn, "name", None)
        nm = getattr(nm, "id", None) if isinstance(nm, A.Name) else None
        if not nm or nm == "devirt":
            continue
        has_nested_fn = any(isinstance(w, (A.Function, A.LocalFunction)) for w in _walknoclosure(fn.body))
        if has_nested_fn:
            continue
        body = _src(fn)
        if "%" in body and "char" in body and ("sub" in body or "byte" in body):
            names.add(nm)
            for idxnode in [w for w in _walknoclosure(fn.body) if isinstance(w, A.Index)]:
                if isinstance(idxnode.value, A.Name):
                    argnames = {p.id for p in fn.args if isinstance(p, A.Name)}
                    if idxnode.value.id not in argnames and idxnode.value.id != "string":
                        cachetables.add(idxnode.value.id)
    return names, cachetables


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
        if isinstance(parent, (A.Function, A.LocalFunction)):
            pass
        for k in flds(parent):
            v = getattr(parent, k, None)
            req_prefix = (isinstance(parent, A.Index) and k == "value") or \
                         (isinstance(parent, A.Call) and k == "func") or \
                         (isinstance(parent, A.Invoke) and k == "source")
            cands = v if isinstance(v, list) else [v]
            for j, item in enumerate(cands):
                if not isinstance(item, A.Call):
                    continue
                if not (isinstance(item.func, A.Name) and item.func.id in decoders):
                    continue
                if len(item.args) < 3 or not isinstance(item.args[0], A.String):
                    continue
                step = constnum(item.args[2])
                if step is None:
                    continue
                data = _rawbytes(item.args[0])
                plain = oluks_decrypt(data, int(step))
                if not printable(plain):
                    continue
                new = mkstringnode(plain)
                if req_prefix:
                    new.wrapped = True
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
                    and _isregtable(t.value.id) and t.notation != A.IndexNotation.DOT):
                i += 1
                continue
            name, k = t.value.id, constnum(t.idx)
            if k is None or not issimple(st.values[0]):
                i += 1
                continue
            k = int(k)
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
    packfns = []
    for fn in [x for x in walk(tree)
               if isinstance(x, (A.Function, A.LocalFunction))]:
        body = getattr(fn, "body", None)
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
        if _rawbytes(args[0]) != b"#":
            continue
        if not isinstance(vals[0], A.Table):
            continue
        packfns.append(fn)
        target = second.func
        if target.id != "select":
            for parent in list(walk(tree)):
                for k in flds(parent):
                    if (isinstance(parent, A.Index) and k == "idx" and parent.notation == A.IndexNotation.DOT) or \
                       (isinstance(parent, A.Invoke) and k == "func") or \
                       (isinstance(parent, A.Field) and k == "key" and not parent.between_brackets):
                        continue
                    v = getattr(parent, k, None)
                    items = v if isinstance(v, list) else [v]
                    for j, item in enumerate(items):
                        if isinstance(item, A.Name) and item.id == target.id and item is not target:
                            if isinstance(v, list):
                                v[j] = A.Name("select")
                            else:
                                setattr(parent, k, A.Name("select"))
                            n += 1
            second.func = A.Name("select")
            n += 1
    for fn in packfns:
        fnname = fn.name.id if isinstance(fn.name, A.Name) else None
        if fnname and _count_var_refs(tree, fnname, exclude_def=fn) == 0:
            _removestmt(tree, fn)
            n += 1
    return n


def _is_prop_name_slot(parent, k):
    if isinstance(parent, A.Index) and k == "idx" and parent.notation == A.IndexNotation.DOT:
        return True
    if isinstance(parent, A.Invoke) and k == "func":
        return True
    if isinstance(parent, A.Field) and k == "key" and not parent.between_brackets:
        return True
    return False


def _count_var_refs(root, name, exclude_def=None):
    cnt = [0]

    def rec(node):
        if node is None or isinstance(node, (str, bytes, int, float, bool)):
            return
        if node is exclude_def:
            return
        if isinstance(node, list):
            for x in node:
                rec(x)
            return
        for k in flds(node):
            if _is_prop_name_slot(node, k):
                continue
            v = getattr(node, k, None)
            if isinstance(v, A.Name) and v.id == name:
                cnt[0] += 1
            else:
                rec(v)

    rec(root)
    return cnt[0]


def _as_prefix(node):
    if not isinstance(node, (A.Name, A.Index, A.Call, A.Invoke)):
        node.wrapped = True
    return node


def _evalconst(node):
    if isinstance(node, A.Number):
        return True, float(node.n)
    if isinstance(node, A.UMinusOp) and isinstance(node.operand, A.Number):
        return True, -float(node.operand.n)
    if isinstance(node, A.String):
        return True, _rawbytes(node)
    if isinstance(node, A.TrueExpr):
        return True, True
    if isinstance(node, A.FalseExpr):
        return True, False
    if isinstance(node, A.Nil):
        return True, None
    return False, None


def _isluatuthy(val):
    return not (val is False or val is None)


def foldconstants(tree):
    changed = [0]

    def visit(node, req_prefix=False):
        if node is None or isinstance(node, (str, bytes, int, float, bool)):
            return node
        if isinstance(node, list):
            for i in range(len(node)):
                node[i] = visit(node[i], False)
            return node
        for k in flds(node):
            if _is_prop_name_slot(node, k):
                continue
            if isinstance(node, (A.Assign, A.LocalAssign)) and k == "targets":
                for t in node.targets:
                    if isinstance(t, A.Index):
                        t.value = visit(t.value, True)
                        if t.notation != A.IndexNotation.DOT:
                            t.idx = visit(t.idx, False)
                continue
            if isinstance(node, FN_NODES) and k in ("name", "args"):
                continue
            if isinstance(node, A.Fornum) and k == "target":
                continue
            if isinstance(node, A.Forin) and k == "targets":
                continue
            rp = (isinstance(node, A.Index) and k == "value") or \
                 (isinstance(node, A.Call) and k == "func") or \
                 (isinstance(node, A.Invoke) and k == "source")
            setattr(node, k, visit(getattr(node, k, None), rp))

        res = _fold_one_expr(node)
        if res is not node:
            changed[0] += 1
            if req_prefix:
                res = _as_prefix(res)
            return res
        return node

    visit(tree, False)
    return changed[0]


def _fold_one_expr(node):
    if isinstance(node, A.ULNotOp):
        opnd = node.operand
        ok, v = _evalconst(opnd)
        if ok:
            return A.FalseExpr() if _isluatuthy(v) else A.TrueExpr()
        if isinstance(opnd, A.EqToOp):
            return A.NotEqToOp(left=opnd.left, right=opnd.right)
        if isinstance(opnd, A.NotEqToOp):
            return A.EqToOp(left=opnd.left, right=opnd.right)
        if isinstance(opnd, A.ULNotOp) and isinstance(opnd.operand, (
                A.EqToOp, A.NotEqToOp, A.LessThanOp, A.LessOrEqThanOp,
                A.GreaterThanOp, A.GreaterOrEqThanOp)):
            return opnd.operand
        return node

    if isinstance(node, A.ULengthOP):
        if isinstance(node.operand, A.String):
            return mknumbernode(len(_rawbytes(node.operand)))
        return node

    if isinstance(node, A.UMinusOp):
        if isinstance(node.operand, A.UMinusOp) and isinstance(node.operand.operand, A.Number):
            return A.Number(node.operand.operand.n)
        if isinstance(node.operand, A.Number) and node.operand.n == 0:
            return A.Number(0)
        return node

    if isinstance(node, A.Concat):
        if isinstance(node.left, A.String) and isinstance(node.right, A.String):
            return mkstringnode(_rawbytes(node.left) + _rawbytes(node.right))
        return node

    if isinstance(node, A.AndLoOp):
        ok, lv = _evalconst(node.left)
        if ok:
            return node.right if _isluatuthy(lv) else node.left
        return node

    if isinstance(node, A.OrLoOp):
        ok, lv = _evalconst(node.left)
        if ok:
            return node.left if _isluatuthy(lv) else node.right
        return node

    if isinstance(node, (A.AddOp, A.SubOp, A.MultOp, A.FloatDivOp, A.ModOp, A.ExpoOp)):
        ok1, a = _evalconst(node.left)
        ok2, b = _evalconst(node.right)
        if ok1 and ok2 and isinstance(a, float) and isinstance(b, float):
            try:
                if isinstance(node, A.AddOp):
                    r = a + b
                elif isinstance(node, A.SubOp):
                    r = a - b
                elif isinstance(node, A.MultOp):
                    r = a * b
                elif isinstance(node, A.FloatDivOp):
                    if b == 0:
                        return node
                    r = a / b
                elif isinstance(node, A.ModOp):
                    if b == 0:
                        return node
                    r = a - math.floor(a / b) * b
                else:
                    if abs(b) > 1024:
                        return node
                    r = a ** b
                if math.isfinite(r):
                    return mknumbernode(r)
            except Exception:
                return node
        return node

    if isinstance(node, (A.EqToOp, A.NotEqToOp)):
        ok1, a = _evalconst(node.left)
        ok2, b = _evalconst(node.right)
        if ok1 and ok2:
            same = (type(a) is type(b)) and (a == b)
            res = same if isinstance(node, A.EqToOp) else (not same)
            return A.TrueExpr() if res else A.FalseExpr()
        return node

    if isinstance(node, (A.LessThanOp, A.LessOrEqThanOp, A.GreaterThanOp, A.GreaterOrEqThanOp)):
        ok1, a = _evalconst(node.left)
        ok2, b = _evalconst(node.right)
        if ok1 and ok2 and type(a) is type(b) and isinstance(a, (float, bytes)):
            if isinstance(node, A.LessThanOp):
                res = a < b
            elif isinstance(node, A.LessOrEqThanOp):
                res = a <= b
            elif isinstance(node, A.GreaterThanOp):
                res = a > b
            else:
                res = a >= b
            return A.TrueExpr() if res else A.FalseExpr()
        return node

    return node


def _walknoclosure(node):
    if node is None or isinstance(node, (str, bytes, int, float, bool)):
        return
    yield node
    if isinstance(node, FN_NODES):
        return
    if isinstance(node, list):
        for c in node:
            yield from _walknoclosure(c)
        return
    for k in flds(node):
        yield from _walknoclosure(getattr(node, k, None))


def _expr_free_names(node, out=None):
    if out is None:
        out = set()
    if node is None or isinstance(node, (str, bytes, int, float, bool)):
        return out
    if isinstance(node, A.Name):
        out.add(node.id)
        return out
    if isinstance(node, list):
        for x in node:
            _expr_free_names(x, out)
        return out
    for k in flds(node):
        if _is_prop_name_slot(node, k):
            continue
        _expr_free_names(getattr(node, k, None), out)
    return out


def _assignednames(node):
    out = set()
    for w in walk(node):
        if isinstance(w, (A.Assign, A.LocalAssign)):
            for t in w.targets:
                if isinstance(t, A.Name):
                    out.add(t.id)
        elif isinstance(w, A.LocalFunction) and isinstance(w.name, A.Name):
            out.add(w.name.id)
        elif isinstance(w, A.Function) and isinstance(w.name, A.Name):
            out.add(w.name.id)
        elif isinstance(w, A.Fornum) and isinstance(w.target, A.Name):
            out.add(w.target.id)
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


def _evict_name(env, nm):
    env.pop(nm, None)
    for k in list(env):
        if nm in _expr_free_names(env[k]):
            env.pop(k, None)


def _subst_expr(expr, env, req_prefix=False, count=None):
    if expr is None or isinstance(expr, (str, bytes, int, float, bool)):
        return expr
    if isinstance(expr, A.Name):
        if expr.id in env:
            nv = dup(env[expr.id])
            if req_prefix:
                nv = _as_prefix(nv)
            if count is not None:
                count[0] += 1
            return nv
        return expr
    if isinstance(expr, FN_NODES):
        return expr
    if isinstance(expr, list):
        for i in range(len(expr)):
            expr[i] = _subst_expr(expr[i], env, False, count)
        return expr
    for k in flds(expr):
        if _is_prop_name_slot(expr, k):
            continue
        rp = (isinstance(expr, A.Index) and k == "value") or \
             (isinstance(expr, A.Call) and k == "func") or \
             (isinstance(expr, A.Invoke) and k == "source")
        setattr(expr, k, _subst_expr(getattr(expr, k, None), env, rp, count))
    return expr


def propagateconstantsandaliases(tree):
    alllocals = set()
    for w in walk(tree):
        if isinstance(w, A.LocalAssign):
            for t in w.targets:
                if isinstance(t, A.Name):
                    alllocals.add(t.id)
        elif isinstance(w, A.LocalFunction) and isinstance(w.name, A.Name):
            alllocals.add(w.name.id)
        elif isinstance(w, FN_NODES):
            for p in w.args:
                if isinstance(p, A.Name):
                    alllocals.add(p.id)
        elif isinstance(w, A.Fornum) and isinstance(w.target, A.Name):
            alllocals.add(w.target.id)
        elif isinstance(w, A.Forin):
            for t in w.targets:
                if isinstance(t, A.Name):
                    alllocals.add(t.id)

    total = [0]

    def closure_mutated_in(fnbody):
        mut = set()
        for w in walk(fnbody):
            if isinstance(w, FN_NODES):
                mut |= _assignednames(w.body)
        return mut

    def prop_block(blk, env, closure_mut):
        if blk is None:
            return
        for st in blk.body:
            prop_stmt(st, env, closure_mut)

    def prop_nested_fns(node):
        for w in _walknoclosure(node):
            for k in flds(w):
                v = getattr(w, k, None)
                items = v if isinstance(v, list) else [v]
                for it in items:
                    if isinstance(it, FN_NODES):
                        cm = closure_mutated_in(it.body)
                        prop_block(it.body, {}, cm)

    def prop_stmt(st, env, closure_mut):
        if isinstance(st, (A.Function, A.LocalFunction)):
            if isinstance(st.name, A.Name):
                _evict_name(env, st.name.id)
            cm = closure_mutated_in(st.body)
            prop_block(st.body, {}, cm)
            return

        prop_nested_fns(st)

        if isinstance(st, (A.Assign, A.LocalAssign)):
            for t in st.targets:
                if isinstance(t, A.Index):
                    t.value = _subst_expr(t.value, env, True, total)
                    if t.notation != A.IndexNotation.DOT:
                        t.idx = _subst_expr(t.idx, env, False, total)
            for i in range(len(st.values)):
                st.values[i] = _subst_expr(st.values[i], env, False, total)

            if _hascall_now(st):
                for nm in list(env):
                    deps = {nm} | _expr_free_names(env[nm])
                    if any((d not in alllocals and d not in IMMUTABLE_LIBS) or d in closure_mut for d in deps):
                        env.pop(nm, None)

            if len(st.targets) == len(st.values):
                new_bindings = []
                for t, v in zip(st.targets, st.values):
                    if isinstance(t, A.Name):
                        _evict_name(env, t.id)
                        if ispropagatable(v) and t.id not in _expr_free_names(v):
                            deps = {t.id} | _expr_free_names(v)
                            if not (deps & closure_mut):
                                new_bindings.append((t.id, dup(v)))
                for nm, val in new_bindings:
                    env[nm] = val
            else:
                for t in st.targets:
                    if isinstance(t, A.Name):
                        _evict_name(env, t.id)
            return

        if isinstance(st, A.If):
            st.test = _subst_expr(st.test, env, False, total)
            if _hascall_now(st.test):
                for nm in list(env):
                    deps = {nm} | _expr_free_names(env[nm])
                    if any((d not in alllocals and d not in IMMUTABLE_LIBS) or d in closure_mut for d in deps):
                        env.pop(nm, None)
            prop_block(st.body, dict(env), closure_mut)
            cur = st.orelse
            while isinstance(cur, A.ElseIf):
                benv = dict(env)
                cur.test = _subst_expr(cur.test, benv, False, total)
                prop_nested_fns(cur.test)
                prop_block(cur.body, benv, closure_mut)
                cur = cur.orelse
            if isinstance(cur, A.Block):
                prop_block(cur, dict(env), closure_mut)
            for nm in _assignednames(st):
                _evict_name(env, nm)
            return

        if isinstance(st, A.While):
            mut = _assignednames(st)
            lenv = {k: dup(v) for k, v in env.items()
                    if k not in mut and not (_expr_free_names(v) & mut)}
            st.test = _subst_expr(st.test, lenv, False, total)
            prop_block(st.body, dict(lenv), closure_mut | mut)
            for nm in mut:
                _evict_name(env, nm)
            return

        if isinstance(st, A.Repeat):
            mut = _assignednames(st)
            lenv = {k: dup(v) for k, v in env.items()
                    if k not in mut and not (_expr_free_names(v) & mut)}
            benv = dict(lenv)
            prop_block(st.body, benv, closure_mut | mut)
            st.test = _subst_expr(st.test, benv, False, total)
            for nm in mut:
                _evict_name(env, nm)
            return

        if isinstance(st, A.Fornum):
            st.start = _subst_expr(st.start, env, False, total)
            st.stop = _subst_expr(st.stop, env, False, total)
            if not isinstance(st.step, (int, float)) and st.step is not None:
                st.step = _subst_expr(st.step, env, False, total)
            mut = _assignednames(st)
            lenv = {k: dup(v) for k, v in env.items()
                    if k not in mut and not (_expr_free_names(v) & mut)}
            prop_block(st.body, lenv, closure_mut | mut)
            for nm in mut:
                _evict_name(env, nm)
            return

        if isinstance(st, A.Forin):
            for i in range(len(st.iter)):
                st.iter[i] = _subst_expr(st.iter[i], env, False, total)
            mut = _assignednames(st)
            lenv = {k: dup(v) for k, v in env.items()
                    if k not in mut and not (_expr_free_names(v) & mut)}
            prop_block(st.body, lenv, closure_mut | mut)
            for nm in mut:
                _evict_name(env, nm)
            return

        if isinstance(st, A.Do):
            prop_block(st.body, env, closure_mut)
            return

        if isinstance(st, A.Return):
            for i in range(len(st.values)):
                st.values[i] = _subst_expr(st.values[i], env, False, total)
            env.clear()
            return

        if isinstance(st, A.Break):
            env.clear()
            return

        _subst_expr(st, env, False, total)
        if _hascall_now(st):
            for nm in list(env):
                deps = {nm} | _expr_free_names(env[nm])
                if any((d not in alllocals and d not in IMMUTABLE_LIBS) or d in closure_mut for d in deps):
                    env.pop(nm, None)

    root_cm = closure_mutated_in(tree.body)
    prop_block(tree.body, {}, root_cm)
    return total[0]


def simplifycontrolflow(tree):
    changed = [0]

    def negate_expr(e):
        if isinstance(e, A.ULNotOp):
            return e.operand
        if isinstance(e, A.EqToOp):
            return A.NotEqToOp(left=e.left, right=e.right)
        if isinstance(e, A.NotEqToOp):
            return A.EqToOp(left=e.left, right=e.right)
        return A.ULNotOp(operand=e)

    def can_splice_directly(sub_blk, later_stmts):
        sub_locals = set()
        for x in sub_blk.body:
            if isinstance(x, A.LocalAssign):
                for t in x.targets:
                    if isinstance(t, A.Name):
                        sub_locals.add(t.id)
            elif isinstance(x, A.LocalFunction) and isinstance(x.name, A.Name):
                sub_locals.add(x.name.id)
        if not sub_locals or not later_stmts:
            return True
        later_refs = set()
        opt.collectallnamesdeep(later_stmts, later_refs)
        return not (sub_locals & later_refs)

    def clean_block(blk):
        if blk is None:
            return
        for st in list(blk.body):
            for fn in [w for w in _walknoclosure(st) if isinstance(w, FN_NODES)]:
                clean_block(fn.body)
            if isinstance(st, (A.Function, A.LocalFunction)):
                clean_block(st.body)
            elif isinstance(st, A.If):
                clean_block(st.body)
                cur = st.orelse
                while isinstance(cur, A.ElseIf):
                    clean_block(cur.body)
                    cur = cur.orelse
                if isinstance(cur, A.Block):
                    clean_block(cur)
            elif isinstance(st, LOOPST + (A.Do,)):
                clean_block(st.body)

        newbody = []
        for idx_st, st in enumerate(blk.body):
            later_stmts = blk.body[idx_st + 1:]
            if isinstance(st, A.Do):
                if not st.body.body:
                    changed[0] += 1
                    continue
                if can_splice_directly(st.body, later_stmts):
                    newbody.extend(st.body.body)
                    changed[0] += 1
                    continue
            if isinstance(st, A.If):
                ok, cv = _evalconst(st.test)
                if ok:
                    changed[0] += 1
                    if _isluatuthy(cv):
                        if can_splice_directly(st.body, later_stmts):
                            newbody.extend(st.body.body)
                        else:
                            newbody.append(A.Do(body=st.body))
                        continue
                    if st.orelse is None:
                        continue
                    if isinstance(st.orelse, A.Block):
                        if can_splice_directly(st.orelse, later_stmts):
                            newbody.extend(st.orelse.body)
                        else:
                            newbody.append(A.Do(body=st.orelse))
                        continue
                    if isinstance(st.orelse, A.ElseIf):
                        newbody.append(A.If(test=st.orelse.test, body=st.orelse.body, orelse=st.orelse.orelse))
                        continue
                if not st.body.body and st.orelse is None and opt.ispure(st.test):
                    changed[0] += 1
                    continue
                if not st.body.body and isinstance(st.orelse, A.Block):
                    if not st.orelse.body and opt.ispure(st.test):
                        changed[0] += 1
                        continue
                    if st.orelse.body:
                        st.test = negate_expr(st.test)
                        st.body = st.orelse
                        st.orelse = None
                        changed[0] += 1
                elif isinstance(st.orelse, A.Block) and not st.orelse.body:
                    st.orelse = None
                    changed[0] += 1
            newbody.append(st)
            if isinstance(st, (A.Return, A.Break)):
                if len(newbody) < len(blk.body):
                    changed[0] += 1
                break
        blk.body = newbody

    clean_block(tree.body)
    return changed[0]


def fixvmregisterscoping(tree):
    changed = [0]

    def strip_inner_local(node, name):
        if node is None or isinstance(node, (str, bytes, int, float, bool)):
            return
        if isinstance(node, FN_NODES):
            return
        if isinstance(node, A.Block):
            for idx, s in enumerate(node.body):
                if (isinstance(s, A.LocalAssign) and len(s.targets) == 1
                        and isinstance(s.targets[0], A.Name) and s.targets[0].id == name):
                    if s.values:
                        node.body[idx] = A.Assign(targets=s.targets, values=s.values)
                    else:
                        node.body[idx] = A.Assign(targets=s.targets, values=[A.Nil()])
                    changed[0] += 1
                else:
                    strip_inner_local(s, name)
            return
        if isinstance(node, list):
            for x in node:
                strip_inner_local(x, name)
            return
        for k in flds(node):
            strip_inner_local(getattr(node, k, None), name)

    def visit_scope(root_blk, paramnames, outer_locals):
        fn_proto_prefixes = set()
        for p in paramnames:
            m = re.match(r"^p(\d+)_\d+$", p)
            if m:
                fn_proto_prefixes.add("v" + m.group(1) + "_")
        for w in _walknoclosure(root_blk):
            if isinstance(w, A.LocalAssign):
                for t in w.targets:
                    if isinstance(t, A.Name):
                        m = re.match(r"^v(\d+)_\d+$", t.id)
                        if m:
                            fn_proto_prefixes.add("v" + m.group(1) + "_")

        def belongs_here(nm):
            if nm in paramnames or nm in outer_locals:
                return False
            if not VM_REG_RE.match(nm):
                return False
            if nm.startswith(("_ssa_", "vtbl", "vreg", "vfl")):
                return True
            if fn_proto_prefixes:
                return any(nm.startswith(pref) for pref in fn_proto_prefixes)
            return not outer_locals

        def collect_shallow(node, out):
            if node is None or isinstance(node, (str, bytes, int, float, bool)):
                return
            if isinstance(node, FN_NODES):
                if isinstance(node, (A.Function, A.LocalFunction)) and isinstance(node.name, A.Name):
                    if belongs_here(node.name.id):
                        out.add(node.name.id)
                for w in walk(node.body):
                    if isinstance(w, A.Name) and belongs_here(w.id):
                        out.add(w.id)
                return
            if isinstance(node, list):
                for x in node:
                    collect_shallow(x, out)
                return
            if isinstance(node, A.Name):
                if belongs_here(node.id):
                    out.add(node.id)
                return
            for k in flds(node):
                if _is_prop_name_slot(node, k):
                    continue
                collect_shallow(getattr(node, k, None), out)

        def iter_direct_fns(stmt):
            found_fns = []

            def rec(n):
                if n is None or isinstance(n, (str, bytes, int, float, bool)):
                    return
                if isinstance(n, A.Block):
                    return
                if isinstance(n, FN_NODES):
                    found_fns.append(n)
                    return
                if isinstance(n, list):
                    for x in n:
                        rec(x)
                    return
                for k in flds(n):
                    rec(getattr(n, k, None))

            if isinstance(stmt, (A.Function, A.LocalFunction)):
                found_fns.append(stmt)
            else:
                rec(stmt)
            return found_fns

        def visit_blk(blk, encl_declared):
            if blk is None:
                return
            cur_decl = set(encl_declared)
            stmts = blk.body
            used_at = {}
            for idx, s in enumerate(stmts):
                names = set()
                collect_shallow(s, names)
                for nm in names:
                    used_at.setdefault(nm, []).append(idx)

            inserts_before = {}
            for nm in sorted(used_at):
                if nm in cur_decl:
                    continue
                idxs = used_at[nm]
                first = idxs[0]
                s0 = stmts[first]
                if isinstance(s0, A.LocalAssign) and any(isinstance(t, A.Name) and t.id == nm for t in s0.targets):
                    cur_decl.add(nm)
                    continue
                if isinstance(s0, A.LocalFunction) and isinstance(s0.name, A.Name) and s0.name.id == nm:
                    cur_decl.add(nm)
                    continue
                if (isinstance(s0, A.Assign) and len(s0.targets) == 1 and len(s0.values) == 1
                        and isinstance(s0.targets[0], A.Name) and s0.targets[0].id == nm
                        and nm not in _expr_free_names(s0.values[0])):
                    stmts[first] = A.LocalAssign(targets=s0.targets, values=s0.values)
                    for later in idxs[1:]:
                        strip_inner_local(stmts[later], nm)
                    cur_decl.add(nm)
                    changed[0] += 1
                    continue
                if len(idxs) == 1 and isinstance(s0, A.If) and s0.orelse is None and nm not in _expr_free_names(s0.test):
                    continue
                if len(idxs) == 1 and isinstance(s0, A.Do):
                    continue
                if len(idxs) > 1 or not any(
                        isinstance(w, A.LocalAssign) and any(isinstance(t, A.Name) and t.id == nm for t in w.targets)
                        for w in _walknoclosure(s0)):
                    inserts_before.setdefault(first, []).append(nm)
                    for kidx in idxs:
                        strip_inner_local(stmts[kidx], nm)
                    cur_decl.add(nm)
                    changed[0] += 1

            if inserts_before:
                newstmts = []
                for idx, s in enumerate(stmts):
                    for nm in inserts_before.get(idx, ()):
                        newstmts.append(A.LocalAssign(targets=[A.Name(nm)], values=[A.Nil()]))
                    newstmts.append(s)
                blk.body = newstmts

            run_decl = set(encl_declared)
            for s in blk.body:
                if isinstance(s, A.LocalAssign):
                    for t in s.targets:
                        if isinstance(t, A.Name):
                            run_decl.add(t.id)
                elif isinstance(s, A.LocalFunction) and isinstance(s.name, A.Name):
                    run_decl.add(s.name.id)
                for fn in iter_direct_fns(s):
                    pnames = {p.id for p in fn.args if isinstance(p, A.Name)}
                    visit_scope(fn.body, pnames, outer_locals | run_decl)
                if isinstance(s, (A.Function, A.LocalFunction)):
                    continue
                if isinstance(s, A.Fornum) and isinstance(s.target, A.Name):
                    visit_blk(s.body, run_decl | {s.target.id})
                    continue
                if isinstance(s, A.Forin):
                    visit_blk(s.body, run_decl | {t.id for t in s.targets if isinstance(t, A.Name)})
                    continue
                for b in opt.getchildblocks(s):
                    visit_blk(b, run_decl)

        visit_blk(root_blk, set(paramnames))

    visit_scope(tree.body, set(), set())
    return changed[0]


def splitblockliveranges(tree):
    seq = [0]
    changed = [0]

    def closure_mentions(stmts_slice, name):
        for s in stmts_slice:
            for w in walk(s):
                if isinstance(w, FN_NODES):
                    out = set()
                    opt.collectallnamesdeep(w, out)
                    if name in out:
                        return True
        return False

    def rename_free_in_node(node, old, new):
        if node is None or isinstance(node, (str, bytes, int, float, bool)):
            return
        if isinstance(node, list):
            for x in node:
                rename_free_in_node(x, old, new)
            return
        if isinstance(node, A.Block):
            rename_free_in_stmts(node.body, old, new)
            return
        if isinstance(node, FN_NODES):
            if isinstance(node, (A.Function, A.LocalFunction)) and isinstance(node.name, A.Name):
                if node.name.id == old:
                    node.name.id = new
            if any(isinstance(p, A.Name) and p.id == old for p in node.args):
                return
            rename_free_in_stmts(node.body.body, old, new)
            return
        if isinstance(node, A.Fornum):
            rename_free_in_node(node.start, old, new)
            rename_free_in_node(node.stop, old, new)
            if not isinstance(node.step, (int, float)):
                rename_free_in_node(node.step, old, new)
            if isinstance(node.target, A.Name) and node.target.id == old:
                return
            rename_free_in_stmts(node.body.body, old, new)
            return
        if isinstance(node, A.Forin):
            rename_free_in_node(node.iter, old, new)
            if any(isinstance(t, A.Name) and t.id == old for t in node.targets):
                return
            rename_free_in_stmts(node.body.body, old, new)
            return
        for k in flds(node):
            if _is_prop_name_slot(node, k):
                continue
            v = getattr(node, k, None)
            if isinstance(v, A.Name) and v.id == old:
                v.id = new
            else:
                rename_free_in_node(v, old, new)

    def rename_free_in_stmts(stmts, old, new):
        for s in stmts:
            if isinstance(s, A.LocalAssign):
                rename_free_in_node(s.values, old, new)
                if any(isinstance(t, A.Name) and t.id == old for t in s.targets):
                    return
                continue
            if isinstance(s, A.LocalFunction) and isinstance(s.name, A.Name) and s.name.id == old:
                return
            rename_free_in_node(s, old, new)

    for blk in [b for b in walk(tree) if isinstance(b, A.Block)]:
        decl_at = {}
        i = 0
        while i < len(blk.body):
            s = blk.body[i]
            if isinstance(s, A.LocalAssign):
                for t in s.targets:
                    if isinstance(t, A.Name):
                        decl_at[t.id] = i
                i += 1
                continue
            if isinstance(s, A.LocalFunction) and isinstance(s.name, A.Name):
                decl_at[s.name.id] = i
                i += 1
                continue
            if (isinstance(s, A.Assign) and len(s.targets) == 1 and len(s.values) == 1
                    and isinstance(s.targets[0], A.Name)):
                nm = s.targets[0].id
                if nm in decl_at:
                    d_i = decl_at[nm]
                    if not closure_mentions(blk.body[d_i:i], nm):
                        seq[0] += 1
                        fresh = "_ssa_" + str(seq[0])
                        blk.body[i] = A.LocalAssign(targets=[A.Name(fresh)], values=s.values)
                        rename_free_in_stmts(blk.body[i + 1:], nm, fresh)
                        decl_at.pop(nm, None)
                        decl_at[fresh] = i
                        changed[0] += 1
            i += 1
    return changed[0]


def dropdeadlocalsandstores(tree):
    removed = [0]

    def is_pure_rhs(v):
        return opt.ispure(v) or isinstance(v, A.AnonymousFunction)

    for blk in [b for b in walk(tree) if isinstance(b, A.Block)]:
        i = 0
        while i < len(blk.body):
            s = blk.body[i]
            if isinstance(s, A.LocalAssign) and len(s.targets) == 1 and isinstance(s.targets[0], A.Name):
                nm = s.targets[0].id
                vals = s.values
                if len(vals) <= 1 and all(is_pure_rhs(v) for v in vals):
                    used = False
                    for later in blk.body[i + 1:]:
                        out = set()
                        opt.collectallnamesdeep(later, out)
                        if nm in out:
                            used = True
                            break
                    if not used:
                        blk.body.pop(i)
                        removed[0] += 1
                        continue
            elif isinstance(s, A.LocalFunction) and isinstance(s.name, A.Name):
                nm = s.name.id
                used = False
                for later in blk.body[i + 1:]:
                    out = set()
                    opt.collectallnamesdeep(later, out)
                    if nm in out:
                        used = True
                        break
                if not used:
                    in_self = set()
                    opt.collectallnamesdeep(s.body, in_self)
                    if nm not in in_self or not any(
                            nm in (lambda st2: (opt.collectallnamesdeep(st2, z := set()), z)[1])(st2)
                            for st2 in blk.body[i + 1:]):
                        blk.body.pop(i)
                        removed[0] += 1
                        continue
            i += 1
    return removed[0]


def removedeadmoonsecscaffolding(tree, decoders, cachetables):
    removed = 0
    for dec in list(decoders):
        for fn in [w for w in walk(tree) if isinstance(w, (A.Function, A.LocalFunction))]:
            if isinstance(fn.name, A.Name) and fn.name.id == dec:
                if _count_var_refs(tree, dec, exclude_def=fn) == 0:
                    _removestmt(tree, fn)
                    removed += 1
    for ct in list(cachetables):
        for blk in [b for b in walk(tree) if isinstance(b, A.Block)]:
            i = 0
            while i < len(blk.body):
                s = blk.body[i]
                if (isinstance(s, (A.Assign, A.LocalAssign)) and len(s.targets) == 1
                        and isinstance(s.targets[0], A.Name) and s.targets[0].id == ct
                        and len(s.values) == 1 and isinstance(s.values[0], A.Table)
                        and not s.values[0].fields):
                    if _count_var_refs(tree, ct, exclude_def=s) == 0:
                        blk.body.pop(i)
                        removed += 1
                        continue
                i += 1

    top = tree.body.body
    if top and isinstance(top[0], A.Assign):
        tnames = [t.id for t in top[0].targets if isinstance(t, A.Name)]
        if "Protected_by_MoonSecV2" in tnames or "Discord" in tnames:
            if all(_count_var_refs(tree, nm, exclude_def=top[0]) == 0 for nm in tnames):
                top.pop(0)
                removed += 1

    if len(top) >= 2:
        fn_st = top[-2]
        call_st = top[-1]
        if (isinstance(fn_st, (A.Function, A.LocalFunction))
                and isinstance(fn_st.name, A.Name) and fn_st.name.id == "devirt"
                and isinstance(call_st, A.Call)
                and isinstance(call_st.func, A.Name) and call_st.func.id == "devirt"):
            has_shallow_varargs = any(
                isinstance(w, (A.Varargs, A.Dots)) and w not in fn_st.args
                for w in _walknoclosure(fn_st.body)
            )
            if not has_shallow_varargs and _count_var_refs(tree, "devirt", exclude_def=fn_st) == 1:
                prefix = top[:-2]
                tree.body.body = prefix + fn_st.body.body
                removed += 1
    return removed


def splitdeclarationsonebyone(tree):
    changed = 0
    for blk in [b for b in walk(tree) if isinstance(b, A.Block)]:
        declared_empty = set()
        for s in blk.body:
            if isinstance(s, A.LocalAssign) and len(s.values) == 0:
                for t in s.targets:
                    if isinstance(t, A.Name):
                        declared_empty.add(t.id)
        if declared_empty:
            opt.consolidatelocals(blk, declared_empty)
            changed += 1

        newbody = []
        for s in blk.body:
            if isinstance(s, A.LocalAssign) and len(s.targets) > 1:
                if len(s.values) == 0:
                    for t in s.targets:
                        newbody.append(A.LocalAssign(targets=[t], values=[A.Nil()]))
                    changed += 1
                    continue
                if len(s.values) >= len(s.targets):
                    earlier = set()
                    conflict = False
                    for t, v in zip(s.targets, s.values):
                        if _expr_free_names(v) & earlier:
                            conflict = True
                            break
                        if isinstance(t, A.Name):
                            earlier.add(t.id)
                    if not conflict:
                        for idx_tv, (t, v) in enumerate(zip(s.targets, s.values)):
                            newbody.append(A.LocalAssign(targets=[t], values=[v]))
                        changed += 1
                        continue
            if (isinstance(s, A.Assign) and len(s.targets) > 1
                    and len(s.values) == len(s.targets)
                    and all(isinstance(t, A.Name) for t in s.targets)):
                earlier = set()
                conflict = False
                for t, v in zip(s.targets, s.values):
                    if _expr_free_names(v) & earlier:
                        conflict = True
                        break
                    earlier.add(t.id)
                if not conflict:
                    for t, v in zip(s.targets, s.values):
                        newbody.append(A.Assign(targets=[t], values=[v]))
                    changed += 1
                    continue
            newbody.append(s)
        blk.body = newbody
    return changed


def normalizeunpack(tree):
    n = 0
    for parent in list(walk(tree)):
        for k in flds(parent):
            if _is_prop_name_slot(parent, k):
                continue
            if isinstance(parent, A.Index) and k == "idx":
                continue
            if isinstance(parent, FN_NODES) and k in ("name", "args"):
                continue
            if isinstance(parent, (A.Assign, A.LocalAssign)) and k == "targets":
                continue
            v = getattr(parent, k, None)
            if isinstance(v, A.Name) and v.id == "unpack":
                setattr(parent, k, A.Index(idx=A.Name("unpack"), value=A.Name("table")))
                n += 1
            elif isinstance(v, list):
                for i, item in enumerate(v):
                    if isinstance(item, A.Name) and item.id == "unpack":
                        v[i] = A.Index(idx=A.Name("unpack"), value=A.Name("table"))
                        n += 1
    return n


def renamevfp(tree):
    opt.resugarfunctions(tree)

    all_globals = set()

    def collect_globals(node, scope_set):
        if node is None or isinstance(node, (str, bytes, int, float, bool)):
            return
        if isinstance(node, list):
            for x in node:
                collect_globals(x, scope_set)
            return
        if isinstance(node, A.Block):
            cur = set(scope_set)
            for s in node.body:
                if isinstance(s, A.LocalAssign):
                    collect_globals(s.values, cur)
                    for t in s.targets:
                        if isinstance(t, A.Name):
                            cur.add(t.id)
                        else:
                            collect_globals(t, cur)
                elif isinstance(s, A.LocalFunction):
                    if isinstance(s.name, A.Name):
                        cur.add(s.name.id)
                    inner = cur | {p.id for p in s.args if isinstance(p, A.Name)}
                    collect_globals(s.body, inner)
                elif isinstance(s, A.Function):
                    if isinstance(s.name, A.Name) and s.name.id not in cur:
                        all_globals.add(s.name.id)
                    inner = cur | {p.id for p in s.args if isinstance(p, A.Name)}
                    collect_globals(s.body, inner)
                elif isinstance(s, A.Fornum):
                    collect_globals(s.start, cur)
                    collect_globals(s.stop, cur)
                    if not isinstance(s.step, (int, float)):
                        collect_globals(s.step, cur)
                    inner = cur | ({s.target.id} if isinstance(s.target, A.Name) else set())
                    collect_globals(s.body, inner)
                elif isinstance(s, A.Forin):
                    collect_globals(s.iter, cur)
                    inner = cur | {t.id for t in s.targets if isinstance(t, A.Name)}
                    collect_globals(s.body, inner)
                else:
                    collect_globals(s, cur)
            return
        if isinstance(node, A.AnonymousFunction):
            inner = set(scope_set) | {p.id for p in node.args if isinstance(p, A.Name)}
            collect_globals(node.body, inner)
            return
        if isinstance(node, A.Name):
            if node.id not in scope_set:
                all_globals.add(node.id)
            return
        for k in flds(node):
            if _is_prop_name_slot(node, k):
                continue
            collect_globals(getattr(node, k, None), scope_set)

    collect_globals(tree.body, set())

    f_counter = [0]

    def alloc_name(prefix, counter_box, forbidden):
        while True:
            counter_box[0] += 1
            cand = "%s%d" % (prefix, counter_box[0])
            if cand not in forbidden and cand not in all_globals:
                return cand

    def captured_targets_in(fn_node, env_map):
        raw_used = set()
        opt.collectallnamesdeep(fn_node.body, raw_used)
        local_params = {p.id for p in fn_node.args if isinstance(p, A.Name)}
        raw_used -= local_params
        return {env_map[u] for u in raw_used if u in env_map}

    def rename_expr(expr, env_map):
        if expr is None or isinstance(expr, (str, bytes, int, float, bool)):
            return
        if isinstance(expr, list):
            for x in expr:
                rename_expr(x, env_map)
            return
        if isinstance(expr, A.AnonymousFunction):
            rename_fn(expr, env_map)
            return
        if isinstance(expr, A.Name):
            if expr.id in env_map:
                expr.id = env_map[expr.id]
            return
        for k in flds(expr):
            if _is_prop_name_slot(expr, k):
                continue
            rename_expr(getattr(expr, k, None), env_map)

    def rename_fn(fn_node, outer_map):
        used_upvals = captured_targets_in(fn_node, outer_map)
        fn_map = dict(outer_map)
        p_counter = [0]
        p_forbidden = set(used_upvals)
        for p in fn_node.args:
            if isinstance(p, A.Name):
                newp = alloc_name("p", p_counter, p_forbidden)
                p_forbidden.add(newp)
                fn_map[p.id] = newp
                p.id = newp
        v_counter = [0]
        v_forbidden = set(used_upvals) | p_forbidden
        rename_block(fn_node.body, fn_map, v_counter, v_forbidden)

    def rename_block(blk, env_map, v_counter, v_forbidden):
        if blk is None:
            return
        cur_map = dict(env_map)
        for s in blk.body:
            if isinstance(s, A.LocalAssign):
                if (len(s.targets) == 1 and len(s.values) == 1
                        and isinstance(s.targets[0], A.Name)
                        and isinstance(s.values[0], A.AnonymousFunction)):
                    rename_expr(s.values, cur_map)
                    old = s.targets[0].id
                    newf = alloc_name("f", f_counter, v_forbidden)
                    v_forbidden.add(newf)
                    cur_map[old] = newf
                    s.targets[0].id = newf
                    continue
                rename_expr(s.values, cur_map)
                for t in s.targets:
                    if isinstance(t, A.Name):
                        old = t.id
                        newv = alloc_name("v", v_counter, v_forbidden)
                        v_forbidden.add(newv)
                        cur_map[old] = newv
                        t.id = newv
            elif isinstance(s, A.LocalFunction):
                if isinstance(s.name, A.Name):
                    old = s.name.id
                    newf = alloc_name("f", f_counter, v_forbidden)
                    v_forbidden.add(newf)
                    cur_map[old] = newf
                    s.name.id = newf
                rename_fn(s, cur_map)
            elif isinstance(s, A.Function):
                if isinstance(s.name, A.Name):
                    if s.name.id in cur_map:
                        s.name.id = cur_map[s.name.id]
                elif isinstance(s.name, A.Index):
                    rename_expr(s.name, cur_map)
                rename_fn(s, cur_map)
            elif isinstance(s, A.Assign):
                for t in s.targets:
                    if isinstance(t, A.Name):
                        if t.id in cur_map:
                            t.id = cur_map[t.id]
                    elif isinstance(t, A.Index):
                        rename_expr(t.value, cur_map)
                        if t.notation != A.IndexNotation.DOT:
                            rename_expr(t.idx, cur_map)
                rename_expr(s.values, cur_map)
            elif isinstance(s, A.If):
                rename_expr(s.test, cur_map)
                rename_block(s.body, cur_map, v_counter, v_forbidden)
                cur = s.orelse
                while isinstance(cur, A.ElseIf):
                    rename_expr(cur.test, cur_map)
                    rename_block(cur.body, cur_map, v_counter, v_forbidden)
                    cur = cur.orelse
                if isinstance(cur, A.Block):
                    rename_block(cur, cur_map, v_counter, v_forbidden)
            elif isinstance(s, A.While):
                rename_expr(s.test, cur_map)
                rename_block(s.body, cur_map, v_counter, v_forbidden)
            elif isinstance(s, A.Repeat):
                rmap = dict(cur_map)
                rename_block_in_place(s.body, rmap, v_counter, v_forbidden)
                rename_expr(s.test, rmap)
            elif isinstance(s, A.Fornum):
                rename_expr(s.start, cur_map)
                rename_expr(s.stop, cur_map)
                if not isinstance(s.step, (int, float)):
                    rename_expr(s.step, cur_map)
                bmap = dict(cur_map)
                if isinstance(s.target, A.Name) and s.target.id != "_":
                    newv = alloc_name("v", v_counter, v_forbidden)
                    v_forbidden.add(newv)
                    bmap[s.target.id] = newv
                    s.target.id = newv
                rename_block(s.body, bmap, v_counter, v_forbidden)
            elif isinstance(s, A.Forin):
                rename_expr(s.iter, cur_map)
                bmap = dict(cur_map)
                for t in s.targets:
                    if isinstance(t, A.Name) and t.id != "_":
                        newv = alloc_name("v", v_counter, v_forbidden)
                        v_forbidden.add(newv)
                        bmap[t.id] = newv
                        t.id = newv
                rename_block(s.body, bmap, v_counter, v_forbidden)
            elif isinstance(s, A.Do):
                rename_block(s.body, cur_map, v_counter, v_forbidden)
            elif isinstance(s, A.Return):
                rename_expr(s.values, cur_map)
            elif isinstance(s, A.Break):
                pass
            else:
                rename_expr(s, cur_map)

    def rename_block_in_place(blk, cur_map, v_counter, v_forbidden):
        if blk is None:
            return
        for s in blk.body:
            if isinstance(s, A.LocalAssign):
                rename_expr(s.values, cur_map)
                for t in s.targets:
                    if isinstance(t, A.Name):
                        old = t.id
                        newv = alloc_name("v", v_counter, v_forbidden)
                        v_forbidden.add(newv)
                        cur_map[old] = newv
                        t.id = newv
            elif isinstance(s, A.LocalFunction):
                if isinstance(s.name, A.Name):
                    old = s.name.id
                    newf = alloc_name("f", f_counter, v_forbidden)
                    v_forbidden.add(newf)
                    cur_map[old] = newf
                    s.name.id = newf
                rename_fn(s, cur_map)
            else:
                sub = A.Block(body=[s])
                rename_block(sub, cur_map, v_counter, v_forbidden)

    top_v_counter = [0]
    top_forbidden = set(all_globals)
    rename_block(tree.body, {}, top_v_counter, top_forbidden)
    opt.resugarfunctions(tree)


def _leaks_table(stmt, name):
    covered = set()
    for w in walk(stmt):
        if isinstance(w, A.Index) and isname(w.value, name) and w.notation != A.IndexNotation.DOT:
            covered.add(id(w.value))
    for w in walk(stmt):
        if isinstance(w, A.Name) and w.id == name and id(w) not in covered:
            if not _is_unpack_arg(w, stmt):
                return True
    return False


def _is_unpack_arg(namenode, stmt):
    for w in walk(stmt):
        if _is_unpack_call_generic(w) and w.args[0] is namenode:
            return True
    return False


def _writes(stmt, name, k):
    if isinstance(stmt, A.Assign) and len(stmt.targets) == 1:
        t = stmt.targets[0]
        return (isinstance(t, A.Index) and isname(t.value, name)
                and t.notation != A.IndexNotation.DOT and constnum(t.idx) == k)
    return False


def _reads(stmt, name, k):
    for w in walk(stmt):
        if isinstance(w, A.Index) and isname(w.value, name) \
           and w.notation != A.IndexNotation.DOT and constnum(w.idx) == k:
            return True
        u = unpack_of(w, name)
        if u is not None and u[0] <= k <= u[1]:
            return True
    return False


def removesecureeq(tree):
    target = None
    for fn in [n for n in walk(tree)
               if isinstance(n, (A.Function, A.LocalFunction))]:
        nm = getattr(fn, "name", None)
        nm = getattr(nm, "id", None) if isinstance(nm, A.Name) else None
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


def _strip_all_comments(tree):
    for w in walk(tree):
        if hasattr(w, "comments"):
            w.comments = []


def _tidy_lua_text(text):
    text = re.sub(r"\{\s*\n\s*\}", "{}", text)
    lines = text.splitlines()
    out = []
    blank = False
    for line in lines:
        s = line.strip()
        if s == ";":
            if out:
                k = len(out) - 1
                while k >= 0 and not out[k]:
                    k -= 1
                if k >= 0 and not out[k].endswith(";"):
                    out[k] = out[k] + ";"
            continue
        if not s:
            if not blank and out:
                out.append("")
            blank = True
        else:
            if s.startswith("(") and out:
                k = len(out) - 1
                while k >= 0 and not out[k]:
                    k -= 1
                if k >= 0:
                    prev = out[k].strip()
                    if not prev.endswith(("then", "do", "else", "repeat", ",", "{", "(", ";", "=")) and not re.search(r"\bfunction\b[^)]*\)\s*$", prev):
                        out[k] = out[k] + ";"
            blank = False
            out.append(line.rstrip())
    while out and not out[-1]:
        out.pop()
    return "\n".join(out) + "\n"


def run(inpath, outpath, rounds=8):
    src = open(inpath, encoding="utf-8", errors="replace").read()
    banner = None
    first_nl = src.find("\n")
    first_line = src[:first_nl] if first_nl != -1 else src
    if first_line.startswith("-- [["):
        banner = first_line

    tree = ast.parse(src)
    _strip_all_comments(tree)

    decoders, cachetables = find_decoders(tree)
    c3 = removesecureeq(tree)
    c6 = resolvepackhelper(tree)
    fixvmregisterscoping(tree)

    c0 = 0
    c1 = 0
    c2 = 0
    c7 = 0
    for _ in range(rounds):
        a = foldunpackgroups(tree)
        r = regtabletolocals(tree)
        p = propagateconstantsandaliases(tree)
        f = foldconstants(tree)
        b = decryptstrings(tree, decoders)
        s = simplifycontrolflow(tree)
        c0 += a
        c1 += r
        c2 += b
        c7 += p + f + s
        if not (a or r or p or f or b or s):
            break

    c5 = deadstoreelim(tree)
    removedeadmoonsecscaffolding(tree, decoders, cachetables)
    fixvmregisterscoping(tree)

    for _ in range(4):
        split_n = splitblockliveranges(tree)
        opt.optimizetree(tree, maxlaps=20)
        p2 = propagateconstantsandaliases(tree)
        f2 = foldconstants(tree)
        b2 = decryptstrings(tree, decoders)
        s2 = simplifycontrolflow(tree)
        d2 = dropdeadlocalsandstores(tree)
        c2 += b2
        c7 += p2 + f2 + s2
        if not (split_n or p2 or f2 or b2 or s2 or d2):
            break

    removedeadmoonsecscaffolding(tree, decoders, cachetables)
    sinknilpredecls(tree)
    c8 = dropdeadlocalsandstores(tree)
    c9 = normalizeunpack(tree)
    splitdeclarationsonebyone(tree)
    renamevfp(tree)
    splitdeclarationsonebyone(tree)
    _strip_all_comments(tree)

    raw_out = ast.to_lua_source(tree)
    out = _tidy_lua_text(raw_out)
    if banner:
        out = banner + "\n" + out
    open(outpath, "w", encoding="utf-8").write(out)
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


def sinknilpredecls(tree):
    changed = [0]

    def visit_blk(blk):
        if blk is None:
            return
        loop = True
        while loop:
            loop = False
            i = 0
            while i < len(blk.body):
                s = blk.body[i]
                if (isinstance(s, A.LocalAssign) and len(s.targets) == 1
                        and isinstance(s.targets[0], A.Name)
                        and (len(s.values) == 0 or (len(s.values) == 1 and isinstance(s.values[0], A.Nil)))):
                    nm = s.targets[0].id
                    uses = []
                    shadowed_at = None
                    for j in range(i + 1, len(blk.body)):
                        sj = blk.body[j]
                        if isinstance(sj, A.LocalAssign) and any(isinstance(t, A.Name) and t.id == nm for t in sj.targets):
                            in_vals = set()
                            opt.collectallnamesdeep(sj.values, in_vals)
                            if nm in in_vals:
                                uses.append(j)
                            shadowed_at = j
                            break
                        if isinstance(sj, A.LocalFunction) and isinstance(sj.name, A.Name) and sj.name.id == nm:
                            shadowed_at = j
                            break
                        refs = set()
                        opt.collectallnamesdeep(sj, refs)
                        if nm in refs:
                            uses.append(j)
                    if not uses:
                        blk.body.pop(i)
                        changed[0] += 1
                        loop = True
                        continue
                    if len(uses) == 1 and shadowed_at is None:
                        k = uses[0]
                        sk = blk.body[k]
                        if (isinstance(sk, A.Assign) and len(sk.targets) == 1 and len(sk.values) == 1
                                and isinstance(sk.targets[0], A.Name) and sk.targets[0].id == nm
                                and nm not in _expr_free_names(sk.values[0])):
                            blk.body[k] = A.LocalAssign(targets=sk.targets, values=sk.values)
                            blk.body.pop(i)
                            changed[0] += 1
                            loop = True
                            continue
                        if isinstance(sk, A.If):
                            branches = []
                            trefs = set()
                            opt.collectallnamesdeep(sk.test, trefs)
                            if nm not in trefs:
                                brefs = set()
                                opt.collectallnamesdeep(sk.body, brefs)
                                if nm in brefs:
                                    branches.append(sk.body)
                                cur = sk.orelse
                                ok_if = True
                                while isinstance(cur, A.ElseIf):
                                    er = set()
                                    opt.collectallnamesdeep(cur.test, er)
                                    if nm in er:
                                        ok_if = False
                                        break
                                    eb = set()
                                    opt.collectallnamesdeep(cur.body, eb)
                                    if nm in eb:
                                        branches.append(cur.body)
                                    cur = cur.orelse
                                if ok_if and isinstance(cur, A.Block):
                                    eb = set()
                                    opt.collectallnamesdeep(cur, eb)
                                    if nm in eb:
                                        branches.append(cur)
                                if ok_if and len(branches) == 1:
                                    branches[0].body.insert(0, s)
                                    blk.body.pop(i)
                                    changed[0] += 1
                                    loop = True
                                    continue
                i += 1
        for st in blk.body:
            for b in opt.getchildblocks(st):
                visit_blk(b)
            for fn in [w for w in _walknoclosure(st) if isinstance(w, FN_NODES)]:
                visit_blk(fn.body)
            if isinstance(st, (A.Function, A.LocalFunction)):
                visit_blk(st.body)

    visit_blk(tree.body)
    return changed[0]


def finalize(inpath, outpath):
    src = open(inpath, encoding="utf-8", errors="replace").read()
    banner = None
    first_nl = src.find("\n")
    first_line = src[:first_nl] if first_nl != -1 else src
    if first_line.startswith("-- [["):
        banner = first_line
    tree = ast.parse(src)
    _strip_all_comments(tree)
    simplifycontrolflow(tree)
    sinknilpredecls(tree)
    splitblockliveranges(tree)
    sinknilpredecls(tree)
    dropdeadlocalsandstores(tree)
    splitdeclarationsonebyone(tree)
    renamevfp(tree)
    splitdeclarationsonebyone(tree)
    _strip_all_comments(tree)
    out = _tidy_lua_text(ast.to_lua_source(tree))
    if banner:
        out = banner + "\n" + out
    open(outpath, "w", encoding="utf-8").write(out)


if __name__ == "__main__":
    if len(sys.argv) >= 4 and sys.argv[1] == "--finalize":
        finalize(sys.argv[2], sys.argv[3])
    else:
        run(sys.argv[1], sys.argv[2])
