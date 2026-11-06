import copy
import sys
import time
from luaparser import ast, astnodes as A

def isblock(x):
    return isinstance(x, A.Block)

def getchildblocks(stmt):
    blocks = []
    if isinstance(stmt, A.If):
        blocks.append(stmt.body)
        node = stmt.orelse
        while isinstance(node, A.ElseIf):
            blocks.append(node.body)
            node = node.orelse
        if isblock(node):
            blocks.append(node)
    elif isinstance(stmt, (A.While, A.Repeat, A.Fornum, A.Forin, A.Do)):
        blocks.append(stmt.body)
    return blocks

def getfunctionbodies(stmt):
    bodies = []
    if isinstance(stmt, (A.Function, A.LocalFunction)):
        bodies.append(stmt.body)
    for val in getattr(stmt, 'values', []) or []:
        bodies.extend(findanonfuncbodies(val))
    if isinstance(stmt, A.Call):
        bodies.extend(findanonfuncbodies(stmt.func))
        for arg in stmt.args:
            bodies.extend(findanonfuncbodies(arg))
    elif isinstance(stmt, A.Invoke):
        bodies.extend(findanonfuncbodies(stmt.source))
        for arg in stmt.args:
            bodies.extend(findanonfuncbodies(arg))
    return bodies

def findanonfuncbodies(expr):
    out = []
    if isinstance(expr, A.AnonymousFunction):
        out.append(expr.body)
    elif isinstance(expr, A.Call):
        out.extend(findanonfuncbodies(expr.func))
        for arg in expr.args:
            out.extend(findanonfuncbodies(arg))
    elif isinstance(expr, A.Invoke):
        out.extend(findanonfuncbodies(expr.source))
        for arg in expr.args:
            out.extend(findanonfuncbodies(arg))
    elif isinstance(expr, A.Index):
        out.extend(findanonfuncbodies(expr.value))
        out.extend(findanonfuncbodies(expr.idx))
    elif isinstance(expr, A.Table):
        for f in expr.fields:
            out.extend(findanonfuncbodies(f.value))
    elif isinstance(expr, A.BinaryOp):
        out.extend(findanonfuncbodies(expr.left))
        out.extend(findanonfuncbodies(expr.right))
    elif isinstance(expr, A.UnaryOp):
        out.extend(findanonfuncbodies(expr.operand))
    return out

def allblocks(root):
    stack = [root.body if isinstance(root, A.Chunk) else root]
    while stack:
        blk = stack.pop()
        if blk is None:
            continue
        yield blk
        for stmt in blk.body:
            for b in getchildblocks(stmt):
                stack.append(b)
            for b in getfunctionbodies(stmt):
                stack.append(b)

def collectnames(expr, out):
    if expr is None:
        return
    if isinstance(expr, A.Name):
        out.add(expr.id)
    elif isinstance(expr, A.Index):
        collectnames(expr.value, out)
        collectnames(expr.idx, out)
    elif isinstance(expr, A.Call):
        collectnames(expr.func, out)
        for arg in expr.args:
            collectnames(arg, out)
    elif isinstance(expr, A.Invoke):
        collectnames(expr.source, out)
        for arg in expr.args:
            collectnames(arg, out)
    elif isinstance(expr, A.BinaryOp):
        collectnames(expr.left, out)
        collectnames(expr.right, out)
    elif isinstance(expr, A.UnaryOp):
        collectnames(expr.operand, out)
    elif isinstance(expr, A.Table):
        for f in expr.fields:
            if f.between_brackets:
                collectnames(f.key, out)
            collectnames(f.value, out)
    elif isinstance(expr, A.AnonymousFunction):
        pass

def ispure(expr):
    if expr is None:
        return True
    if isinstance(expr, (A.Name, A.Number, A.String, A.TrueExpr,
                          A.FalseExpr, A.Nil, A.AnonymousFunction, A.Dots)):
        return True
    if isinstance(expr, A.Index):
        return ispure(expr.value) and ispure(expr.idx)
    if isinstance(expr, A.BinaryOp):
        return ispure(expr.left) and ispure(expr.right)
    if isinstance(expr, A.UnaryOp):
        return ispure(expr.operand)
    if isinstance(expr, A.Table):
        return all((not f.between_brackets or ispure(f.key)) and ispure(f.value) for f in expr.fields)
    return False

def exprcontainsname(expr, name):
    s = set()
    collectnames(expr, s)
    return name in s

def stmttargetsnames(stmt):
    names = set()
    if isinstance(stmt, (A.Assign, A.LocalAssign)):
        for t in stmt.targets:
            if isinstance(t, A.Name):
                names.add(t.id)
    elif isinstance(stmt, (A.Fornum,)):
        if isinstance(stmt.target, A.Name):
            names.add(stmt.target.id)
    elif isinstance(stmt, (A.Forin,)):
        for t in stmt.targets:
            if isinstance(t, A.Name):
                names.add(t.id)
    return names

def stmtispurestandalone(stmt):
    if isinstance(stmt, (A.Assign, A.LocalAssign)):
        return all(ispure(v) for v in stmt.values)
    if isinstance(stmt, (A.Call, A.Invoke)):
        return False
    return True

def issafeprefixexp(node):
    return isinstance(node, (A.Name, A.Index, A.Call, A.Invoke))

def stmtusesetters(stmt, name):
    setters = []

    def mk(cb, prefixrequired):
        cb.prefixrequired = prefixrequired
        return cb

    def scanexpr(expr, replacecb, prefixrequired=False):
        if expr is None:
            return
        if isinstance(expr, A.Name):
            if expr.id == name:
                setters.append(mk(replacecb, prefixrequired))
            return
        if isinstance(expr, A.Index):
            scanexpr(expr.value, lambda v, e=expr: setattr(e, 'value', v), True)
            scanexpr(expr.idx, lambda v, e=expr: setattr(e, 'idx', v), False)
            return
        if isinstance(expr, A.Call):
            scanexpr(expr.func, lambda v, e=expr: setattr(e, 'func', v), True)
            for i in range(len(expr.args)):
                scanexpr(expr.args[i], lambda v, e=expr, i=i: e.args.__setitem__(i, v), False)
            return
        if isinstance(expr, A.Invoke):
            scanexpr(expr.source, lambda v, e=expr: setattr(e, 'source', v), True)
            for i in range(len(expr.args)):
                scanexpr(expr.args[i], lambda v, e=expr, i=i: e.args.__setitem__(i, v), False)
            return
        if isinstance(expr, A.BinaryOp):
            scanexpr(expr.left, lambda v, e=expr: setattr(e, 'left', v), False)
            scanexpr(expr.right, lambda v, e=expr: setattr(e, 'right', v), False)
            return
        if isinstance(expr, A.UnaryOp):
            scanexpr(expr.operand, lambda v, e=expr: setattr(e, 'operand', v), False)
            return
        if isinstance(expr, A.Table):
            for f in expr.fields:
                if f.between_brackets:
                    scanexpr(f.key, lambda v, ff=f: setattr(ff, 'key', v), False)
                scanexpr(f.value, lambda v, ff=f: setattr(ff, 'value', v), False)
            return

    if isinstance(stmt, (A.Assign, A.LocalAssign)):
        for i in range(len(stmt.values)):
            scanexpr(stmt.values[i], lambda v, s=stmt, i=i: s.values.__setitem__(i, v), False)
        for t in stmt.targets:
            if isinstance(t, A.Index):
                scanexpr(t.value, lambda v, e=t: setattr(e, 'value', v), True)
                if t.idx is not None and not isinstance(t.idx, A.Name):
                    scanexpr(t.idx, lambda v, e=t: setattr(e, 'idx', v), False)
    elif isinstance(stmt, A.Invoke):
        scanexpr(stmt.source, lambda v, e=stmt: setattr(e, 'source', v), True)
        for i in range(len(stmt.args)):
            scanexpr(stmt.args[i], lambda v, e=stmt, i=i: e.args.__setitem__(i, v), False)
    elif isinstance(stmt, A.Call):
        scanexpr(stmt.func, lambda v, e=stmt: setattr(e, 'func', v), True)
        for i in range(len(stmt.args)):
            scanexpr(stmt.args[i], lambda v, e=stmt, i=i: e.args.__setitem__(i, v), False)
    elif isinstance(stmt, A.If):
        scanexpr(stmt.test, lambda v, s=stmt: setattr(s, 'test', v), False)
    elif isinstance(stmt, A.While):
        scanexpr(stmt.test, lambda v, s=stmt: setattr(s, 'test', v), False)
    elif isinstance(stmt, A.Repeat):
        scanexpr(stmt.test, lambda v, s=stmt: setattr(s, 'test', v), False)
    elif isinstance(stmt, A.Return):
        for i in range(len(stmt.values)):
            scanexpr(stmt.values[i], lambda v, s=stmt, i=i: s.values.__setitem__(i, v), False)
    elif isinstance(stmt, A.Fornum):
        scanexpr(stmt.start, lambda v, s=stmt: setattr(s, 'start', v), False)
        scanexpr(stmt.stop, lambda v, s=stmt: setattr(s, 'stop', v), False)
        if stmt.step is not None:
            scanexpr(stmt.step, lambda v, s=stmt: setattr(s, 'step', v), False)
    elif isinstance(stmt, A.Forin):
        for i in range(len(stmt.iter)):
            scanexpr(stmt.iter[i], lambda v, s=stmt, i=i: s.iter.__setitem__(i, v), False)

    return setters

def countdeepuses(stmt, name):
    count = [0]

    def walkexpr(node):
        if node is None:
            return
        if isinstance(node, A.Name):
            if node.id == name:
                count[0] += 1
        elif isinstance(node, list):
            for x in node:
                walkexpr(x)
        elif isinstance(node, A.Index):
            walkexpr(node.value)
            walkexpr(node.idx)
        elif isinstance(node, A.Call):
            walkexpr(node.func)
            walkexpr(node.args)
        elif isinstance(node, A.Invoke):
            walkexpr(node.source)
            walkexpr(node.args)
        elif isinstance(node, A.BinaryOp):
            walkexpr(node.left)
            walkexpr(node.right)
        elif isinstance(node, A.UnaryOp):
            walkexpr(node.operand)
        elif isinstance(node, A.Table):
            for f in node.fields:
                if f.between_brackets:
                    walkexpr(f.key)
                walkexpr(f.value)
        elif isinstance(node, (A.AnonymousFunction, A.Function, A.LocalFunction)):
            if not isshadowedinnestedfn(node, name):
                walkblock(node.body)

    def walktarget(t):
        if isinstance(t, A.Index):
            walkexpr(t.value)
            walkexpr(t.idx)

    def walkstmt(stmt):
        if isinstance(stmt, (A.Assign, A.LocalAssign)):
            for v in stmt.values:
                walkexpr(v)
            for t in stmt.targets:
                walktarget(t)
        elif isinstance(stmt, A.Invoke):
            walkexpr(stmt.source)
            walkexpr(stmt.args)
        elif isinstance(stmt, A.Call):
            walkexpr(stmt.func)
            walkexpr(stmt.args)
        elif isinstance(stmt, A.If):
            walkexpr(stmt.test)
            walkblock(stmt.body)
            n = stmt.orelse
            while isinstance(n, A.ElseIf):
                walkexpr(n.test)
                walkblock(n.body)
                n = n.orelse
            if isblock(n):
                walkblock(n)
        elif isinstance(stmt, (A.While, A.Repeat)):
            walkexpr(stmt.test)
            walkblock(stmt.body)
        elif isinstance(stmt, A.Fornum):
            walkexpr(stmt.start)
            walkexpr(stmt.stop)
            walkexpr(stmt.step)
            walkblock(stmt.body)
        elif isinstance(stmt, A.Forin):
            walkexpr(stmt.iter)
            walkblock(stmt.body)
        elif isinstance(stmt, A.Return):
            walkexpr(stmt.values)
        elif isinstance(stmt, A.Do):
            walkblock(stmt.body)

    def walkblock(block):
        if block is None:
            return
        for st in block.body:
            walkstmt(st)

    walkstmt(stmt)
    return count[0]

def stmtreassignsnamedeep(stmt, name):
    found = [False]

    def walk(node):
        if found[0] or node is None:
            return
        if isinstance(node, list):
            for x in node:
                walk(x)
        elif isinstance(node, A.Block):
            for st in node.body:
                walk(st)
        elif isinstance(node, (A.Assign, A.LocalAssign)):
            for t in node.targets:
                if isinstance(t, A.Name) and t.id == name:
                    found[0] = True
        elif isinstance(node, (A.AnonymousFunction, A.Function, A.LocalFunction)):
            if not isshadowedinnestedfn(node, name):
                walk(node.body)
        elif isinstance(node, A.If):
            walk(node.body)
            n = node.orelse
            while isinstance(n, A.ElseIf):
                walk(n.body)
                n = n.orelse
            if isblock(n):
                walk(n)
        elif isinstance(node, (A.While, A.Repeat)):
            walk(node.body)
        elif isinstance(node, A.Fornum):
            if isinstance(node.target, A.Name) and node.target.id == name:
                found[0] = True
            walk(node.body)
        elif isinstance(node, A.Forin):
            for t in node.targets:
                if isinstance(t, A.Name) and t.id == name:
                    found[0] = True
            walk(node.body)

    walk(stmt)
    return found[0]

def findsingleuseandcheck(blockstmts, startidx, name, rhsispure, rhsfreevars, rhs=None):
    total = 0
    useidx = None
    for idx in range(startidx, len(blockstmts)):
        stmt = blockstmts[idx]
        deepn = countdeepuses(stmt, name)
        samelevelsetters = stmtusesetters(stmt, name)
        if deepn:
            total += deepn
            if useidx is None:
                useidx = idx
                if not samelevelsetters:
                    return False
                if (len(samelevelsetters) == 1 and samelevelsetters[0].prefixrequired
                        and rhs is not None and not issafeprefixexp(rhs)):
                    return False
            if total > 1:
                return False
        if stmtreassignsnamedeep(stmt, name):
            break

    if total != 1:
        return False
    for j in range(startidx, useidx):
        tnames = stmttargetsnames(blockstmts[j])
        if tnames & rhsfreevars:
            return False
        if not rhsispure and not stmtispurestandalone(blockstmts[j]):
            return False
    return True

def copypropagationpass(block):
    changed = False
    stmts = block.body
    i = 0
    while i < len(stmts):
        stmt = stmts[i]
        if (isinstance(stmt, (A.Assign, A.LocalAssign))
                and len(stmt.targets) == 1 and len(stmt.values) == 1
                and isinstance(stmt.targets[0], A.Name)):
            name = stmt.targets[0].id
            rhs = stmt.values[0]
            if isinstance(rhs, A.AnonymousFunction):
                pure = True
            else:
                pure = ispure(rhs)
            freevars = set()
            collectnames(rhs, freevars)
            freevars.discard(name)
            ok = findsingleuseandcheck(stmts, i + 1, name, pure, freevars, rhs)
            if ok:
                applysinglesubstitution(stmts, i + 1, name, rhs)
                del stmts[i]
                changed = True
                continue
        i += 1
    return changed

def applysinglesubstitution(blockstmts, startidx, name, rhstemplate):
    for idx in range(startidx, len(blockstmts)):
        stmt = blockstmts[idx]
        setters = stmtusesetters(stmt, name)
        if setters:
            assert len(setters) == 1, "caller must have verified exactly one use"
            setters[0](copy.deepcopy(rhstemplate))
            return
        if name in stmttargetsnames(stmt):
            return

def astequal(a, b):
    if a is None or b is None:
        return a is b
    if isinstance(a, list) or isinstance(b, list):
        if not (isinstance(a, list) and isinstance(b, list)):
            return False
        if len(a) != len(b):
            return False
        return all(astequal(x, y) for x, y in zip(a, b))
    if isinstance(a, A.Node) or isinstance(b, A.Node):
        if type(a) is not type(b):
            return False
        skip = {'_first_token', '_last_token', 'comments', 'wrapped', '_name'}
        akeys = {k for k in vars(a) if k not in skip}
        bkeys = {k for k in vars(b) if k not in skip}
        if akeys != bkeys:
            return False
        return all(astequal(getattr(a, k), getattr(b, k)) for k in akeys)
    return a == b

def iscommutativecomparepair(ta, tb):
    return (isinstance(ta, A.EqToOp) and isinstance(tb, A.EqToOp)) or \
           (isinstance(ta, A.NotEqToOp) and isinstance(tb, A.NotEqToOp))

def testsequivalent(ta, tb):
    if astequal(ta, tb):
        return True
    if iscommutativecomparepair(ta, tb):
        return astequal(ta.left, tb.right) and astequal(ta.right, tb.left)
    return False

def redundantifpass(block):
    stmts = block.body
    for i, stmt in enumerate(stmts):
        if not isinstance(stmt, A.If):
            continue
        if isinstance(stmt.orelse, A.ElseIf):
            continue
        if len(stmt.body.body) != 1:
            continue
        inner = stmt.body.body[0]
        if not isinstance(inner, A.If):
            continue
        if isinstance(inner.orelse, A.ElseIf):
            continue
        if not testsequivalent(stmt.test, inner.test):
            continue
        outerelse = stmt.orelse
        innerelse = inner.orelse
        if isblock(outerelse) != isblock(innerelse):
            continue
        if isblock(outerelse) and not astequal(outerelse.body, innerelse.body):
            continue
        if outerelse is None and innerelse is not None:
            continue
        newif = A.If(test=stmt.test, body=inner.body, orelse=outerelse)
        stmts[i] = newif
        return True
    return False

def tablefoldingpass(block):
    stmts = block.body
    for i, stmt in enumerate(stmts):
        if not (isinstance(stmt, (A.Assign, A.LocalAssign))
                and len(stmt.targets) == 1 and len(stmt.values) == 1
                and isinstance(stmt.targets[0], A.Name)
                and isinstance(stmt.values[0], A.Table)
                and len(stmt.values[0].fields) == 0):
            continue
        name = stmt.targets[0].id
        fieldstmtidxs = []
        fields = []
        j = i + 1
        blocked = False
        skippedany = False
        while j < len(stmts):
            s2 = stmts[j]
            if (isinstance(s2, A.Assign) and len(s2.targets) == 1 and len(s2.values) == 1
                    and isinstance(s2.targets[0], A.Index)
                    and isinstance(s2.targets[0].value, A.Name)
                    and s2.targets[0].value.id == name):
                tgt = s2.targets[0]
                keyexpr = tgt.idx
                between_brackets = (tgt.notation == A.IndexNotation.SQUARE)
                fieldval = s2.values[0]
                if not (ispure(fieldval) or isinstance(fieldval, A.AnonymousFunction)) and skippedany:
                    blocked = True
                    break
                fields.append(A.Field(key=copy.deepcopy(keyexpr), value=copy.deepcopy(fieldval), between_brackets=between_brackets))
                fieldstmtidxs.append(j)
                j += 1
                continue
            if countdeepuses(s2, name) or stmtreassignsnamedeep(s2, name):
                break
            skippedany = True
            j += 1
        if blocked or not fields:
            continue
        tablefreevars = set()
        for f in fields:
            if f.between_brackets:
                collectnames(f.key, tablefreevars)
            collectnames(f.value, tablefreevars)
        tablefreevars.discard(name)
        tablepure = all(
            (not f.between_brackets or ispure(f.key)) and
            (ispure(f.value) or isinstance(f.value, A.AnonymousFunction))
            for f in fields
        )
        if not tablepure and skippedany:
            continue
        newtable = A.Table(fields=fields)
        useok = findsingleuseandcheck(stmts, j, name, tablepure, tablefreevars, newtable)
        if not useok:
            continue
        applysinglesubstitution(stmts, j, name, newtable)
        for idx in sorted(fieldstmtidxs + [i], reverse=True):
            del stmts[idx]
        return True
    return False

def findcallwithtrailingargs(expr, targets):
    if expr is None:
        return None
    if isinstance(expr, (A.Call, A.Invoke)):
        args = expr.args
        n = len(targets)
        if len(args) >= n:
            suffix = args[-n:]
            if all(isinstance(a, A.Name) and a.id == t for a, t in zip(suffix, targets)):
                othernames = set()
                for a in args[:-n]:
                    collectnames(a, othernames)
                if isinstance(expr, A.Invoke):
                    collectnames(expr.source, othernames)
                if not any(t in othernames for t in targets):
                    return expr
        sub = expr.func if isinstance(expr, A.Call) else expr.source
        found = findcallwithtrailingargs(sub, targets)
        if found:
            return found
        for a in expr.args:
            found = findcallwithtrailingargs(a, targets)
            if found:
                return found
        return None
    if isinstance(expr, A.Index):
        return findcallwithtrailingargs(expr.value, targets) or findcallwithtrailingargs(expr.idx, targets)
    if isinstance(expr, A.BinaryOp):
        return findcallwithtrailingargs(expr.left, targets) or findcallwithtrailingargs(expr.right, targets)
    if isinstance(expr, A.UnaryOp):
        return findcallwithtrailingargs(expr.operand, targets)
    if isinstance(expr, A.Table):
        for f in expr.fields:
            found = findcallwithtrailingargs(f.value, targets)
            if found:
                return found
    return None

def multiretfoldingpass(block):
    stmts = block.body
    for i in range(len(stmts) - 1):
        s1 = stmts[i]
        if not (isinstance(s1, (A.Assign, A.LocalAssign)) and len(s1.targets) > 1
                and len(s1.values) == 1 and isinstance(s1.values[0], (A.Call, A.Invoke))
                and all(isinstance(t, A.Name) for t in s1.targets)):
            continue
        targets = [t.id for t in s1.targets]
        s2 = stmts[i + 1]
        candidates = []
        if isinstance(s2, (A.Assign, A.LocalAssign)):
            candidates.extend(s2.values)
        elif isinstance(s2, (A.Call, A.Invoke)):
            candidates.append(s2)
        elif isinstance(s2, A.Return):
            candidates.extend(s2.values)

        match = None
        for c in candidates:
            match = findcallwithtrailingargs(c, targets)
            if match:
                break
        if match is None:
            continue
        n = len(targets)
        match.args = match.args[:-n] + [s1.values[0]]
        del stmts[i]
        return True
    return False

def luaidentname(s):
    import re
    luakeywords = {"and", "break", "do", "else", "elseif", "end", "false",
        "for", "function", "if", "in", "local", "nil", "not", "or",
        "repeat", "return", "then", "true", "until", "while", "continue"}
    return bool(re.match(r'^[A-Za-z_][A-Za-z0-9_]*$', s)) and s not in luakeywords

def invokefoldingpass(node):
    changed = [False]

    def samesimplename(a, b):
        return isinstance(a, A.Name) and isinstance(b, A.Name) and a.id == b.id

    def methodnamefor(idxnode):
        if isinstance(idxnode, A.Name):
            return idxnode
        if isinstance(idxnode, A.String) and luaidentname(idxnode.raw):
            return A.Name(identifier=idxnode.raw)
        return None

    def visitexpr(expr):
        if expr is None:
            return expr
        if isinstance(expr, A.Call):
            expr.func = visitexpr(expr.func)
            expr.args = [visitexpr(a) for a in expr.args]
            if isinstance(expr.func, A.Index) and expr.args and samesimplename(expr.func.value, expr.args[0]):
                methodname = methodnamefor(expr.func.idx)
                if methodname is not None:
                    new = A.Invoke(source=expr.func.value, func=methodname, args=expr.args[1:])
                    changed[0] = True
                    return new
            return expr
        if isinstance(expr, A.Invoke):
            expr.source = visitexpr(expr.source)
            expr.args = [visitexpr(a) for a in expr.args]
            return expr
        if isinstance(expr, A.Index):
            expr.value = visitexpr(expr.value)
            if expr.notation == A.IndexNotation.SQUARE and isinstance(expr.idx, A.String) and luaidentname(expr.idx.raw):
                expr.idx = A.Name(identifier=expr.idx.raw)
                expr.notation = A.IndexNotation.DOT
            else:
                expr.idx = visitexpr(expr.idx)
            return expr
        if isinstance(expr, A.BinaryOp):
            expr.left = visitexpr(expr.left)
            expr.right = visitexpr(expr.right)
            return expr
        if isinstance(expr, A.UnaryOp):
            expr.operand = visitexpr(expr.operand)
            return expr
        if isinstance(expr, A.Table):
            for f in expr.fields:
                if f.between_brackets:
                    if isinstance(f.key, A.String) and luaidentname(f.key.raw):
                        f.key = A.Name(identifier=f.key.raw)
                        f.between_brackets = False
                    else:
                        f.key = visitexpr(f.key)
                f.value = visitexpr(f.value)
            return expr
        if isinstance(expr, A.AnonymousFunction):
            visitblock(expr.body)
            return expr
        return expr

    def visitstmt(stmt):
        if isinstance(stmt, (A.Assign, A.LocalAssign)):
            stmt.values = [visitexpr(v) for v in stmt.values]
            for t in stmt.targets:
                if isinstance(t, A.Index):
                    t.value = visitexpr(t.value)
                    if t.notation == A.IndexNotation.SQUARE and isinstance(t.idx, A.String) and luaidentname(t.idx.raw):
                        t.idx = A.Name(identifier=t.idx.raw)
                        t.notation = A.IndexNotation.DOT
                    else:
                        t.idx = visitexpr(t.idx)
        elif isinstance(stmt, (A.Call, A.Invoke)):
            new = visitexpr(stmt)
            return new
        elif isinstance(stmt, A.If):
            stmt.test = visitexpr(stmt.test)
            visitblock(stmt.body)
            node2 = stmt.orelse
            while isinstance(node2, A.ElseIf):
                node2.test = visitexpr(node2.test)
                visitblock(node2.body)
                node2 = node2.orelse
            if isblock(node2):
                visitblock(node2)
        elif isinstance(stmt, A.While):
            stmt.test = visitexpr(stmt.test)
            visitblock(stmt.body)
        elif isinstance(stmt, A.Repeat):
            stmt.test = visitexpr(stmt.test)
            visitblock(stmt.body)
        elif isinstance(stmt, A.Fornum):
            stmt.start = visitexpr(stmt.start)
            stmt.stop = visitexpr(stmt.stop)
            if stmt.step is not None:
                stmt.step = visitexpr(stmt.step)
            visitblock(stmt.body)
        elif isinstance(stmt, A.Forin):
            stmt.iter = [visitexpr(v) for v in stmt.iter]
            visitblock(stmt.body)
        elif isinstance(stmt, A.Return):
            stmt.values = [visitexpr(v) for v in stmt.values]
        elif isinstance(stmt, (A.Function, A.LocalFunction)):
            visitblock(stmt.body)
        return stmt

    def visitblock(blk):
        for i in range(len(blk.body)):
            blk.body[i] = visitstmt(blk.body[i])

    visitblock(node.body if isinstance(node, A.Chunk) else node)
    return changed[0]

def resugarglobals(block):
    for i, stmt in enumerate(block.body):
        if (isinstance(stmt, A.Assign) and len(stmt.targets) == 1
                and len(stmt.values) == 1 and isinstance(stmt.targets[0], A.Name)
                and isinstance(stmt.values[0], A.AnonymousFunction)):
            fn = stmt.values[0]
            block.body[i] = A.Function(name=stmt.targets[0], args=fn.args, body=fn.body)

def isshadowedinnestedfn(fnnode, name):
    for p in fnnode.args:
        if isinstance(p, A.Name) and p.id == name:
            return True
    for stmt in fnnode.body.body:
        if isinstance(stmt, A.LocalAssign):
            for t in stmt.targets:
                if isinstance(t, A.Name) and t.id == name:
                    return True
    return False

def collectallnamesdeep(node, out, shadowed=frozenset()):
    if node is None:
        return
    if isinstance(node, A.Name):
        if node.id not in shadowed:
            out.add(node.id)
    elif isinstance(node, list):
        for x in node:
            collectallnamesdeep(x, out, shadowed)
    elif isinstance(node, A.Block):
        for s in node.body:
            collectallnamesdeep(s, out, shadowed)
    elif isinstance(node, (A.Assign, A.LocalAssign)):
        for t in node.targets:
            collectallnamesdeep(t, out, shadowed)
        for v in node.values:
            collectallnamesdeep(v, out, shadowed)
    elif isinstance(node, A.Index):
        collectallnamesdeep(node.value, out, shadowed)
        collectallnamesdeep(node.idx, out, shadowed)
    elif isinstance(node, (A.Call,)):
        collectallnamesdeep(node.func, out, shadowed)
        collectallnamesdeep(node.args, out, shadowed)
    elif isinstance(node, A.Invoke):
        collectallnamesdeep(node.source, out, shadowed)
        collectallnamesdeep(node.args, out, shadowed)
    elif isinstance(node, A.BinaryOp):
        collectallnamesdeep(node.left, out, shadowed)
        collectallnamesdeep(node.right, out, shadowed)
    elif isinstance(node, A.UnaryOp):
        collectallnamesdeep(node.operand, out, shadowed)
    elif isinstance(node, A.Table):
        for f in node.fields:
            if f.between_brackets:
                collectallnamesdeep(f.key, out, shadowed)
            collectallnamesdeep(f.value, out, shadowed)
    elif isinstance(node, (A.AnonymousFunction, A.Function, A.LocalFunction)):
        innershadowed = set(shadowed)
        for p in node.args:
            if isinstance(p, A.Name):
                innershadowed.add(p.id)
        for s in node.body.body:
            if isinstance(s, A.LocalAssign):
                for t in s.targets:
                    if isinstance(t, A.Name):
                        innershadowed.add(t.id)
        collectallnamesdeep(node.body, out, frozenset(innershadowed))
    elif isinstance(node, A.If):
        collectallnamesdeep(node.test, out, shadowed)
        collectallnamesdeep(node.body, out, shadowed)
        n = node.orelse
        while isinstance(n, A.ElseIf):
            collectallnamesdeep(n.test, out, shadowed)
            collectallnamesdeep(n.body, out, shadowed)
            n = n.orelse
        if isblock(n):
            collectallnamesdeep(n, out, shadowed)
    elif isinstance(node, (A.While, A.Repeat)):
        collectallnamesdeep(node.test, out, shadowed)
        collectallnamesdeep(node.body, out, shadowed)
    elif isinstance(node, A.Fornum):
        collectallnamesdeep(node.target, out, shadowed)
        collectallnamesdeep(node.start, out, shadowed)
        collectallnamesdeep(node.stop, out, shadowed)
        collectallnamesdeep(node.step, out, shadowed)
        collectallnamesdeep(node.body, out, shadowed)
    elif isinstance(node, A.Forin):
        collectallnamesdeep(node.targets, out, shadowed)
        collectallnamesdeep(node.iter, out, shadowed)
        collectallnamesdeep(node.body, out, shadowed)
    elif isinstance(node, A.Return):
        collectallnamesdeep(node.values, out, shadowed)

def consolidatelocals(block, declarednames):
    stmts = [
        s for s in block.body
        if not (isinstance(s, A.LocalAssign) and len(s.values) == 0
                and all(isinstance(t, A.Name) and t.id in declarednames for t in s.targets))
    ]

    safefirstwriteidx = {}
    unsafe = set()
    for name in declarednames:
        firstidx = None
        issafe = False
        for idx, s in enumerate(stmts):
            touched = set()
            collectallnamesdeep(s, touched)
            if name not in touched:
                continue
            firstidx = idx
            issafe = (
                isinstance(s, A.Assign) and len(s.targets) == 1
                and isinstance(s.targets[0], A.Name) and s.targets[0].id == name
            )
            break
        if firstidx is None:
            continue
        if issafe:
            safefirstwriteidx[name] = firstidx
        else:
            unsafe.add(name)

    for name, idx in safefirstwriteidx.items():
        s = stmts[idx]
        stmts[idx] = A.LocalAssign(targets=s.targets, values=s.values)

    if unsafe:
        decl = A.LocalAssign(targets=[A.Name(n) for n in sorted(unsafe)], values=[])
        stmts = [decl] + stmts

    block.body = stmts

def getdeclarednames(block):
    names = set()
    for stmt in block.body:
        if isinstance(stmt, A.LocalAssign) and len(stmt.values) == 0:
            for t in stmt.targets:
                if isinstance(t, A.Name):
                    names.add(t.id)
    return names

def optimizeblocklocally(block):
    changed = True
    while changed:
        changed = False
        if copypropagationpass(block):
            changed = True
        if tablefoldingpass(block):
            changed = True

def normalizefunctionsugar(root):
    waslocalfunction = set()

    def visitblock(blk):
        for i in range(len(blk.body)):
            stmt = blk.body[i]
            if isinstance(stmt, A.LocalFunction):
                fn = A.AnonymousFunction(args=stmt.args, body=stmt.body)
                waslocalfunction.add(id(fn))
                blk.body[i] = A.LocalAssign(targets=[stmt.name], values=[fn])
            elif isinstance(stmt, A.Function) and isinstance(stmt.name, A.Name):
                fn = A.AnonymousFunction(args=stmt.args, body=stmt.body)
                blk.body[i] = A.Assign(targets=[stmt.name], values=[fn])
        for stmt in blk.body:
            for b in getchildblocks(stmt):
                visitblock(b)
            if isinstance(stmt, (A.Assign, A.LocalAssign)):
                for v in stmt.values:
                    for b in findanonfuncbodies(v):
                        visitblock(b)

    visitblock(root.body if isinstance(root, A.Chunk) else root)
    return waslocalfunction

def run(pathin, pathout):
    starttime = time.time()
    src = open(pathin, encoding='utf-8').read()
    tree = ast.parse(src)

    normalizefunctionsugar(tree)

    for lap in range(40):
        anychanged = False
        for blk in list(allblocks(tree)):
            if copypropagationpass(blk):
                anychanged = True
            if tablefoldingpass(blk):
                anychanged = True
            if multiretfoldingpass(blk):
                anychanged = True
            while redundantifpass(blk):
                anychanged = True
        if invokefoldingpass(tree):
            anychanged = True
        if not anychanged:
            break

    for blk in list(allblocks(tree)):
        declared = getdeclarednames(blk)
        if declared:
            consolidatelocals(blk, declared)

    for blk in list(allblocks(tree)):
        resugarglobals(blk)

    out = ast.to_lua_source(tree)
    elapsedms = round((time.time() - starttime) * 1000)
    header = "-- [[ deobfuscated by axom - moonsec deobfuscator | our YouTube channel : https://youtube.com/@axos0022 | our discord server : https://discord.gg/Sps39CydcZ - finished in " + str(elapsedms) + " ms ]]"
    open(pathout, 'w', encoding='utf-8').write(header + "\n" + out)

if __name__ == '__main__':
    run(sys.argv[1], sys.argv[2])
    print('wrote', sys.argv[2])

