import luaparser.ast as last
import luaparser.astnodes as A

FIELD_ENV = {"le": 1, "l": 2, "t": 3, "r": 4}


class Opaque(Exception):
    pass


_BIN = {
    "GreaterOrEqThanOp": lambda a, b: a >= b,
    "LessThanOp":        lambda a, b: a < b,
    "GreaterThanOp":     lambda a, b: a > b,
    "LessOrEqThanOp":    lambda a, b: a <= b,
    "NotEqToOp":         lambda a, b: a != b,
    "EqToOp":            lambda a, b: a == b,
    "AddOp":             lambda a, b: a + b,
    "SubOp":             lambda a, b: a - b,
    "MultOp":            lambda a, b: a * b,
    "FloatDivOp":        lambda a, b: a / b if b else None,
}


def foldexpr(node, env):
    if node is None:
        raise Opaque("none")
    n = type(node).__name__

    if n == "Number":
        return node.n
    if n == "Name":
        key = node.id
        if key in env:
            return env[key]
        raise Opaque("unknown name %s" % key)
    if n in ("True", "TrueExpr"):
        return True
    if n in ("False", "FalseExpr"):
        return False
    if n == "Nil":
        return None
    if n == "String":
        return node.s

    if n in _BIN:
        a = foldexpr(node.left, env)
        b = foldexpr(node.right, env)
        if a is None or b is None:
            raise Opaque("nil operand")
        if isinstance(a, bool) or isinstance(b, bool):
            raise Opaque("bool operand")
        return _BIN[n](a, b)

    if n == "UMinusOp":
        v = foldexpr(node.operand, env)
        if v is None:
            raise Opaque("neg of nil")
        return -v

    if n == "ExpoOp":
        a = foldexpr(node.left, env)
        b = foldexpr(node.right, env)
        return a ** b

    if n == "ULengthOP" or n == "LenOp":
        try:
            operand = node.operand
        except AttributeError:
            operand = getattr(node, "exp", None)
        if type(operand).__name__ == "Table":
            return len(list(operand.fields))
        raise Opaque("len of non-literal")

    if n in ("UCondNotOp", "NotOp", "ULNotOp"):
        v = foldexpr(node.operand, env)
        return not v

    if n == "OrLoOp":
        a = foldexpr(node.left, env)
        if a:
            return a
        return foldexpr(node.right, env)
    if n == "AndLoOp":
        a = foldexpr(node.left, env)
        if not a:
            return a
        return foldexpr(node.right, env)

    raise Opaque("expr %s" % n)


def isconst(node, env):
    try:
        return foldexpr(node, env) is not None or True
    except Opaque:
        return False


def const(node, env):
    try:
        return foldexpr(node, env)
    except (Opaque, TypeError, ZeroDivisionError, AttributeError):
        return None


CTRL_RE = None


def truncate_after_control(stmts):
    import re
    out = []
    for i, st in enumerate(stmts):
        out.append(st)
        flat = st
        if re.search(r"\bn\s*=\s*e\[t\]", flat) or re.search(r"\breturn\b", flat):
            break
        if re.search(r"e\s*=\s*f\[n\]", flat):
            break
    return out


def render(node):
    try:
        return last.to_lua_source(node)
    except Exception:
        return "<%s>" % type(node).__name__


def fold_block(block, env, out):
    stmts = list(block.body) if hasattr(block, "body") else list(block)
    for st in stmts:
        r = fold_stmt(st, env, out)
        if r is False:
            return False
    return True


def fold_stmt(st, env, out):
    n = type(st).__name__

    if n == "Break":
        return False

    if n == "Do":
        return fold_block(st.body, env, out)

    if n == "If":
        val = const(st.test, env)
        if val is None:
            out.append(render(st))
            return True
        branch = st.body if val else st.orelse
        if branch is None:
            return True
        return fold_block(branch, env, out)

    if n in ("Fornum", "Forin"):
        if n == "Fornum":
            try:
                startv = const(st.start, env)
            except AttributeError:
                startv = None
            target = render(st.target)
            if startv is None:
                out.append(render(st))
                return True
            inner = dict(env)
            inner[target] = startv
        else:
            inner = dict(env)
        fell = fold_block(st.body, inner, out)
        return fell

    if n == "While":
        val = const(st.test, env)
        if val is None:
            out.append(render(st))
            return True
        if not val:
            return True
        fell = fold_block(st.body, env, out)
        return fell

    if n == "Repeat":
        fell = fold_block(st.body, env, out)
        if not fell:
            return False
        val = const(st.test, env)
        if val is None:
            out.append(render(st))
            return True
        return True

    if n == "LocalAssign":
        names = [render(t) for t in st.targets]
        vals = []
        try:
            vals = st.expressions if hasattr(st, "expressions") else st.values
        except AttributeError:
            vals = []
        if len(names) == 1 and len(list(vals)) == 1:
            v = const(list(vals)[0], env)
            if v is not None or type(list(vals)[0]).__name__ in ("Number", "TrueExpr", "FalseExpr"):
                env[names[0]] = v
        out.append(render(st))
        return True

    if n == "Assign":
        targets = list(st.targets)
        values = list(st.expressions if hasattr(st, "expressions") else st.values)
        if len(targets) == 1 and len(values) == 1:
            tn = type(targets[0]).__name__
            if tn == "Name":
                v = const(values[0], env)
                if v is None:
                    env.pop(targets[0].id, None)
                else:
                    env[targets[0].id] = v
        out.append(render(st))
        return True

    out.append(render(st))
    return True


def find_dispatch(src):
    import re
    m = re.search(r"e\s*=\s*f\s*\[\s*n\s*\]\s*;\s*o\s*=\s*e\s*\[\s*le\s*\]\s*;", src)
    if not m:
        return None
    rest = src[m.end():]
    toks = [(mm.start(), mm.group()) for mm in
            re.finditer(r"\b(?:do|then|function|repeat|end|until|elseif|else)\b", rest)]
    depth = 0
    for pos, t in toks:
        if t in ("do", "then", "repeat", "function"):
            depth += 1
        elif t == "end":
            depth -= 1
            if depth == 0:
                return rest[:pos + 3]
        elif t == "until":
            depth -= 1
            if depth == 0:
                return rest[:pos + len("until")]
    return None


def dispatch_bounds(tree_src):
    import re
    return sorted({int(x, 0) for x in re.findall(r"o\s*(?:>=|<=|>|<|~=|==)\s*(0x[0-9a-fA-F]+|\d+)", tree_src)})


def analyze(src, opcodes=None, verbose=False):
    tree = find_dispatch(src)
    if tree is None:
        raise RuntimeError("dispatch tree not found")
    ast = last.parse("function __d()\nif true then\n" + tree + "\nend\nend")
    root = ast.body.body[0].body.body[0]

    if opcodes is None:
        lits = dispatch_bounds(tree)
        opcodes = range(0, (lits[-1] if lits else 90) + 2)

    table = {}
    for op in opcodes:
        env = dict(FIELD_ENV)
        env["o"] = op
        out = []
        try:
            fold_stmt(root, env, out)
        except RecursionError:
            out = ["<recursion>"]
        out = truncate_after_control(out)
        kept = [x for x in out if x.strip() and x.strip() not in ("end", ";")]
        if kept:
            table[op] = kept
    return table


if __name__ == "__main__":
    import sys
    src = open(sys.argv[1], encoding="utf-8", errors="replace").read()
    t = analyze(src)
    for op in sorted(t):
        print("op %-3d : %s" % (op, " ".join(s.replace("\n", " ") for s in t[op])))
