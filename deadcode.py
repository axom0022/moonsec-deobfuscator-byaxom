import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LUAU_AST = os.path.abspath(os.path.join(HERE, "..", "tools", "luau-ast"))

sys.path.insert(0, HERE)
import luasubset as LS
import devirtv2jinterp as J


class DeadCodeError(Exception):
    pass


def _parse(text_bytes, workdir=None):
    import tempfile
    fd, path = tempfile.mkstemp(suffix=".lua", prefix="dce_")
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(text_bytes)
        r = subprocess.run([LUAU_AST, path], capture_output=True, timeout=120)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise DeadCodeError("luau-ast failed: %s" % r.stderr[:200])
    return json.loads(r.stdout.decode("utf-8", errors="surrogateescape"))


def _line_starts(data):
    starts = [0]
    for i, b in enumerate(data):
        if b == 10:
            starts.append(i + 1)
    return starts


def _offset(starts, pos):
    line, col = pos
    return starts[line] + col


def _span(starts, loc):
    a, b = loc.split(" - ")
    la, ca = (int(x) for x in a.split(","))
    lb, cb = (int(x) for x in b.split(","))
    return _offset(starts, (la, ca)), _offset(starts, (lb, cb))


def _lkey(local):
    return (local["name"], local["location"])


_KEYWORD = {
    "AstStatLocal": ("local",),
    "AstStatLocalFunction": ("local",),
    "AstStatIf": ("if",),
    "AstStatWhile": ("while",),
    "AstStatReturn": ("return",),
    "AstStatBreak": ("break",),
    "AstStatBlock": ("do",),
}


class _Analysis:
    def __init__(self):
        self.uses = {}

    def walk(self, node):
        if isinstance(node, dict):
            t = node.get("type")
            if t == "AstExprLocal" or t == "AstStatLocalFunction":
                key = _lkey(node["local"] if t == "AstExprLocal" else node["name"])
                self.uses[key] = self.uses.get(key, 0) + (1 if t == "AstExprLocal" else 0)
            if t == "AstStatAssign":
                for v in node.get("vars", []):
                    if v.get("type") == "AstExprLocal":
                        k = _lkey(v["local"])
                        self.uses[k] = self.uses.get(k, 0) + 1
            if t == "AstStatCompoundAssign":
                v = node.get("var", {})
                if v.get("type") == "AstExprLocal":
                    k = _lkey(v["local"])
                    self.uses[k] = self.uses.get(k, 0) + 1
            for v in node.values():
                self.walk(v)
        elif isinstance(node, list):
            for v in node:
                self.walk(v)


def _const(e):
    t = e["type"]
    if t == "AstExprConstantNumber":
        return True, float(e["value"])
    if t == "AstExprConstantString":
        return True, e["value"].encode("utf-8", "surrogateescape").decode("latin-1")
    if t == "AstExprConstantBool":
        return True, bool(e["value"])
    if t == "AstExprConstantNil":
        return True, None
    if t == "AstExprGroup":
        return _const(e["expr"])
    if t == "AstExprUnary":
        ok, v = _const(e["expr"])
        if not ok:
            return False, None
        if e["op"] == "Not":
            return True, not LS.truthy(v)
        if e["op"] == "Minus" and LS.tonum(v) is not None:
            return True, -LS.tonum(v)
        return False, None
    if t == "AstExprBinary":
        op = e["op"]
        ok1, a = _const(e["left"])
        ok2, b = _const(e["right"])
        if not (ok1 and ok2):
            return False, None
        if op == "And":
            return True, (b if LS.truthy(a) else a)
        if op == "Or":
            return True, (a if LS.truthy(a) else b)
        if op in ("CompareEq", "CompareNe"):
            r = LS.lua_eq(a, b)
            return True, (r if op == "CompareEq" else (not r))
        if op in ("CompareLt", "CompareLe", "CompareGt", "CompareGe"):
            numeric = LS.tonum(a) is not None and LS.tonum(b) is not None and \
                isinstance(a, float) and isinstance(b, float)
            stringy = isinstance(a, str) and isinstance(b, str)
            if not (numeric or stringy):
                return False, None
            if op == "CompareLt":
                return True, LS._lt(a, b)
            if op == "CompareLe":
                return True, LS._le(a, b)
            if op == "CompareGt":
                return True, LS._lt(b, a)
            return True, LS._le(b, a)
        if op in ("Add", "Sub", "Mul", "Div", "Mod", "Pow") and LS.tonum(a) is not None and LS.tonum(b) is not None:
            return _arith(op, LS.tonum(a), LS.tonum(b))
        return False, None
    return False, None


def _arith(op, x, y):
    if op == "Add":
        return True, x + y
    if op == "Sub":
        return True, x - y
    if op == "Mul":
        return True, x * y
    if op == "Div":
        return True, LS._div(x, y)
    if op == "Mod":
        return True, LS._mod(x, y)
    return True, LS._pow(x, y)


def _side_effect_free(e):
    t = e["type"]
    if t in ("AstExprConstantNumber", "AstExprConstantString", "AstExprConstantBool",
             "AstExprConstantNil", "AstExprFunction", "AstExprLocal", "AstExprGlobal",
             "AstExprVarargs"):
        return True
    if t == "AstExprGroup":
        return _side_effect_free(e["expr"])
    if t == "AstExprTable":
        return all(_side_effect_free(it["value"]) and (it.get("key") is None or _side_effect_free(it["key"]))
                   for it in e.get("items", []))
    if t == "AstExprUnary":
        return e["op"] == "Not" and _side_effect_free(e["expr"])
    if t == "AstExprBinary":
        if e["op"] in ("And", "Or"):
            return _side_effect_free(e["left"]) and _side_effect_free(e["right"])
        ok, _ = _const(e)
        return ok
    return False


class _Edits:
    def __init__(self):
        self.items = []

    def add(self, start, end, repl, reason):
        self.items.append((start, end, repl, reason))


class DeadCode:
    def __init__(self, data, workdir):
        self.data = data
        self.text = data.decode("latin-1")
        self.workdir = workdir
        self.starts = _line_starts(data)
        self.log = []

    def check_span(self, node, start, end):
        kws = _KEYWORD.get(node["type"])
        if kws is None:
            return
        head = self.text[start:start + 12]
        if not any(head.startswith(k) for k in kws):
            raise DeadCodeError("span check failed for %s at %d: %r" % (node["type"], start, head))

    def plan(self, ast):
        ana = _Analysis()
        ana.walk(ast)
        edits = _Edits()
        self._visit_block(ast["root"]["body"], ana, edits, top=True)
        return edits

    def _span_of(self, node):
        return _span(self.starts, node["location"])

    def _visit_block(self, stmts, ana, edits, top=False):
        for i, st in enumerate(stmts):
            if st["type"] in ("AstStatReturn", "AstStatBreak") and i + 1 < len(stmts):
                s, _ = self._span_of(stmts[i + 1])
                _, e = self._span_of(stmts[-1])
                edits.add(s, e, "", "dead after %s" % st["type"])
                break
        for st in stmts:
            self._visit_stmt(st, ana, edits)

    def _visit_stmt(self, st, ana, edits):
        t = st["type"]
        s, e = self._span_of(st)
        if t == "AstStatLocal":
            if all(ana.uses.get(_lkey(v), 0) == 0 for v in st["vars"]) and \
                    all(_side_effect_free(v) for v in st.get("values", [])):
                self.check_span(st, s, e)
                edits.add(s, e, "", "unused local")
                return
        elif t == "AstStatLocalFunction":
            if ana.uses.get(_lkey(st["name"]), 0) == 0:
                self.check_span(st, s, e)
                edits.add(s, e, "", "unused local function")
                return
        elif t == "AstStatIf":
            ok, v = _const(st["condition"])
            if ok:
                self.check_span(st, s, e)
                if LS.truthy(v):
                    body = st["thenbody"]
                    edits.add(s, e, "do " + self.text[self._body_inner(body)] + " end", "constant true if")
                    return
                eb = st.get("elsebody")
                if eb is None:
                    edits.add(s, e, "", "constant false if")
                    return
                if eb["type"] == "AstStatIf":
                    es, ee = self._span_of(eb)
                    part = self.text[es:ee]
                    if not part.startswith("elseif"):
                        raise DeadCodeError("elseif span does not start with 'elseif'")
                    edits.add(s, e, "if" + part[len("elseif"):], "constant false if (elseif)")
                    return
                edits.add(s, e, "do " + self.text[self._body_inner(eb)] + " end", "constant false if (else)")
                return
            self._visit_block(st["thenbody"]["body"], ana, edits)
            if st.get("elsebody") is not None:
                eb = st["elsebody"]
                if eb["type"] == "AstStatIf":
                    self._visit_stmt(eb, ana, edits)
                else:
                    self._visit_block(eb["body"], ana, edits)
        elif t == "AstStatWhile":
            ok, v = _const(st["condition"])
            if ok and not LS.truthy(v):
                self.check_span(st, s, e)
                edits.add(s, e, "", "constant false while")
                return
            self._visit_block(st["body"]["body"], ana, edits)
        elif t == "AstStatFor":
            self._visit_block(st["body"]["body"], ana, edits)
        elif t == "AstStatBlock":
            if not st["body"]:
                self.check_span(st, s, e)
                edits.add(s, e, "", "empty do block")
                return
            self._visit_block(st["body"], ana, edits)
        elif t == "AstStatLocalFunction":
            self._visit_expr_functions(st["func"], ana, edits)
        elif t == "AstStatFunction":
            self._visit_expr_functions(st["func"], ana, edits)
        elif t == "Comment":
            return
        elif t not in ("AstStatLocal", "AstStatAssign", "AstStatReturn", "AstStatExpr",
                       "AstStatBreak", "AstStatCompoundAssign"):
            self._visit_generic(st, ana, edits)
        elif t == "AstStatLocal" or t == "AstStatAssign" or t == "AstStatReturn" or t == "AstStatExpr":
            for k in ("values", "list", "expr"):
                v = st.get(k)
                if isinstance(v, list):
                    for x in v:
                        self._visit_expr_functions(x, ana, edits)
                elif isinstance(v, dict):
                    self._visit_expr_functions(v, ana, edits)

    def _visit_generic(self, node, ana, edits):
        for v in node.values():
            if isinstance(v, dict):
                if str(v.get("type", "")).startswith("AstStat") and v.get("type") != "AstStatBlock":
                    self._visit_stmt(v, ana, edits)
                elif v.get("type") == "AstStatBlock":
                    self._visit_block(v["body"], ana, edits)
                else:
                    self._visit_generic(v, ana, edits)
            elif isinstance(v, list):
                if v and isinstance(v[0], dict) and str(v[0].get("type", "")).startswith("AstStat"):
                    self._visit_block(v, ana, edits)
                else:
                    for x in v:
                        if isinstance(x, dict):
                            self._visit_generic(x, ana, edits)

    def _visit_expr_functions(self, node, ana, edits):
        if isinstance(node, dict):
            if node.get("type") == "AstExprFunction":
                self._visit_block(node["body"]["body"], ana, edits)
                return
            for v in node.values():
                self._visit_expr_functions(v, ana, edits)
        elif isinstance(node, list):
            for v in node:
                self._visit_expr_functions(v, ana, edits)

    def _body_inner(self, block):
        s, e = self._span_of(block)
        body = block["body"]
        if body:
            bs, _ = self._span_of(body[0])
            _, be = self._span_of(body[-1])
            return slice(bs, be)
        return slice(s, s)

    def apply(self, edits):
        items = sorted(edits.items, key=lambda x: (x[0], -x[1]))
        chosen = []
        last_end = -1
        for s, e, repl, reason in items:
            if s < last_end:
                continue
            chosen.append((s, e, repl, reason))
            last_end = e
        out = []
        pos = 0
        for s, e, repl, reason in chosen:
            out.append(self.data[pos:s])
            out.append(repl.encode("latin-1"))
            pos = e
            self.log.append(reason)
        out.append(self.data[pos:])
        return b"".join(out), len(chosen)


def eliminate(data, workdir="/tmp", max_rounds=50):
    cur = data
    log = []
    for _ in range(max_rounds):
        ast = _parse(cur, workdir)
        dc = DeadCode(cur, workdir)
        try:
            edits = dc.plan(ast)
        except DeadCodeError as ex:
            log.append("stopped: %s" % ex)
            return cur, log
        if not edits.items:
            break
        new, n = dc.apply(edits)
        log.extend(dc.log)
        if n == 0 or new == cur:
            break
        try:
            _parse(new, workdir)
        except DeadCodeError as ex:
            log.append("stopped: result did not parse (%s)" % ex)
            return cur, log
        cur = new
    return cur, log


if __name__ == "__main__":
    src_path, out_path = sys.argv[1], sys.argv[2]
    data = open(src_path, "rb").read()
    new, log = eliminate(data, workdir=os.path.dirname(os.path.abspath(out_path)) or "/tmp")
    with open(out_path, "wb") as f:
        f.write(new)
    from collections import Counter
    print("bytes %d -> %d" % (len(data), len(new)))
    for reason, n in Counter(log).most_common():
        print("  %4d  %s" % (n, reason) if isinstance(reason, str) else "")
