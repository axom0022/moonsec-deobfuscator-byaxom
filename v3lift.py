import math
import sys

import v3bootstrap
import v3proto


LOADK = {4, 9, 10, 12, 14, 24, 30, 31, 40, 42, 60}
GETTABLE = {2, 38}
SETTABLE = {3, 15, 25, 34, 45, 52, 59, 63, 67, 68}
SETTABLE_LIT = {35, 37}
JMP = {5, 54}
CALL_RES1_TOP = {6, 13}
CALL_RES1_B = {46, 51}
CALL_NORES = {41, 62}
CALL0 = {8, 27}
CALL1 = {39, 55}
TAILCALL0 = {20, 44}
CALL_MULTI = {17, 33}
RETURN = {21, 53}
TEST_TRUE = {50, 58}
TEST_FALSE = {23, 49}
TEST_NE = {11, 29}
NEWTABLE = {36, 47}
CLOSURE = {64, 26}
SETGLOBAL = {16, 22, 43}
SELF = {1, 18, 56, 65}
LOADBOOL = {0, 28, 32, 57}
NOP = {7, 19, 48, 66}
UNSUPPORTED = {61}


JUMP_OFFSET = 1


class LiftError(Exception):
    pass


def lua_string(s):
    out = ['"']
    for ch in s:
        o = ord(ch)
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif 32 <= o <= 126:
            out.append(ch)
        else:
            out.append("\\%d" % o)
    out.append('"')
    return "".join(out)


def lua_number(v):
    if v != v:
        return "(0/0)"
    if v == math.inf:
        return "(1/0)"
    if v == -math.inf:
        return "(-1/0)"
    if float(v).is_integer() and abs(v) < 2 ** 53:
        return str(int(v))
    return repr(float(v))


def lua_literal(v):
    if v is None:
        return "nil"
    if v is True:
        return "true"
    if v is False:
        return "false"
    if isinstance(v, str):
        return lua_string(v)
    if isinstance(v, (int, float)):
        return lua_number(float(v))
    raise LiftError("unsupported literal %r" % (v,))


class Emitter:
    def __init__(self, proto, name, children_names):
        self.p = proto
        self.name = name
        self.children = children_names
        self.errors = []

    def _flag(self, ins, which):
        return which in ins["refs"]

    def _rv(self, ins, which):
        v = ins["raw"][{"A": 0, "B": 1, "C": 2}[which]]
        if v is None:
            raise LiftError("operand %s not encoded (mode_b=%d)" % (which, ins["mode_b"]))
        return v

    def reg(self, ins, which):
        if self._flag(ins, which):
            raise LiftError("register operand %s is a constant" % which)
        return "R[%d]" % self._rv(ins, which)

    def rk(self, ins, which):
        if self._flag(ins, which):
            return lua_literal(ins[which])
        if ins["raw"][2 if which == "C" else 1] is None and which == "C":
            return "nil"
        return "R[%d]" % self._rv(ins, which)

    def kidx(self, ins, which):
        if self._flag(ins, which):
            return lua_literal(ins[which])
        return "K[%d]" % self._rv(ins, which)

    def lit(self, ins, which):
        if self._flag(ins, which):
            return lua_literal(ins[which])
        if ins["raw"][2] is None and which == "C":
            return "nil"
        return lua_number(float(self._rv(ins, which)))

    def raw(self, ins, which):
        return self._rv(ins, which)

    def target(self, ins, which):
        if self._flag(ins, which):
            raise LiftError("flagged jump target (no pc)")
        return self.raw(ins, which) + JUMP_OFFSET

    def jump_stmt(self, ins, which):
        try:
            return "pc = %d" % self.target(ins, which)
        except LiftError as e:
            return 'error("V3 lifter: %s at pc %d")' % (str(e), ins["pc"])

    def stmts(self, ins):
        op = ins["op"]
        pc = ins["pc"]
        nxt = "pc = %d" % (pc + 1)

        if op in LOADK:
            return ["R[%d] = %s" % (self.raw(ins, "A"), self.kidx(ins, "B"))], nxt
        if op in GETTABLE:
            return ["R[%d] = (%s)[%s]" % (self.raw(ins, "A"), self.rk(ins, "B"),
                                         self.rk(ins, "C"))], nxt
        if op in SETTABLE:
            return ["%s[%s] = %s" % (self.reg(ins, "A"), self.rk(ins, "B"),
                                      self.rk(ins, "C"))], nxt
        if op in SETTABLE_LIT:
            return ["%s[%s] = %s" % (self.reg(ins, "A"), self.rk(ins, "B"),
                                      self.lit(ins, "C"))], nxt
        if op in JMP and ins["mode_b"] == 1 and self._flag(ins, "B"):
            return ["R[%d] = %s" % (self.raw(ins, "A"), self.lit(ins, "B"))], nxt
        if op in JMP:
            return [], self.jump_stmt(ins, "B")
        if op in CALL_RES1_TOP:
            a = self.raw(ins, "A")
            return ["R[%d] = R[%d](table.unpack(R, %d, #R))" % (a, a, a + 1)], nxt
        if op in CALL_RES1_B:
            a = self.raw(ins, "A")
            b = self.raw(ins, "B")
            return ["R[%d] = R[%d](table.unpack(R, %d, %d))" % (a, a, a + 1, b)], nxt
        if op in CALL_NORES:
            a = self.raw(ins, "A")
            b = self.raw(ins, "B")
            return ["R[%d](table.unpack(R, %d, %d))" % (a, a + 1, b)], nxt
        if op in CALL0:
            return ["R[%d]()" % self.raw(ins, "A")], nxt
        if op in CALL1:
            a = self.raw(ins, "A")
            return ["R[%d](R[%d])" % (a, a + 1)], nxt
        if op in TAILCALL0:
            a = self.raw(ins, "A")
            return ["R[%d] = R[%d]()" % (a, a)], nxt
        if op in CALL_MULTI:
            a = self.raw(ins, "A")
            b = self.raw(ins, "B")
            return [
                "local _res = {R[%d](table.unpack(R, %d, %d))}" % (a, a + 1, b),
                "for _i = 1, #_res do R[%d + _i - 1] = _res[_i] end" % a,
            ], nxt
        if op in RETURN:
            return ["return"], None
        if op in TEST_TRUE:
            a = self.raw(ins, "A")
            return [], "if R[%d] then pc = %d else %s end" % (a, pc + 1, self.jump_stmt(ins, "B"))
        if op in TEST_FALSE:
            a = self.raw(ins, "A")
            return [], "if not R[%d] then pc = %d else %s end" % (a, pc + 1, self.jump_stmt(ins, "B"))
        if op in TEST_NE:
            a = self.raw(ins, "A")
            return [], "if R[%d] ~= %s then pc = %d else %s end" % (
                a, self.rk(ins, "C"), pc + 1, self.jump_stmt(ins, "B"))
        if op in NEWTABLE:
            return ["R[%d] = {}" % self.raw(ins, "A")], nxt
        if op in CLOSURE:
            idx = self.raw(ins, "B")
            if self._flag(ins, "B") or idx < 0 or idx >= len(self.children):
                raise LiftError("CLOSURE child index %s unresolved (flagged B or out of range)" % (idx,))
            return ["R[%d] = %s" % (self.raw(ins, "A"), self.children[idx])], nxt
        if op in SETGLOBAL:
            return ["G[%s] = R[%d]" % (self.kidx(ins, "B"), self.raw(ins, "A"))], nxt
        if op in SELF:
            a = self.raw(ins, "A")
            return [
                "local _o = %s" % self.rk(ins, "B"),
                "R[%d] = _o" % (a + 1),
                "R[%d] = _o[%s]" % (a, self.rk(ins, "C")),
            ], nxt
        if op in LOADBOOL:
            return ["R[%d] = %s" % (self.raw(ins, "A"), "true" if self.raw(ins, "B") != 0 else "false")], nxt
        if op in NOP:
            return [], nxt
        if op in UNSUPPORTED:
            raise LiftError("unsupported opcode %d" % op)
        raise LiftError("unknown opcode %d" % op)

    def emit(self):
        p = self.p
        lines = []
        lines.append("local function %s(...)" % self.name)
        lines.append("  local K = {%s}" % ", ".join(lua_literal(c) for c in p.consts))
        lines.append("  local R = {}")
        lines.append("  local VA = {...}")
        lines.append("  for i = 1, #VA do R[i - 1] = VA[i] end")
        lines.append("  local pc = 1")
        lines.append("  while true do")
        for i, ins in enumerate(p.instrs):
            kw = "if" if i == 0 else "elseif"
            lines.append("    %s pc == %d then" % (kw, ins["pc"]))
            try:
                body, update = self.stmts(ins)
            except LiftError as e:
                self.errors.append((ins["pc"], ins["op"], str(e)))
                body = ['error("V3 lifter: %s at pc %d")' % (str(e), ins["pc"])]
                update = None
            for s in body:
                lines.append("      " + s)
            if update is not None:
                lines.append("      " + update)
        if p.instrs:
            lines.append("    else")
            lines.append("      return")
            lines.append("    end")
        lines.append("  end")
        lines.append("end")
        return lines


def lift_proto(p, name, out_defs, all_errors):
    children = []
    for i, child in enumerate(p.protos):
        cname = "%s_%d" % (name, i + 1)
        lift_proto(child, cname, out_defs, all_errors)
        children.append(cname)
    em = Emitter(p, name, children)
    out_defs.append("\n".join(em.emit()))
    for pc, op, msg in em.errors:
        all_errors.append((name, pc, op, msg))


def lift(blob):
    root, consumed, numtag, layout = v3proto.parse_blob(blob)
    if consumed != len(blob):
        raise LiftError("blob not fully consumed (%d of %d)" % (consumed, len(blob)))
    defs = []
    errors = []
    lift_proto(root, "P0", defs, errors)
    out = []
    out.append("local G = getfenv()")
    out.append("")
    out.append("\n\n".join(defs))
    out.append("")
    out.append("return P0(...)")
    return "\n".join(out) + "\n", errors


def main(path, outpath, verbose=False):
    blob = v3bootstrap.static_blob(path).encode("latin-1")
    src, errors = lift(blob)
    import deadcode
    before = len(src)
    new_bytes, log = deadcode.eliminate(src.encode("utf-8"))
    src = new_bytes.decode("utf-8")
    open(outpath, "w", encoding="utf-8").write(src)
    print("dead code elimination: %d -> %d bytes" % (before, len(src)))
    print("wrote %s (%d bytes)" % (outpath, len(src)))
    by_kind = {}
    for name, pc, op, msg in errors:
        by_kind.setdefault(msg, 0)
        by_kind[msg] += 1
    print("instructions with no lifting: %d" % len(errors))
    for msg, n in sorted(by_kind.items(), key=lambda x: -x[1]):
        print("  %3d  %s" % (n, msg))
    if verbose:
        for name, pc, op, msg in errors:
            print("    %s pc=%d op=%d: %s" % (name, pc, op, msg))


if __name__ == "__main__":
    import threading
    sys.setrecursionlimit(1000000)
    threading.stack_size(512 * 1024 * 1024)
    box = {}

    def target():
        try:
            main(sys.argv[1], sys.argv[2], "-v" in sys.argv)
        except BaseException as e:
            box["err"] = e

    t = threading.Thread(target=target)
    t.start()
    t.join()
    if "err" in box:
        raise box["err"]
