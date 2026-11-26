import json
import sys

LOOP_FLAG = "Strength"


def lit(v):
    if isinstance(v, dict):
        if "proxy" in v:
            return v["proxy"]
        if "fn" in v:
            return v["fn"]
        if "table" in v:
            parts = []
            for k, x in v["table"]:
                parts.append("%s = %s" % (k, lit(x)))
            return "{ " + ", ".join(parts) + " }"
        return "nil"
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return str(v)
    if isinstance(v, str):
        return '"' + v.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'
    return "nil"


def build(evs):
    root, stack = [], []
    cur = root
    for e in evs:
        k = e["k"]
        if k == "pcall_begin":
            node = ("pcall", [], None, None)
            cur.append(node)
            stack.append(cur)
            cur = node[1]
        elif k == "pcall":
            if not stack:
                cur.append(("pcall_top", e["ok"], e["msg"], e.get("where")))
                continue
            cur = stack.pop()
            opener = cur[-1]
            cur[-1] = ("pcall", opener[1], e["ok"], e["msg"], e.get("where"))
        else:
            cur.append(("ev", e))
    return root


def call_line(e, pad):
    p = e["path"]
    args = e["args"]
    if p.endswith("SignalPromptProductPurchaseFinished"):
        return pad + "game.MarketplaceService:SignalPromptProductPurchaseFinished(%s)" % (
            ", ".join(lit(a) for a in args[1:]))
    if "." in p and args and isinstance(args[0], dict) and args[0].get("proxy") == p.rsplit(".", 1)[0]:
        obj, meth = p.rsplit(".", 1)
        return pad + "%s:%s(%s)" % (obj, meth, ", ".join(lit(a) for a in args[1:]))
    return pad + "%s(%s)" % (p, ", ".join(lit(a) for a in args))


def render(nodes, indent, fnmap=None):
    pad = " " * indent
    out = []
    for idx, n in enumerate(nodes):
        if n[0] == "pcall":
            _, kids, ok, msg, where = n
            if kids:
                out.append(pad + "pcall(function()")
                out.extend(render(kids, indent + 4, fnmap))
                out.append(pad + "end)")
        elif n[0] == "pcall_top":
            continue
        else:
            e = n[1]
            k = e["k"]
            if k == "call":
                out.append(call_line(e, pad))
            elif k == "wait":
                out.append(pad + "wait()")
            elif k == "print":
                out.append(pad + "print(%s)" % ", ".join(lit(a) for a in e["args"]))
            elif k == "global_read":
                if (e["name"] == LOOP_FLAG and e["value"] is True and idx + 1 < len(nodes)
                        and nodes[idx + 1][0] == "ev" and nodes[idx + 1][1]["k"] == "cb_error"):
                    sfn = fnmap.get("Strength", "Strength") if fnmap else "Strength"
                    out.append(pad + "%s()" % sfn)
    return out


def split_loop(evs):
    idx = [i for i, e in enumerate(evs) if e["k"] == "global_read" and e["name"] == LOOP_FLAG]
    if not idx:
        return evs, [], None
    pre = evs[:idx[0]]
    iters = []
    for a, b in zip(idx, idx[1:]):
        iters.append(evs[a + 1:b])
    last = evs[idx[-1]]
    return pre, iters, last["value"]


def main(evpath, outpath, note=""):
    data = json.load(open(evpath, encoding="utf-8"))
    ev = data["events"]
    ret = next(i for i, e in enumerate(ev) if e["k"] == "return")
    top, cbs = ev[:ret], ev[ret + 1:]

    sections, order, cur = {}, [], None
    for e in cbs:
        if e["k"] == "cb_begin":
            cur = e["fn"]
            sections[cur] = {"args": e.get("args", []), "evs": []}
            order.append(cur)
        elif e["k"] == "cb_end":
            cur = None
        elif cur is not None:
            sections[cur]["evs"].append(e)

    L = []
    L.append('if game:GetService("CoreGui"):FindFirstChild("ToraScript") then')
    L.append('    game:GetService("CoreGui").ToraScript:Destroy()')
    L.append("end")
    http = [e for e in top if e["k"] == "call" and e["path"] == "game.HttpGet"]
    url = http[0]["args"][1] if http else "?"
    L.append("local v1 = loadstring(game:HttpGet(%s, true))()" % lit(url))
    win = [e for e in top if e["k"] == "call" and e["path"] == "chunk()().CreateWindow"]
    title = win[0]["args"][1] if win else "?"
    L.append("local v2 = v1:CreateWindow(%s)" % lit(title))
    L.append("")

    emit_order = [n for n in order if n == "Strength"] + [n for n in order if n != "Strength"]
    fnmap = {}
    for idx, name in enumerate(emit_order, 1):
        fnmap[name] = "f%d" % idx

    for name in emit_order:
        sec = sections[name]
        fname = fnmap[name]
        if name == "Strength":
            body = sec["evs"]
            sb = next(i for i, e in enumerate(body) if e["k"] == "spawn_begin")
            se = next(i for i, e in enumerate(body) if e["k"] == "spawn_end")
            inner = body[sb + 1:se]
            pre, iters, last = split_loop(inner)
            L.append("local function %s()" % fname)
            L.append("    spawn(function()")
            L.append("        _G.Strength = true")
            if pre:
                L.extend(render(build(pre), 8, fnmap))
            if iters:
                L.append("        while true do")
                L.append("            if not _G.%s then break end" % LOOP_FLAG)
                L.extend(render(build(iters[0]), 12, fnmap))
                L.append("        end")
            L.append("    end)")
            L.append("end")
        else:
            params = "p1" if (sec["args"] and sec["args"][0] is True) else ""
            L.append("local function %s(%s)" % (fname, params))
            evs = sec["evs"]
            if params == "p1" and any(e["k"] == "global_read" and e["name"] == LOOP_FLAG for e in evs):
                L.append("    _G.%s = p1" % LOOP_FLAG)
            L.extend(render(build(evs), 4, fnmap))
            L.append("end")
        L.append("")

    for e in top:
        if e["k"] == "call" and e["path"].endswith((".AddButton", ".AddToggle", ".AddLabel")):
            meth = e["path"].rsplit(".", 1)[1]
            rec = e["args"][1]
            fields = []
            for k, x in rec["table"]:
                if isinstance(x, dict) and "fn" in x:
                    fields.append("%s = %s" % (k, fnmap.get(x["fn"], x["fn"])))
                else:
                    fields.append("%s = %s" % (k, lit(x)))
            L.append("v2:%s({ %s })" % (meth, ", ".join(fields)))
    L.append("")
    L.append("v1:Init()")
    open(outpath, "w", encoding="utf-8").write("\n".join(L) + "\n")
    print("wrote", outpath, sum(len(x) for x in L), "chars;", len(ev), "events")


if __name__ == "__main__":
    if len(sys.argv) not in (3, 4):
        sys.exit("usage: python3 v3emit.py <events.json> <out.lua> [note]")
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) == 4 else "")
