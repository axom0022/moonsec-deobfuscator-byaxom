import json
import os
import subprocess
import sys

TOOLSDIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "tools")
LUAUAST = os.path.join(TOOLSDIR, "luau-ast")

ROBLOX_GLOBALS = {
    "game", "workspace", "script", "plugin", "Instance", "Vector3", "Vector2",
    "CFrame", "UDim2", "UDim", "Color3", "BrickColor", "Ray", "Rect", "Region3",
    "Region3int16", "TweenInfo", "NumberRange", "NumberSequence",
    "NumberSequenceKeypoint", "ColorSequence", "ColorSequenceKeypoint",
    "PhysicalProperties", "RaycastParams", "Faces", "Axes", "PathWaypoint",
    "Random", "DateTime", "buffer", "task", "coroutine", "warn", "print",
    "typeof", "type", "ipairs", "pairs", "next", "select", "tostring",
    "tonumber", "require", "getmetatable", "setmetatable", "rawget",
    "rawset", "rawequal", "rawlen", "pcall", "xpcall", "error", "assert",
    "unpack", "newproxy", "getfenv", "setfenv", "tick", "wait", "delay",
    "spawn", "elapsedTime", "collectgarbage", "gcinfo", "math", "string",
    "table", "os", "bit32", "utf8", "coroutine", "debug", "_G", "_VERSION",
    "Enum", "shared", "getgenv", "getrenv", "getreg", "getgc", "getinstances",
    "getnilinstances", "getscripts", "getloadedmodules", "getconnections",
    "fireclickdetector", "getclipboard", "setclipboard", "httpget",
    "HttpGet", "game", "Workspace", "Lighting", "ReplicatedStorage",
    "ServerStorage", "Players", "LocalPlayer", "StarterGui", "CoreGui",
    "RunService", "UserInputService", "TweenService", "MarketplaceService",
    "TeleportService", "VirtualUser", "VirtualInputManager", "Stats",
    "Debris", "PhysicsService", "ContextActionService", "GuiService",
    "ContentProvider", "AssetService", "InsertService", "SoundService",
}

BANNED_APIS = {
    "loadstring": "not available in Roblox (use loadstring only if the exec provides it)",
    "load": "not available in Roblox",
    "dofile": "not available in Roblox",
    "loadfile": "not available in Roblox",
    "io": "io library not available in Roblox",
    "require": "only for ModuleScripts; will error on a raw script",
    "string.dump": "not available in Roblox",
    "newproxy": "not available in Luau",
    "os.exit": "not available in Roblox",
    "os.execute": "not available in Roblox",
    "os.getenv": "not available in Roblox",
    "os.remove": "not available in Roblox",
    "os.rename": "not available in Roblox",
    "os.tmpname": "not available in Roblox",
    "debug.getregistry": "restricted in Roblox",
    "debug.setmetatable": "restricted in Roblox",
    "unpack": "Luau uses table.unpack; bare unpack may be nil",
}

STDLIB_PARENTS = {"math", "string", "table", "os", "bit32", "utf8", "coroutine", "debug"}

def parse(path):
    r = subprocess.run([LUAUAST, path], capture_output=True, timeout=60)
    txt = r.stdout.decode("utf-8", "replace")
    i = txt.find("{")
    if i < 0:
        return None, txt.strip()
    return json.loads(txt[i:]), None

def walk(node):
    if isinstance(node, dict):
        yield node
        for k, v in node.items():
            if k in ("type", "location", "name"):
                continue
            yield from walk(v)
    elif isinstance(node, list):
        for x in node:
            yield from walk(x)

def audit(path):
    print("=" * 70)
    print(os.path.basename(path))
    print("=" * 70)
    tree, err = parse(path)
    if tree is None:
        print("  PARSE FAIL:", err)
        return False

    ok = True
    stmts = tree["root"]["body"]

    calls = [n for n in walk(tree) if n.get("type") == "AstExprCall"]
    assigns = [n for n in walk(tree) if n.get("type") == "AstStatAssign"]
    funcs = [n for n in walk(tree)
             if n.get("type") in ("AstStatLocalFunction", "AstStatFunction")]
    print(f"  statements={len(stmts)} functions={len(funcs)} calls={len(calls)}")
    if not calls:
        print("  !! NO CALL SITES -- the script defines code but never runs it")
        ok = False

    read = {}
    for n in walk(tree):
        if n.get("type") == "AstExprGlobal":
            read.setdefault(n["global"], 0)
            read[n["global"]] += 1
    assigned = set()
    for n in walk(tree):
        if n.get("type") in ("AstStatAssign",):
            for v in n.get("vars", []) or []:
                if v.get("type") == "AstExprGlobal":
                    assigned.add(v["global"])
        if n.get("type") in ("AstStatLocal",):
            for v in n.get("vars", []) or []:
                assigned.add(v.get("name"))
        if n.get("type") == "AstStatLocalFunction":
            assigned.add((n.get("name") or {}).get("name"))
        if n.get("type") == "AstStatFunction":
            nm = n.get("name") or {}
            if nm.get("type") == "AstExprGlobal":
                assigned.add(nm["global"])
            elif nm.get("type") == "AstExprLocal":
                assigned.add((nm.get("local") or {}).get("name"))

    unknown = sorted(g for g in read
                     if g not in ROBLOX_GLOBALS and g not in assigned)
    if unknown:
        print(f"  !! globals read but never assigned ({len(unknown)}):")
        for g in unknown[:15]:
            print(f"       {g}  (x{read[g]})")
        ok = False
    else:
        print("  globals: all resolved")

    hits = []
    src = open(path, errors="replace").read()
    for api, why in BANNED_APIS.items():
        if api == "unpack":
                                                               
            import re
            if re.search(r"(?<![\w.])unpack\s*\(", src):
                hits.append((api, why))
        elif api in ("io",):
            import re
            if re.search(r"(?<![\w.])io\s*\.", src):
                hits.append((api, why))
        else:
            import re as _re
            if _re.search(r"(?<![" + "\w." + r"])" + _re.escape(api) + r"\s*[\(\.]", src):
                hits.append((api, why))
    if hits:
        print(f"  !! APIs unavailable/restricted in Roblox ({len(hits)}):")
        for api, why in hits:
            print(f"       {api}: {why}")
        ok = False
    else:
        print("  sandbox APIs: clean")

    artifacts = []
    for pat, label in (("_UPVALUE", "unluac upvalue placeholder"),
                       ("<unrecoverable", "unrecoverable constant marker"),
                       ("nil + 3", "unresolved constant"),
                       ("trulyunbound", "compiler error leaked into output")):
        if pat in src:
            artifacts.append(f"{label} ({src.count(pat)})")
                                                       
    if "vreg" in src:
        artifacts.append(f"register-array refs ({src.count('vreg')})")
    if artifacts:
        print("  artifacts: " + ", ".join(artifacts))
    else:
        print("  artifacts: none")

    print("  VERDICT:", "RUNNABLE" if ok else "NEEDS WORK")
    return ok

if __name__ == "__main__":
    results = [audit(p) for p in sys.argv[1:]]
    print()
    print("=" * 70)
    print(f"{sum(1 for r in results if r)}/{len(results)} runnable")
