set -e
SRC="$1"; SLUG="$2"; D=/tmp/rb_$SLUG
mkdir -p "$D"
python3 rundevirtv2static.py "$SRC" "$D" "$D/raw.lua" >/dev/null
python3 - "$D/raw.lua" "$D/wrap.lua" <<'PY'
import sys
s=open(sys.argv[1]).read()
s=s.replace("'discord.gg/gQEH2uZxUk'\n\n\n,nil,nil;","'discord.gg/gQEH2uZxUk', nil, nil",1)
lines=s.split("\n")
for i,l in enumerate(lines):
    if l.strip()=="function(...)":
        lines[i]="local function devirt(...)"; break
lines.append("devirt(...)")
open(sys.argv[2],"w").write("\n".join(lines) + "\n")
PY
python3 optimizeast.py "$D/wrap.lua" "$D/restyled.lua" >/dev/null
python3 postprocessv2.py "$D/restyled.lua" "$D/pp.lua" | sed "s/^/  [$SLUG] /"
python3 deadcode.py "$D/pp.lua" "$D/dce.lua" | sed "s/^/  [$SLUG] /"
python3 postprocessv2.py --finalize "$D/dce.lua" "$SLUG.deobf.txt"
LAST="$(cd "$(dirname "$0")/.." && pwd)/tools/luau-ast"
"$LAST" "$SLUG.deobf.txt" >/dev/null 2>&1 && echo "  [$SLUG] PARSE OK" || echo "  [$SLUG] PARSE FAIL"
wc -c "$SLUG.deobf.txt"
