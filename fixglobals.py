import re

def luastringliteral(s):
    out = ['"']
    for ch in s:
        if ch == '"':
            out.append('\\"')
        elif ch == '\\':
            out.append('\\\\')
        elif ch == '\n':
            out.append('\\n')
        elif ch == '\r':
            out.append('\\r')
        elif ch == '\t':
            out.append('\\t')
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)

def fixbareglobals(source, badnames):
    for name in sorted(badnames, key=len, reverse=True):
        escaped = re.escape(name)
        pattern = re.compile(r'(?<!["\'\w])' + escaped + r'(?!["\'\w])')
        replacement = "_G[" + luastringliteral(name) + "]"
        source = pattern.sub(lambda m: replacement, source)
    return source
