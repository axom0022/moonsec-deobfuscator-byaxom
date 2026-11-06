import re
import sys

tokenretmpl = r'\b([AL])(\d+)_({depth})\b'
headerlhsre = re.compile(r'^(?:local\s+)?function\s+([AL]\d+_\d+)\s*\(')
headerassignre = re.compile(r'^([AL]\d+_\d+)\s*=\s*function\s*\(')

def findfunctionspans(lines):
    spans = []
    stack = []
    for i, line in enumerate(lines):
        stripped = line.strip()
        indent = len(line) - len(line.lstrip(' '))
        m = headerlhsre.match(stripped) or headerassignre.match(stripped)
        isfuncopen = bool(m) or re.match(r'^function\s*\(', stripped)
        if isfuncopen:
            depth = len(stack) + 2
            lhs = m.group(1) if m else None
            stack.append((indent, i, depth, lhs))
        elif stripped == 'end' and stack and stack[-1][0] == indent:
            startindent, starti, depth, lhs = stack.pop()
            spans.append((starti, i, depth, lhs))
    return spans

def renamefile(pathin, pathout):
    text = open(pathin, encoding='utf-8').read()
    lines = text.split('\n')

    spans = findfunctionspans(lines)
    funcholdertokens = {lhs for (ignored, ignored, ignored, lhs) in spans if lhs}

    allspans = spans + [(0, len(lines) - 1, 1, None)]

    outlines = list(lines)

    for starti, endi, depth, ignoredlhs in allspans:
        pattern = re.compile(tokenretmpl.format(depth=depth))
        mapping = {}
        counters = {'A': 0, 'L_func': 0, 'L_var': 0}

        def repl(m, mapping=mapping, counters=counters):
            kind, slot, d = m.group(1), m.group(2), m.group(3)
            key = f'{kind}{slot}_{d}'
            if key in mapping:
                return mapping[key]
            if kind == 'A':
                counters['A'] += 1
                newname = f'p{counters["A"]}'
            elif key in funcholdertokens:
                counters['L_func'] += 1
                newname = f'f{counters["L_func"]}'
            else:
                counters['L_var'] += 1
                newname = f'v{counters["L_var"]}'
            mapping[key] = newname
            return newname

        for li in range(starti, endi + 1):
            outlines[li] = pattern.sub(repl, outlines[li])

    result = '\n'.join(outlines)
    open(pathout, 'w', encoding='utf-8').write(result)

if __name__ == '__main__':
    renamefile(sys.argv[1], sys.argv[2])
    print('wrote', sys.argv[2])

