#!/usr/bin/env python3
"""Conservative source guard; the actual logical check is Lean plus #print axioms."""
import pathlib
import re
root = pathlib.Path(__file__).resolve().parent.parent
banned = re.compile(r"\b(sorry|admit|axiom|unsafe|implemented_by|extern|native_decide|run_tac)\b")

def strip_comments(text):
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif not depth and text[i:i+2] == '--':
            j = text.find('\n', i)
            i = len(text) if j == -1 else j
        else:
            if not depth:
                out.append(text[i])
            i += 1
    if depth:
        raise SystemExit('Unclosed block comment')
    return ''.join(out)

for path in sorted((root / 'Erdos143').glob('*.lean')) + [root / 'Erdos143.lean']:
    match = banned.search(strip_comments(path.read_text()))
    if match:
        raise SystemExit(f'Forbidden proof escape in {path.name}: {match.group()}')
print('Source guard passed; no proof placeholders, added axioms, or unsafe bypasses')
