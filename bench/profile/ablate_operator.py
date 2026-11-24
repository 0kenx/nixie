#!/usr/bin/env python3
"""Ablate operator `op` in a QF_BV file: every `(op ...)` node becomes a fresh free var."""
import re, sys
src = open(sys.argv[1]).read()
op = sys.argv[2]
head = src[:src.find('(declare-fun')]
body = src[src.find('(declare-fun)') if False else src.find('(declare-fun'):]
toks = re.findall(r'\(|\)|[^\s()]+', body)
def parse(i):
    if toks[i] == '(':
        out = []; i += 1
        while toks[i] != ')':
            n, i = parse(i); out.append(n)
        return out, i + 1
    return toks[i], i + 1
forms = []; i = 0
while i < len(toks):
    f, i = parse(i); forms.append(f)
BOOL_OPS = {'bvule','bvult','bvugt','bvslt','bvsgt','='}
fresh = []
def abl(n):
    if isinstance(n, list):
        if n and isinstance(n[0], str) and n[0] == op:
            v = f"abl_{len(fresh)}"; fresh.append((v, op in BOOL_OPS)); return v
        return [abl(c) for c in n]
    return n
forms = [abl(f) for f in forms]
def emit(n):
    return '(' + ' '.join(emit(c) for c in n) + ')' if isinstance(n, list) else n
decls = "".join(f"(declare-fun {v} () {'Bool' if b else '(_ BitVec 32)'})\n" for v, b in fresh)
out = head + decls + "\n".join(emit(f) for f in forms) + "\n"
assert out.count('(') == out.count(')')
open(sys.argv[3], 'w').write(out)
print(f"ablated {len(fresh)} `{op}` nodes")
