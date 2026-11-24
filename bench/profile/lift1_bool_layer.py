#!/usr/bin/env python3
"""Lift the width-1 BV boolean layer of a QF_BV instance to Bool sort.

Usage: lift1.py IN.smt2 OUT.smt2

Every let-bound term is classified by sort.  Width-1 `bvnot/bvand/
bvor/bvxor/ite`/`=` over liftable operands become `not/and/or/xor/ite/=`
on Bool; a single-bit extract of a WIDE term becomes the Bool atom
`(= ((_ extract i i) t) #b1)`.  Anything else keeps its BV form.  The
script REFUSES to write output if any definition fails to lift (a
partial lift is a different formula).
"""
import re, sys
sys.setrecursionlimit(100000)

src = open(sys.argv[1]).read()
a, b = src.find('(assert'), src.find('(check-sat)')
head = src[:a]
toks = re.findall(r'\(|\)|[^\s()]+', src[a:b])

def parse(i):
    if toks[i] == '(':
        out = []
        i += 1
        while toks[i] != ')':
            node, i = parse(i)
            out.append(node)
        return out, i + 1
    return toks[i], i + 1

tree, _ = parse(0)
assert tree[0] == 'assert'
defs = {}
def collect(n):
    if isinstance(n, list):
        if n[0] == 'let':
            for name, d in n[1]:
                defs[name] = d
            return collect(n[2])
        return n
    return n
core = collect(tree[1])

def const(n): return isinstance(n, list) and n[0] == '_' and n[1].startswith('bv')
def bvnum(n):
    m = re.fullmatch(r'bv(\d+)', n[1]); return int(m.group(1)), int(n[2])

decl = {m.group(1): int(m.group(2)) for m in re.finditer(r'\(declare-fun (\S+) \(\) \(_ BitVec (\d+)\)\)', head)}
W = dict(decl)
for k in defs: W.setdefault(k, None)
BOOL = set()
BV_BIN = ('bvand','bvor','bvxor','bvadd','bvsub','bvmul','bvshl','bvlshr','bvashr','bvudiv','bvurem')
PRED = ('=','bvult','bvule','bvslt','bvsgt','bvugt','bvuge','bvsle','bvsge','distinct')

def is_extract(n):
    return (isinstance(n, list) and len(n) == 2 and isinstance(n[0], list)
            and n[0][0] == '_' and n[0][1] == 'extract')
def width(n):
    if isinstance(n, str): return W.get(n)
    h = n[0]
    if is_extract(n): return int(n[0][2]) - int(n[0][3]) + 1  # ((_ extract i j) t)
    if h == '_':
        if n[1].startswith('bv'): return int(n[2])             # (_ bvN w)
        return None
    if h == 'ite': return width(n[2])
    if h == 'bvnot': return width(n[1])
    if h in BV_BIN: return width(n[1])
    if h == 'concat': return (width(n[1]) or 0) + (width(n[2]) or 0)
    if h in PRED: return 'BOOL'
    if h in ('not','and','or','xor','=>'): return 'BOOL'
    return None
for _ in range(len(defs) + 5):
    ch = False
    for k, v in defs.items():
        w = width(v)
        if w != W[k]: W[k] = w; ch = True
    if not ch: break
for k in defs:
    if W[k] == 'BOOL': BOOL.add(k)

def b2bool(n):
    if isinstance(n, list):
        h = n[0]
        if h == '_':
            v, w = bvnum(n); return ('true' if v else 'false') if w == 1 else None
        if h == 'bvnot':
            x = b2bool(n[1]); return ['not', x] if x is not None else None
        if h in ('bvand','bvor','bvxor'):
            x, y = b2bool(n[1]), b2bool(n[2])
            if x is None or y is None: return None
            return [{'bvand':'and','bvor':'or','bvxor':'xor'}[h], x, y]
        if h == 'ite':
            c = boolof(n[1]); t, e = b2bool(n[2]), b2bool(n[3])
            if c is None or t is None or e is None: return None
            return ['ite', c, t, e]
        if is_extract(n) and n[0][2] == n[0][3]:
            if width(n[1]) == 1: return b2bool(n[1])
            return ['=', n, ['_','bv1','1']]
        if h in PRED: return boolof(n)
        return None
    if W.get(n) == 1 or W.get(n) == 'BOOL': return 'b!' + n
    return None

def boolof(n):
    if isinstance(n, list) and n[0] == '=' and width(n[1]) == 1:
        a, b = n[1], n[2]
        if const(a) and bvnum(a)[0] == 1: return b2bool(b)
        if const(b) and bvnum(b)[0] == 1: return b2bool(a)
        x, y = b2bool(a), b2bool(b)
        return ['=', x, y] if x is not None and y is not None else None
    if isinstance(n, list) and n[0] in PRED: return [n[0]] + n[1:]
    if isinstance(n, list) and n[0] in ('not','and','or','xor','=>'):
        xs = [boolof(c) for c in n[1:]]
        return [n[0]] + xs if all(x is not None for x in xs) else None
    return b2bool(n)

LIFTED = {k for k in defs if W[k] == 'BOOL' or W[k] == 1}

def bitof(n):
    """BV-side view: a lifted Bool referenced from an unlifted BV term is
    re-materialised as the bit `(ite b #b1 #b0)`; a Bool-sorted predicate
    used as a bit likewise."""
    if isinstance(n, str):
        return ['ite', 'b!' + n, ['_','bv1','1'], ['_','bv0','1']] if n in LIFTED and W[n] == 1 else (
               ['ite', 'b!' + n, ['_','bv1','1'], ['_','bv0','1']] if n in LIFTED else n)
    if is_extract(n):
        return [n[0], bitof(n[1])]
    if not isinstance(n[0], str):
        return [n[0]] + [bitof(c) for c in n[1:]]
    h = n[0]
    if h == '_': return n
    if h in PRED:   # a Bool predicate used inside a BV term as a bit
        return ['ite', boolof(n), ['_','bv1','1'], ['_','bv0','1']]
    if h in ('ite',):
        c = boolof(n[1])
        if c is None: c = ['=', bitof(n[1]), ['_','bv1','1']]
        return ['ite', c, bitof(n[2]), bitof(n[3])]
    return [h] + [bitof(c) for c in n[1:]]

out = []
for k, v in defs.items():
    w = W[k]
    if w == 'BOOL': out.append(('b!' + k, boolof(v)))
    elif w == 1:    out.append(('b!' + k, b2bool(v)))
    else:           out.append((k, bitof(v)))
fails = [k for k, bd in out if bd is None]
if fails:
    for k in fails:
        kk = k[2:] if k.startswith('b!') else k
        print("  FAIL", k, "W=", W.get(kk), "def=", repr(defs.get(kk))[:140])
    sys.exit(f"REFUSED: {len(fails)} definitions failed to lift")
cb = boolof(core)
if cb is None:
    sys.exit("REFUSED: core failed to lift")

def emit(n):
    if isinstance(n, list): return '(' + ' '.join(emit(c) for c in n) + ')'
    return n
expr = emit(cb)
for name, bd in reversed(out):
    expr = f"(let (({name} {emit(bd)})) {expr})"
s = head + f"(assert {expr})\n(check-sat)\n"
assert s.count('(') == s.count(')'), "paren imbalance"
open(sys.argv[2], 'w').write(s)
lifted = sum(1 for k, _ in out if k.startswith('b!'))
print(f"lifted {lifted}/{len(out)} definitions to Bool")
