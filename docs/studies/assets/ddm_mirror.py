# DdM on nixie's dumped initial state
from fractions import Fraction as F
import sys

lines = open('/tmp/simplex_state.txt').read().strip().split('\n')
nv = int(lines[0].split()[0].split('=')[1])
x = [F(0)]*nv; lo = [None]*nv; hi = [None]*nv; is_basic=[False]*nv
tab = {}
for ln in lines[1:]:
    p = ln.split()
    if p[0] == 'v':
        i = int(p[1])
        def frac(s):
            if s in ('-',): return None
            n,d = s.split('/'); return F(int(n), int(d))
        x[i] = frac(p[2].split('=')[1])
        lo[i] = frac(p[3].split('=')[1])
        hi[i] = frac(p[4].split('=')[1])
        is_basic[i] = p[5].split('=')[1]=='true'
    elif p[0] == 'r':
        b = int(p[1])
        const = F(p[3])
        row = {}
        for t in p[5:]:
            v, c = t.split('*')
            row[int(v)] = F(int(c), 1) if '/' not in c else F(*map(int, c.split('/')))
        tab[b] = [row, const]

def nonfree_deps(v):
    return sum(1 for r in tab if r != v and (lo[r] is not None or hi[r] is not None) and v in tab[r][0])

def find_violating():
    worst=None
    for b in tab:
        if lo[b] is not None and x[b] < lo[b]: k='lo'
        elif hi[b] is not None and x[b] > hi[b]: k='hi'
        else: continue
        if worst is None or b < worst[0]: worst=(b,k)
    return worst

def can_inc(v): return hi[v] is None or x[v] < hi[v]
def can_dec(v): return lo[v] is None or x[v] > lo[v]

def find_entering(b, k):
    row,_ = tab[b]
    best=None
    for v,c in row.items():
        if k=='lo': e = (c>0 and can_inc(v)) or (c<0 and can_dec(v))
        else: e = (c<0 and can_inc(v)) or (c>0 and can_dec(v))
        if not e: continue
        key=(nonfree_deps(v), sum(1 for r in tab if r!=v and v in tab[r][0]), v)
        if best is None or key<best[0]: best=(key,v)
    return None if best is None else best[1]

def inf_sum():
    s=F(0)
    for b in tab:
        if lo[b] is not None and x[b]<lo[b]: s+=lo[b]-x[b]
        elif hi[b] is not None and x[b]>hi[b]: s+=x[b]-hi[b]
    return s

npiv=0
TRACE = int(sys.argv[1]) if len(sys.argv)>1 else 0
while True:
    w = find_violating()
    if w is None:
        print(f"FEASIBLE after {npiv} pivots"); break
    b,k = w
    v = find_entering(b,k)
    if v is None:
        print(f"INFEASIBLE after {npiv}"); break
    if TRACE and npiv<TRACE:
        cands = []
        for cv, cc in tab[b][0].items():
            if k=='lo': e = (cc>0 and can_inc(cv)) or (cc<0 and can_dec(cv))
            else: e = (cc<0 and can_inc(cv)) or (cc>0 and can_dec(cv))
            if e:
                d = nonfree_deps(cv)
                l = sum(1 for r in tab if r!=cv and cv in tab[r][0])
                cands.append((d, l, cv))
        cands.sort()
        rowh = hash(tuple(sorted((vv, str(c)) for vv, c in tab[b][0].items())))
        print(f"#{npiv}: basic={b} enters={v} {k} inf={float(inf_sum()):.1f} rowhash={rowh % 100000} nterms={len(tab[b][0])}")
    # pivot: solve row b for v; snap b to bound
    row, const = tab[b]
    coef = row.pop(v)
    target = lo[b] if k=='lo' else hi[b]
    newrow = {vv: -c/coef for vv,c in row.items()}
    newrow[b] = newrow.get(b, F(0)) + F(1)/coef   # the leaving basic enters the solved form
    newconst = (target-const)/coef
    # new value of v:
    newv = newconst + sum(c*x[vv] for vv,c in newrow.items())
    dv = newv - x[v]
    x[v] = newv
    x[b] = target
    tab[v] = [newrow, newconst]
    del tab[b]
    is_basic[b]=False; is_basic[v]=True
    # substitute v out of other rows & propagate deltas to their basics
    for b2 in list(tab):
        if b2 == v: continue
        row2, const2 = tab[b2]
        if v in row2:
            c2 = row2.pop(v)
            for vv,c in newrow.items():
                row2[vv] = row2.get(vv,F(0)) + c2*c
                if row2[vv]==0: del row2[vv]
            const2 += c2*newconst
            tab[b2]=[row2,const2]
            # value change for b2: a_iv * dv
    # simpler exact: recompute all basic values
    for b2 in tab:
        row2, const2 = tab[b2]
        x[b2] = const2 + sum(c*x[vv] for vv,c in row2.items())
    maxbits = max((max(abs(c.numerator).bit_length(), c.denominator.bit_length()) for row,_ in tab.values() for c in row.values()), default=0)
    if npiv % 10 == 0 or npiv < 5:
        print(f"  [bits] pivot {npiv}: max coef bits = {maxbits}")
    npiv+=1
    if npiv>20000:
        print(f"GIVE UP inf={float(inf_sum())}"); break
