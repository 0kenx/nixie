"""Compare this evaluator's values against TLC's, structurally.

String comparison does not work: sets are unordered, TLC prints a function on
1..n as a sequence and a function on strings as a record, and record fields
keep source order. All of those are the *same value*. So both sides are parsed
into a canonical form and compared as values.
"""
import sys, os, re, glob

class P:
    def __init__(self, s): self.s = s; self.i = 0
    def ws(self):
        while self.i < len(self.s) and self.s[self.i].isspace(): self.i += 1
    def peek(self):
        self.ws(); return self.s[self.i] if self.i < len(self.s) else ''
    def eat(self, tok):
        self.ws()
        if self.s.startswith(tok, self.i): self.i += len(tok); return True
        return False
    def value(self):
        self.ws()
        if self.eat('<<'):
            items = []
            if not self.eat('>>'):
                while True:
                    items.append(self.value())
                    if self.eat('>>'): break
                    if not self.eat(','): raise ValueError('tuple')
            # A tuple is a function on 1..n.
            return ('fun', frozenset((('int', i + 1), v) for i, v in enumerate(items)))
        if self.eat('{'):
            items = []
            if not self.eat('}'):
                while True:
                    items.append(self.value())
                    if self.eat('}'): break
                    if not self.eat(','): raise ValueError('set')
            return ('set', frozenset(items))
        if self.eat('['):
            fields = []
            if not self.eat(']'):
                while True:
                    self.ws(); m = re.match(r'[A-Za-z0-9_]+', self.s[self.i:])
                    if not m: raise ValueError('field')
                    k = m.group(0); self.i += len(k)
                    if not self.eat('|->'): raise ValueError('|->')
                    fields.append((('str', k), self.value()))
                    if self.eat(']'): break
                    if not self.eat(','): raise ValueError('record')
            # A record is a function on its field names.
            return ('fun', frozenset(fields))
        if self.eat('('):
            pairs = []
            while True:
                k = self.value()
                if not self.eat(':>'): raise ValueError(':>')
                pairs.append((k, self.value()))
                if self.eat(')'): break
                if not self.eat('@@'): raise ValueError('@@')
            return ('fun', frozenset(pairs))
        if self.peek() == '"':
            j = self.s.index('"', self.i + 1)
            v = self.s[self.i + 1:j]; self.i = j + 1
            return ('str', v)
        m = re.match(r'(-?\d+)\s*\.\.\s*(-?\d+)', self.s[self.i:])
        if m:
            self.i += len(m.group(0))
            lo, hi = int(m.group(1)), int(m.group(2))
            return ('set', frozenset(('int', i) for i in range(lo, hi + 1)))
        m = re.match(r'-?\d+', self.s[self.i:])
        if m:
            self.i += len(m.group(0)); return ('int', int(m.group(0)))
        for kw, v in (('TRUE', True), ('FALSE', False)):
            if self.eat(kw): return ('bool', v)
        raise ValueError(f'unparsed at {self.s[self.i:self.i+30]!r}')

def parse(s):
    p = P(s); v = p.value(); p.ws()
    if p.i != len(p.s): raise ValueError('trailing')
    return v

# Operators TLC implements in Java, overriding whatever the TLA+ module says.
# Comparing against them measures TLC's runtime, not this evaluator: the
# `TLC.tla` shipped with the examples defines `JavaTime == 123` as a
# placeholder while the tool substitutes the real clock.
TLC_OVERRIDDEN = {"JavaTime", "TLCGet", "TLCSet", "RandomElement", "Permutations"}

sp = sys.argv[1]
agree = 0; mism = []; missing = 0; unparsed = 0; unparsed_ex = []; probes = 0
for exp in sorted(glob.glob(f"{sp}/probes/*.expected")):
    probe = os.path.basename(exp)[:-len(".expected")]
    out = f"{sp}/tlcout/{probe}.out"
    want = {}
    for line in open(exp):
        if line.startswith("#"): continue
        if "\t" in line:
            n, v = line.rstrip("\n").split("\t", 1); want[n] = v
    if not os.path.exists(out) or os.path.getsize(out) == 0:
        missing += len(want); continue
    probes += 1
    got = {}
    for line in open(out):
        m = re.match(r'^<<"([^"]+)", (.*)>>\s*$', line.rstrip("\n"))
        if m: got[m.group(1)] = m.group(2)
    for n, v in want.items():
        if n in TLC_OVERRIDDEN: continue
        if n not in got: missing += 1; continue
        try:
            a, b = parse(v), parse(got[n])
        except Exception:
            # An unparsed value is an *untested* value. Surfacing it is the
            # difference between a differential and a differential that
            # quietly shrinks its own sample.
            unparsed += 1
            unparsed_ex.append((probe, n, v, got[n]))
            continue
        if a == b: agree += 1
        else: mism.append((probe, n, v, got[n]))
print(f"probes TLC evaluated: {probes}")
print(f"  definitions agreeing with TLC : {agree}")
print(f"  SEMANTIC MISMATCHES           : {len(mism)}")
print(f"  not printed by TLC            : {missing}")
print(f"  value unparsed by comparator  : {unparsed}")
for p_, n, a, b in mism[:20]:
    print(f"    MISMATCH {p_}!{n}\n       nixie: {a[:120]}\n       TLC  : {b[:120]}")
for p_, n, a, b in unparsed_ex[:10]:
    print(f"    UNPARSED {p_}!{n}\n       nixie: {a[:120]}\n       TLC  : {b[:120]}")
sys.exit(1 if (mism or unparsed) else 0)
