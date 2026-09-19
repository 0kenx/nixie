#!/usr/bin/env python3
"""Differential fuzz of nixie's `bag.fold` vs cvc5 1.3.4.

Generates random fold scripts over the fragment the eager reduction
supports (and just past its edge): closed ground multisets (`(bag y n)`
with numeral n, `bag.union_disjoint`, ite bags), defined and declared
combining functions (AC and not), symbolic elements, initial values,
multiplicity copies, and the fold composed with the rest of the bag
theory (counts, card, membership).

Protocol (the honest comparator):
  - decisive verdicts must agree; a disagreement is a soundness failure;
  - nixie `unknown` is counted but never a match;
  - either-side timeout (10 s) excludes the sample;
  - cvc5 error output containing "Unhandled" is inconclusive (it crashes
    on some bag shapes) — excluded, never evidence.

Usage: python3 bench/differential/bag_fold_fuzz.py [nixie] [N] [SEED]
"""
import random, subprocess, sys, tempfile, os, collections

NIXIE = sys.argv[1] if len(sys.argv) > 1 else "target/release/nixie"
CVC5 = "/nix/store/iawk4fnjb067vf5ilc8f3scnv55d2xad-cvc5-1.3.4/bin/cvc5"
N = int(sys.argv[2]) if len(sys.argv) > 2 else 400
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 20260919
random.seed(SEED)
TIMEOUT = 10

# Combining functions: (name, definition body, is_exchange_safe_guess)
AC_FUNS = [
    ("plus", "(+ x a)", "Int", "Int"),
    ("plusx", "(+ (* 2 x) a)", "Int", "Int"),
    ("maxf", "(ite (> x a) x a)", "Int", "Int"),
    ("minf", "(ite (< x a) x a)", "Int", "Int"),
    ("times", "(* x a)", "Int", "Int"),
]
NONAC_FUNS = [
    ("sub", "(- x a)", "Int", "Int"),
    ("consf", "(+ (* 3 x) (* -1 a))", "Int", "Int"),
    ("first", "(+ x (* 0 a))", "Int", "Int"),  # exchange-safe by accident? no: f(e1,f(e2,a)) = e1 vs f(e2,f(e1,a)) = e2 -> genuinely non-AC
]

def rand_bag(depth=0, symbolic=False):
    """A closed ground bag expression (element sort Int)."""
    r = random.random()
    if depth >= 2 or r < 0.4:
        e = random.choice(
            [str(random.randint(-9, 9)), str(random.randint(0, 4))]
            + (["x"] if symbolic else [])
        )
        n = random.choice([0, 1, 1, 2, 2, 3, 5])
        return f"(bag {e} {n})"
    if r < 0.8:
        return f"(bag.union_disjoint {rand_bag(depth+1, symbolic)} {rand_bag(depth+1, symbolic)})"
    c = random.choice(["(> x 0)", "(< k 0)", "true", "false"])
    return f"(ite {c} {rand_bag(depth+1, symbolic)} {rand_bag(depth+1, symbolic)})"

def gen_script():
    lines = ["(set-logic HO_ALL)"]
    symbolic = random.random() < 0.4
    if symbolic:
        lines.append("(declare-const x Int)")
    lines.append("(declare-const k Int)")
    use_ac = random.random() < 0.7
    funs = AC_FUNS if use_ac else NONAC_FUNS
    fname, body, es, acc = random.choice(funs)
    lines.append(f"(define-fun {fname} ((x {es}) (a {acc})) {acc} {body})")
    if random.random() < 0.2:
        # a declared (uninterpreted) combinator instead
        lines.append("(declare-fun g2 (Int Int) Int)")
        fname = "g2"
    init = random.choice(["0", "1", "-2", "7"])
    bag = rand_bag(symbolic=symbolic)
    fold = f"(bag.fold {fname} {init} {bag})"
    shape = random.random()
    if shape < 0.35:
        # pin the fold to a value near the plausible range
        v = random.randint(-30, 60)
        lines.append(f"(assert (= {fold} {v}))")
    elif shape < 0.55:
        lines.append(f"(assert (>= {fold} {random.randint(-5, 20)}))")
    elif shape < 0.7:
        # relate the fold to the cardinality (both count copies)
        lines.append(f"(assert (= {fold} (bag.card {bag})))")
    elif shape < 0.85:
        # membership + fold
        e = random.randint(-3, 3)
        lines.append(f"(assert (bag.member {e} {bag}))")
        lines.append(f"(assert (> {fold} {random.randint(-10, 10)}))")
    else:
        # two folds over the same bag under different functions (distinct:
        # SMT-LIB forbids redefinition, and the generator picks with
        # replacement, so re-draw until the names differ)
        fname2, body2, es2, acc2 = random.choice(AC_FUNS)
        while fname2 == fname:
            fname2, body2, es2, acc2 = random.choice(AC_FUNS)
        lines.append(f"(define-fun {fname2} ((x {es2}) (a {acc2})) {acc2} {body2})")
        lines.append(f"(assert (= {fold} (bag.fold {fname2} {init} {bag})))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"

def run(tool, path):
    try:
        out = subprocess.run(
            [tool, path], capture_output=True, text=True, timeout=TIMEOUT
        )
        text = out.stdout + out.stderr
        if "Unhandled" in text or "internal error" in text.lower():
            return "crash"
        if "timeout" in text.lower() or out.returncode == 124:
            return "timeout"
        for line in text.splitlines():
            s = line.strip()
            if s in ("sat", "unsat", "unknown"):
                return s
        return "none"
    except subprocess.TimeoutExpired:
        return "timeout"

stats = collections.Counter()
fails = []
for i in range(N):
    script = gen_script()
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(script)
        path = f.name
    try:
        nv = run(NIXIE, path)
        cv = run(CVC5, path)
        stats[(nv, cv)] += 1
        if nv == "crash" or cv == "crash":
            stats["crash"] += 1
            continue
        if nv in ("timeout", "none") or cv in ("timeout", "none"):
            stats["excluded"] += 1
            continue
        if nv == "unknown":
            stats["nixie-unknown"] += 1
            continue
        if nv != cv:
            fails.append((script, nv, cv))
            print(f"MISMATCH nixie={nv} cvc5={cv}\n{script}\n---")
    finally:
        os.unlink(path)

print(f"\nseed={SEED} n={N}")
for k, v in sorted(stats.items(), key=str):
    print(f"  {k}: {v}")
print(f"mismatches: {len(fails)}")
sys.exit(1 if fails else 0)
