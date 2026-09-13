#!/usr/bin/env python3
"""Differential fuzz of nixie's mixed-integer arithmetic vs z3.

Companion to `bench_diff.py` (the pinned-sample harness): this one GENERATES
random small formulas targeting the arithmetic surface — mixed Int/Real
variables, div/mod by constants, strict inequalities, constants near the
i64 boundary — and diffs every decisive verdict against z3, validating
nixie's `sat` models through z3 when z3 itself is undecided.

Found two soundness bugs within minutes of its first run (`/` silently
being integer division: `(/ 7 2) = 3` answered `sat`), which is the bar a
generator has to clear to be worth keeping.

Usage:
    python3 bench/differential/mixed_fuzz.py [path-to-nixie] [N] [SEED]

Targets the surface changed by the wide-literal/mixed-mode fix:
  - Int and Real variables in ONE problem (per-variable integrality)
  - integer holes (fractional-only LP solutions)
  - div/mod by small constants (Euclidean axioms)
  - strict inequalities on integer rows
  - constants near the i64 boundary
  - numeral arithmetic that folds at construction

A disagreement on a decisive verdict, or a nixie `sat` whose model z3
refutes, is a soundness failure.  nixie `unknown` is allowed (counted).
"""
import random, subprocess, sys, tempfile, os, collections

NIXIE = sys.argv[1] if len(sys.argv) > 1 else "target/release/nixie"
N = int(sys.argv[2]) if len(sys.argv) > 2 else 500
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 20260914
random.seed(SEED)

INT_VARS = ["xi", "yi", "zi"]
REAL_VARS = ["xr", "yr"]

def rint():
    kind = random.random()
    if kind < 0.55: return random.randint(-9, 9)
    if kind < 0.8:  return random.randint(-100, 100)
    if kind < 0.92: return random.choice([2**31 - 1, 2**31, 2**62, 2**62 + 1, 2**63 - 1])
    return random.choice([-(2**31), -(2**62), 2**40, -(2**40)])

def rreal():
    k = random.random()
    if k < 0.6: return f"{random.randint(-9, 9)}.0"
    if k < 0.85: return f"{random.randint(-20, 20)}.{random.randint(1, 9)}"
    return f"(/ {random.randint(-5, 5)} {random.randint(2, 7)})"

def lin_var(int_pool, real_pool):
    """One linear term: coeff * var, Int or Real."""
    if int_pool and real_pool:
        pool = int_pool if random.random() < 0.6 else real_pool
    else:
        pool = int_pool or real_pool
    v = random.choice(pool)
    c = random.choice([1, 1, 2, 3, -1, -2, 5, 10])
    return f"(* {c} {v})"

def arith_expr(int_pool, real_pool, depth=0):
    """A small arithmetic expression.  Returns (text, int_pure): div/mod are
    only applied to Int-pure dividends so the generator stays well-sorted."""
    r = random.random()
    if depth > 2 or r < 0.35:
        if random.random() < 0.7:
            v = lin_var(int_pool, real_pool)
            return v, "xr" not in v and "yr" not in v
        return str(rint()), True
    if r < 0.75:
        n = random.randint(2, 3)
        parts = [arith_expr(int_pool, real_pool, depth + 1) for _ in range(n)]
        return "(+ " + " ".join(t for t, _ in parts) + ")", all(p for _, p in parts)
    if r < 0.9:
        a, pure = arith_expr(int_pool, real_pool, depth + 1)
        b = random.choice([1, 2, 3, 4, 5, 7])
        op = random.choice(["div", "mod"])
        if not pure:
            # keep well-sorted: real-sorted dividend takes `/` instead
            return f"(/ {a} {b})", False
        return f"({op} {a} {b})", op == "div" or True  # div/mod over Int stays Int
    a, pure = arith_expr(int_pool, real_pool, depth + 1)
    b = random.choice([2, 3, -2])
    return f"(- {a} {b})", pure

def atom(int_pool, real_pool):
    a, _ = arith_expr(int_pool, real_pool)
    if random.random() < 0.75:
        b, _ = arith_expr(int_pool, real_pool) if random.random() < 0.4 else (
            str(rint()), True) if (not real_pool or random.random() < 0.6) else (rreal(), False)
        op = random.choice(["=", "<", "<=", ">", ">="])
        return f"({op} {a} {b})"
    return f"(> {a} {random.randint(0,5)})"

def formula(int_pool, real_pool, depth=0):
    if depth >= 2 or random.random() < 0.5:
        return atom(int_pool, real_pool)
    op = random.choice(["and", "or"])
    n = random.randint(2, 3)
    parts = [formula(int_pool, real_pool, depth + 1) for _ in range(n)]
    f = f"({op} " + " ".join(parts) + ")"
    if random.random() < 0.3:
        f = f"(not {f})"
    return f

LOGICS = [None, "QF_LIA", "QF_LRA", "QF_LIRA"]


def gen():
    """A random goal, stratified over the declared logic so the `set-logic`
    routing matrix (LIA / mixed / LRA-by-shape / unset-default) is
    exercised, not just the default mode."""
    logic = random.choice(LOGICS)
    n_int = random.randint(1, 3)
    n_real = random.randint(0, 2)
    if logic == "QF_LRA":
        n_int = 0
        n_real = random.randint(1, 2)
    if logic == "QF_LIA":
        n_real = 0
        n_int = random.randint(1, 3)
    int_pool = INT_VARS[:n_int]
    real_pool = REAL_VARS[:n_real]
    header = f"(set-logic {logic})\n" if logic else ""
    decls = "".join(f"(declare-const {v} Int)\n" for v in int_pool)
    decls += "".join(f"(declare-const {v} Real)\n" for v in real_pool)
    conjs = [formula(int_pool, real_pool) for _ in range(random.randint(1, 3))]
    return header + decls + "(assert (and " + " ".join(conjs) + "))\n(check-sat)\n"

def run(binary, path, extra=None):
    args = [binary, path]
    try:
        out = subprocess.run(args, capture_output=True, text=True, timeout=10).stdout
    except subprocess.TimeoutExpired:
        return "timeout", None
    lines = [l.strip() for l in out.splitlines() if l.strip() and not l.startswith("Processing")]
    if not lines: return "none", None
    verdict = lines[0]
    model = None
    if extra == "model" and verdict == "sat" and len(lines) > 1:
        model = "\n".join(lines[1:])
    return verdict, model

stats = collections.Counter()
bad = []
for i in range(N):
    src = gen()
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(src); path = f.name
    try:
        nz, _ = run(NIXIE, path)
        z3v, _ = run("z3", path)
        stats[f"nixie={nz}"] += 1
        if nz == z3v:
            continue
        if nz in ("sat", "unsat") and z3v in ("sat", "unsat"):
            bad.append(("VERDICT", src, nz, z3v))
        elif nz == "sat" and z3v == "unknown":
            # no oracle; validate the model with z3 instead
            with open(path, "w") as f:
                f.write(src + "(check-sat)\n(get-model)\n")
            _, model = run(NIXIE, path, extra="model")
            if model:
                defs = "\n".join(l for l in model.splitlines() if l.startswith("(define"))
                with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as g:
                    g.write(src + defs + "\n(check-sat)\n"); gpath = g.name
                zv, _ = run("z3", gpath)
                if zv == "unsat":
                    bad.append(("MODEL", src + defs, "sat(model)", "z3 refutes model"))
                os.unlink(gpath)
        elif nz in ("unsat",) and z3v == "unknown":
            pass  # no oracle
        # nixie unknown vs z3 decisive: completeness gap, count only
        elif nz == "unknown" and z3v in ("sat", "unsat"):
            stats["gap_vs_decisive"] += 1
    finally:
        os.unlink(path)
    if len(bad) >= 5:
        break

print("seed", SEED, "instances", N)
for k, v in sorted(stats.items()):
    print(f"  {k}: {v}")
if bad:
    print(f"\n!!! {len(bad)} FAILURES")
    for kind, src, a, b in bad:
        print(f"--- {kind}: nixie={a} z3={b}\n{src}\n")
    sys.exit(1)
print("\nOK: no verdict disagreements, no refuted models")
