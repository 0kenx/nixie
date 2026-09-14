#!/usr/bin/env python3
"""Wide-literal cancellation differential: random linear formulas whose
coefficients/constants sit at and beyond the i64 boundary, compared against
z3. This is the oracle that found the item-32 wrong-`sat` (wide
coefficients silently dropped as free Booleans) and the f1 false-`unsat`
(the lying assignment_current) — its fourth generator revision added the
`not/and` nesting over div/mod + wide constants that exposed f1, so shape
coverage matters more than seed count here.

On nixie-`sat`-vs-z3-`unknown` splits, nixie's model is validated by
replaying it through z3 (mixed_fuzz.py's pattern).

Comparator trap: z3's QF_LRA front end ERRORS on `(- 0 2^63)`-shaped
literals ("logic does not support nonlinear arithmetic") while its
no-logic mode decides the same formula correctly — error output is
treated as non-evidence (`z3err`), never read as a verdict.
"""
import random, subprocess, sys, tempfile, os, collections

NIXIE = sys.argv[1] if len(sys.argv) > 1 else "target/release/nixie"
N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 20260963
random.seed(SEED)

def r64():
    # The i64 boundary and just past it: 2^62..2^64-scale magnitudes, the
    # odd-prime relief class (3*MAX-ish), and a 2^100-scale prime (no
    # small odd factor: the honest wall).
    return random.choice([
        2**62, -(2**62), 2**61, -(2**61), 2**60 + 7, -(2**60 + 9),
        9223372036854775807, -9223372036854775807, 4611686018427387904,
        3037000499, 2**59 - 11, 2**63, -(2**63), 2**63 + 2, -(2**63 + 2),
        2**64 + 13, 1267650600228229401496703205653,
    ])

def gen():
    sort = random.choice(["Real", "Int"])
    logic = {"Real": "QF_LRA", "Int": "QF_LIA"}[sort]
    nvars = random.randint(2, 4)
    L = [f"(set-logic {logic})"] + [f"(declare-const v{i} {sort})" for i in range(nvars)]
    for _ in range(random.randint(1, 3)):
        terms = []
        for _ in range(random.randint(2, 4)):
            c = r64(); v = random.randrange(nvars)
            terms.append(f"(* {c} v{v})" if c >= 0 else f"(* (- 0 {-c}) v{v})")
        rhs = r64() if random.random() < 0.5 else random.randint(-5, 5)
        op = random.choice(["=", ">", "<", ">=", "<="])
        lhs = terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"
        L.append(f"(assert ({op} {lhs} {rhs}))")
    # Nested Boolean structure over div/mod — the f1 shape (fourth
    # revision; keep it).
    if random.random() < 0.3:
        a, b = (random.randrange(nvars) for _ in range(2))
        L.append(
            f"(assert (and (not (and (> (mod (* 3 v{a}) 7) 2) (<= (div (* -1 v{b}) 4) 1))) "
            f"(> (+ (mod (div -3 7) 4) (mod -5 5)) 2)))"
        )
    if random.random() < 0.7:
        for i in random.sample(range(nvars), random.randint(1, nvars)):
            L.append(f"(assert (= v{i} {random.randint(-3, 3)}))")
    L.append("(check-sat)")
    return "\n".join(L) + "\n"

def run(binary, path, get_model=False):
    try:
        script = open(path).read()
        if get_model:
            with open(path, "w") as f:
                f.write(script + "(get-model)\n")
        p = subprocess.run([binary, path], capture_output=True, text=True, timeout=15)
        out = p.stdout
    except subprocess.TimeoutExpired:
        return "timeout", None
    lines = [l.strip() for l in out.splitlines() if l.strip() and not l.startswith("Processing")]
    if not lines:
        return "none", None
    if lines[0].startswith("(error"):
        return "z3err", None
    return lines[0], ("\n".join(lines[1:]) if get_model and len(lines) > 1 else None)

stats = collections.Counter()
bad = []
for i in range(N):
    src = gen()
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(src); path = f.name
    try:
        nz, _ = run(NIXIE, path)
        zv, _ = run("z3", path)
        stats[f"nixie={nz}"] += 1
        if nz == zv:
            continue
        if nz in ("sat", "unsat") and zv in ("sat", "unsat"):
            bad.append(("VERDICT", src, nz, zv))
        elif nz == "sat" and zv == "unknown":
            _, model = run(NIXIE, path, get_model=True)
            if model:
                defs = "\n".join(l for l in model.splitlines() if l.startswith("(define"))
                with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as g:
                    g.write(src + defs + "\n(check-sat)\n"); gpath = g.name
                zval, _ = run("z3", gpath)
                if zval == "unsat":
                    bad.append(("MODEL", src + defs, "sat(model)", "z3 refutes model"))
                os.unlink(gpath)
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
