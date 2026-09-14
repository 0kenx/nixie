#!/usr/bin/env python3
"""Differential fuzz of nixie's quantifier/MBQI surface vs z3.

Companion to `mixed_fuzz.py` (the arithmetic generator): this one
GENERATES random small *quantified* formulas targeting the machinery the
2026-09 UFLRA unit landed — uninterpreted sorts with free constants,
Bool-valued predicates over them, definitional equalities (macro and
quasi-macro shapes), implication axioms with nested exists/forall,
tautological antecedents, and ground pins that force witness structure.

Oracle: every decisive verdict must agree with z3.  nixie `unknown` is
allowed (counted); a disagreement on sat/unsat is a soundness failure.

Usage:
    python3 bench/differential/quant_fuzz.py [path-to-nixie] [N] [SEED]
"""
import random, subprocess, sys, tempfile, os, collections

NIXIE = sys.argv[1] if len(sys.argv) > 1 else "target/release/nixie"
N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 20260914
random.seed(SEED)

TIMEOUT = 10


def run(binary, path):
    try:
        out = subprocess.run(
            [binary, path], capture_output=True, text=True, timeout=TIMEOUT
        ).stdout.split()
        for tok in reversed(out):
            if tok in ("sat", "unsat", "unknown"):
                return tok
        return "err"
    except subprocess.TimeoutExpired:
        return "timeout"


def gen_case():
    """One random quantified goal over an uninterpreted sort."""
    lines = ["(set-logic UFLRA)"]
    lines.append("(declare-sort S 0)")
    n_const = random.randint(2, 3)
    consts = [f"c{i}" for i in range(n_const)]
    for c in consts:
        lines.append(f"(declare-fun {c} () S)")
    # A Bool-valued observer over (S) or (S S); an S-valued constructor.
    obs_arity = random.choice([1, 2])
    obs_args = " ".join(["S"] * obs_arity)
    lines.append(f"(declare-fun P ({obs_args}) Bool)")
    if random.random() < 0.7:
        lines.append("(declare-fun F (S S) S)")
    # An arithmetic-indexed predicate (the member shape).
    lines.append("(declare-fun M (Real S) Bool)")

    obs_vars = ["(x S)", "(y S)"][:obs_arity]
    obs_app = "(P " + " ".join(v.strip("() ").split()[0] for v in obs_vars) + ")"

    def bool_leaf(vars_):
        r = random.random()
        if r < 0.4:
            return f"(P {random.choice(vars_)})" if obs_arity == 1 else (
                f"(P {random.choice(vars_)} {random.choice(vars_)})"
            )
        if r < 0.6:
            return f"(M {random.choice(['0.0', '1.0', '(- 1.0)', '2.5'])} {random.choice(vars_)})"
        if r < 0.7 and len(vars_) >= 2:
            return f"(= {vars_[0]} {vars_[1]})"
        return random.choice(["true", "false"])

    def bool_expr(vars_, depth=2):
        if depth <= 0 or random.random() < 0.4:
            return bool_leaf(vars_)
        op = random.choice(["not", "and", "or", "=>"])
        if op == "not":
            return f"(not {bool_expr(vars_, depth - 1)})"
        a = bool_expr(vars_, depth - 1)
        b = bool_expr(vars_, depth - 1)
        return f"({op} {a} {b})"

    n_axioms = random.randint(2, 5)
    for _ in range(n_axioms):
        kind = random.random()
        vs = ["x", "y"][:obs_arity]
        decls = " ".join(f"({v} S)" for v in vs)
        if kind < 0.25:
            # Definitional equality (macro shape).
            lines.append(
                f"(assert (forall ({decls}) (= {obs_app} {bool_expr(vs)})))"
            )
        elif kind < 0.45 and obs_arity == 2:
            # Witness shape: implication with a nested exists.
            lines.append(
                f"(assert (forall ({decls}) (=> (not {obs_app}) "
                f"(exists ((r Real)) (and (M r x) (not (M r y)))))))"
            )
        elif kind < 0.6:
            # Tautological-antecedent forcing (the emission-collapse shape).
            p = bool_expr(vs, 1)
            lines.append(
                f"(assert (forall ({decls}) (=> (forall ((z S)) (=> {p} {p})) {obs_app})))"
            )
        elif kind < 0.8:
            # Nested-forall antecedent (the A3 shape).
            q = f"(forall ((r Real)) (=> (M r x) (M r x)))" if obs_arity == 1 else (
                f"(forall ((r Real)) (=> (M r x) (M r y)))"
            )
            lines.append(f"(assert (forall ({decls}) (=> {q} {obs_app})))")
        else:
            # Ground pin over the constants.
            a, b = random.sample(consts, 2)
            leaf = bool_leaf([a, b][:obs_arity] if obs_arity <= 2 else [a])
            if obs_arity == 2:
                ground = f"(P {a} {b})"
            else:
                ground = f"(P {a})"
            lines.append(f"(assert (not (= {ground} {leaf})))" if random.random() < 0.5 else f"(assert {ground})")

    # One or two ground constraints that make the goal non-trivial.
    a, b = random.sample(consts, 2)
    if obs_arity == 2:
        lines.append(f"(assert (not (= {a} {b})))" if random.random() < 0.6 else f"(assert (P {a} {b}))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def main():
    stats = collections.Counter()
    failures = []
    for i in range(N):
        script = gen_case()
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
            f.write(script)
            path = f.name
        try:
            n = run(NIXIE, path)
            z = run("z3", path)
            stats[f"nixie={n}"] += 1
            stats[f"z3={z}"] += 1
            decisive = lambda v: v in ("sat", "unsat")
            if decisive(n) and decisive(z) and n != z:
                failures.append((path, n, z, script))
                print(f"DISAGREE file={path} nixie={n} z3={z}")
            elif n == "err":
                stats["nixie_err"] += 1
        finally:
            if not failures or failures[-1][0] != path:
                os.unlink(path)
    print("stats:", dict(stats))
    if failures:
        print(f"{len(failures)} DISAGREEMENTS")
        for path, n, z, script in failures[:3]:
            print("=" * 60)
            print(script)
        sys.exit(1)
    print("CLEAN: no decisive disagreements")


if __name__ == "__main__":
    main()
