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
    python3 bench/differential/quant_fuzz.py [path-to-nixie] [N] [SEED] [FAMILY]

FAMILY "random" (default) is the original generator.  FAMILY "unsat"
generates goals that are UNSAT BY CONSTRUCTION: each case is built from
a semantically guaranteed contradiction, so the oracle does not need z3
- a nixie `sat` is a soundness bug outright, an `unknown` is a counted
completeness gap, and z3 is run only as a cross-check of the generator
itself (z3 must answer unsat; if it does not, the generator is wrong).
The unsat families and the machinery each stresses:

  chain       - P(c) and forall x. P(x) => P(f(x)), asserted with
                (not (P (f^k c))): instantiation-depth refutation.
  skolem      - forall x. exists y. Q(x,y) conjoined with
                forall x y. not Q(x,y): pure two-quantifier logic.
  pigeonhole  - finite enumeration + distinct + injective f whose range
                misses a forced element: finite-model reasoning.
  card        - |S| <= n by enumeration, n+1 distinct constants.
  cycle       - transitivity+irreflexivity axioms, ground R-cycle.
  extensional - set-family semantics (member/difference/union) with a
                forced membership collision: the model-finder surface.

"""
import random, subprocess, sys, tempfile, os, collections

NIXIE = sys.argv[1] if len(sys.argv) > 1 else "target/release/nixie"
N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 20260914
FAMILY = sys.argv[4] if len(sys.argv) > 4 else "random"
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
        elif kind < 0.9:
            # Contradictory definitional twin: the same observer defined
            # as phi and as (not phi) — unsat once any pair instantiates.
            lines.append(
                f"(assert (forall ({decls}) (= {obs_app} {bool_expr(vs)})))"
            )
            lines.append(
                f"(assert (forall ({decls}) (= {obs_app} (not {bool_expr(vs)}))))"
            )
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
    # Spoil (~35%): a ground literal that contradicts a forcing axiom if
    # one exists — turns sat-shaped goals into their unsat twins (the
    # false-`unsat` class matters most: a wrong refutation claims a proof).
    if random.random() < 0.35:
        a, b = random.sample(consts, 2)
        ground = f"(P {a} {b})" if obs_arity == 2 else f"(P {a})"
        lines.append(f"(assert (not {ground}))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Unsat-forcing families: every generated goal is unsat by construction.
# ---------------------------------------------------------------------------


def _wrap_taut(body):
    """Wrap `body` (a closed Bool) in a random tautology-preserving shape
    so the contradiction is not syntactically obvious."""
    r = random.random()
    if r < 0.3:
        return f"(or {body} {body})"
    if r < 0.5:
        return f"(=> {body} {body})"
    if r < 0.7:
        return f"(and {body} (or true false))"
    if r < 0.85:
        return f"(=> (and true true) {body})"
    return body


def _gen_chain():
    """P(c0), forall x. P(x) => P(f(x)), and (not (P (f^k c0))).
    Unsat by a k-step instantiation chain - the refutation-depth test."""
    k = random.randint(1, 4)
    n_noise = random.randint(0, 2)
    lines = ["(set-logic UFLRA)", "(declare-sort S 0)",
             "(declare-fun c0 () S)", "(declare-fun P (S) Bool)",
             "(declare-fun f (S) S)"]
    for i in range(n_noise):
        lines.append(f"(declare-fun d{i} () S)")
    lines.append("(assert (P c0))")
    # The forcing axiom, optionally disguised under a random boolean wrap
    # that simplifies to P(x) => P(f(x)) at every instantiation.
    if random.random() < 0.5:
        lines.append(
            "(assert (forall ((x S)) (=> (and (P x) (or (P x) (not (P x)))) (P (f x)))))"
        )
    else:
        lines.append("(assert (forall ((x S)) (=> (P x) (P (f x)))))")
    # Distractor axioms that never interact.
    for i in range(n_noise):
        lines.append(f"(assert (forall ((x S)) (=> (P d{i}) (P (f x)))))")
    term = "c0"
    for _ in range(k):
        term = f"(f {term})"
    lines.append(f"(assert (not (P {term})))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _gen_skolem():
    """forall x. exists y. Q(x,y) with forall x y. not Q(x,y): unsat by
    pure logic (S is inhabited by c0).  Random surface dressing."""
    lines = ["(set-logic UFLRA)", "(declare-sort S 0)",
             "(declare-fun c0 () S)", "(declare-fun Q (S S) Bool)"]
    use_witness = random.random() < 0.6
    if use_witness:
        lines.append("(declare-fun g (S) S)")
        # exists y disguised as a witness plus totality of the disguise.
        lines.append("(assert (forall ((x S)) (Q x (g x))))")
    else:
        lines.append("(assert (forall ((x S)) (exists ((y S)) (Q x y))))")
    if random.random() < 0.5:
        lines.append(
            "(assert (forall ((x S) (y S)) (not (Q x y))))"
        )
    else:
        # Same content under a double negation and a tautology wrap.
        lines.append(
            "(assert (forall ((x S) (y S)) (not (or (Q x y) false))))"
        )
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _gen_pigeonhole():
    """|S| <= n by enumeration, n+1 distinct constants, injective f whose
    range misses one of them: unsat by the pigeonhole principle."""
    n = random.randint(2, 4)
    lines = ["(set-logic UFLRA)", "(declare-sort S 0)",
             "(declare-fun f (S) S)"]
    consts = [f"c{i}" for i in range(n + 1)]
    for c in consts:
        lines.append(f"(declare-fun {c} () S)")
    enum = " ".join(consts)
    lines.append(
        f"(assert (forall ((x S)) (or {' '.join(f'(= x {c})' for c in consts)})))"
    )
    lines.append(f"(assert (distinct {enum}))")
    lines.append(
        "(assert (forall ((x S) (y S)) (=> (= (f x) (f y)) (= x y))))"
    )
    missed = random.choice(consts)
    lines.append(f"(assert (forall ((x S)) (not (= (f x) {missed}))))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _gen_card():
    """|S| <= n by enumeration over the FIRST n constants, but n+1
    distinct constants asserted: unsat by construction."""
    n = random.randint(2, 5)
    lines = ["(set-logic UFLRA)", "(declare-sort S 0)"]
    consts = [f"c{i}" for i in range(n + 1)]
    for c in consts:
        lines.append(f"(declare-fun {c} () S)")
    # Enumerate over c0..c_{n-1} only: every element is one of the first
    # n constants, yet n+1 pairwise-distinct ones exist.
    lines.append(
        f"(assert (forall ((x S)) (or {' '.join(f'(= x {c})' for c in consts[:n])})))"
    )
    lines.append(f"(assert (distinct {' '.join(consts)}))")
    # Random noise predicate to keep the shape non-syntactic.
    lines.append("(declare-fun R (S S) Bool)")
    lines.append("(assert (forall ((x S) (y S)) (=> (R x y) (R y x))))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _gen_cycle():
    """Transitivity + irreflexivity over R, then a ground cycle of length
    3 or 4: unsat by pure first-order reasoning over the order axioms."""
    k = random.randint(3, 4)
    lines = ["(set-logic UFLRA)", "(declare-sort S 0)",
             "(declare-fun R (S S) Bool)"]
    consts = [f"c{i}" for i in range(k)]
    for c in consts:
        lines.append(f"(declare-fun {c} () S)")
    lines.append(
        "(assert (forall ((x S) (y S) (z S)) (=> (and (R x y) (R y z)) (R x z))))"
    )
    lines.append("(assert (forall ((x S)) (not (R x x))))")
    for i in range(k):
        lines.append(f"(assert (R c{i} c{(i + 1) % k}))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _gen_extensional():
    """Set-family semantics with a forced membership collision: the model-
    finder surface on the refutation side.  a = difference(a,b) together
    with M(w,a) and M(w,b): the difference semantics gives
    M(w,a) <=> M(w,a) and (not M(w,b)) - unsatisfiable with both true."""
    lines = ["(set-logic UFLRA)",
             "(declare-sort Elem 0)", "(declare-sort Set 0)",
             "(declare-fun M (Elem Set) Bool)",
             "(declare-fun subset (Set Set) Bool)",
             "(declare-fun difference (Set Set) Set)",
             "(declare-fun union (Set Set) Set)",
             "(declare-fun a () Set)", "(declare-fun b () Set)",
             "(declare-fun w () Elem)"]
    lines.append(
        "(assert (forall ((x Elem) (s1 Set) (s2 Set)) "
        "(= (M x (difference s1 s2)) (and (M x s1) (not (M x s2))))))"
    )
    lines.append(
        "(assert (forall ((x Elem) (s1 Set) (s2 Set)) "
        "(= (M x (union s1 s2)) (or (M x s1) (M x s2)))))"
    )
    lines.append(
        "(assert (forall ((s1 Set) (s2 Set)) "
        "(=> (forall ((x Elem)) (=> (M x s1) (M x s2))) (subset s1 s2))))"
    )
    # The collision, under one of three random dressings.
    shape = random.random()
    if shape < 0.34:
        lines += ["(assert (= a (difference a b)))",
                  "(assert (M w a))", "(assert (M w b))"]
    elif shape < 0.67:
        # Same, with the difference key hidden one application deeper.
        lines += ["(assert (= a (difference (union a b) b)))",
                  "(assert (M w a))", "(assert (M w b))",
                  "(assert (forall ((x Elem)) (=> (M x a) (M x a))))"]
    else:
        # superset-direction collision: a = union(a,b), b strictly
        # subset a witnessed, both memberships forced.
        lines += ["(assert (= b (difference b a)))",
                  "(assert (M w b))", "(assert (M w a))",
                  "(assert (not (subset a b)))"]
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


UNSAT_GENERATORS = {
    "chain": _gen_chain,
    "skolem": _gen_skolem,
    "pigeonhole": _gen_pigeonhole,
    "card": _gen_card,
    "cycle": _gen_cycle,
    "extensional": _gen_extensional,
}


def gen_case_unsat():
    name = random.choice(list(UNSAT_GENERATORS))
    return name, UNSAT_GENERATORS[name]()


def main():
    stats = collections.Counter()
    failures = []
    unsat_mode = FAMILY == "unsat"
    for i in range(N):
        if unsat_mode:
            fam, script = gen_case_unsat()
        else:
            fam, script = "random", gen_case()
        with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
            f.write(script)
            path = f.name
        try:
            n = run(NIXIE, path)
            z = run("z3", path)
            stats[f"nixie={n}"] += 1
            stats[f"z3={z}"] += 1
            if unsat_mode:
                stats[f"fam:{fam}:nixie={n}"] += 1
                # The oracle is the construction: the goal IS unsat.
                if z != "unsat":
                    # Generator defect - construction not actually unsat.
                    failures.append((path, n, z, script))
                    print(f"GENERATOR BUG fam={fam} file={path} z3={z}")
                elif n == "sat":
                    # Soundness failure, no comparator needed.
                    failures.append((path, n, z, script))
                    print(f"FALSE-SAT fam={fam} file={path}")
                elif n == "err":
                    stats["nixie_err"] += 1
                # nixie unknown: counted completeness gap, not a failure.
            else:
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
        print(f"{len(failures)} FAILURES")
        for path, n, z, script in failures[:3]:
            print("=" * 60)
            print(script)
        sys.exit(1)
    print("CLEAN: no decisive disagreements")


if __name__ == "__main__":
    main()
