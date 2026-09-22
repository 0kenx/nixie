#!/usr/bin/env python3
"""Paired FSM-synthesis instance generator: Nixie fsm commands vs the
standard exact SMT encoding for Z3.

Both files of a pair encode the SAME problem over the SAME guard
variables: a candidate NFA (fixed states/alphabet/initial/accepting,
guarded transitions) must accept every positive word and reject every
negative word. Z3 has no FSM theory, so its file uses the layered
one-hot reachability encoding with bounded epsilon relaxation
(|Q| monotone iterations; the layering makes the biconditional system
acyclic, hence exact — the same construction as nixie-solver's
independent-encoding test oracle).

Deterministic given --seed. Output: <outdir>/{nixie,z3}/<name>.smt2 plus
manifest.json.
"""

import argparse
import json
import random
from pathlib import Path


def candidate_transitions(n_states, alphabet, rng):
    """(from, to, label) candidate set: stay / advance / jump per (q, s),
    plus epsilon advances on half the states. Nondeterministic, cyclic."""
    out = []
    seen = set()
    for q in range(n_states):
        for s in range(alphabet):
            for d in {q, (q + 1) % n_states, (q * s + 3) % n_states}:
                if (q, d, s) not in seen:
                    seen.add((q, d, s))
                    out.append((q, d, ("sym", s)))
        if q % 2 == 0:
            t = (q, (q + 1) % n_states, -1)
            if t not in seen:
                seen.add(t)
                out.append((q, (q + 1) % n_states, ("eps",)))
    return out


def guard_name(q, d, label):
    if label[0] == "eps":
        return f"g_e{q}"
    return f"g_{q}_{label[1]}_{d}"


def gen_words(rng, alphabet, count, length):
    return [[rng.randrange(alphabet) for _ in range(length)] for _ in range(count)]


def emit_nixie(name, n_states, alphabet, initial, accepting, trans, pos, neg):
    lines = ["(set-logic ALL)"]
    for (q, d, label) in trans:
        lines.append(f"(declare-const {guard_name(q, d, label)} Bool)")
    lines.append(f"(declare-fsm A {n_states} {alphabet})")
    lines.append(f"(fsm.initial A {initial})")
    for a in accepting:
        lines.append(f"(fsm.accepting A {a})")
    for (q, d, label) in trans:
        lbl = "eps" if label[0] == "eps" else str(label[1])
        lines.append(f"(fsm.transition A {q} {d} {lbl} {guard_name(q, d, label)})")
    for i, w in enumerate(pos):
        word = "(" + " ".join(str(x) for x in w) + ")"
        lines.append(f"(fsm.accepts A {word} p{i})")
        lines.append(f"(assert p{i})")
    for i, w in enumerate(neg):
        word = "(" + " ".join(str(x) for x in w) + ")"
        lines.append(f"(fsm.accepts A {word} n{i})")
        lines.append(f"(assert (not n{i}))")
    lines.append("(check-sat)")
    lines.append("(exit)")
    return "\n".join(lines) + "\n"


def emit_z3(name, n_states, alphabet, initial, accepting, trans, pos, neg):
    nq = n_states
    # Index transitions by (label, to) for the per-position implications.
    sym_into = {}
    eps_into = {}
    for (q, d, label) in trans:
        if label[0] == "eps":
            eps_into.setdefault(d, []).append((q, guard_name(q, d, label)))
        else:
            sym_into.setdefault((label[1], d), []).append(
                (q, guard_name(q, d, label)))

    def iff(a, b):
        return f"(= {a} {b})"

    def or_of(xs):
        xs = list(xs)
        if not xs:
            return "false"
        if len(xs) == 1:
            return xs[0]
        return "(or " + " ".join(xs) + ")"

    def and_of(xs):
        xs = list(xs)
        if not xs:
            return "true"
        if len(xs) == 1:
            return xs[0]
        return "(and " + " ".join(xs) + ")"

    lines = ["(set-logic ALL)"]
    for (q, d, label) in trans:
        lines.append(f"(declare-const {guard_name(q, d, label)} Bool)")

    for wi, w in enumerate(pos + neg):
        n = len(w)
        R = [[f"R{wi}_{p}_{q}" for q in range(nq)] for p in range(n + 1)]
        E = [[[f"E{wi}_{i}_{p}_{q}" for q in range(nq)]
              for p in range(n + 1)] for i in range(nq + 1)]
        for p in range(n + 1):
            for q in range(nq):
                lines.append(f"(declare-const {R[p][q]} Bool)")
            for q in range(nq):
                lines.append(f"(declare-const {E[0][p][q]} Bool)")
        for i in range(1, nq + 1):
            for p in range(n + 1):
                for q in range(nq):
                    lines.append(f"(declare-const {E[i][p][q]} Bool)")
        # Base layer.
        lines.append(f"(assert {R[0][initial]})")
        for q in range(nq):
            if q != initial:
                lines.append(f"(assert (not {R[0][q]}))")
        # Consuming steps and relaxation biconditionals.
        for p in range(n):
            for q in range(nq):
                terms = [
                    and_of([E[nq][p][src], g])
                    for (src, g) in sym_into.get((w[p], q), [])
                ]
                lines.append(f"(assert {iff(R[p + 1][q], or_of(terms))})")
        for p in range(n + 1):
            for q in range(nq):
                lines.append(f"(assert {iff(E[0][p][q], R[p][q])})")
                for i in range(nq):
                    terms = [and_of([E[i][p][src], g])
                             for (src, g) in eps_into.get(q, [])]
                    body = or_of([E[i][p][q]] + terms)
                    lines.append(f"(assert {iff(E[i + 1][p][q], body)})")
        finals = or_of([E[nq][n][a] for a in accepting])
        if wi < len(pos):
            lines.append(f"(assert {finals})")
        else:
            lines.append(f"(assert (not {finals}))")
    lines.append("(check-sat)")
    lines.append("(exit)")
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--seed", type=int, default=20260922)
    args = ap.parse_args()

    out = Path(args.outdir)
    (out / "nixie").mkdir(parents=True, exist_ok=True)
    (out / "z3").mkdir(parents=True, exist_ok=True)

    manifest = []
    # families: (states, word_len, n_pos, n_neg) - synthesis-shaped grid
    families = []
    for states in (8, 16, 32, 64):
        for wlen in (10, 40, 80):
            families.append((states, wlen, 2, 2))
    # a few unsat canaries: same word demanded accepted and rejected
    families.append((16, 20, 1, 0))
    families.append((32, 40, 0, 1))

    for fam_idx, (states, wlen, n_pos, n_neg) in enumerate(families):
        for rep in range(3):
            rng = random.Random(args.seed + fam_idx * 100 + rep)
            trans = candidate_transitions(states, 2, rng)
            accepting = sorted({states - 1, states // 2})
            pos = gen_words(rng, 2, n_pos, wlen)
            neg = gen_words(rng, 2, n_neg, wlen)
            unsat = False
            if n_pos == 1 and n_neg == 0:
                pos = gen_words(rng, 2, 1, wlen)
                neg = [pos[0]]  # same word both ways -> unsat
                unsat = True
            if n_pos == 0 and n_neg == 1:
                pos = gen_words(rng, 2, 1, wlen)
                neg = [pos[0]]
                unsat = True
            name = f"fsm_s{states}_w{wlen}_r{rep}"
            (out / "nixie" / f"{name}.smt2").write_text(
                emit_nixie(name, states, 2, 0, accepting, trans, pos, neg))
            (out / "z3" / f"{name}.smt2").write_text(
                emit_z3(name, states, 2, 0, accepting, trans, pos, neg))
            manifest.append({
                "name": name, "states": states, "word_len": wlen,
                "n_pos": len(pos), "n_neg": len(neg),
                "guards": len(trans), "expect_unsat": unsat,
            })
    (out / "manifest.json").write_text(json.dumps(manifest, indent=1))
    print(f"{len(manifest)} instance pairs -> {out}")


if __name__ == "__main__":
    main()
