#!/usr/bin/env python3
"""Random GNF instance generator for the Nixie-vs-MonoSAT differential campaign.

Generates the unweighted directed subset: one or two digraphs, random edges
(including self-loops), reach atoms restricted to distinct endpoints
(MonoSAT's reflexive reach and Nixie's strict reach coincide exactly there),
an optional acyclicity atom, and random CNF constraints mixing unit and
two-literal clauses over the theory variables.

Usage: gen_instance.py SEED [--vertices N] [--reach-max K] [--graphs {1,2}]
prints one GNF instance on stdout.
"""
import argparse
import random
import sys


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("seed", type=int)
    ap.add_argument("--vertices", type=int, default=0,
                    help="vertex count override (default random 2..8)")
    ap.add_argument("--reach-max", type=int, default=0,
                    help="max reach atoms per graph (default random 1..4)")
    ap.add_argument("--graphs", type=int, default=1, choices=[1, 2])
    ap.add_argument("--polarity-bias", type=float, default=0.5)
    ap.add_argument("--unit-prob", type=float, default=0.35,
                    help="probability a theory variable gets a fixing unit clause")
    ap.add_argument("--clause-size", type=int, default=0,
                    help="literal count of the coupling clauses (default random 2); "
                         "3+ forces real CDCL search with backtracking, exercising the "
                         "propagator's post-backtrack re-read path")
    ap.add_argument("--coupling", type=int, default=0,
                    help="number of coupling clauses (default random 0..4)")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    lines = []
    clauses = []
    var = 0

    def new_var() -> int:
        nonlocal var
        var += 1
        return var

    for g in range(args.graphs):
        n = args.vertices if args.vertices else rng.randint(2, 8)
        edge_count = rng.randint(0, n * n)
        gid = g
        # Pre-mint edge variables so reach/acyclic clauses can reuse them.
        edge_vars = [new_var() for _ in range(edge_count)]
        reach_max = args.reach_max if args.reach_max else rng.randint(1, 4)
        pairs = [(u, v) for u in range(n) for v in range(n) if u != v]
        rng.shuffle(pairs)
        reach_pairs = pairs[: min(reach_max, len(pairs))]
        reach_vars = {p: new_var() for p in reach_pairs}
        acyclic_var = new_var() if rng.random() < 0.6 else None

        total_vars_needed = var
        lines.append(f"digraph int {n} {edge_count} {gid}")
        edges = []
        for i in range(edge_count):
            u = rng.randrange(n)
            v = rng.randrange(n)
            edges.append((u, v, edge_vars[i]))
            lines.append(f"edge {gid} {u} {v} {edge_vars[i]}")
        for (u, v), rv in reach_vars.items():
            lines.append(f"reach {gid} {u} {v} {rv}")
        if acyclic_var is not None:
            lines.append(f"acyclic {gid} {acyclic_var}")

        # Random constraints: unit clauses fix some theory variables (both
        # polarities), two-literal clauses couple them.
        theory_vars = list(edge_vars) + list(reach_vars.values())
        if acyclic_var is not None:
            theory_vars.append(acyclic_var)
        for tv in theory_vars:
            if rng.random() < args.unit_prob:
                lit = tv if rng.random() < args.polarity_bias else -tv
                clauses.append([lit])
        coupling = args.coupling if args.coupling else rng.randint(0, 4)
        clause_size = args.clause_size if args.clause_size else 2
        for _ in range(coupling):
            k = min(clause_size, len(theory_vars))
            if k < 2:
                break
            chosen = rng.sample(theory_vars, k)
            clauses.append([v if rng.random() < 0.5 else -v for v in chosen])
        del total_vars_needed

    header = f"p cnf {var} {len(clauses)}"
    out = [header] + lines
    for c in clauses:
        out.append(" ".join(map(str, c)) + " 0")
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
