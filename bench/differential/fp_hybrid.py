#!/usr/bin/env python3
"""Deterministic functional differential checks; no performance comparison.

Run with --nixie target/release/nixie --z3 z3. Every generated formula is
submitted once to each solver. Unknowns/timeouts are reported separately,
never counted as agreement. The seed generates inputs, not search policies.
"""
import argparse
import collections
import hashlib
import json
import random
import subprocess


def cases(seed, count):
    rng = random.Random(seed)
    for _ in range(count):
        e, p = rng.choice([(2, 2), (2, 3), (3, 4)])

        def literal():
            return "(fp #b{} #b{} #b{})".format(
                rng.randrange(2),
                format(rng.randrange(1 << e), f"0{e}b"),
                format(rng.randrange(1 << (p - 1)), f"0{p - 1}b"),
            )

        terms = ["x", "y", literal(), literal()]
        for _ in range(2):
            op = rng.choice(["add", "sub", "mul"])
            rm = rng.choice(["RNE", "RNA", "RTP", "RTN", "RTZ"])
            terms.append(f"(fp.{op} {rm} {rng.choice(terms)} {rng.choice(terms)})")
        atoms = []
        for _ in range(3):
            if rng.randrange(3) == 0:
                pred = rng.choice(["isNormal", "isSubnormal", "isZero", "isNaN", "isInfinite", "isPositive", "isNegative"])
                atom = f"(fp.{pred} {rng.choice(terms)})"
            else:
                pred = rng.choice(["=", "distinct", "fp.eq", "fp.lt", "fp.leq"])
                atom = f"({pred} {rng.choice(terms)} {rng.choice(terms)})"
            atoms.append(f"(not {atom})" if rng.randrange(3) == 0 else atom)
        if rng.randrange(2):
            atoms = [f"(or {atoms[0]} {atoms[1]})", atoms[2]]
        yield (
            f"(set-logic QF_FP)\n(declare-const x (_ FloatingPoint {e} {p}))\n"
            f"(declare-const y (_ FloatingPoint {e} {p}))\n"
            + "\n".join(f"(assert {a})" for a in atoms)
            + "\n(check-sat)\n"
        )


def run(command, script):
    try:
        proc = subprocess.run(command, input=script, text=True, capture_output=True, timeout=15)
    except subprocess.TimeoutExpired:
        return "timeout"
    answers = [s.strip() for s in proc.stdout.splitlines() if s.strip() in ("sat", "unsat", "unknown")]
    if proc.returncode or len(answers) != 1 or "(error" in proc.stdout:
        raise RuntimeError(f"{command}: {proc.stdout}\n{proc.stderr}\n{script}")
    return answers[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nixie", default="target/release/nixie")
    parser.add_argument("--z3", default="z3")
    parser.add_argument("--seed", type=int, default=20260908)
    parser.add_argument("--count", type=int, default=300)
    args = parser.parse_args()
    counts = collections.Counter()
    digest = hashlib.sha256()
    wrong = []
    for i, script in enumerate(cases(args.seed, args.count)):
        digest.update(script.encode())
        n, z = run([args.nixie], script), run([args.z3, "-in"], script)
        counts[f"{n}/{z}"] += 1
        if n in ("sat", "unsat") and z in ("sat", "unsat") and n != z:
            wrong.append({"index": i, "nixie": n, "z3": z, "script": script})
    report = {
        "z3_version": subprocess.check_output([args.z3, "--version"], text=True).strip(),
        "seed": args.seed,
        "count": args.count,
        "input_sha256": digest.hexdigest(),
        "verdict_pairs": dict(counts),
        "wrong": wrong,
    }
    print(json.dumps(report, indent=2))
    return bool(wrong)


if __name__ == "__main__":
    raise SystemExit(main())
