#!/usr/bin/env python3
"""Generate the QF_FF chain corpus family (`bench/ff/bn254_chain_planted_*`).

Reverse-engineered from the committed corpus (the original generator was
not kept). The load-bearing structure — verified against the committed
files' variable-sharing patterns — is RESIDUE PASSES:

  pass 1: rows over {6k, 6k+1, 6k+2}, quads over {6k+2..+4} and {6k+4..+6}
  pass 2: rows over {6k+1, ..+3},     quads over {6k+3..+5} and {6k+5..+7}
  pass 3: rows over {6k+2, ..+4},     quads over {6k+4..+6} and {6k+6..+8}
  tail:   the final row {3,4,5} and seam quads {1,2,3},{5,6,7},{7,8,9}

totalling ~1.5 constraints per variable (n/2 affine rows, n product
quads). The pass structure is what keeps the linear core's RREF
elimination chains LOCAL: consecutive-offset rows (a single stride-6
sequence wrapping the ring) chain every row into one long elimination,
and the pivot definitions go global (measured: a 62-variable definition
for pivot 0, 1891-term substituted quads — nothing window-shaped
survives). The corpus's residue passes overlap only pairwise, so
definitions stay 2-local and the substituted quads stay at ≤4 variables
— the shape the window decomposition eats.

Coefficients are < 40; every RHS is the constraint's LHS evaluated at
the planted witness, so the goal is satisfiable by construction (any
`unsat` on a generated file is a solver bug). Deterministic given the
seed.

Usage: gen_chain.py <n_vars> <seed> [outfile]     (n_vars % 4 == 0)
"""

import sys
from typing import List

BN254 = 21888242871839275222246405745257275088548364400416034343698204186575808495617


class Rng:
    def __init__(self, seed: int) -> None:
        self.s = seed & 0xFFFFFFFFFFFFFFFF

    def next(self) -> int:
        self.s = (self.s * 6364136223846793005 + 1442695040888963407) & 0xFFFFFFFFFFFFFFFF
        return self.s >> 16

    def coeff(self) -> int:
        return self.next() % 39 + 1

    def witness(self) -> int:
        return self.next() % BN254


def affine(rng: Rng, idxs: List[int], w: List[int]) -> tuple[str, int]:
    """A random affine form over the given variables: (smt text, value)."""
    terms = []
    value = 0
    for i in idxs:
        c = rng.coeff()
        terms.append(f"(ff.mul #f{c}m{BN254} w{i})")
        value = (value + c * w[i]) % BN254
    k = rng.coeff()
    terms.append(f"#f{k}m{BN254}")
    value = (value + k) % BN254
    return "(ff.add " + " ".join(terms) + ")", value


def main() -> None:
    n = int(sys.argv[1])
    seed = int(sys.argv[2], 0)
    out = sys.argv[3] if len(sys.argv) > 3 else f"bn254_chain_planted_{n}x{3 * n // 2}.smt2"
    if n % 4 != 0:
        raise SystemExit("n_vars must be a multiple of 4")
    rng = Rng(seed)
    w = [rng.witness() for _ in range(n)]

    lines = ["(set-logic QF_FF)"]
    lines += [f"(declare-const w{i} (_ FiniteField {BN254}))" for i in range(n)]

    def emit(lhs: str, value: int) -> None:
        lines.append(f"(assert (= {lhs} #f{value}m{BN254}))")

    def quad(a: int, b: int, c: int) -> None:
        """Product of two affine forms over {a,b} and {b,c} (sharing b)."""
        l, lv = affine(rng, [a, b], w)
        r, rv = affine(rng, [b, c], w)
        emit(f"(ff.mul {l} {r})", (lv * rv) % BN254)

    max_rows = n // 2
    max_quads = n
    rows = quads = 0

    def row(a: int, b: int, c: int) -> None:
        nonlocal rows
        if rows < max_rows:
            s, v = affine(rng, [a, b, c], w)
            emit(s, v)
            rows += 1

    def q3(a: int, b: int, c: int) -> None:
        nonlocal quads
        if quads < max_quads:
            quad(a, b, c)
            quads += 1

    for (r_off, q1_off, q2_off) in ((0, 2, 4), (1, 3, 5), (2, 4, 6)):
        k = 0
        while True:
            base = 6 * k
            # Rows and quads extend independently to the ring's end (the
            # corpus's pass 3 has rows reaching {n-6..n-4} while its quads
            # reach {n-4..n-2}); a shared bound truncates the pass short
            # and leaves the chain under-constrained.
            did = False
            if base + r_off + 2 <= n - 1 and rows < max_rows:
                row(base + r_off, base + r_off + 1, base + r_off + 2)
                did = True
            for q_off in (q1_off, q2_off):
                if base + q_off + 2 <= n - 1 and quads < max_quads:
                    q3(base + q_off, base + q_off + 1, base + q_off + 2)
                    did = True
            if not did:
                break
            k += 1
        if rows >= max_rows and quads >= max_quads:
            break
    # The final row and the seam quads (the cycle's closure).
    row(3, 4, 5)
    for start in (1, 5, 7):
        q3(start, start + 1, start + 2)

    lines.append("(check-sat)")
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"{out}: {n} vars, {rows} affine rows, {quads} quads")


if __name__ == "__main__":
    main()
