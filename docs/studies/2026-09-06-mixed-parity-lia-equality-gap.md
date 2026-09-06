# Study: mixed Bool+LIA parity stalls — root cause decomposition and the LIA equality-system gap

**Date:** 2026-09-06
**Found by:** the obligation-grammar fuzzer (`bench/obligation`, finding A4)
**Status:** root cause isolated; partial fix landed (ite-domain lemma); complete fix scoped but not implemented (Smith/HNF equality fast path)

## The finding

The parity family realizes the same graph-parity obstruction through
different theories. Nixie decides the pure-CNF (Tseitin) and pure-BV1
realizations at 26–60 vertices, but the **mixed Bool+LIA encoding**
(Bool XOR chains at some vertices, LIA sums `Σ i_e = c_v + 2·k_v` at
others, edges linked by `(= i_e (ite b_e 1 0))`) answers `unknown` at
~26 vertices in *both* polarities, where z3 answers `sat`/`unsat` in
seconds.

## Decomposition (each step a minimal, checked repro)

1. **Bounds on the linked variables fix the SAT side.** Appending
   `(assert (<= 0 i_k 1))` for every Int edge variable flips the
   even-charge instance from `unknown` to `sat`. The ite side-conditions
   (`b → i=1`, `¬b → i=0`) only constrain `i_e` disjunctively; LIA gets
   no interval until CDCL decides `b_e`. → Landed the **ite-domain
   lemma** (`const_branch_bounds` in `nixie-solver/src/solver/encode.rs`):
   an ite with two numeric-constant branches also asserts
   `min ≤ v ≤ max` (implied, hence sound). This is the standard
   `solve-eqs`-adjacent enrichment and helps every finite-domain ite
   encoding — but it does **not** fix this family, because…

2. …**the pure-Int edges carry no ite and cannot be bounded.** Edges
   between two LIA vertices are plain Int variables constrained only by
   the vertex equations. The obstruction is still decided correctly
   (odd charge: rationally infeasible, refuted by the LP relaxation
   itself), but…

3. …**the even-charge (SAT) side stalls in LIA branch-and-bound.** A
   *pure-LIA* instance with no Booleans at all reproduces it:

   - 26 vertices / 45 edges, one Int var per edge, one slack `k_v` per
     vertex, equation `Σ_{e∋v} i_e = c_v + 2·k_v` per vertex, even
     total charge.
   - nixie: `unknown`; z3: `sat` (instantly).

   `ArithmeticSolver::check` step 3 runs `lia_branch_and_bound`, which
   is sound and complete *for bounded problems* — with
   `LIA_MAX_NODES = 20_000` as the honesty budget — but the system is
   **unbounded** (nothing pins the slack or edge values), the LP
   relaxation returns fractional vertices, and branch-and-bound wanders
   until the node budget is exhausted. The `unknown` is honest; the
   capability is missing.

## Why z3 answers

z3's `solve_eqs` preprocessing eliminates integer equalities
Gaussian-style before the simplex search, turning the vertex-equation
system into explicit assignments. The class “integer feasibility of
`A·x = b`” is decidable in polynomial time (Smith / Hermite normal
form); no search is required.

## The principled fix (scoped, not implemented here)

An **equality fast path** in the integer arithmetic check:

- When the *entire* active constraint set is integer equalities (no
  inequality rows, no propagated bounds, no active cuts — needs a
  maintained counter at the row-assertion sites), build `A·x = b` and
  run Smith normal form with checked `i128` arithmetic (bail to the
  ordinary path on overflow — never fabricate).
  - Unsat: the SNF divisibility failure is a certificate.
  - Sat: `x* = Q·diag(1/d)·P⁻¹·b` with free parameters zeroed; assert
    the (implied) fixings `x_j = x*_j` under the current scope and let
    the existing pipeline confirm.
- Note the repo's `lia/hnf.rs` is **not** a canonical HNF (no
  sub-pivot elimination, unchecked `i64` ops) — it cannot be reused
  as-is for a solve; a correct checked implementation is part of the
  work. The `LiaSolver` in `lia/` is also not on the QF_LIA path
  (only the NLA engine uses it); the fast path belongs in
  `arithmetic/solver.rs::check`.
- Expected effect: pure-equality QF_LIA (the parity family, and every
  “network flow over integers” / congruence-style encoding) decided
  instantly instead of exhausting 20 000 B&B nodes. Mixed instances
  converge to this path as CDCL fixes the linked Booleans, provided
  the ite-domain lemma has bounded the crossing variables.

## What landed alongside this study

- **ite-domain lemma** (sound, implied-clause enrichment) — helps
  finite-domain ite encodings; necessary but not sufficient here.
- **Associative-chain normalization** in the depth-rescue pass
  (`rewrite::ground_fold`): deep constant `bvxor`/`bvadd`/`bvmul`
  chains over a variable collapse to `x ⊕ C` etc. before the
  encode-depth guard — fixes the reconverge-bv stressed finding.

## Reproducers

Deterministic (SplitMix64, same construction as the generator):

- `bench/obligation` parity family: `obligation-run --family parity
  --seeds 1 --size medium` — `parity-mixedboolint-{sat,unsat}-s0-medium`
  both `unknown` (z3: sat/unsat).
- Pure-LIA minimal case (generator sketch inlined):

  ```python
  # 26 vertices, 45 edges; even charge => SAT, odd => UNSAT
  # vars: i_e per edge, k_v per vertex; assert per vertex:
  #   (= (+ i_e1 i_e2 ...) (+ c_v (* 2 k_v)))
  ```

  nixie: `unknown` (even) / `unsat` (odd). z3: `sat` / `unsat`.
