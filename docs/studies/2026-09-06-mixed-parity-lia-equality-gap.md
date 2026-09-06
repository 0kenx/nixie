# Study: mixed Bool+LIA parity stalls — root cause decomposition and the LIA equality-system gap

**Date:** 2026-09-06 (parity-lemma rung implemented 2026-09-07)
**Found by:** the obligation-grammar fuzzer (`bench/obligation`, finding A4)
**Status:** **CLOSED** — the mod-2 parity lemma (`nixie-solver/src/solver/parity_lemma.rs`) decides both mixed-parity classes; implementation record below

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

## The principled fix (IMPLEMENTED 2026-09-06, see below)

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

## Implementation record (2026-09-06, later the same day)

`lia/hnf.rs` was rewritten from scratch (the old file is gone):

* **Canonical column-echelon (Hermite) reduction** with the
  `A · U = H` invariant maintained by construction (unimodular column
  operations only, applied to `U` in lockstep), Euclidean gcd pair
  elimination per pivot row, column swaps installing pivots at
  `0..rank`, positive pivots, and the canonical reduction pass
  (`0 ≤ H[i][j] < H[i][i]` below the diagonal).  `pivot_rows` is the
  authoritative echelon ordering for rank-deficient inputs (pure column
  ops cannot reorder rows).  All arithmetic is checked `i128` under a
  `2^40` magnitude guard: guards trip → `None`, never a wrapped result.
  Unit tests pin every invariant (`A·U == H`, `|det U| = 1`, echelon
  shape, canonical bounds, known values, overflow bail) including the
  exact inputs the old implementation broke on.
* **`solve_integer_eq_system`**: complete decision of `A·x = b` over ℤ
  by forward substitution over pivot rows — pivot variables are uniquely
  determined by their predecessors, so free variables are genuinely
  free and setting them to zero is lossless (the row-Gaussian + free=0
  trap, `2x + y = 1`, is covered by a test and a 400-case randomized
  brute-force cross-check).
* **Wiring** (`arithmetic/solver.rs`): the memoized one-sided
  `int_equalities_infeasible` fallback in `lia_branch_and_bound` became
  the complete `IntEqVerdict` — `Infeasible` (proof) / `Incumbent`
  (witness) / `GiveUp`.  An incumbent is never trusted: it is re-pinned
  through a scoped LP re-solve (`try_eq_incumbent`: push, pin every
  covered variable, one simplex pass + integrality scan, pop) so rows
  beyond the equalities get to veto it.  Rejections are memoized per
  equality-set state (a doomed pinning costs one LP, once).

Measured outcomes (this tree vs the finding):

| instance (medium, seed 0) | before | after |
|---|---|---|
| pure-LIA parity, even charge (the study repro) | `unknown` | `sat`, 0.05 s |
| pure-LIA parity, odd charge | `unsat` | `unsat` |
| `parity-mixedboolint-sat` | `unknown` | `sat`, 0.3 s |
| `parity-mixedboolint-unsat` | `unknown` (0.26 s) | honest long search → timeout |
| `parity-mixedboundary` (div/mod links) | `unknown` | `unknown` (unchanged, separate gap) |

The mixed-UNSAT trajectory change deserves note: the theory now
(correctly) reports `sat` under partial assignments where it used to
abort the whole check with `unknown`, so the SMT core keeps searching
instead of bailing in 0.26 s — honest but slower on that class; the
refutation needs bounds-aware Diophantine reasoning (below).  Gates on
this tree: nextest 10542/10542 (corpora present), clippy/fmt/doc
`-D warnings` clean, z3 parity 170 entries / 0 mismatches; obligation
fuzzer sweeps 57/58 (stressed) and 56/58 (medium) decided, 0 wrong.

### Remaining gaps (next rungs)

1. **Bounds-aware Diophantine reasoning (search integration) —
   attempted 2026-09-06, measured negative, not landed.**  The theory
   side is *proven complete*: with every cross-edge Boolean decided
   (fixes present as level-0 rows), `parity-mixedboolint-unsat` is
   refuted instantly (z3 agreement).  The attempted integration —
   folding the propagation-bound tracker's active fixes
   (`active_int_fixes`: tightest lower==upper, integral, δ=0) into the
   equality system, cache keyed by the fix fingerprint — measured
   *negative* on search: `mixedboolint-sat` 0.3 s → 6.2 s (recompute
   churn on every fix-set change + fix-respecting incumbents steering
   longer searches), `parity-incremental` regressed to timeout, and
   mixed-UNSAT still timed out (the informative leaves are never
   reached early enough for per-check folding to pay).  Reverted; do
   not retry per-check folding.  What would actually close the rung:
   firing the folded verdict only at near-full Boolean assignments
   (the theory lacks that signal — it would need solver-side plumbing
   of an "atoms-fully-decided" flag), or lifting the mod-2 signature
   of the equality system into a parity lemma for the SAT core.

   **Attempt #2 (2026-09-06, landed as infrastructure, negative on the
   target class):** lineage-tracked Diophantine cores (the failing
   pivot-prefix is itself an infeasible subsystem — column ops preserve
   rows) + eager Infeasible firing before the B&B burn. Cores are a
   real win where infeasibility is local (the classic `y = 2x ∧ y =
   2z + 1` now conflicts on its 2 equations), and no instance
   regressed (suite, parity, fuzzer sweeps all clean). But the
   mixed-UNSAT class still times out: the parity-failure core spans
   the *entire* Int view (~60 literals — every vertex equation, link,
   and fix), and a clause that wide teaches CDCL nothing. Conclusion
   after two attempts: no core-size or firing-order variant closes
   this; the constraint genuinely needs to reach the SAT core as an
   **xor lemma** (`Σ b_e ≡ c (mod 2)` synthesized from the equality
   system's mod-2 signature through the link structure, handed to
   `XorDetector`), which is lemma-export infrastructure plus literal
   synthesis — a dedicated feature, the last rung.
2. **`parity-mixedboundary` (rung 2) — theory side complete, same
   search gap (measured 2026-09-06).**  With every cross-edge Boolean
   fixed at level 0, the div/mod-linked instance is refuted instantly
   (z3 agreement): the Euclidean axiom chains (`v = 4q + r1`,
   `q = 2w + t2`, `i = t2`) plus the fixed links give the Hermite view
   exactly what it needs.  During search the instance fast-bails to
   `unknown` (~1.2 s) rather than long-searching: the incumbent is
   always rejected (the axiom rows bound `t2 ∈ [0,1]`), so the theory
   reports `Unknown` and the core stops — honest, incomplete.  The
   integration design that would close *both* rungs is the mod-2
   parity lemma: derive the equality system's parity signature over
   the linked literals (`Σ b_e ≡ Σc (mod 2)` through `t2 ≡ b_e`) and
   hand it to the SAT core as a lemma, where `XorDetector` machinery
   can consume it.  That is a cross-theory derivation feature, not a
   patch; scoped here, not attempted.

## The parity-lemma rung (IMPLEMENTED 2026-09-07, closes both gaps)

After the two measured negatives above, the conclusion stood: the
constraint must reach the SAT core as a synthesized xor lemma.  A
hand-written spike confirmed the design first — appending the
hand-derived `xor(b_cross…) = Σc (mod 2)` lemma to the medium
`mixedboolint`/`mixedboundary` instances flipped timeout/unknown to
`unsat` in ~0.1 s — before any derivation machinery was built.

### Design (see `nixie-solver/src/solver/parity_lemma.rs` for the full
soundness argument)

The derivation lives **solver-side**, not in `ArithSolver`, for two
reasons: the theory can only return `TheoryResult` (it cannot assert
Bool lemmas), and its recorded rows include search-time
(decided-literal) equalities that would make a lemma derived from them
scope-invalid.  Working from the preprocessed level-0 `assertions`
(that list is exactly the asserted formulas) keeps every ingredient a
logical consequence of the input:

1. **Rows**: walk the assertions' top-level conjunctions and collect
   every Int-sorted linear equality (via `extract_linear_terms`, which
   treats `div`/`mod`/`ite` terms as opaque columns), integral `i64`
   coefficients only.
2. **Mod-2 elimination**: GF(2) Gaussian elimination pivoting on the
   *non-image-determined* columns; the surviving rows (zero
   non-determined support) are the mod-2 consequences over
   literal-linked columns — for the parity graphs exactly
   `Σ_cross i_e ≡ Σ_I c_v (mod 2)` (interior edges and `2·k_v` slack
   have even coefficients and vanish).
3. **Literal images**: a column is *image-determined* when its value is
   fixed under both phases of one Boolean — the fresh variable of a
   non-Bool `ite` over constant branches (`ite_defs`, recorded by
   `eliminate_nonbool_ite`), possibly chained through exact Euclidean
   `div`/`mod` by constants (the `mixedboundary` link).  Both images are
   evaluated exactly in checked `i128` Rust arithmetic (`div_euclid` /
   `rem_euclid`; zero divisor or a second distinct condition bails).
   Differing parities map the column to `b` or `¬b`; agreeing parities
   fold a constant into the rhs.
4. **Lemma**: `xor(l_1 … l_k) = c`, asserted as a ground unit lemma
   through the `arith_axioms` channel (`encode` + unit clause, scoped
   clause store + trail journal so `pop` retracts rows, lemmas and
   clauses in lockstep).

Timing: derived once per **assertion generation** (bumped by
`assert`/`assert_named`/`pop`), consumed at the next `check_core`
entry — never per theory check (the measured failure mode of attempt
#1).  All quantities are capped (rows/columns ≤ 1024, ≤ 256 lemmas,
width ≤ 256, evaluation depth ≤ 64); a cap tripping emits nothing.

The SAT-side xor machinery is *not* involved: the input's Bool xor
chains and the lemma are Tseitin-encoded with full equivalences, and
plain CDCL closes the parity contradiction through the shared `b_e`
literals (the phase-seeding xor slice only reads strict `2^(k-1)`
clause groups and neither needs nor uses this lemma).

### Measured outcome (this tree vs the finding, medium, seeds 0/1)

| instance | before | after |
|---|---|---|
| `parity-mixedboolint-unsat-s0` | timeout | `unsat`, 0.06 s |
| `parity-mixedboolint-unsat-s1` | timeout | `unsat`, 0.02 s |
| `parity-mixedboundary-unsat-s0` | `unknown` 1.2 s | `unsat`, 0.03 s |
| `parity-mixedboundary-unsat-s1` | `unknown` | `unsat`, 0.02 s |
| `parity-mixedboolint-sat-s0/s1` | `sat` 0.3 s | `sat` 0.6 / 0.2 s |
| `parity-incremental` (sat unsat sat unsat sat) | correct | correct |
| fuzzer `--seeds 2 --size medium --family parity` | 12/16 | **16/16**, 0 wrong |
| fuzzer small+stress-heavy / medium / large | 58/58, 56/58, 46/58 | 58/58, 56/58, 50/58 (0 FAIL/CRASH/GENFAIL; large gained the two mixed-unsat unknowns, same 12 honest timeouts as baseline) |

Gates on this tree: build/nextest 10557/10557, clippy/fmt/doc
`-D warnings` clean, z3 parity 170 entries / 0 mismatches (timings
unchanged within noise), 60 spot-checked industrial QF_LIA/UFLIA/
UFIDL instances (incl. mux-heavy `cmodelsdiff`) with 0 verdict changes.
Unit tests pin the GF(2) elimination shape, image classification
(ite link, div/mod chain, two-condition bail, zero-divisor bail,
negative-constant Euclidean semantics), literal folding, both fuzzer
graph shapes end-to-end (odd ⇒ unsat + lemma fired; even ⇒ sat and
re-asserting the lemmas keeps it sat), and pop-retraction.

Remaining (unchanged): the `large` mixed instances beyond ~60 vertices
still exceed a 10 s budget (`s0` solves in 6–10 s, `s1` times out) —
honest timeouts on bigger graphs, not wrong answers.

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
