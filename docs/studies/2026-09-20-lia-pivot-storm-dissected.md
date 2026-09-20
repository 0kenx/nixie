# The LIA pivot storm dissected: a faithful DdM mirror, the mopup architecture, and the i64 cliff

**Date:** 2026-09-19/20 (the arith eq-chain session, taking the
`2026-09-19-mbqi-closed-perf-attributed` handoff's ordered step 1).
**Input:** the standing perf table's QF_LIA −22 (32/60 vs z3's 54/60),
the attribution study's two mechanisms (the nec-smt deep-encoding class;
the CAV/SMPT integer-reasoning class), and the deep-split's second
pathology (the eq-chain pivot storm).
**Landed:** the Z3 `patch_basic_columns` integrality move (exact-read
discipline), Z3's per-firing Gomory cut budget, five unit pins.  **Table:
QF_LIA 32/60 (unchanged), QF_BV 50→51/60 (bench_11463 timeout→unsat),
zero disagreements.**
**Deliverable for the next session:** the mechanism is now measured
layer-by-layer with a pivot-exact reference mirror — the remaining gap is
*architectural* (CDCL-invisible branching) plus one arithmetic layer (the
wide store's per-op gcd), both with concrete entry points.

## The probe discipline that got there

`docs/studies/assets/ddm_mirror.py` is an exact-rational Python mirror of
nixie's `make_feasible` (Dutertre–de Moura tableau-rows mode: smallest-index
violated basic; entering = min (non-free dependents, column length, var);
snap-to-violated-bound; full substitution).  It reproduces nixie's pivot
sequence **pivot-for-pivot** (verified: identical (basic, entering) pairs
and row term-counts through pivot #62 on `CAV/45-vars/problem__022`), so
every behavioral question about the loop can be answered in seconds, with
state dumps, without touching Rust.

Key mirror corrections on the way (recorded so nobody repeats them): the
mirror must (a) propagate the entering move to dependent basics, (b)
include the leaving basic (`1/a_v · b`) in the solved form, (c) recompute
basic values exactly per pivot.  Without those it "converges" by accident.

## Layer 1 — the DdM loop itself is FAITHFUL (not the bug)

On `problem__022` (45 free integer vars, 40 dense ±1 rows): the mirror
needs **63 pivots** to reach LP feasibility — nixie does exactly the same
63.  z3's old simplex (arith.solver=2) needs 44 pivots + 4 branches on the
same instance; z3's default (solver=6) needs **2 patches**.  The
infeasibility sum *explodes* mid-pass (8 → 16 → 31 → … → 2727 by pivot
~58) — in the mirror too: that is *real* DdM behavior of this entering
rule on this family (collateral bound violations from large-θ repairs),
not an implementation defect.  Nixie's delta propagation, column index,
and assignment-vs-tableau consistency were all verified clean on the way
(`mismatches=0`, column drift 0, delta-verify silent).

**Consequence:** no fix at this layer.  (A coefficient-magnitude guard on
the entering rule was mirror-positive — 63→45 pivots, 55→41-bit entries —
but regressed two standing-table instances `sat→timeout` and was REVERTED;
see negatives.)

## Layer 2 — the coefficient blowup is legitimate, and it falls off the i64 cliff

By pivot 60 the mirror's tableau entries reach **55 bits** — determinant
ratios of dense ±1 minors (Hadamard allows ~2^110 at 45 columns).  This is
intrinsic to exact pivoting, not a bug: nixie's `Rational64` rows hold to
~62-bit entries and then the *intermediate* products overflow i64/i128 →
rows fall to the BigRational wide store — after the cut rounds' 10^6-scale
denominators join, entries pass i64 legitimately.  Once wide:

- every substitution pays num-bigint `gcd` per term (90 %+ of wall on
  both `problem__022` and `problem__011` in perf — `BigUint::gcd` +
  `biguint_shr2` ≈ 90 %),
- entries COMPOUND per wide pivot (204 → 217 → … bits), so cost per pivot
  grows monotonically until the pivot rate collapses (<10/s measured),
- `pop`-scoped B&B nodes re-derive the whole assignment (`crash_basis`)
  over the wide table — the invisible per-node cost.

z3 lives here in `mpq` comfortably; nixie's wide store is its mpq, but at
~1000× the per-op cost.  **This is the arithmetic-layer owning item.**

## Layer 3 — the mopup architecture: where the pivots actually come from

`problem__022`'s first check is 63 pivots (fine).  The death is what
follows inside ONE theory check (zero SAT conflicts, `--conflict-limit 1`
never returns): Gomory cut rounds (**24 × 16 cuts**, each round a full
re-feasibilization through the dirtier table), then an *internal* 20k-node
branch-and-bound (each node a scoped re-check), then 2^k free-var splits
recursing the whole machinery — **285 make_feasible invocations measured
in 8 s**.  Z3's `int_solver::check` cascade (`src/math/lp/int_solver.cpp`)
instead does ONE cheap move per call — gcd test → `patch_basic_columns` →
cube → HNF (period-gated) → DIO → Gomory **`get_gomory_cuts(2)` on a
period-4 gate** → `int_branch` — and its branching is CDCL-VISIBLE (branch
bounds become literals; learned clauses prune; z3-old's whole run on
`problem__022` is 44 pivots + 4 branches).

## What landed

1. **`Simplex::patch_int_columns`** (Z3 `patch_basic_columns`, the cheap
   integrality move): for each fractional integer basic, move a nonbasic
   integer column by the minimal integral δ (Z3 `get_patching_deltas`:
   `δ₊ = (−u·t·x₁) mod a₂` from the Bézout witness) so the basic lands on
   an integer — pure assignment updates, bounds preserved, no pivots.
   Runs before any cut machinery, **all-or-nothing with rollback**, and
   every value read is EXACT (`point_value_exact`) — the acceptance may
   never rest on a wide-stale assignment entry (that exact false-`sat`
   class is documented on `find_fractional_int_var`; the first version of
   this patch recreated it and the wide-literal pins caught it live).
   Unit-pinned: the congruence math, the genuine positive shape (3x+2y+1),
   the blocked/rollback shape, the no-fractional-coefficient decline, the
   fractional-nonbasic decline.
2. **`LIA_MAX_CUTS_PER_ROUND` 16 → 2** (Z3's `get_gomory_cuts(2)`): the
   per-check cut flood is now Z3-shaped.  Rounds stay 24.  Effect seen on
   the table: `Sage2/bench_11463` timeout → **unsat** (0 → 9818 conflicts
   — the theory hands control back to CDCL, which learns and refutes);
   no other cell moved, LIA holds 32/60, zero disagreements.

## Negative results (do not retry blind)

- **Entering-rule magnitude guard** (keep only |coef| ≥ max/8 candidates):
  mirror-positive (fewer pivots, smaller entries) but **regressed
  `slacks/35-26` and `v35_problem__031` `sat→timeout`** on the standing
  table (guard-off restores both).  CDCL is chaotic; the mirror's merit
  did not survive contact with the search.  Reverted.  A table-positive
  variant (factor 2? guard only at small max?) would need a powered
  matched-null campaign per `docs/BENCHMARKING.md`.
- **`LIA_MAX_NODES` 20 000 → 512**: converts solvable instances to
  `unknown` (the wide-literal bnb snapshot pin needs >512 nodes) — an
  internal budget cut does NOT pay the way z3's per-check budget does,
  because z3 hands off to a CDCL-visible branch and nixie's internal
  search has no clause learning to fall back on.  Reverted.
- **Loose patch acceptance** (basic-only reads, no rollback): "flips"
  `problem__022` to sat — but the acceptance rode a wide-stale fabricated
  read laundered through the model validator.  That is the false-sat
  class, not a win.  The honest (exact-read) patch does not flip 022.
- **`total_infeasibility` integer-truncating probes**: a probe that
  truncates fractional violations to integers reports `inf_sum=0` while
  the solver keeps pivoting — δ-level and fractional-level violations
  need exact reads even in throwaway instrumentation.

## The map for the next session (ordered)

1. **The CDCL-visible branch channel** — the architecture gap that owns
   the CAV/SMPT timeouts.  `TheoryResult` has no Branch move; the LIA
   branch happens inside the theory (`bnb_search`'s scoped bounds) where
   no clause learning can prune.  Z3's `int_branch` returns a branch
   literal to the SAT core.  This is a solver-core feature: a new
   `TheoryResult` variant (or a case-split lemma channel), the arith
   branch emitting `x ≤ k` literals, the internal B&B reduced to a dive.
   With it, z3-old's 44-pivot + 4-branch shape becomes reachable; the
   standing-table LIA class (17 of 22 losses are nec-smt/CAV/SMPT-shaped)
   is the payoff.  Probes: `problem__022`, `problem__011` (30 vars, z3
   solves with 1 patch — the patch-only route exists but nixie's LP vertex
   after 63 churny pivots is 39-var fractional and unpatchable; a
   warm-start/near-crash-basis LP point is patchable), plus the mirror.
2. **The wide-store arithmetic layer** — per-op bigint gcd on 200-bit
   entries is 90 % of wall once a search goes wide.  Options in rigor
   order: (a) fraction-free / integer-preserving row representation
   (Bareiss-style common-denominator rows; exact division instead of gcd
   per term — the textbook cure for exact simplex), (b) an i128-backed
   middle tier (entries to ~126 bits stay out of bigint), (c) a
   bits()-sized narrow gate on the wide-capture attempts.  Measured
   profile shape: `BigUint::gcd` + `biguint_shr2` dominate; every wide
   substitution is ~45 terms × (mul+reduce+add+reduce).
3. **Warm-start discipline for scoped checks** — `pop` conservatively
   marks the assignment stale; each B&B node then pays a full
   `crash_basis` re-derivation over the (possibly wide) table.  An
   incremental repair (only the out-of-window nonbasics move — `pop`
   already does this; make `check` trust it) removes the per-node O(table)
   pass.
4. **The deep-split flip** stays OFF: the eq-chain storm's root is items
   1–2 above, not the split; flipping `NIXIE_DEEP_SPLIT` now still buys
   honest-but-slow searches (the two independent probes' verdict stands).

## Adjacent observations

- `nixie-sat::watch_position_soundness::si2_b03m_is_not_unsat` failed
  ONCE mid-session under full-suite parallel load and passed on every
  retry (deterministic conflict budget 30k) — a load-sensitive flake
  worth a second look from the SAT arc; nixie-sat does not depend on
  nixie-theories, so it is unrelated to this landing.
- z3 counters on this family: `problem__011` = 1 make-feasible, 1 patch,
  1 patch-success (the patch route is real and cheap when the LP point is
  near the crash basis).  The DIO solver (`dioph_eq.cpp`, Griggio-style
  HNF over equalities) is NOT the mechanism on these instances —
  `arith-dio-calls 1` fires and no-ops on the equality-free CAV shapes.
