# Wide-row bound propagation (slice 6): built, measured, reverted — a negative result with fingerprints

**Status:** NOT LANDED (code reverted; this document is the record). 2026-09-15.
**Context:** the 09-15 continuation handoff's open item 2 — the unlanded
slice-6 rebuild. Read
[`2026-09-13-lia-wide-literal-arithmetic.md`](2026-09-13-lia-wide-literal-arithmetic.md)
items 34/36 (the mixed-magnitude twins) and Continuation 13's rebuild
description first; this session followed it exactly.

## What was built (the full design, verified to compile and run)

- **Exact both-direction derivations** through wide rows in
  `Simplex::propagate_bounds_in(&int_vars)`:
  - *Direction 1* (basic-ward): `derive_bound_big_parts` — the infimum of
    `basic = Σ cᵢxᵢ + k` from the needed endpoint of each variable's
    bounds, exact `(BigRational real, BigRational delta)` pairs.
  - *Direction 2* (variable-ward): `derive_var_bound_big_parts` — solve the
    row for one non-basic (`xᵢ = (basic − k − Σ_{j≠i} cⱼxⱼ)/cᵢ`), inf/sup
    endpoint per term sign, division mapping by `cᵢ`'s sign.
- **Exact crossing tests** (`cmp_bound_big`, lexicographic `(real, delta)`)
  against the stored opposite bound, planting `pending_crossing` — never on
  a weakened form.
- **Weakened-integer storage** (`weaken_int_bound`): non-narrowing bounds
  store `ceil/floor ± 1` with `delta = 0` on INTEGER basics only (both
  `narrow_pair` lessons encoded; sound for any delta sign — an
  infinitesimal cannot cross an integer).
- **Direction 2 through narrow rows** (capped at 8 terms) — because the
  atom-bound encoding hides pinned variables behind `s = var` slack rows
  (Z3's `lar_solver` gets this structurally with a row per variable).
- **Cadence**: `tighten_tableau_bounds` at every `ArithSolver::check` entry
  (the only place wide rows from earlier rounds exist), consuming the
  pending crossing immediately after its own tighten.
- **Guards**: branch-local bounds (`BRANCH_REASON` in primary or aux
  reasons) excluded from every derivation (the `gomory_cut` rule); stale
  pending crossings discarded before the tighten (reason ids RECYCLE
  across pops — see the traps).

## What it closed (momentarily)

- The **mixed-magnitude LRA unsat twin** (`v0 = 2^63·v1 + 1`, `v0 = 0`,
  `v1 > 0`, all Real): decidably `unsat` matching z3 — the chain was
  narrow-dir2 (pin `s = var5`'s variable) → wide-dir1 (`v1`'s exact upper
  `−1/2^63`) → exact crossing against `(0,+1)`.
- The LIA twin was already closed by the item-42 fix (exact
  floor/ceil branching) — verified on the parent binary; slice 6 added
  nothing there.

## Why it was reverted — two live false `unsat`s

1. **`wide_cancellation_value_is_decidable_sat`** (the slice-1 sat twin,
   `2^62·1 − 2^62·2 + 1`): `unsat` with **narrow direction-2 on**.
   Bisected precisely: removing the narrow-dir2 loop alone restores
   `sat`. Root cause NOT fully resolved; the crossing cited
   `[5,2,10,4,9]` with reason ids that RE-MAP across scopes (the id table
   truncates on pop) — at least one contributing bound was a
   case-split/disequality-half slack's (`s6 > 0`-shaped, reason 5) whose
   conjunction-validity at the consumption point could not be
   established. The stale-pending discard (consume only what this
   check's own tighten planted) did NOT cure it — the unsoundness is in
   a derivation path, not only the consumption.
2. **`wide_chain_is_decidable_sat_after_scaling`** (the c7 chain-sat
   twin, 40-deep `2·v + i64::MAX` recurrence): `unsat` with **only the
   wide propagation on** (narrow-dir2 removed). **CORRECTION
   (2026-09-16): the originally recorded "off by exactly 10^9 stored
   bound" fingerprint was FALSE** — the probed store
   `−8070450532247928831` is v3's exact true value; the "true value"
   it was compared against was a hand-arithmetic typo in this study's
   own session. The wide propagation's stores on the chain were
   correct as far as probed; the false `unsat`'s actual source was
   never identified (only the first ten stores were inspected). The
   decisive instrument the next attempt needs from the start: a
   DERIVATION AUDITOR — the chain has a known feasible model, so every
   sound stored bound must hold at it (`lower ≤ model(v)` /
   `model(v) ≤ upper`); any violating store printed with its full
   derivation chain localizes the unsoundness in one run.

## Traps recorded (each cost real time)

- **Endpoint orientation**: the infimum of a term `s·x` takes `x`'s
  LOWER bound when `s > 0` (not the upper — my first draft had it
  inverted; the mislabeled supremum then derived a backwards bound).
- **Reason-id recycling**: `ArithSolver::reasons` truncates on pop and
  ids are REUSED. Any conflict consumed outside the scope that planted
  it maps ids to WRONG terms — an invalid learned clause and a silent
  false `unsat` in release. Never consume `pending_crossing` late; if
  you must, discard-first (see the built design).
- **Branch-local bounds**: `BRANCH_REASON`-marked bounds are
  search-local; deriving from them leaks branch-scoped refutations to
  the root. The existing `gomory_cut` guard is the pattern; the filter
  belongs on ANY propagation that runs at final-check cadence.
- **Variable-identity archaeology is a time sink**: dump the reason
  table (`id → TermId`) and every var's bounds+reasons at the FIRST
  anomaly — the atoms' slack structure (`s = expr`, bounds on slacks,
  three same-form rows per atom with different reason keys) makes
  guessing identities hopeless.
- **The twins are not the test**: both momentary closures were verified
  against z3, and the false `unsat`s still shipped in the same tree. The
  wide regressions caught them — run the full wide suite (not just the
  twins) before believing a slice-6 build.

## What is worth salvaging verbatim

- `weaken_int_bound` (the ceil/floor ± 1, delta = 0 weakening) — sound
  standalone, unit-testable, the second `narrow_pair` lesson encoded.
- `cmp_bound_big` (lexicographic big `(real, delta)` compare) and the
  exact-crossing-never-on-weakened-forms rule.
- The per-final-check tighten cadence observation: wide rows only exist
  after earlier rounds' pivots, so assert-time propagation alone can
  never chain through them.

## The next attempt's entry points

1. Build the derivation auditor FIRST (see the correction above): a
   known-model instance (the chain; the cancellation twin) plus a check
   that every stored bound holds at the model — the false `unsat`'s
   source localizes in one instrumented run instead of ten probes.
2. The wcancel root cause (the disequality-half slack bounds' liveness
   through the crossing) and the chain's unidentified source are
   probably the same defect; instrument both with the auditor.
3. Keep the BRANCH_REASON filter and the discard-first consumption from
   the start; they are soundness requirements, not optimizations.
