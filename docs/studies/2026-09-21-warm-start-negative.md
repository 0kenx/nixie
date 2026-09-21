# Warm-start scoped checks: closes NEGATIVE — the per-node re-derivation pass no longer exists

**Date:** 2026-09-21 (morning).  **Item:** the pivot-storm addendum's map
entry 3 — "`pop` conservatively marks the assignment stale; each B&B node
then pays a full `crash_basis` re-derivation over the (possibly wide)
table.  An incremental repair … removes the per-node O(table) pass."
**Verdict: do not build it.**  Measured on the current tree (branch
channel default + Bareiss + fold), the re-derivation path is not a cost
center on either named probe — the premise does not hold anymore.

## The measurement (symbolized release, 12-25 s windows)

- `CAV/30-vars/problem__011` — `sat` at 0 conflicts in 18.4 s (the
  probe: "z3 solves with 1 patch").  Self-time: `pivot` 39.0 %,
  `checked_ratio_i128` 21.9 %, `gcd_i128` 17.0 % — the fraction-free
  substitution machinery is ~78 % of wall.  **`crash_basis` 0.00 %,
  `update_assignment` 0.03 %, `make_feasible` 0.34 %,
  `find_violating` 0.45 %.**
- `CAV/45-vars/problem__022` (the churn probe): `gcd_i128` + `pivot` +
  `checked_ratio_i128` dominate (35/14/9 %); `make_feasible` 0.30 %,
  `find_violating` 0.36 %, re-derivation absent from the visible mass.

## Why the premise expired (the layers that fixed it for free)

1. **`pop`'s re-snap already skips the flag for relax-only pops** ("no
   flag when nothing moved, keeping the incremental maintenance for the
   common relax-only pop") — and the B&B's branch bounds
   (`take_branch`) go on **BASIC** variables (`find_fractional_int_var`
   branches fractional *basics*), which the re-snap logic skips
   entirely: the per-node pop restores basic bounds, moves nothing, and
   never flags.
2. **The pivots maintain the assignment incrementally** (the snap-delta
   propagation with exact retry), so the vector stays current through
   the scoped search.
3. What remains of `on_nonbasic_bound_change`'s wholesale path fires on
   nonbasic bound assertions at the ATOM level, not per node — off the
   hot loop.

The addendum's hypothesis was written 2026-09-20 (pre-Bareiss,
pre-channel); the intervening landings retired the cost without
targeting it.

## What actually owns the two probes now

Both are **substitution-volume** cells: ~78 % of wall in
`pivot`+`checked_ratio_i128`+`gcd_i128` — the fraction-free machinery's
write-back floor (per-term canonical `Rational64` output: one
`checked_ratio_i128` gcd per term, plus the row chain) multiplied by
the pivot COUNT.  The write-back share is the known canonical-output
floor (see the Bareiss study); the count is the architectural item
(the internal B&B's node volume vs z3's one-cheap-move-per-check
cascade — the pivot-storm study's Layer 3, still open, arithmetic-arc
coordination required).

Side observation for whoever profiles 022 next: `gcd_i128`'s self-time
share on the 12 s window moved ~9.9 % → ~35 % between two adjacent
trees (cf8e497c vs the J5-b2 tree) with no simplex-side landing in
between — plausibly a phase-mix shift from the arith-solver changes,
possibly sample noise; not chased (the absolute picture — substitution
dominates — is stable).

## The trap

The mirror (`ddm_mirror.py`) models pivot sequences, not the
assignment-staleness lifecycle — an item like this one can only be
sized by a PROFILE on the current tree, and the addendum's
layer-by-layer attribution ages as adjacent landings land.  Re-profile
before building anything from a stale map entry; this session's
one-build cost bought the negative result that saves the next agent
the build.
