# Handoff: the derivation stamps — design, the cure they complete, the hole that remains

**Date:** 2026-09-18 (evening)
**Landed by:** this session (my stamp design was swept into the arith
owner's `010f0e7e` from the shared tree; my follow-up landed as
`574a59b6`; binaries under `precompile/574a59b6/`)
**Read first:** `docs/studies/2026-09-18-rehome-wide-rational-blowup.md`
(the blowup study), the arith owner's
`docs/studies/2026-09-18-exact-arithmetic-wide-lp-handoff.md`.

## What the cure was (and is)

The rehome blowup's root shape: **`tighten_tableau_bounds` re-derives
every row's every directional bound on every theory round even when
nothing it reads has moved** — measured: 908 tighten calls, 10 879
passes, 2.1 M `BigRational` derivations for ONE assertion. The cure
that landed: **row-level derivation stamps** (`bound_ver` per variable,
bumped by every bound write/undo; `rows_ver` on every row
insert/remove/rewrite; `cross_ver` on crossing consumption; a
`derive_stamp` per basic variable; `propagate_bounds_in` skips a row
while its stamp is unchanged, and returns the STORE count as the
fixpoint signal instead of the derived count).

Measured effect: the rehome instance 564 s → 88 s, the delta-debugged
minimal 107 s → 9 s, the canary 1180 s → 79.8 s (test profile,
un-ignored in `574a59b6` with its own 4×60 s budget).

## ⚠ The stamps as landed are NOT value-identical — open, arith owner

`equal_pin_endpoint_reasons_cite_their_own_side` (their item-74 test)
**fails on `010f0e7e`** and passes at its parent `d75fa881`; at
`010f0e7e` with only the three skip `if`s neutralized (`if false && …`)
it **passes again** — the stamps are the cause. This is on `main` now.

Evidence gathered:
- Store-sequence divergence (env-gated `[store]` trace in
  `set_*_delta`): first divergence is a **reordering** — the no-stamp
  build applies 209 531 stores where the stamp build applies 127 140
  on the equal-pin input; the stamp build is missing *legitimate*
  stores (e.g. `U v100 -1/1` arrives at store 20 847 instead of 4 719),
  not just reordering them.
- The failing invariant downstream: `delta propagation mismatch`
  (`simplex/mod.rs`, the `debug_assert` in the snap-delta propagation —
  got ≠ want by 1/2) — the divergent trajectory reaches a state where
  the incremental delta update disagrees with exact evaluation. That is
  a **latent delta-propagation inconsistency** exposed by the new
  trajectory (any trajectory may reach it) — worth an item of its own.
- My stamp input-coverage argument has a hole I could not close in
  session: the stamp is `(rows_ver, cross_ver, max bound_ver over the
  row's variables ∪ {basic}, int_vars.len())`; every candidate I
  audited (weakened stores, branch-local bounds, pops, migrations,
  pivot rewrites, crossing consumption) routes through a bump, yet a
  derivation demonstrably misses. Suspects not yet excluded: an
  in-place `Bound` mutation (reason augmentation?) invisible to
  versions; an application-order sensitivity in `record_crossing`'s
  snapshot; a `slice6` store path that bypasses `note_bound_change`.

**Until closed, treat the stamps as a heuristic (trajectory-changing)
change**: every landing that keeps them needs the arith arc's
differential discipline, and `equal_pin` is the red canary on main.

## What landed in `574a59b6` (mine, verified)

1. **`find_fractional_int_var`'s `hi - lo` is CHECKED**: straddling
   ±2^62 bounds overflow `i64` (debug panic — the canary's debug run
   hit it under the new trajectory; release wrap silently misranked).
   Non-representable ranges now rank worst-of-class (any branch choice
   is sound). Trajectory-independent fix — the site was latent.
2. **The rehome canary un-ignored** (79.8 s; 4×60 s budget) — the
   always-on guard is back in the default suite.
3. Formatting + doc for the landed stamp surface.

Verification: wide+mixed differentials (3 rounds, 600 fresh instances
vs z3) — no verdict disagreements, no refuted models; parity 176/177
clean (clean-worktree build: the sat owner's in-flight
`nixie-sat/congruence.rs` fails the workspace compile in the primary);
perf gate PASS (1.018× vs the pre-item-77 base — includes the landed
item-77, not just this change); theories+solver suites green except
the pre-existing `equal_pin` (above).

## Environment

The sat owner's `nixie-sat/congruence.rs` WIP is a compile error in
the shared tree — scope verification to worktrees/private targets. The
arith owner's arc is ACTIVE on `docs/studies/2026-09-13-lia-wide-
literal-arithmetic.md` (items 74–77 landed today; item 76's design is
their next step) — the stamps' hole and the delta-propagation
invariant belong in their queue with this handover's evidence.

---

# RESOLVED (same night): three stacked defects, bit-identity proven

The open hole above is closed (`5f5dc847`). The skip-audit (re-derive
inside the skip, compare) plus store-sequence alignment isolated three
INDEPENDENT defects, stacked:

1. **Shared stamp namespace across derivation families** — loops (a)
   (direction-2 per-target) and (b) (direction-1 basic) derive
   different bounds for the same row; one key let (a) suppress (b).
   Families now keyed `(VarId, 0|1|2)`.
2. **Max-of-versions stamp** — a bump on any non-max variable was
   invisible (the audit caught `basic=100` skipped with a tighter
   `U -1` derivable); the component is now the SUM of the versions
   (bump-monotone).
3. **Last-writer-wins `pending_crossing`** — the exported conflict
   depended on which unchanged-input rows re-derived; every plant site
   is now first-writer-wins, a deterministic function of the input
   state (this re-baselines trajectories — a semantic change, sound
   both ways, screened by the differentials).

**Proof**: store sequences (env-gated `[store]` trace) cand vs
skips-neutralized: equal-pin 160 136/160 136 and rehome-original
690 070/690 070 — IDENTICAL. Perf: rehome 564 s → 34 s, minimal
107 s → 9 s, canary 1180 s → 55 s; 4637/4637 theories+solver green
(`equal_pin` back); differentials, parity, gate clean. The
delta-propagation debug_assert no longer fires.

Also: `fa0d59c9` repairs a one-line compile error the sat XOR landing
shipped on main (workspace was unbuildable at `570d8ad5`).
