# The `NIXIE_DEEP_SPLIT` audit — superseded by the assert-fold, measured wall-negative again, deleted (2026-09-21, night)

**Date:** 2026-09-21 (night).  **Item:** an unowned hygiene audit in
the surgery-deletion precedent's shape (`52bfea70`): `deep_split`
(default-off since its 2026-09-19 landing, whose own study recorded
"it currently buys no verdict — the unknown→timeout conversion is
strictly worse wall-wise") against the tree the assert-fold campaign
built on top.

## The audit

`deep_split`'s depth-guard arm sat between the fold rescue
(`deep_fold_rescue`) and the honest refusal: armed, it split
genuinely-deep non-foldable terms into shallow equi-satisfiable
pieces and searched them.  Two questions on the current tree
(`precompile/bf938922`):

1. **Is its flagship class still its own?**  No — the nec-smt deep
   members it was built for are owned by the DEFAULT assert-fold
   (refute-only, `661fb774`): 69 members recovered outright, and of
   the five large non-folding members one now solves via the fold
   (`checkpass` `unsat`) — a verdict `deep_split` never produced.
2. **Does its residual class (deep non-foldable) gain anything
   armed?**  No — measured both arms: the five large members (4 same
   `unknown`, 1 wall-worse timeout); the med class (24 sampled):
   **18/24 convert honest instant `unknown`s into 15 s+ cap-timeouts,
   zero verdicts gained, 6 bit-identical**.  Its own negative
   verdict, re-measured post-fold with a stronger ratio.

## The deletion

`deep_split.rs` (245 lines), both depth-guard arms in `encode.rs`
(`assert` + `assert_named` — the ladder is now fold-rescue → honest
refusal), the `mod` declaration, and the `encode_guards.rs` doc
reference.  Default-path behavior identical (the arm was behind an
env that defaulted off).

## Verification

* Workspace suite `--all-features`: 12 122 run, all green after the
  documented `-j1` flake-class re-run (10/10).
* Perf gate (BASELINE `bf938922`): **PASS — 1.000/1.000, wall 0.94**.
* Z3 parity (z3 4.16.0): **176/177, 0 wrong-verdict pairs** (the
  standing inconclusive).
* clippy/fmt clean on every touched file.  (Main currently carries 5
  clippy warnings in `simplex/tests.rs` — the arith owner's in-flight
  Phase-3 work, not touched here.)
* Deep-member spot check on the deletion binary: the default answers
  are unchanged (`checkpass` `unsat` via the fold; the non-folding
  members' honest `unknown`s intact).
