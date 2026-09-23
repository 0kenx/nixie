# Order-preserving theory-reason deduplication

## Preregistration (2026-09-23)

The larger-case CP investigation identified the growing explanation-clause
vector's duplicate scan as about 30% of sampled instructions in sparse 16x32.
Replace only that membership test with a local variable set for explanations
longer than eight premises. Eight follows the existing inline SmallVec capacity;
retain the allocation-free scan for short reasons. Do not tune this threshold
using the measurements. Keep first occurrence by variable, polarity, propagated
variable exclusion, literal order, watches, LBD, proof output and search counters.
The set is never iterated and does not survive the call or introduce scope state.

This is a representation change, not a heuristic or shortened explanation.
A separate trajectory-perturbing null would answer a different question; require
exact baseline/candidate transcripts and exhaustive old/new clause construction
checks instead. Any trajectory change falsifies that classification and blocks
landing until understood. Independent model, callback and proof checks stay on.

Freeze the current main source `34285f11` as the Nixie baseline, using the
unchanged external default-feature release driver/profile/lockfile from the
preceding CP studies. The installed Z3 4.16.0 binary remains the external
reference. Use the current reference harness without changing its hash.
Existing matching Z3 cells are reused; never refresh a cell for a nicer number.
Whole-process user instructions pinned to CPU 0 are the primary metric, with
at least 99% counter coverage and the existing 120-second external cap.

Selection: seeds 10..19, ordinary and certified modes, two push/check/pop
rounds; all seven families at 4x4 and 8x16, and unknown/present/sparse at
16x32 and 32x16. Confirmation: fresh seeds 20..29 over the same grid. Report
family/shape distributions, solved-at-cap outcomes, current/previous Nixie
and current/Z3 ratios separately. The target regime is already solved below
the cap; no solved-count improvement is expected. Require more than 5% lower
instructions on sparse 16x32 in both grids, no per-family/shape regression
beyond 5%, identical Nixie transcripts and all checked verdicts retained.

Short-reason/SMT protection includes the small CP grid, full release workspace
suite and doctests, all-feature build/Clippy/docs/formatting, the installed-Z3
parity suite, and the deterministic perf landing gate. The latter's counters
do not measure this scan's cost; the instruction experiment does. All Rust
builds and checks use release mode. The existing complete CP proof chain and
push/pop oracles must still pass. No variable-duration/demand or stronger
cumulative propagation feature is part of this change.
