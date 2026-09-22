# Native sequence row-copy experiments: neutral

**Verdict: no solver change landed.** Three mechanical candidates failed the
preregistered >5% history-family bar. The largest-case improvement reached
8.4%, but the family remained neutral at 3.1%. Reproduction patches and all
case distributions are retained below; do not repeat these experiments as
unmeasured optimization proposals.

## Pre-registration

Baseline: `6925082367c2d34390616dd7b6efa4ed5f1f87a3`, cached release
SHA-256 `e4e76cbc4f6f8c5e00d13553089f4b6f4336b4f77679b299c9cb4f187f25c2bf`.
Its saved history-512 instruction profile attributes 32.10% to
`propagate_bounds_in`, 10.86% to small-vector copies and 4.69% to
`TableRow::term_vars`. The narrow direction-2 selector copies every row's
variable list to obtain its length, even when both eligibility gates are
false. These reads do not materialize or mutate rows.

Skip that selector's scan when both gates are false; when enabled, read
stored term counts directly in all three row representations. Preserve
the gate values, per-call environment reads, row order, exact derivations,
stamps, scope state and model validation. This is mechanical work removal,
not a propagation or search policy change. Z3's static matrix similarly
gets row cardinality directly from stored row size
(`src/math/lp/static_matrix.h:217`); CVC5 similarly uses
`basicRowLength` / `getRowLength`
(`src/theory/arith/linear/tableau.h:125-128`).

Accept a >5% history-family instruction reduction with no lost decisive
results, complete history-512 diagnostic trace identity, and all required
correctness/performance gates. Reuse the baseline's 220 cells and original
Z3 4.16.0 cells; measure each candidate cell once with the existing 22-case,
ten-requested-seed runner, CPU 6, user instructions and six-second cap.
Requested seeds still do not reach the native scalar child; report this
limitation, not ten independent search trajectories. Preserve all results,
including a neutral or negative outcome. Check the enabled selector paths
as well as the default path. Any trajectory-changing work requires a
separate matched-null experiment and is outside this change.


## Soundness audit

For every `Lin`, `LinNoInt` and `Int` row, the previous `term_vars` maps
one entry to one variable without filtering; its length is exactly the
stored term-list length. This equivalence even holds for noncanonical
lists: the new accessor does not rely on zero elimination or uniqueness.
It borrows the row and does not call `row_lin`, normalize coefficients,
or change the integer-row cache. The exhaustive match covers all variants.

When both policy booleans are false, the old filter accepts no entries;
the replacement empty vector is identical and makes no table reads.
Otherwise the same iterator, predicate, cutoff (eight), and collection
order are used. Both environment probes retain their original frequency
and short-circuit conditions. In particular, this does not cache policy
flags or enable narrow direction-2 in ordinary non-wide states.

All subsequent materializations, stamp checks/writes, bound derivations,
reason collection and fixpoint updates are unchanged. The new accessor
has no scope state. Pop continues to restore bounds and rows through the
existing trails. AST/model traversal and independent sequence validation
are unchanged. Existing arithmetic representation, bound derivation,
wide-row and rollback regressions exercise these paths; fresh full-suite,
reference parity and explicit enabled-policy comparisons verify integration.


## First experiment: neutral

The scan-only binary (`f9e236771503f2a215698a5c73f68e41608f05254d1732e566f99e5fd37315a9`)
completed all 220 cells (190 decisive, 30 Unknown, no wrong/error/timeout).
Paired with the baseline, history-512 used 7.699B instructions (ratio
0.95054), history-128 84.057M (0.98164), history-32 13.078M (0.99500),
and history-8 5.173M (0.99688). History-family ratio 0.98084 and whole-corpus
ratio 0.99727: neutral, below the preregistered bar. Do not cite this
scan removal alone as a material optimization. All 264 paired diagnostic
traces over 66 sequence/arithmetic cases and four gate configurations were
identical, including row-cutoff boundary and wide-coefficient cases.

A follow-up 384-sample profile suggests that the row-variable-list copy
ceased to dominate, with small-vector copying at 10.42% and bound
propagation at 33.59%. This diagnostic capture has one throttle/unthrottle
pair (no lost events), so its percentages are indicative only; it is not
complete-work cost evidence. The measured perf-stat cells are separate,
valid unscaled counters. The stack unwind is incomplete; it cannot attribute all
small-vector copies to individual callers. Inspection finds that both
bound setters clone the previous bound into the undo trail immediately
before overwriting and dropping the original. Try moving the old bound
into the trail with Option::take, preserving trail entries, reason ordering,
all exact values, and the subsequent notification/crossing calls. This
adds no policy or cache. The same >5% history-family bar and verification
requirements apply to the combined candidate; retain both distinct binaries'
measurements without replacing cells.


The bound move follows Z3's trail-before-install contract
(`src/smt/theory_arith_core.h:2475-2476`, restoration at 3420-3440).
Nixie still validates/deduplicates reasons before touching the live slot,
ensures the variable exists, pushes the same None/Some undo variant, then
installs the new bound before notifications or crossing checks. `take`
transfers the complete old bound (including its wide Arc and reason vector)
instead of cloning and dropping it. No solver callback observes the
momentarily empty slot. The allocation failure boundary remains process
allocation failure; no recoverable solver path is inserted between take
and install. Pop consumes the same values in the same order.

The new nested-scope regression covers narrow and beyond-i64 values,
strict rational deltas, inline and spilled auxiliary reasons, rejected
empty-reason updates, crossed windows and restoration to absent bounds.
It compares complete bound snapshots after each pop, including all reasons.


## Second experiment: neutral; bound move removed

The combined scan/bound-move binary
`29b40c13c6b36fca7e65e3f1bcdedcac5d2e6fa05f1f3f2abe8c6cb1af4fd5d2`
again completed 190 decisive / 30 Unknown cells without errors, wrong
answers or timeouts. History-family ratio was 0.98018, whole-corpus
0.99263, and history-512 0.95089 (7.702B instructions). Moving old bounds
does not explain the remaining copy cost. The focused regression passed,
but the production change and its new test were removed; retain the patch
and measurements as the negative finding rather than adding neutral scope
changes to the final solver.

## Third experiment pre-registration

Inspection of the exact hot SmallVec instantiation and its call sites
points to two remaining copies in bound propagation: the column's Arc
contents are deep-copied solely to release a borrow, and the entire
pending propagation vector is cloned before individual bound values and
reasons are cloned again into the setter. Borrow an Arc clone of the
column instead, and index the unchanged pending vector while cloning only
the values passed to the setters. Neither inner update path mutates its
source list. This preserves list order and contents, materialization and
stamp behavior, exact fallback, and full reasons. Keep the same acceptance
bar and trace/gate requirements. The scan-only binary is the control for
attributing incremental cost; the previous landed binary remains the
reported baseline. No search policy or seed behavior is changed.


The column borrow starts only after stale-state repair, bound snapping and
checked delta formation. Its loop calls `row_lin` (tableau materialization),
checked arithmetic and immutable exact expression evaluation, then updates
assignments or their staleness flag. None can change `columns`; therefore
holding one extra Arc reference cannot trigger copy-on-write elsewhere.
The reference is dropped before returning. An absent column still performs
no dependent updates, and every stale/wide entry still marks the assignment
stale. No entry is dropped or reordered.

The pending-bound loop uses the same initial length and order. Its setters
can register variables, update/trail bounds, snap assignments, rederive or
migrate rows, and record crossings, but none modifies `propagated`. Existing
bounds remain readable through `get_propagated` after application. A focused
extension of the multi-hop explanation regression checks that the pending
result retains every antecedent after application; the existing conflict
check independently verifies the downstream explanation. The wide delta,
exact retry and stale-column regressions continue to cover all inner paths.


## Third result and landing decision

The scan-plus-borrowed-lists binary
`eae12c4393e5480b6db06b141e404dc7562604b6e282159adb10e77e6b5b3d58`
completed 190 decisive / 30 Unknown cells, with no wrong answers, errors,
timeouts or invalid counters. It uses 7.417B instructions on history-512
(0.91562 of baseline), 83.189M on history-128 (0.97147), 13.064M on
history-32 (0.99395), and 5.165M on history-8 (0.99552).

| Candidate | History-family ratio | Whole supported corpus | History-512 ratio | Verdict |
|---|---:|---:|---:|---|
| Skip disabled scan / direct row length | 0.98084 | 0.99727 | 0.95054 | Neutral |
| Scan + move previous bounds to trail | 0.98018 | 0.99263 | 0.95089 | Neutral |
| Scan + borrow column/pending lists | 0.96859 | 0.99590 | 0.91562 | Neutral family; below preregistered bar |

Ratios are geometric means of paired whole-process user instruction
counts. The largest-case gain in the third arm is real under an identical
search, but does not meet the family-level acceptance criterion. **Remove
all three production experiments and their experimental test changes.**
The landed changes are this report, reproduction patches, distributions,
and the benchmark index link. Native support, soundness boundaries,
model validation and solving policy remain those of the baseline.

Across three distinct candidates there are **660 new benchmark cells**:
570 decisive and 90 honest Unknown, no wrong/error/timeout. All historical
Nixie/Z3 cells were reused. This is the existing restricted finite-shape
corpus, not evidence for a general sequence procedure. The original Z3
4.16.0 timeout/coverage limitations remain; Unknown is never a match.

The first and third candidates each have **264 byte-identical paired
traces**, across 66 sequence/arithmetic cases and four propagation gate
configurations. Those cases include the 22 native corpus members, 12
bound cases with seven/eight/nine x variables plus y, and narrow
or beyond-i64 coefficients, and the 32 QF_LIA/QF_LRA parity cases. The 12 generated
bound cases were also checked by Z3 4.16.0. The third comparison reuses
all first-comparison baseline traces. Complete history-512 traces retain
462,672 decisions, 671 conflicts, and 1,536 variable legend lines, SHA-256
`6749ea7391c6b7128e47a2e81e923ab6635d76d37434f5ae5246e58dd72284d5`.

This is mechanical ownership/read-cost work, not a search-heuristic
comparison; structural equivalence and full trace identity support that
claim. The ten requested seeds remain repeated native-child default
trajectories, not independent random replications. No matched-null search
merit is claimed, and no post-hoc threshold change justifies landing.

## Reproduction and retained evidence

The three [patches and per-case distributions](assets/2026-09-22-sequence-row-copies/)
are committed. Apply each patch independently to a throwaway worktree at
`69250823` (first/second) or `40851e3e` (third); never stack the patches.
The relevant arithmetic sources are identical at both revisions. Build
with `CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4
CARGO_PROFILE_RELEASE_STRIP=none cargo build --release` and freeze the
executable before running other builds. Use
`bench/native_sequences/compare_optimization.py` with the original
`3a42cb2d` result directory, then join saved cells to `69250823`'s
`native-sequences-integer-evaluation/comparison` by case and seed.

The newly landed heap commit `40851e3e` was integrated before the third
build. Its cached CLI hash is identical to `69250823`'s (`e4e76cbc...`), so
that integration does not confound the CLI comparisons. This identity says
nothing about the standalone Context-based parity executable.

Raw benchmark cells, baseline trace references, candidate traces, input
files, profiles, binary hashes, prototype executables and verification logs
are retained under the report commit's
`precompile/<sha>/benchmark/native-sequences-row-copies/`. Prototypes live
inside that experiment directory and are clearly rejected; they are not
installed as the commit's solver executable. The benchmark schema does not
claim native UNSAT proof certification. Reuse recorded cells; do not rerun
one and silently replace it. The sampled profile has limited stack unwind
coverage, so caller attribution above uses inspected source/call sites,
not a claimed complete sampled call graph.


The final candidate profile has 370 samples at a 20M instruction period,
with zero lost/throttle/unthrottle events. `propagate_bounds_in` remains
32.97%, SmallVec slice copies 7.03%, hash-map insertion and simplex pop
5.41% each. Removing these specific list copies does not remove the
remaining repeated propagation/rollback work. A future attempt needs a
separately justified reduction in that work; this study is not evidence
for changing propagation scheduling or omitting derivations.


## Verification of the documentation-only landing

After removing the rejected production/test edits, the all-feature build
passed and the full workspace/all-feature nextest suite passed **12,216
tests, 17 skipped** (876.180 seconds of tests). The longer scope convergence
regression passed in 245.281 seconds. Tests ran on P-cores 0–7 with two
workers; no timeout or test budget was widened.

The experimental release builds and focused checks above are evidence for
the experiments, not full landing certification of those rejected patches.
The full suite here checks the unchanged solver plus this report. The
subsequent `cb50c87e` integration added only heap benchmark/report files;
its four Python tests passed and no Rust verification was invalidated.

For the unchanged solver, reuse the recorded Z3 **4.16.0** parity at
`40851e3e`: 176 Correct, one Inconclusive (`array_unique`, Z3 Unknown), zero
Wrong/Timeout/Error. The byte-identical CLI retains the recorded general
perf-gate PASS (conflict and decision ratios 1.000 over nine nontrivial
cases, three external verdicts unchanged) and the standing instruction
ratio 1.0011 over 12 cells. Those existing benchmark cells are not rerun.
These are explicitly inherited baseline gates, not newly executed gates
for a rejected candidate or evidence about its unmeasured search paths.


Clippy (`--all-features --all-targets -- -D warnings`), formatting, and
rustdoc with warnings denied passed. Separate doctests passed **114** with
31 ignored; the explicit native-sequence group passed **14** tests,
including the 214-case Z3 4.16.0 differential. These checks ran on the
unchanged production source after all experimental edits were removed.

The explicit `pete_cxs_bp_is_unsat_on_every_trajectory` congruence canary
also passed (129.303 seconds). All prescribed non-benchmark checks are
green; reused parity/performance evidence is identified separately above.
