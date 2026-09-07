# Mode-matched throughput follow-up (2026-09-07)

## Correction and pre-registration

The four-file, 40,000-conflict comparison in
[`2026-09-07-elimination-fill-cursors.md`](2026-09-07-elimination-fill-cursors.md)
does not establish the general distance to Kissat. The user's nine-file
completion runs at `0263862` show a substantially larger gap. They include
three UNSAT families and the long-running `noL_11_14` SAT trajectory; the earlier
study incorrectly described all four of its input families as SAT (`j3037`
is UNSAT). The cursor engineering comparison remains valid within its scope.

Supplied evidence: `/tmp/opencode/mini_bench_mode_matched_0263862.jsonl`
and its adjacent per-solver logs. Preserve these observations; do not rerun
their wall-only cells. Nixie is the `stats_solve` CaDiCaL preset. Kissat 4.0.4
uses `--probe=0 --preprocess=0 --factor=0 --substitute=0 --sweep=0
--vivify=0 --transitive=0 --backbone=0 --congruence=0`. These switches suppress
named mechanisms, but do not equate the solvers' search heuristics or work
per conflict. Their printed tick units are not interchangeable.

Before new measurements:

- Preserve `0263862` as baseline and its cached release binary. Use the
  byte-identified perf binary from source-equivalent `72720d9` for sampled
  attribution; verify counters against the supplied completion logs.
- First profile the default-seed completion runs on `break_unsat_06_07`,
  `circuit_48in64out`, and `noL_11_14`. These are attribution runs, distinct
  from uninstrumented throughput cells. Pin outside perf on CPU 10; retain
  raw samples and counters. No simultaneous solver measurements.
- New standing cells use hardware `instructions:u` (complete-work primary),
  `cycles:u`, `branches:u`, and `branch-misses:u`, seeds 1–10, and all eight
  nontrivial inputs. Preserve `sat_simple` as a smoke case, excluding its
  zero-conflict denominator. A 10,000,000-conflict resource cap replaces the
  previous 40,000 cap, with a 900-second emergency kill reported explicitly.
  Both reference arms (Kissat with the supplied switches; CaDiCaL default)
  use the same cap/seeds. Report distributions, per-family ratios, SAT/UNSAT,
  and decisive-at-cap counts. Unverified UNSAT observations are not stored
  as proof-verified verdicts; validate every SAT model against the input.
- Consult the result store before each run. Record every completed cell
  once, including bad timings. A process lock prevents overlapping runners.
  Preserve commands, binary hashes, input hashes, stdout and perf output.
- Any engineering candidate must preserve all search counters, verdicts and
  SAT models. Screen on the three profiled inputs before a ten-seed paired
  comparison using stored baseline cells. No tick or policy changes. Require
  at least 5% fewer cycles in the targeted component and neutral-or-better
  whole-run cost; a broad win requires clearing the repository's 5% band.
  Fresh SMT parity and the full validation suite are required before landing
  any shared solver change. Rejected experiments receive a recorded verdict.

## Candidate registered after the first profiles

`break_unsat_06_07` attributes 72.4% of sampled cycles to propagation;
`circuit_48in64out` attributes 60.9%. The replacement scan's assembly branches
on `v > 0` and then `v != 0` for every candidate literal. Kissat's `proplit.h`
first finds a non-false literal with one `v >= 0` exit predicate.

Try that exit shape while retaining Nixie's existing satisfied/unassigned
handling, normalization, literal selection, watcher ordering, and ticks.
This is a trajectory-preserving scan refactor, not the previously rejected
saved-position or watch-placement policies. Use the already registered
three-file completion screen, seed 0, before expanding the candidate.

### Scan candidate verdict: rejected

All three default-seed completion runs produced byte-identical stdout,
including the SAT models. The paired release-binary PMU screen was:

| input | instructions candidate/base | cycles/conflict candidate/base | branch misses candidate/base |
|---|---:|---:|---:|
| break_unsat_06_07 | 0.9865 | 1.0266 | 1.0716 |
| circuit_48in64out | 0.9884 | 1.0193 | 1.0313 |
| noL_11_14 | 0.9891 | 1.0404 | 1.0690 |

This is a rejection screen, not a multi-seed neutrality claim. Fewer retired
instructions did not turn into lower cycles on any of the three inputs;
branch misses increased throughout. The source refactor was removed. Do not
repeat this single-exit scan rewrite without a new mechanism addressing that
branch behavior. The baseline completion cells remain reusable.

Raw evidence and the discarded patch fragments are archived under
`precompile/0263862/benchmark/mode-matched-gap/`; the six PMU records are in
`precompile/0263862/benchmark/runs/mode-matched-throughput/`. The candidate
records are explicitly dirty and are excluded from committed-result reuse.

## Second candidate: subsumption variable signatures

The completed default-seed `noL_11_14` profile assigns 11.15% of cycles to
`subsume_round`; its connected-clause scan dominates that component. Z3
`src/sat/sat_simplifier.cpp:collect_subsumed1_core` rejects pairs whose variable
abstractions cannot be subsets before the exact subsumption test. Its
`sat_clause.cpp:approx` deliberately ignores polarity, so the filter also
admits self-subsuming resolution.

Try a 32-bit variable signature cached with each connected clause, computed
from the post-strengthening literal set. Keep liveness validation and the
`subchecks` increment before filtering so budgets and later opportunities
are identical. A rejected signature means some subsumer variable is absent
from the candidate; collisions only retain unnecessary exact checks. Keep
the current exact signed-mark scan for passing signatures. Connected clauses
are never subsequently strengthened in this round (each schedule id appears
once, and only the current candidate is rewritten); debug-audit the cache.
Clear all cached signatures with the existing per-round occurrence lists.

Use two 8-byte entries inline instead of four 4-byte ids to keep each empty
occurrence-list header the same size. Overflow entries double in width;
report this cost and reject if it overwhelms the component saving. Apply the
same three-file seed-0 screen and ten-seed confirmation bar. This candidate
is independent of the BCP scan refactor, which is removed before building it.

### Signature candidate screen: not qualified for landing

All three outputs remain byte-identical. The single-seed screen gives:

| input | instructions candidate/base | cycles/conflict candidate/base | branch misses candidate/base |
|---|---:|---:|---:|
| break_unsat_06_07 | 0.9962 | 0.9873 | 0.9783 |
| circuit_48in64out | 0.9783 | 1.0040 | 0.9334 |
| noL_11_14 | 0.9818 | 0.9872 | 0.9372 |

The filter lowers instructions and branch misses, but the whole-run cycle
screen does not establish a useful saving. It adds a cached-signature
invariant and doubles each connected occurrence's storage. It was removed
before full qualification; these three cells do **not** establish either a
multi-seed win or neutrality. The two targeted tests passed, including an
independent exhaustive exact-match oracle with hash collisions and a round
that must connect a post-strengthening signature. The discarded source/tests
and binary are archived as `stats_solve-sub-signature-pilot.patch` and
`stats_solve-sub-signature-pilot` under the experiment directory.

## Third candidate: repair scratch reuse

The normal-return allocation-reuse omission below is a simpler independent
mechanism. Restore the three scratch buffers on that return, just as the
empty-schedule return already does. At next entry, schedules and occurrence
lists are cleared and mark sizes reconciled by existing code. Every candidate
unmarks both signs before any round exit, so the reused mark array starts
zero. Test successful, repeated, budget-limited, and empty-schedule returns;
preserve signatures' original absence and the original occurrence width.

Use the same three-file seed-0 completion screen (reuse baseline cells),
then ten seeds on the whole eight-file panel. No tick, scheduling, or clause
mutation change. It must satisfy the existing component/whole-run bars and
fresh SMT correctness gate. Unlike a cached match summary, this restores the
already documented lifetime of existing scratch data.

### Scratch-return candidate verdict: rejected

The regression test passed all four return paths, and all three completion
outputs were byte-identical to baseline. Nevertheless the independent PMU
screen gave:

| input | instructions candidate/base | cycles/conflict candidate/base | branch misses candidate/base |
|---|---:|---:|---:|
| break_unsat_06_07 | 0.9997 | 1.0738 | 0.9968 |
| circuit_48in64out | 0.9989 | 1.0932 | 0.9969 |
| noL_11_14 | 0.9996 | 1.0281 | 0.9991 |

It fails the no-obvious-regression screen, so the production change and its
test were removed. The existing reuse comments do not describe the normal
return's actual allocation lifetime; simply making that lifetime persistent
is not an established optimization. Retaining buffers also changes heap
placement and retained memory, even with identical logical state. The screen
does not isolate which of those effects caused the cycle result. Do not
reinstate this three-assignment change solely from the misleading comment.
The discarded binary, patch/test, and complete PMU records are archived.

## Attribution notes

All three sampled baseline completion runs exactly reproduce every diagnostic
line in the supplied logs (models were additionally requested). Propagation
shares are 72.41% (`break`), 60.90% (`circuit`) and 61.80% (`noL`); subsumption
shares are 3.04%, 16.32% and 11.15%, respectively. The `noL` attribution run's
tail overlapped a 16-second release build pinned to CPUs 0–1. It remains an
approximate hotspot map, and will not be used as a quiet paired component
measurement. All PMU throughput screen cells ran without our builds or other
solver measurements overlapping.

Source review also found that `subsume_round` returns scratch buffers to
`subsume_scratch` only on its empty-schedule early return; the normal return
drops them, despite the reuse comment. This is a separate allocation-reuse
candidate; it is not bundled into the signature-filter experiment.

Status: attribution and corrected standing measurements in progress.
