# Elimination occurrence lists: absolute fill cursors

**Landed:** `72720d9`. About half the sampled elimination cycles and 12.9%
fewer whole-invocation cycles/conflict on si2-b03m. The four-file aggregate
is 4.0% lower, **neutral** under the repository's ±5% rule.

## Pre-registration

Baseline solver source `482b806` (later commits `4a88b3c` and `0970b39`
only record rejected experiments). On si2-b03m, `elim_round` accounts for
21.2% of cycle samples; its CSR connection loop accounts for over half of
those. The hottest instruction increments the per-literal relative cursor.
Every occurrence loads a previous span boundary, loads its relative cursor,
adds them, stores the clause id, and increments both that cursor and an
occurrence count already computed by the sizing pass.

Store the cursor as an absolute live end instead. `connect` indexes directly
with it and increments it. Span boundaries remain immutable; every other
operation derives live length as `end - start`. No extra storage, new unsafe
code, clause ordering change, or policy change. Keep the sizing pass's
occurrence counts instead of clearing and recomputing them in the connect
pass. All retire/mark effects are deferred until both passes complete, so
their clause and assignment snapshots are identical. Retain exact semantics
of partial construction, rewrite, clear, and primary/overflow swap removal.

Use the same baseline PMU cells from the blocker-batching study, all four
available competition CNFs, 40k conflicts, CPU 10, seeds 0–9. Primary metric
is whole-invocation user-mode instructions; require cycle confirmation using
cycles/conflict. Alternate paired arm order by seed and reuse existing
cells. A one-seed screen can reject, never establish an improvement.
Require byte-identical printed counters, ticks, verdicts and SAT models.

Landing bar: geometric-mean cycles/conflict at least 5% lower, instructions
non-increasing, no family over 5% slower. If the whole-run effect is neutral,
the documented component-improvement rule requires a measured >5% reduction
in elimination itself and evidence for every path that executes it. No
changed search trajectory can be called an engineering improvement.

Extend the occurrence-list reference differential to cover empty reads
between layout and connect, interleaved construction of different lists,
and checking every list after each mutation (including the final span).
Run full workspace verification, doctests, SAT differential/model checks
and Z3 parity before a source landing. Report missing corpus inputs and
pre-existing failures explicitly. Kissat/CaDiCaL context uses the same
available files/seeds/cap, separately from the trajectory-paired control.

## Committed-binary result (ten seeds per file)

Baseline `482b806`, treatment **`72720d9`**, independently rebuilt from the
clean committed tree. The following figures use the treatment's clean
result-store cells, reusing the original baseline and reference cells.

Every one of the 40 pairs has byte-identical diagnostic output, including
conflicts, decisions, propagations, restart counts, learned/deleted clauses,
subsumption/elimination counts, ticks, verdict and any printed SAT model.
All 14 SAT models per arm pass independent checking against the original
CNF. The other 26 cells hit the conflict cap; they are not counted as solved.
All four input families are satisfiable, so these are not UNSAT performance
measurements.

Ratios below are treatment/baseline geometric means over paired seeds.
The baseline distribution is amortized user-mode cycles/conflict; it includes
parsing, preprocessing, search and cleanup.

| file | baseline min / median / max cycles per conflict | instructions T/B | cycles/conflict T/B | solved at 40k B/T |
|---|---:|---:|---:|---:|
| j3037 | 434,892 / 458,346 / 475,933 | 0.9992 | 1.0170 | 0 / 0 |
| circuit_48in | 116,669 / 124,887 / 133,238 | 0.9818 | 0.9689 | 0 / 0 |
| constraints_17 | 935,269 / 1,031,964 / 1,099,963 | 0.9875 | 0.9876 | 5 / 5 |
| si2-b03m | 243,177 / 277,365 / 316,599 | 0.9556 | **0.8714** | 9 / 9 |
| equal-family aggregate | | **0.9809** | **0.9596** | **14 / 14** |

The aggregate is **neutral under the ±5% rule**, not a general solver
speedup claim. si2-b03m's improvement is consistent: its ten ratios range
from 0.8134 to 0.9107. No family regresses beyond the neutrality band.
Individual cycle outliers are retained, including j3037's maximum 1.1751
and constraints_17's maximum 1.2000; no timing-based trimming or reruns.

### Component attribution

Separate paired cycle sampling (`perf record -e cycles:u -c 5000003`, pinned
CPU 10, seeds 0/4/9) stays below the kernel's 2000-samples/second ceiling.
Sum sample periods attributed to `elim_round`; these are estimates of
component cycles, not exact PMU function counters.

| si2 seed | baseline elimination sampled cycles | treatment | T/B |
|---|---:|---:|---:|
| 0 | 2.275 G | 1.070 G | 0.4703 |
| 4 | 1.895 G | 0.945 G | 0.4987 |
| 9 | 1.750 G | 0.845 G | 0.4829 |

Elimination falls from about 20–21% to 11% of whole-run samples; its own
sampled cycle cost roughly halves. This clears the pre-registered component
bar while the aggregate remains neutral. Unlike the earlier PGO result,
this removes a dependent cursor load/address calculation and redundant
count update at the measured stall site, and converts to actual cycles.

The full verification gates below passed before the source landing.
The representation is private to `RoundOccs`; every accessor preserves the
same primary/overflow sequence, and the independent vector-reference test
checks all lists throughout construction and mutation. The counting and
connection passes see identical immutable clauses and assignment snapshots;
retire/mark effects occur only after both finish. This argument also applies
under attached proofs and under frozen-variable CDCL(T), which execute the
same round; these paths additionally require their integration/differential
checks before landing.

### Reference context

Kissat 4.0.4 (`8af8e56`) and CaDiCaL 3.0.1 (`68fdd30`), all four files,
seeds 0–9, CPU 10, the same 40k conflict cap. All 11 Kissat and 19 CaDiCaL
SAT models were checked against their original CNFs. Entries below are
medians of amortized cycles/conflict, not pure conflict-analysis costs.

| file | Nixie baseline | Nixie cursors | Kissat | CaDiCaL |
|---|---:|---:|---:|---:|
| j3037 | 458,346 | 460,563 | 389,404 | 342,485 |
| circuit_48in | 124,887 | 122,921 | 104,304 | 66,601 |
| constraints_17 | 1,031,964 | 989,238 | 657,217 | 723,689 |
| si2-b03m | 277,365 | 245,784 | 309,697 | 337,285 |

Across the 40 paired instance/seed rows, geometric-mean Nixie/Kissat
cycles/conflict changes from **1.1332 to 1.0874**. This is descriptive
context on four available files, not a competition-wide standing claim.
Searches differ: for example, median constraints_17 conflicts are 36,788
for Nixie, 39,362 for Kissat, and 7,075 for CaDiCaL. Solved-at-40k counts
are Nixie 14/40 in both arms, Kissat 11/40, CaDiCaL 19/40. These are
conflict-budget scores, not a wall-clock competition score.

## Measurement audit

A user interruption left the first runner alive. A mistakenly started
second runner reused the completed cells, then overlapped the treatment at
seed 6 and both arms at seed 7. Both runners were stopped. All 12 potentially
affected cells were removed from the reusable result-store directory and
archived under `precompile/482b806/benchmark/bcp-blocker-batching/
invalidated-overlap/`, with an explicit `reason.json`. Those cells are
invalid because of concurrent CPU execution and output-file races, regardless
of their measured values; they were replaced by a single sequential run.
Seeds 0–5 and baseline seed 6 completed before the overlap and are retained.

The installed Z3 is 4.16.0. The user explicitly authorized using the
available version instead of downloading the methodology's older 4.15.4.

## Verification

All commands completed successfully on the final proposed source:

* `cargo build --all-features`.
* `cargo nextest run --workspace --all-features`: **10,622 passed**, 12
  existing skips. Includes the expanded occurrence-list reference differential,
  corpus soundness regressions, scope/theory checks and LRAT proof checks.
* `cargo test --workspace --all-features --doc`: **111 passed**, 29 ignored.
* `cargo clippy --all-features --all-targets -- -D warnings`.
* `cargo fmt --all -- --check`.
* `cargo doc --no-deps --all-features`, with `-D warnings` enforced by the
  existing `.cargo/config.toml` rustdoc flags.
* `./bench/z3_parity/run_parity.sh`, Z3 **4.16.0**: **169 correct, zero
  disagreements, one inconclusive Z3 Unknown** out of 170. Unknown is not
  counted as a match.
* Release `diff_equiv 100000`: **zero mismatches and zero invalid models**;
  66,993 satisfiable generated formulas checked against their original CNFs.

The initial performance cells are explicitly marked dirty and excluded from
reuse: their aggregate cycle ratio was 0.9617 and si2-b03m ratio 0.8820.
They remain the pre-landing decision evidence, not the final table above.

The clean `72720d9` rebuild is **byte-identical** to the prototype (SHA-256
`693d1ce2ab890d07803834f9ca2bf2577b3dbcaa90dfd0a948af6db5e658b429`), so the
component profiles measure the same executable. Its own 40 fresh cells are
recorded with `git.dirty=false` under
`precompile/72720d9/benchmark/runs/bcp-blocker-batching/`. Raw output,
manifests, the measurement harness and the final summary are under
`precompile/72720d9/benchmark/bcp-blocker-batching/`; verification logs,
the Z3-versioned parity snapshot and the binary-identity check are under
`precompile/72720d9/benchmark/verification/`. Cached executables are
`precompile/72720d9/nixie` and `precompile/72720d9/stats_solve-perf`.
