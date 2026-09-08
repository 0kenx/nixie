# Reusing complete watch-list satisfaction: rejected opportunity

The prior window certificates and grouped watcher kernels failed their cost
screens. This asks a different question: can a certificate from a completed
watch-list scan survive until the next visit of that literal, across search
backtracks? A successful ordinary scan leaves every retained watcher's blocker
true (hits, refreshed satisfied blockers, or newly propagated units). If the
list is unchanged and those same assignments survive, the next scan consists
entirely of blocker hits. Skipping it would preserve arena and watcher state.
Kissat `src/proplit.h` supplies the blocker-before-payload reference semantics;
Nixie's existing propagation loop defines the exact order and accounting.

No skipping or policy is implemented in this step. First measure the actual
opportunity, including its persistence conditions. The previous certificate
studies only reused truth within one scan; they did not measure this lifetime.

## Read-only collector

Select literal keys by a fixed integer hash, one in 64, and observe **every**
visit of each selected key throughout the invocation. This permits consecutive
visit comparisons, unlike the earlier one-in-N-list-ordinal group census.
At each successful sampled scan retain exact ordered watcher tuples and the
assignment identity of each distinct positive blocker. Assignment identities
are observer-only monotonic stamps; reassignment of the same truth value must
invalidate the old certificate. Exhausted stamp space disables certification,
never reuses an identity. Clear histories at solve/scope boundaries.

At the next visit distinguish changed watcher contents, lost blocker
assignments, and fully surviving certificates. Count actual visited prefixes,
not unvisited conflict tails. Report list-size and conflict-epoch breakdowns,
history creation/replacement volume, and distinct blocker counts. Memory is
bounded at 262,144 entries per list, one million retained entries and 65,536
retained lists; report every capacity omission. Current contents are compared
exactly, not by hashes. Observation never authorizes propagation or affects
watch order, clause order, assignment choices, budgets or ticks.

The primary feasibility statistic is the fraction of sampled visited watchers
in surviving whole-list certificates of **at least eight entries**. Advance
only if it is at least **30% on both inputs**, with no unexplained omission or
trajectory discrepancy. Also report the all-size ceiling and the certificate
dependency count. This deliberately optimistic work ceiling assumes free
validity checks and maintenance; it is not a cycle-saving estimate. A positive
screen only justifies designing a bounded-cost validity mechanism.

## Two new observer cells

Use si2-b03m and circuit_48in64out, seed 0, MAXC=40000, CaDiCaL preset,
`NIXIE_SWEEP=0`, model output enabled, CPU 10. Input hashes are pinned in
`2026-09-08-sparse-word-subsumption.md`. Build the observer from clean committed
source based on main `ee35054`, with a separate compile-time feature so ordinary
builds contain no stamps or collector hooks. Instrumented timings are not
performance results.

Reuse existing full stdout: si2 control `490756d`, record
`e45297cb1743dd83`; circuit control `02afce4`, record `a7a1c5fa679a8802`.
The current ordinary SAT source equals `490756d`; the older circuit control
predates the disabled sweep-delay change and unrelated SMT float changes.
Require byte-identical complete stdout, including all counters/model, and
independently check any SAT model. This is an observation/trajectory check,
not a timing comparison between these differently built binaries. Record
each new cell once with source/binary/input hashes and the collector's complete
visit counter as its deterministic observation metric. No new reference
solver panel, repeated cells or sampling-threshold tuning.

Test stamp identity across ordinary/explicit-level assignments, backtracking,
clear/resize and overflow; exact list matching, conflict tails, missing
dependencies, size bins, capacity omissions and history reset; paired observed
and unobserved solves with explicit clause state, models and checked proofs.
If the gate fails, archive the observer and land the negative finding. Any
production source landing still requires the full repository verification
gates and fresh SMT parity. The Kissat throughput objective remains open.

## Result: less than 1% coverage, no reuse kernel

Both registered observer cells ran once from clean committed **`164b5ec`**,
whose direct parent is registration commit `544ee59`. Release binary SHA-256:
`06fb8259c12bfb5c64adc90c3f2f9f2fe3b6eefae514ae552f4eee4506a74cc0`.
The build used Rust 1.96.0 / LLVM 22.1.2 and the pinned lockfile shared by
the controls. No ordinary propagation behavior changed. An initial runner
invocation rejected a mistyped source SHA before launching any solver; it
created no measurement cell.

| input | sampled visits | surviving visits, any list size | surviving visits, size >=8 | registered fraction |
|---|---:|---:|---:|---:|
| si2 | 2,501,701 | 6,383 (0.2551%) | 5,814 | **0.2324%** |
| circuit | 1,853,673 | 10,318 (0.5566%) | 9,858 | **0.5318%** |

Both fractions miss the 30% opportunity gate by a wide margin. Even ignoring
the minimum list size leaves the observed coverage below 0.6%. Those are
sampled logical-visit ceilings with free validity checks, not cycle savings.
No kernel, density adjustment, extra seed sweep or repeat cell follows.

The census covered 11,882 selected-key list visits on si2 and 45,981 on
circuit, including empty lists (which contribute zero to the visit
denominator). All-key actual watcher visits were 161,699,940 and 100,167,701.
There were **zero capacity omissions** and **zero non-positive blockers at
successful sampled scan exits**. The premise that a completed list is
satisfied holds here; its useful lifetime is the failure.

| input | consecutive history pairs | changed list contents | lost blocker assignment | surviving list |
|---|---:|---:|---:|---:|
| si2 | 6,151 | 3,062 | 2,756 | 333 |
| circuit | 43,821 | 17,590 | 25,827 | 404 |

Assignment loss is counted only after exact ordered list equality succeeds;
these categories partition the history pairs. Equality is checked at the
next visit, so the census is optimistic about a production invalidation
scheme that would also reject an intervening mutation later restored to
identical contents. Same-value reassignment cannot masquerade as survival:
the assignment stamp changes.

The result is not just an early-search artifact. At conflicts >=16,384,
size>=8 coverage is 5,665 / 1,144,019 = **0.4952%** on si2 and
3,417 / 1,362,458 = **0.2508%** on circuit. Constructing the shadow histories
copied 1,709,929 and 1,642,896 watcher entries, with 50,715 and 359,910 distinct
blocker dependencies across all builds. These volumes are bookkeeping
observations, not a lower bound on an as-yet-unwritten implementation's cost.

**Decision:** do not build a whole-list satisfaction cache or tune its
minimum-size cutoff. Watch-list contents and blocker assignments change too
often for this measured reuse mechanism to remove material work. A future
proposal needs a different source of reuse, with dynamic evidence first.
This closes another proposed shortcut, not the Kissat throughput gap.

## Verification and retained evidence

Both full stdout files are byte-identical to their registered cached controls.
Si2 is SAT at **39,246 conflicts**, and its model was independently checked
against every original clause. Circuit reaches **40,000 conflicts** and
returns budget Unknown; it is unsolved and has no certified final verdict.
Solved-at-cap remains 1/1 for si2 and 0/1 for circuit, matching the controls.
No performance conclusion uses the instrumented timings.

All **761 SAT library tests** passed with all features, including eight new
tests. The observer tests cover exact tuple/order matching, assignment loss,
partial conflict visits, size bins, capacity omissions and solve/scope resets.
Stamp tests cover both assignment entry points, chronological retention of
lower-level assignments, resize, clear, size backtrack and permanent
disablement at counter saturation. Twenty paired formulas include guaranteed
SAT and UNSAT cases, exhaustive truth-table classification, explicit clause
payload/metadata equality, trail/watch/stat/model equality, identical LRAT
transcripts, independently checked SAT models and independently checked UNSAT
proofs. All-target SAT clippy, formatting and the committed release build
passed.

Canonical records **a9ae262dee0f7de1** (si2) and **e94ef2b00aec18c6** (circuit)
are under `precompile/164b5ec/benchmark/runs/watch-list-reuse/`; their schemas,
identities, paths and histogram denominators were validated. The sibling
`benchmark/watch-list-reuse/` directory retains raw outputs, runner, manifest,
summary, build/test logs and a source patch/bundle. The rejected observer is
archived rather than landed; no full-workspace or SMT parity qualification is
claimed. Main receives this finding only. Its concurrent default sweep-effort
change does not alter these pinned, explicitly sweep-disabled measurements.
