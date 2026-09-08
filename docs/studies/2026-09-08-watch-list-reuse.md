# Reusing complete watch-list satisfaction: opportunity registration

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
