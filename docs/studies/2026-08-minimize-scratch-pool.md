# Conflict-analysis scratch pooling (plan item 2c): neutral, reverted (2026-08-22)

## Pre-registration

Replace `minimize_literal_plain`'s per-recursion-node `SmallVec<[Lit; 8]>`
reason collect with a depth-indexed persistent buffer pool on the solver
(`minimize_reason_pool: Vec<Vec<Lit>>`). Path-preserving by construction
(same literals, order, flags); gates = trajectory identity + instructions
geomean >= 1.02 over the 94-file corpus.

Motivation: worker_550 (10.3M-clause binary-dominated instance) learns
~2679-literal clauses; its reasons exceed the SmallVec inline capacity, so
every minimizer recursion node heap-allocates (`_int_malloc`/`_int_realloc`
visible in the profile; `minimize_literal_plain` ~12% of samples). cadical
iterates the reason in place — the collect is our divergence.

## Results

* Trajectory identity: holds (path-preserving; `nixie-sat` suite 867/867).
* worker_550 at MAXC=20000: 228.78G -> 226.41G instructions (**1.0%**).
* Corpus both-solve cells (72): geomean(base/new) = **0.9994**, new faster
  on 23/72 — neutral.

**Verdict: REVERTED** (bar >= 1.02; 0.9994 is noise-level neutral).

## Why neutral (the closing insight)

`SmallVec<[Lit; 8]>` is stack-inline for reasons of <= 8 literals — the
overwhelming majority on ordinary instances — so the collect only pays a
heap allocation on *giant-reason* instances, and even there the malloc
cost is ~1% of the conflict's work (the analysis walk itself dominates).
The 12% minimizer share of worker_550's profile is the *walk*, not the
allocation. Plan item 2c is now closed by measurement, matching the
earlier closure of 2b (trail-value raw pointer cache, blocked by
`deny(unsafe_code)`) and the two watcher-layout studies (2026-08):
**the remaining item-2-class headroom in conflict analysis is ~1%, not
5-10%**. The profiled hot loop on giant-clause instances is the reason
walk itself — bounded by clause-arena locality, not allocator traffic.

## Residual value recorded for any retry

The pooled-buffer pattern (depth-indexed, re-taken per element because the
recursive call takes `&mut self`) is sound and allocation-free in steady
state; it is the shape to reuse *if* the minimizer is ever converted to
cadical's tick-accounted in-place iteration (which would also require the
`opts.minimizeticks` schedule parity — a different, pre-registrable
experiment).
