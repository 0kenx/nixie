# Miss-only header lookahead: source audit, not an experiment

Paused at the user's request to wrap up. This follow-up to the
[kept-span rejection](2026-09-09-kept-watch-spans.md) inspected current source
and retained evidence only. No solver implementation, build, test run or
performance invocation was added. It does not register a benchmark or claim
a speedup. The production kernel remains unchanged.

## What the audit establishes

`ClauseArena::live_lits_hot` checks null references and deletion before
forming a mutable literal slice. Lazy deleted watchers can remain satisfied
blocker hits, including after compaction coalesces deleted headers into a
tombstone. Thus the header's liveness test cannot simply be removed from
the miss path. Both the local Kissat `src/proplit.h` and Nixie's scalar
oracle retain that distinction. Current eager pair normalization also
preserves literal order observed by subsequent inprocessing.

The old unconditional lookahead prefetch failed partly because it computed
addresses and fetched clause data for cheap satisfied hits; see
[the retained prefetch result](2026-08-30-analyze-quadratics.md#negative-result-4-pass-5-propagation-clause-prefetch--net-negative).
The [positive-certificate experiment](2026-09-08-bcp-positive-certificates.md)
also failed while adding mask preparation/consumption. Neither justifies
repeating those implementations with a different distance or width.

## Possible combination and unresolved obligations

A distinct possibility is one-entry, read-only lookahead **only while
processing a live blocker miss**. Inspect the next watcher's blocker;
prepare its header only if that blocker is not true. Consume that result
on the next iteration, avoiding a second blocker/header load. This could
overlap independent reads while sharing preparation with necessary work.
It adds pending-state dispatch and live registers, and can still do wasted
work just before a unit or conflict. Its net cost is unknown.

The fixed-assignment scan provides a useful boundary: between returns it
changes literal contents and destination lists, but does not assign values,
delete/shrink clauses or grow/compact the arena. Any prepared header must
stay within that boundary. Discard it before Unit/Conflict returns and
prefix-to-suffix transfer; assignment and HBR after a return can invalidate
assumptions or arena addresses. Lookahead must not mutate the next watcher,
normalize its pair or alter its logical visit/tick count before its turn.
Only header metadata may be prepared: duplicate references make caching the
watched pair unsafe because an earlier visit can change that pair.

An implementation would need a sound API enforcing arena provenance,
unchanged length/liveness and exclusive access. Passing a bare cached length
into an unchecked slice constructor would create an additional unsafe
contract; no such API was implemented or approved by this audit. Exact-state
tests would need ghost hits, duplicate references, overlapping compaction,
consecutive misses/hits, every return, HBR/arena growth, resumption and
backtracking. Generated code would then have to show early independent
header loads, no duplicate consumed load, and the actual dispatch/spill cost
before a separately registered performance screen could be considered.

The prior span and delayed-move results remain rejected. This candidate's
purpose would be to overlap a retained dependency, not to infer a combined
gain by subtracting percentages from their different profiles. No evidence
currently establishes that it closes any part of the Kissat wall gap.
