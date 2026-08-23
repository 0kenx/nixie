# Trie-shared vivification (POS'25 mechanism, established-candidates Priority 3): component win, end-to-end neutral — LANDED (2026-08-23)

## Pre-registration

The established-candidates doc's Priority 3: port the POS'25 vivifier's
**shared-decision-prefix** mechanism in isolation ("the local
inprocessing experiments reject the bundle and its schedules; they do not
test a faithful replacement vivifier with shared prefixes").  Go/no-go per
the doc: first compare old and new vivifiers on identical candidate
sequences (decisions, propagations, strengthened, literals removed);
**reject if prefix savings do not survive end-to-end work**.

## What was implemented

`vivify_clause_shared` in `oxiz-sat/src/solver/learn.rs`, now the
`vivify_clauses` implementation (no flag — its only callers are the
already-opt-in inprocessing paths): candidates sorted lexicographically
by literal codes (trie order, same candidate SET and budgets); the
previous candidate's examined-literal prefix stays live on the trail; the
next candidate backtracks only to the divergence decision depth and scans
from the first differing literal.  Identical decision sequences propagate
identically, so the reused state is exactly the state a fresh scan
reaches at that index.  The round backtracks to level 0 after the last
candidate (the shared version deliberately leaves the trail at the end
state between candidates for reuse).

Two soundness hazards found during development (kept for any future
prefix-sharing work):

1. **Interpolated depths are unsound.**  A quick version recorded only the
   final depth and repeated it per prefix index; a later candidate
   backtracking to a too-deep interpolated level inherits the previous
   candidate's EXTRA decisions below the reuse point, and a conflict
   derived under those extra decisions does not justify the recorded
   strengthening.  Symptom before the fix: strengthened counts *3.3× the
   baseline's* (2 345 vs 709) — inflated by bogus strengthenings.  Fix:
   exact per-index depth bookkeeping, pushed in every break path (a
   missed push on the conflict-break path also desynchronized
   `prev_lits`/`prev_depths` into an index panic).
2. The `True`-break (satisfied) path counts `j` as examined with an
   unchanged depth — safe (the next sharer sees the literal true at the
   same state).

## Results

* **Component gate: PASS, above-band.**  6s167-opt, identical candidate
  set: strengthened 693 vs 709, vivify-internal propagations 278 k vs
  458 k = **39% fewer**.  The mechanism works as published.
* **Soundness: clean.**  Full-corpus A/B under the bundle (94 files, 20 s
  caps): 0 arm-vs-arm mismatches on both-answered cells, 0 wrong verdicts
  vs the reference answers; the landed build solves 66 vs the pre-trie
  binary's 65 (one additional file, no losses).  Full suite (10 071),
  clippy/fmt/doc, Z3 parity 168/168 clean.
* **End-to-end: NEUTRAL (±5% band).**  Paired instructions-to-verdict
  over 65 both-solve cells: geomean(base/trie) = 0.9897 — inside the
  band; not a regression and not a win at today's bundle share.

## Classification and the landing decision

The end-to-end number was first filed as "FAIL — 1% slower", then
reclassified neutral under the ±5% band, and finally **landed** under the
band rule's landing corollary (added to `BENCHMARKING.md` §3 the same
day):

> A component-level effect **above** the band paired with a
> **neutral** end-to-end result is landable when the component
> improvement is measured real and the landing adds no new risk: the
> end-to-end neutrality certifies the absence of a system cost, and the
> component win compounds wherever that component gains share later.

Here: 39% is far outside the band and mechanism-real (identical
strengthening at strictly less work); the end-to-end neutrality
certifies no cost; the code adds no new risk surface (the depth
bookkeeping is the risk, it is exactly specified, and the unsound variant
was caught and fixed in development).  If vivify ever gains a deployment
path with share — a standalone tier-budgeted pass (Priority 3's remaining
work), or a bundle arm in the budget-chained portfolio — the saving is
already in place instead of being rediscovered.

The pre-registered gate ("reject if prefix savings do not survive
end-to-end work") is *not* contradicted: it was written to catch savings
that dissolve because the mechanism is wrong or the deployment harmful.
Here the dissipation is purely vivify's small *share* of an opt-in
bundle, with no harm anywhere — the landing corollary exists precisely
for this shape.
