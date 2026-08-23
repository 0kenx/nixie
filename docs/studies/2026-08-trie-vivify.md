# Trie-shared vivification (POS'25 mechanism, established-candidates Priority 3): first-gate win, end-to-end reject (2026-08-23)

## Pre-registration

The established-candidates doc's Priority 3: port the POS'25 vivifier's
**shared-decision-prefix** mechanism in isolation ("the local
inprocessing experiments reject the bundle and its schedules; they do not
test a faithful replacement vivifier with shared prefixes").  Go/no-go per
the doc: first compare old and new vivifiers on identical candidate
sequences (decisions, propagations, strengthened, literals removed);
**reject if prefix savings do not survive end-to-end work**.

## What was implemented (throwaway worktree, reverted)

`vivify_clause_shared` behind `OXIZ_VIVIFY_TRIE=1`: candidates sorted
lexicographically by literal codes (trie order, same candidate SET and
budgets); the previous candidate's examined-literal prefix stays live on
the trail; the next candidate backtracks only to the divergence decision
depth and scans from the first differing literal.  Identical decision
sequences propagate identically, so the reused state is exactly the state
a fresh scan reaches at that index.

Two soundness hazards found and fixed during the build (kept in the record
for any retry):

1. **Interpolated depths are unsound.**  The quick version recorded only
   the final depth and repeated it for every prefix index; a later
   candidate backtracking to a too-deep interpolated level inherits the
   previous candidate's EXTRA decisions below the reuse point, and a
   conflict derived under those extra decisions does not justify the
   recorded strengthening.  Symptom before the fix: strengthened counts
   *3.3× the baseline's* (2 345 vs 709) with 39× fewer propagations —
   inflated by bogus strengthenings.  Fix: exact per-index depth
   bookkeeping, pushed in every break path (a missed push on the
   conflict-break path also desynchronized `prev_lits`/`prev_depths` and
   panicked on the next candidate).
2. The `True`-break (satisfied) path initially recorded the prefix as
   unexamined past the break, which was merely wasteful, and then as
   examined-through-j, which is safe (the next sharer would also see the
   literal true at the same state).

## Results

* **First gate (in-pass, 6s167-opt, bundle on): PASS.**  Same candidate
  count, strengthened 693 vs 709, vivify-internal propagations 278 k vs
  458 k = **39% fewer**.  The mechanism works as published at the
  component level.
* **Soundness screen: clean.**  Full-corpus A/B under the bundle (94
  files, both arms, 20 s caps): 0 arm-vs-arm mismatches on both-answered
  cells, 0 wrong verdicts vs the reference answers, solved 60/60.
* **End-to-end gate: FAIL.**  Paired instructions-to-verdict over 65
  both-solve cells: geomean(base/trie) = **0.9897** (1% *slower*), trie
  faster on 10/65.  The 39% in-pass saving does not survive.

## Why it does not survive (the structural finding)

Vivify's share of total bundle work is small — improving it 39% moves the
bundle's total ~1%, and the bundle itself is already measured
net-negative as a default (the bisect study).  There is **no standalone
production path to vivify in OxiZ today**: it runs only inside
`inprocess()` (bundled) or under the non-default `presearch_collapse`.
POS'25's mechanism presupposes vivify as an isolated, tier-budgeted,
scheduled pass — Priority 3's real work item is building that pass
(candidate scheduling, tier budgets, on-the-fly subsumption with the
promotion invariants), of which prefix sharing is one sub-mechanism whose
value cannot even be expressed until the pass exists standalone.  This
screen closes only the "does sharing pay inside the current bundle"
question.

**Verdict: reverted; mechanism data recorded.**  Component-level: works.
System-level: no deployment path where it pays.

## Disposition

Code reverted (worktree deleted — the exact bookkeeping design above is
the reusable artifact).  This is the seventh pre-registered null/reject
in the SAT-perf arc, and the first where the component gate passed while
the system gate failed — the cleanest demonstration yet of the
repo-motto: component wins are not system wins.
