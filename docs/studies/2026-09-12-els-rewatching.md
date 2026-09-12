# Incremental ELS rewatching: the negative result and the −0.9% that survived it (2026-09-12)

Priority-4 from the standing brief — "replace ELS's rewrite-all + full
watch/BIG rebuild with in-place rewatching" (~8 % of si2-class walls,
"the last engineering item of size").  Executed end-to-end, measured, and
closed: **the full surgery loses; the deep-dive surfaced one real
redundancy worth a stable −0.9 % on si2, now landed** (`6cdaea11`).

## The surgery (implemented to bit-exact equality, then removed)

Design: the BCP keeps every clause's watch entries keyed on its stored
first two literals (positional swaps on moves), so a rewritten clause's
old entries sit on exactly `¬old_lits[0/1]` — local surgery is possible:

1. strip entries of deleted clauses everywhere (+ normalize every
   survivor's **blocker** to its clause's current other watch literal —
   the rebuild rewrites all blockers, search leaves stale ones);
2. drop the touched clauses' old entries on the affected literals;
3. re-insert replacements at their `ClauseRef`-sorted positions
   (`ClauseRef` order ≡ clause-id order: slots are handed out
   monotonically, never reused, and `shrink` rewrites in place);
4. **sort every drifted list** — the BCP's watch *moves* append, so
   search drifts lists out of ref order between rounds; the rebuild
   silently re-sorts them all;
5. phantom reset + live-binary recount + BIG rebuild.

A check mode (`NIXIE_ELS_REWATCH_CHECK`) verified the surgery's end state
against a true rebuild per round — entry sequences, order, blockers,
phantom ticks — and reached **zero mismatches** with a **bit-identical
full si2 solve**. The engineering was sound.

## Why it loses anyway

Paired PMU instructions (pinned core, worktree A/B at the same source
tree): si2-b03m **23.856 G → 26.179 G (+9.7 %)**.  Matching the rebuild's
end state is the problem, not the surgery mechanics: the rebuild touches
the database **clause-major** (one sequential arena sweep, fresh lists
appended in id order — the ideal cache pattern), while any correct
in-place scheme must normalize **entry-major** (per-entry random arena
reads for the deleted-check/blocker refresh, plus a full sort pass for
the move-drifted order).  The normalization requirements — order,
blockers, strip — are load-bearing (each one was caught by the check
mode as a real divergence when missing), and together they cost more
than the thing being replaced.  **In-place ELS rewatching is closed as
architecturally unprofitable at this watch representation**; the version
that would work is CSR/arena watch lists (rebuild = memcpy, surgery =
sorted splice) — an architecture item, not an engineering one.

## What survived (landed, `6cdaea11`)

1. **The trailing `refresh_binary_graph` was unconditionally
   redundant.**  The mid-round `rebuild_watches_and_binary_graph`
   already purges the gate-congruence augmented edges (it rebuilds the
   BIG from the live binary set), and nothing between it and the
   trailing refresh — level-0 unit assignment, `propagate` — changes the
   clause set.  The trailing rebuild reproduced an identical CSR every
   round; skipped, one full clause-iteration pass per round.
2. **`WatchLists::new` per rebuild** allocated `2·num_vars` fresh `Vec`
   headers each round (si2: ~2.6 M × 6 rounds); `reset_lists_in_place`
   clears in place, capacity retained — zero allocation churn,
   bit-identical contents.

Measured: si2-b03m 23.856 G → 23.641 G (**−0.90 %**, 3 stable paired
reps); 54/54 corpus files trajectory-bit-identical at 25 k caps;
nixie-sat 1075/1075; parity 175/0 wrong.

## Where this leaves the si2-class constant-factor program

The ~35 % inprocessing cluster now consists of: the rewrite loop
(allocation-free since 2026-09-11), the watch/BIG rebuild (sequential,
allocation-free since this study), arena compaction, and the elimination
phase — each individually within ~1 % levers of this shape.  The
remaining structural option is the watch representation itself (CSR),
recorded above.
