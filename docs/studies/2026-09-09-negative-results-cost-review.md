# Revisit negative results through cost and interaction

The user's 2026-09-09 direction changes the follow-up workflow: inspect the
cost of each rejected mechanism, consider an algorithmic repair, and examine
combinations of individually negative or neutral mechanisms. An old failed
gate remains a failed gate. Its conclusion applies to that implementation
and measurement; it does not automatically close a whole design family.
Do not multiply ratios from different instances, seeds or trajectories to
predict a combined gain.

For each follow-up, account for the work removed, the work introduced and
the critical dependencies left in place. Use retained profiles/flamegraphs
and generated code first. If a candidate has no retained profile, say that
its overhead is unresolved rather than treating its aggregate ratio as a
causal explanation. A new profile must resolve a specific missing term.
Separate implementation overhead, a small opportunity, an uninformative
policy signal and invalid measurement: they imply different next actions.

## Cost review of the relevant rejected mechanisms

This is an initial review of the throughput campaign, not a claim that
every historical candidate has a qualified flamegraph. The new
[fixed-factored profile](2026-09-09-factored-search-cost-lbr.md) is evidence
about the current hot path; it cannot retroactively profile older candidates.

| Mechanism / retained evidence | What the result actually establishes | Cost repair or interaction to examine |
|---|---|---|
| [Flat watch arena](2026-08-flat-watch-arena.md) | Additional arena machinery failed its screen. | Price growth, compaction and dispatch separately; a negative aggregate does not isolate density. Combine storage changes only with a direct loop that can exploit them. |
| [8-byte watchers](2026-08-watcher-8byte.md) | A small gain while replacing direct arena references with an ID-to-reference lookup. | The experiment traded stream width against a new dependency. It did not test 8-byte watchers retaining direct addressing. Pair with moving cold header metadata. |
| [8-byte arena header](2026-09-arena-8byte-header.md) | Moving activity aside modestly reduced misses, with neutral aggregate cost. | Reuse the freed four bytes for stable clause identity; preserve the current 12-byte slot geometry while removing IDs from hot watcher entries. This changes the purpose of the side table. |
| Word-split watchers, BIG slice iteration and PGO ([campaign](2026-09-07-throughput-campaign.md)) | Small loop changes failed; PGO removed about 7% of instructions with little cycle movement on its anchors. | Inspect dependencies and branches that remain. PGO is not evidence that all source/codegen changes are exhausted. Consider it only after the serial dependency or branch structure changes. |
| [Fixed-trail kernel](2026-09-09-fixed-trail-watch-kernel.md) | 0.91% fewer instructions and 1.48% fewer cycles in one pair; slightly more branches/misses. Yield overhead and spill savings were not separately measured. | Keep the immutable-view boundary as a possible enabler. Combine it with a stable-filter loop that specializes the pre-removal prefix and the later compaction phase. Inspect both generated loops before another cost screen. |
| [Write elision](2026-09-propagate-write-elision.md), including rejected lazy normalization | Write elision landed; changing stored watched-pair order changed trajectories. | Preserve eager normalization. Move the `write == read` invariant into two loop phases so every kept entry need not rediscover it. This is an algorithmic implementation change, not a watch-choice policy. |
| [Scalar positive certificates](2026-09-08-bcp-positive-certificates.md), [AVX2 certificates](2026-09-08-avx2-blocker-certificates.md), [four-entry batching](2026-09-07-bcp-blocker-batching.md) | Mask construction/consumption failed; AVX2 cut instructions but increased cycles and misses. | Separate gather/mask work, mask dispatch and the unchanged miss path in a candidate flamegraph. A compact watcher stream and a simpler consumer may interact; SIMD plus the same expensive consumer is not yet justified. |
| [Packed groups](2026-09-08-packed-blocker-runs.md) and [direct-loop follow-up](2026-09-08-packed-direct-loops.md) | Removing generic cursor dispatch saved 27.45% instructions and 32.16% cycles versus the old grouped implementation, yet failed the ordinary-cost constraint. | This is direct evidence that implementation overhead can hide a mechanism. Remaining packing, membership repair and scalar-buffer costs are not individually identified. A direct scalar/null comparison is needed before carrying the earlier bulk/null ratio into a redesigned kernel. |
| [Whole-list reuse](2026-09-08-watch-list-reuse.md) | Free-oracle coverage below 0.6%. | Faster bookkeeping alone cannot rescue this scope. The algorithm would need a different reuse unit. |
| [Entry reuse](2026-09-09-watch-entry-reuse.md) | 20–36% reusable visits, but fewer than one reuse per newly established certificate. | Model renewal and validation costs explicitly. A certificate produced by another necessary operation may be viable; a separate subscription structure has no demonstrated cost margin. |
| [Watch-trigger prediction](2026-09-09-watch-trigger-shadow.md) | A 13–16% future-trigger proxy reduction against shuffled scores, below the registered 25% gate. | The signal is modest, not absent. Price counter updates and candidate scans, then distinguish literal triggers from actual clause visits. Reuse necessary counters or cheaper selection only under a new, costed policy/null protocol. Do not tune the old labels as fresh evidence. |
| Saved-position scan ([persistence study](2026-09-eliminator-persistence.md)) | Short scans limit its benefit on the measured loss files. | Current factored learned scans are also short (1.77/payload). A cursor or false-prefix certificate needs a long-scan workload or free production of its certificate. Clause width alone is insufficient. |
| Analysis scratch and elimination capacity persistence ([campaign](2026-09-07-throughput-campaign.md), [study](2026-09-eliminator-persistence.md)) | Millions of avoided allocations translated into tiny aggregate savings. | Count bytes, clearing, construction and indexing work. Reusing an already-built occurrence index is an algorithmic opportunity, but subsumption and elimination use different orderings and mutate the index; capacity reuse did not solve that problem. |
| [First-parent elimination reuse](2026-09-08-elimination-parent-reuse.md) | The near-50% opportunity was tested; si2 improved, the two-input aggregate missed its gate. | Preserve the row-owned cleanup discipline. Price preparation, mark clearing and repeated row invalidation; combine with exact membership representations only if they share preparation instead of adding a second pass. |
| [Sparse-word subsumption](2026-09-08-sparse-word-subsumption.md), [rejection hint](2026-09-09-subsumption-rejection-hint.md), [membership-first](2026-09-07-subsumption-membership-first.md) | Their implementations did not expose large removable whole-run instruction cost. | Candidate generation/index traversal can dominate the final membership test. Audit rejected candidate volume and repeated connections before combining several membership filters. |
| [Analysis metadata fusion](2026-09-08-analysis-metadata-fusion.md) | 0.12% instruction difference and 2.34% cycle difference in the registered screen. | A larger representation change can reuse the fused access, but source-level duplicate reads are not proof of executed duplicate loads. Price activity-side-table accesses in reduction too. |
| [Compact trail metadata](2026-09-07-compact-trail-metadata.md) and [inline assignment](2026-09-07-inline-trail-assignment.md) | Tiny instruction changes; potentially overlapping host load limits cycle attribution. | No established cycle-regression cause. Revisit only alongside a change to assignment frequency, representation or live register state that gives these changes a specific role. |
| [Specialized propagation](2026-09-07-specialized-propagation.md), [watch-move value reuse](2026-09-07-watch-move-value-reuse.md), scan rewrite ([mode-matched study](2026-09-07-mode-matched-throughput.md)) | Narrow branch/load rewrites were sub-threshold. | Include compatible simplifications in the new hot-loop cost model; do not sum their old percentages or rerun each in isolation. |

## First combinations and the underlying algorithm

**Stable filtering plus a fixed assignment view.** Current propagation
loads all three watcher words before testing the blocker, maintains read
and write positions, and repeatedly tests whether compaction has started.
The previous fixed-trail kernel retained that same filtering algorithm.
Split the scan into a no-removal prefix and a compaction suffix. Before the
first removed/moved watcher, kept entries need no whole-entry copy; after
that transition, the write position is strictly behind the read position
and copying is unconditional. Preserve that state across unit/resume exits.
This combines the existing write-elision invariant with the archived
immutable-trail boundary. It may simplify both control flow and register
pressure; assembly must establish the actual change before a solver screen.
The semantic reference remains the original scalar loop and its exact-state
tests, including eager normalization, conflict tails, HBR and LRAT.

**Cold activity plus direct 8-byte watchers.** The proposed hot watcher is
`(arena reference, blocker)`. Replace activity's four header bytes with the
stable ID, and put activity in an ID-indexed side table. The header stays
12 bytes and five-literal clauses keep their 32-byte slots. Identity is
needed for units/conflicts and observers, rather than every ordinary hit or
move. On this sampled long-watch traffic, units plus conflicts are about
3.2% of visits. This is a different tradeoff from the old 8-byte watcher,
which loaded an ID-to-reference map on every payload access.

The lifetime audit found the hard part: compaction currently moves clauses
before rewriting watchers by their stored IDs, and coalesces deleted clauses
into one tombstone. Moving IDs into headers requires a relocation protocol
that obtains live identities before the bytes move. It must also preserve
deleted-watcher behavior, diagnostics' identities, detachment and snapshot
semantics. Do not add a full hot-path reverse lookup or silently discard
these obligations. Activity operations must retain identical f32 order and
bits so reduction is unchanged. This combination is a candidate, not yet
an implemented or qualified improvement.

The stable-filter kernel is the first implementation slice because it can
be checked against the archived exact-state oracle without redesigning
identity lifetimes. The compact representation is the next composable
slice once its relocation contract is complete. Additional mechanisms join
the bundle only when they remove a named remaining cost or share work with
an existing slice. Actual combined cost is measured against current ordinary
Nixie; if it fails, retain a candidate flamegraph and explain the remaining
cost before choosing a repair or stopping.

## First measured combination

The [two-phase fixed-trail kernel](2026-09-09-two-phase-watch-kernel.md)
passes its registered two-input engineering screen: identical trajectories,
5.13% fewer instructions and 17.21% fewer measured cycles/conflict. The
cycle figure is less secure because host interference was substantial.
This supports the combined implementation, not an inferred interaction term
from incomparable older runs. Its own qualified flamegraph retains the
remaining prefix/suffix/driver costs and identifies the next representation
obligations. Full source qualification passed, including 10809 workspace tests and fresh
Z3 4.16.0 parity with zero verdict disagreements; the kernel lands on main.

The follow-up lifetime audit narrows the identity problem. All four production
watch-detachment sites in `learn.rs` first obtain a live clause, then detach
its two current watches before deletion or replacement. This permits a
reference-based detach contract; it does not establish the rest of the
representation. `watched` is a private module. Lucky's packed snapshot stores
watch entries and separately saves clause IDs/literals; its propagation can
append HBR binaries, so rollback must be audited together with that growth.

Two possible tombstone strategies deserve explicit cost accounting before
choosing one. Keeping a separate header for every still-watched deleted ID
preserves identity but adds dead-header storage and GC marking. Alternatively,
observer builds could retain a separate identity word while ordinary entries
use `(reference, blocker)` and a shared tombstone, **only if** every ordinary
reader is proved not to need a deleted watcher's identity. That includes
detach, relocation validation, snapshots and every `Watcher` consumer, not
just the hot scan. Both feature layouts would need real default-build tests;
a wide all-features fallback cannot qualify the compact path. Neither design
may eagerly purge ghost hits or change their tick contribution. Moving activity
aside also retains storage indexed by historical, unreused clause IDs: include
that memory and reduction cost, not only the saved watcher bytes.

## Second combination: direct identity pays a different cost

The [direct compact-watch study](2026-09-09-direct-watch-identity.md) passes
its bounded wall screen: original circuit 9.58 → 7.98 s, si2 2.09 → 2.02 s,
identical Nixie outputs. Mode-matched Kissat remains faster at 5.55 s and
1.22 s. The observed two-input geometric mean reduction is 10.27%; the
retained circuit controls and small panel limit that claim. These are actual
elapsed measurements, not a conversion from cycle or instruction ratios.

The former 8-byte watcher lost direct addressing. This combination instead
moves activity out of the header, puts the stable ID in that word, and
combines direct 8-byte entries with the two-phase scan. Its reverse identity
read is confined to live reasons; moves keep only reference and blocker.
That distinction makes the earlier broad closure of the layout family too
strong. It does not establish a measured factorial interaction term.

Its own qualified original-circuit flamegraph retains the remaining costs:
49.51% of self cycles in the scan phases, 18.54% in subsumption. Generated
copies still use two 32-bit operations, and reason recovery repeats header
validation. The safe cold activity table and GC destination table introduce
real allocation/lookup work; historical IDs are never reused. Future work
should target these named terms or subsumption, with the introduced costs
included, rather than repeating an unmodified historical layout experiment.


## Third combination: price the miss before the next mechanism

The [whole-watch/live-view/scratch screen](2026-09-09-packed-watch-live-view.md)
fails: original-circuit wall 9.58 s versus retained compact control 7.98 s
and Kissat 5.55 s. Two new invocations suffice: one wall result and its
qualified LBR profile; the conditional si2 cell is skipped. A literal-u64
preflight was repaired before timing because it added prefix shifts and
whole-word updates. The repaired kernel has fewer instructions in its
prefix, but the overall wall criterion still fails. Noncontemporaneous
controls leave host/cache effects unresolved; do not label the 20% wall
increase a proven local source regression.

The same audit reproduced a real lifecycle defect: normal subsumption
rounds drop their supposedly reusable scratch buffers. Returning them
preserves exact state/proof behavior, but alone does not remove the index
lookup chain. The profile prices connected-clause lookup/validation at
36.39% of subsumption self-cycle attribution. The next algorithmic
combination should examine compact immutable payloads for already-connected
subsumers plus correctly retained scratch capacity. A first mutation/proof
lifetime audit is recorded with the result. Copy/clear/memory costs and
complete state identity must be checked before another bounded wall screen.
The failed combined prototype is retained for reproducibility and is not
a production landing.
