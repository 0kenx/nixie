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


## Fourth combination: cache the surviving subsumer's residual

The [connected-residual payload screen](2026-09-09-connected-residual-payloads.md)
turns the previous profile into an algorithmic implementation change. After
a candidate survives its scheduled mutation, copy its connected payload
once and omit the connection literal; the query bucket supplies that literal's
mark. Restore empty scratch buffers at return so subsequent rounds reuse
the index and pool capacity. Connection order, budgets, proof identity,
clauses and the complete search trajectory remain unchanged.

The five registered performance invocations produce circuit seed-1 wall
**9.63 -> 8.81 s**, versus mode-matched Kissat **1.88 s** in the same window.
The si2 guard is neutral at **2.02 -> 1.99 s**, using retained controls
(Kissat 1.22 s). The two-input geometric mean **0.94935** narrowly passes its
0.95 gate. The small panel, historical guard and shared-resource uncertainty
remain explicit; this is not a broad speedup or a measured interaction term.
Circuit peak RSS grows from 32972 to 37512 KiB. The valid candidate flamegraph
and generated-code review include the new copying/bounds/counter costs.

The connection index no longer resolves ID -> arena reference -> live header
for every query. Its remaining pool iteration/bounds receive 3.12% of total
sampled cycles, residual membership 3.14%, and per-entry counter updates
1.08%. Fusing bucket scanning with one exact counter charge is a concrete
possible repair, but counter elimination alone has a small ceiling. The
larger watch loops retain 53.68% of sampled cycles. Prior neutral filters
cannot simply be added back without pricing their preparation and miss paths.

The retained outputs also expose a separate work-volume issue: Nixie
processes 104.19 trail literals/conflict versus Kissat's 39.80. Whole wall
amortized over that counter differs 1.615x; together they explain the
observed 4.228x wall/conflict ratio arithmetically, without asserting equal
counter phase coverage or isolated kernel timings. Kissat eliminates 1130
variables versus Nixie's 228 under the requested flags. Audit root/restart
replay and elimination work before assuming another local instruction
rewrite alone can close the gap. These observations use existing outputs,
not another experiment or a justification for an uncontrolled heuristic.

Full source qualification passes on the integrated tree: 10824 workspace
tests, 111 doc tests, strict build/Clippy/fmt/docs and the required correctness
canary with zero disagreements. The residual cache and its regressions land
on main; its measured standalone SAT binaries are reused without retiming.

## Work volume and an explicit representation route

The [propagation-work audit](2026-09-09-propagation-work-audit.md) rejects
scheduled inprocessing or exhausted elimination rounds as a sufficient
explanation for the original circuit's propagation volume: 95.31% lies
outside those scheduled calls, and all 24 elimination rounds complete.
The existing exact relation representation addresses dense source clauses
before they encounter the occurrence cutoff. This is already implemented
in the offline transformer; it is not a newly discovered mechanism.

The [direct relation-solving mode](2026-09-09-direct-relation-solve.md)
connects that transformer to the current solver without a write/reparse
pipeline. Its single complete-path run takes **3.61 s**, including parsing,
checked transformation, search and original-model validation, versus retained
ordinary Nixie **8.81 s** and requested mode-matched Kissat **1.88 s**.
The old factored trajectory is preserved exactly. Peak RSS rises to 58176
KiB because the original formula and certificate preparation cost are real.
This is a useful explicit route, with different-window and one-seed limits;
there is no new default policy or established heuristic/null result.

The retained qualified factored traffic observation still rejects a bespoke
original-five-literal engine: originals contribute at most 23.58% of payloads
plus scans, learned clauses 76.41%, with only 1.77 scanned literals per
learned payload. The watch and subsumption changes since that observation
preserve this recorded search trajectory but are not individually profiled
by that old capture. Do not transfer old cycle shares onto the new 3.61 s
process or add a cursor merely because learned clauses are long. The next
core cost question remains the serial watch/blocker/payload path; another
batching or certificate mechanism must remove an identified consumer or
renewal cost from its failed predecessor, not just add it to this mode.

## Fifth combination: delayed moves simplify code but retain the work

The [delayed destination-write screen](2026-09-09-delayed-watch-moves.md)
combines the old flat-arena experiment's queue with today's direct compact
watches and fixed-trail two-phase scan. It preserves the current Vec lists
and flushes before every unit/conflict/done return. The generated scan bodies
shrink by roughly 14%, with 16 fewer local stack bytes each, but the complete
original-circuit run is **8.88 s versus retained 8.81 s**. Its output and model
match; the wall gate fails, so the si2 guard is skipped and no source lands.

The required candidate flamegraph identifies the cost left behind. Queue
preparation/store regions receive **2.124%** of total sampled cycles, the
separate flush **3.015%**, and the watch scan bodies still **51.284%**.
The flush still appends every watcher individually. Destination stores and
loop control receive 1.521%; target indexing/capacity 0.944%. Its growth-call
block receives no samples, so reserve-size tuning has no demonstrated margin.
These are IP attributions, not precise region timings or a causal explanation
of the small different-window wall delta.

Adjacent equal-destination batching is an algorithmic way to remove some
append operations, but this profile does not establish its reuse frequency
and the entire flush is a small ceiling. Grouping/index preparation must be
priced before adopting it. The old eager-normalization comparison also rules
out presenting conditional pair-store elision as an untried repair. A more
promising core audit is whether the scan's cursor/span invariants can remove
repeated compaction bookkeeping and copies; merely moving the same work
between functions has now been priced. The failed prototype, checked states,
assembly and complete profile remain reproducible from the binary cache.

## Sixth combination: kept spans do not remove the consumer

The [kept-span compaction screen](2026-09-09-kept-watch-spans.md) removes
per-kept-entry copies and output-index checks from the compacting scan's
common hit path. Refreshes update the source entry, and holes/exits publish
consecutive kept spans. It preserves exact state and complete output, but
wall is **9.64 s versus retained ordinary 8.81 s and Kissat 1.88 s**. The
gate fails; only wall and its registered diagnostic run, with no si2 guard.

The diagnostic also fails its registered quality thresholds: four of 3994
samples are kernel-labelled/unresolved, leaving 99.89985% user coverage and
0.100148% unresolved self cycles. Retain its explicitly labelled flamegraph
as exploratory evidence; do not round these into a pass or retry the cell.
Span regions plus captured suffix memmove callers receive about 2.18% of
sampled cycles, while scan bodies still receive 55.38%. The suffix grows
41.3%, reserves 16 more stack bytes and gains four static memmove call sites.
This establishes introduced machinery but does not causally explain the
whole different-window wall delta.

The underlying filter still visits every watcher and retains the dependent
blocker/header/payload reads. The small observed copy regions do not justify
another copy-size tuning run. Combining it with delayed moves adds queue
traffic without removing that consumer or any destination append; no reuse
measurement supports a grouping benefit, and old/new region shares cannot
be subtracted as a predicted interaction. Keep both failed prototypes out
of production. Future combinations need shared preparation or fewer visits
or appends, rather than another relocation of the same work. The existing
direct relation mode remains the measured structural route on this input;
its remaining gap to Kissat still needs substantive work.

## Miss-only header lookahead: dispatch repair did not rescue wall

The [completed header-lookahead experiment](2026-09-10-miss-header-lookahead.md)
combined the fixed-trail boundary with one-entry preparation on live misses.
Its first mixed loop added pending-state dispatch to cheap hits: j3037
37.94 s versus qualified control 36.13 s, with 13.93% more instructions.
The flamegraph and assembly justified one repair: isolate consecutive misses,
consume prepared hits directly, and combine liveness/consumption in the arena
API. That removed 6.97% of the prototype's instructions but still used 6.00%
more than control and took 38.75 s. Both complete trajectories match control.

The deeper cost is not just enum representation. Next-header preparation
still classifies deletion before current literal work, adding dependent
control flow instead of merely issuing an independent read. Destination
appends and their memory accesses remain. Two audited flamegraphs and both
source bundles are retained; five performance invocations sufficed to reject
these implementations. The remaining raw-header/deferred-classification
hypothesis needs a stricter code-generation gate before any new measurement.


## Unified and compact directories: less metadata, too little removed work

The [unified-directory experiment](2026-09-10-propagation-directory.md)
co-locates binary extents/overflow, long-watch ownership and phantom counts.
Its driver gets smaller, but the initial 64-byte row expands the destination
header stride and saves only 0.90% complete instructions. The qualified LBR
profile still puts 23.43% of self cycles in the driver and 48.33% in scanners,
including directory accesses, destination append and the unchanged dependent
blocker/header/value reads. These attributions are not cache-miss counts.

One explicitly registered combination with the prior compact owners reduces
the row to 48 bytes and keeps ordinary append inlined. Fresh strict-provenance
Miri, independent directory-model checks and native Rayon tests pass. Yet the
combined j3037 result saves just 1.47% instructions and takes 36.86 s versus
the retained qualified control's 36.13 s. Both versions preserve complete
output. Passing off-CPU/PMU gates still leaves shared-build effects unresolved;
neither demonstrates the required wall gain. Exactly three performance
invocations cover both cost cells and one profile, with no si2 or timing retry.

The combination had a real structural interaction: compact ownership reduced
the new directory's larger stride and transfer footprint. Its actual cost
still rejects promotion. It removes no watch/edge visits or destination
appends, and only saves 11.58 amortized instructions per processed literal.
Both prototypes are archived; no production representation changes land.
Further progress needs to remove or amortize an actual propagation consumer,
or reduce work volume through the already documented structural algorithms.
Another owner-width or row-alignment screen is not justified by this result.

## Complete propagation: large instruction saving, wall still unqualified

The [complete-engine study](2026-09-10-complete-propagation-engine.md) retains
fixed trail, arena and directory views across all ordinary assignments and
inlines both watch phases into the fixpoint loop. Exact j3037 output survives,
and whole-process instructions fall 15.54%, while wall is 36.72 s against
cached control 36.13 s. Its qualified flamegraph puts 70.24% of self cycles in
the engine, including blocker reads, header classification, directory access
and destination append. Fewer executed instructions have not established
less time on the remaining dependency chain.

One registered combined repair retains watch owners in place and reuses the
negative raw-header pipeline's word encoding for current-header reads. Safe
slice splitting first exceeded the stack gate; a checked excluded-row borrow
passed it, with focused strict-Miri and native Rayon coverage. The repair
removes the intended transfers and second length loads, but saves only 0.051%
additional instructions and takes 41.94 s. The extra exclusion checks, header
mask work and live-state management offset the removed instruction work.
Source and host effects on cycles remain unseparated; these observations do
not license a default switch or a claim of a population regression.

Both prototypes are archived. Exactly two cost cells and one profile were
needed. Their useful new boundary is the full fixpoint's stable arena: unlike
the old per-unit callback, it could retain immutable preparation across
assignments. That is a distinct, untested interaction, with freshness and
register-pressure costs to establish first. The study records its obligations;
another current-header syntax or owner-layout sweep is not the next step.

## Complete engine with persistent header preparation

The [persistent-header experiment](2026-09-10-persistent-engine-headers.md)
implements the previously untested interaction: retain immutable preparation
through assignments inside the complete engine. Refreshing a pending blocker
by comparing it with the single newly assigned literal is exact and avoids a
second value lookup. A phase-local ownership repair reduces its stack frame
from 312 to 264 bytes and removes exit writebacks before any cost run.

The combined implementation still adds **7.49% whole-process instructions**
against the first engine on identical j3037 output, with observed wall
52.31 versus 36.72 seconds. The candidate profile exposes preparation-load
and spill sites, a value-base reload inside tail loops and larger duplicated
suffix code. Host interference prevents assigning the entire wall delta to
those costs. No production change, si2 confirmation or measured repair;
one cost plus one diagnostic invocation. This closes the one-entry pipeline
under the complete ownership boundary too. Further work needs an explicit
reduction in dependency/work or live state, not another revival of the same
lookahead bookkeeping.

## Fixed queue plus separate binary spans: preflight rejection

The [fixed-queue experiment](2026-09-10-fixed-propagation-queue.md) combines
a domain-bounded raw append queue with the original complete engine and
separate primary/overflow binary loops. Safety tests, scalar-state checks,
strict Miri and native Rayon ownership pass. Assembly removes queue-growth
checks, per-edge storage selection and satisfied-edge reason loads.

The first version introduces a per-literal binary-view accessor call; one
registered inline repair removes it. Both versions still have a 264-byte
frame versus the registered 248-byte maximum. The repaired driver spills
the fixed queue pointer at each append, publishes local initialized length
per unit and keeps the checked-view lengths plus duplicated suffix bodies.
This closes at code generation with **zero performance invocations**; it
does not demonstrate a wall regression or a speedup. The source and capacity
proof are archived. Do not retry the same annotation or change the gate
post hoc; further work must reduce the state carried by the whole engine.

## Borrowed reasons and fixed assignments: less work, timing unqualified

The [borrowed-reason experiment](2026-09-10-borrowed-propagation-reasons.md)
changes the access contracts that kept the fixed-queue engine's state large.
An in-domain undefined assignment uses focused unchecked stores, while a
live clause carries disjoint payload and stable-identity borrows. This
removes repeated reason validation and assignment bounds branches, reduces
the local frame to 216 bytes and passes the original code-generation gate.
Scoped tests, strict-provenance Miri and native Rayon ownership pass.

On identical complete j3037 output, whole-process instructions fall
**19.93% against qualified production and 5.20% against the first engine**.
This is a successful instruction-level combination with the fixed queue.
Its wall measurement is unusable: 34.866% off CPU, almost 20000 involuntary
context switches, and heavy concurrent foreign builds and solver sweeps.
Do not label this a demonstrated wall regression, claim a wall gain, or
replace the failed-quality cell with a rerun. No si2 confirmation follows.

The one qualified diagnostic puts 72.90% of sampled self cycles in the
engine. Selected borrowed-identity setup/read IPs account for only 0.247%;
blocker comparisons, deleted-header tests and overflow metadata remain
prominent. These are skid-sensitive address attributions under contention,
not causal time budgets. No introduced dominant cost justifies the optional
measured repair, and changing pointer syntax again would not remove the
remaining dependent access chain. Exactly one cost and one profile were
spent. Source, safety evidence and profile are archived on main; production
promotion remains unqualified pending a separately registered, uncontended
wall comparison. This is an instruction-positive result with missing usable
timing, not another measured negative implementation result.

The [independent-input follow-up](2026-09-10-borrowed-engine-heldout.md)
then supplies usable, adjacent production/candidate timing on crn and
summle, without repeating j3037. Instructions fall 8.46% and 15.83%, but
wall ratios are 1.02083 and 1.06439. Both pass the fixed post-run quality
gates; shared-host cache/frequency effects remain unresolved. The two-input
wall aggregate is 1.04238, failing advancement, and summle exceeds the
individual guard. This closes promotion of the unchanged candidate: its
instruction improvement has breadth, its wall benefit is not demonstrated.

The one summle diagnostic fails due to sampling throttling and excessive
unresolved self weight. Its fixed 1048576-cycle period implies a sampling
rate above the host's 2000/s kernel limit; this was an instrumentation
configuration error, not a solver cost. Retain the explicitly exploratory
flamegraph, never substitute its duration/counters for a cost run, and do
not repeat it. Assembly still exposes dependent blocker/header/payload
accesses and per-literal graph metadata checks. The lifetime/validation
savings do not remove those accesses. Further work requires a concrete
removed dependency or scan, not another timing of this same source.

## Empty long lists: real bookkeeping removed, too small a lever

The [empty-list fast path](2026-09-10-empty-watch-fast-path.md) bypasses vector
extraction/restoration after binary propagation and the unchanged tick charge.
One new j3037 invocation uses 1.33% fewer instructions; wall is 37.76 s versus
the retained control's 36.13 s. It fails the advancement bar, so no second input
or new profile runs. Timing checks pass, but different measurement windows and
shared resources limit attribution. Complete stdout remains identical.

The retained census bounds eligible empty completions above by 33.94% of
propagations, while roughly 2.1 billion offered watcher entries remain.
Assembly confirms that empty ownership work disappears; it also retains a
redundant length guard on nonempty lists. The old empty path already skipped
the scanner call. This is a small bookkeeping opportunity, not a third of
propagation cycles. Its overlap with the complete engine's ownership changes
does not justify adding their instruction savings or another combined timing.
The source is archived; production stays unchanged.
