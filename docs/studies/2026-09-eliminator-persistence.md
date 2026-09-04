# Eliminator round/phase persistence (occurrence capacity reuse): pre-registration + negative result (2026-09-01)

Third follow-up on the propagate/eliminate thread. Fresh profile after
the BIG-authoritative and write-elision landings re-ranked the levers:

| lever | circuit | worker | g2-slp |
|---|---|---|---|
| propagate | 33.3 % | 6.2 % | 26.0 % |
| eliminate_phase | 10.2 % | 4.8 % | **29.4 %** |
| shrink/minimize walk | — | **37.3 %** | 1.1 % |
| parse/attach/add | 17 % | 14 % | — |

Gent's saved-position scan was measured **dead** first: scan
instrumentation (`iters/miss`, `false_examined`) shows the false-prefix
it would skip is 58–65 % of scan iterations on circuit/si2/noL, but
scans there are only 2.1–2.8 iterations per miss → **≤ 1 % end-to-end**
(best file), for a divergence-class change plus header surgery. Not
pursued.

## The target: elimination is allocation-bound

Counting-allocator instrumentation (`MAXC=20000`):

| file | total allocs | in eliminate phases |
|---|---|---|
| g2-slp | 5.33 M (1.13 GB) | **4.08 M (77 %)** |
| circuit | 2.79 M | 0.22 M |
| worker | 14.97 M | 1.71 M |

Source: `elim_round` constructs a fresh `Eliminator` per round —
`Vec<Vec<ClauseId>>` occurrence lists over 2×num_vars (202 k lists on
g2-slp) that re-grow geometrically as the connect pass pushes ~12 M
occurrence entries (789 k clauses × ~15 unassigned literals after phase
1's resolvent bloat), × 2 rounds × 3 phases. Each list growth is a
realloc + memmove; the annotate view shows the allocator family
(`grow_one`, `__rust_dealloc`, `realloc`, `malloc_consolidate`) at the
top of the eliminate self-cost. cadical keeps its occurrence structure
across the whole `elim` phase.

Round structure measured on g2-slp (`NIXIE_LOG_ELIM`): phase 1 round 1
eliminates 59 678 vars via 6.2 M resolutions; **round 2 then pays 861 k
resolutions plus a full 323 k-clause reconnect for 281 vars**, and
phases 2–3 reconnect 789 k clauses per round for triple-digit yields.

## The change

**Round- and phase-persistent `Eliminator` on the Solver** (lazy,
created on first eliminate phase, kept for the solver's life — cadical's
shape): between rounds *and* phases, every occurrence list is **cleared,
not dropped** (capacity retained), and the scratch vectors (`ps`, `ns`,
`collected`, `doomed`, `to_retire`, `to_mark`) become Eliminator fields
reused via `clear()`. The connect pass then pushes into lists that
already hold their high-water capacity — no growth reallocs after the
first phase.

Pure capacity/lifetime refactor: identical pushes in identical order,
identical schedule, identical semantics. The values snapshot
(`Eliminator::new` copies the trail) is refreshed per round as today.

## Go / no-go (pre-registered BEFORE measuring)

1. **Gate 1 — trajectory identity**: 54-file corpus, `stats_solve`,
   `MAXC=60000`, default seed vs `precompile/d3261a6`: counters +
   verdict bit-identical.
2. **Gate 2 — instructions**: fixed `MAXC=40000`, {g2-slp, g2-ak128 ×2
   (elimination-heavy class), circuit + worker + frb45 (elim-active
   controls)}: elimination-class geomean ≥ **1.02**, controls in
   0.99–1.01; both-solve corpus geomean ≥ 1.00.
3. **Soundness** (if landed): workspace suite, clippy/fmt/doc,
   `diff_equiv` ≥ 100 k, corpus verdict sweep 0 mismatches, SMT
   differential 0 disagreements, z3 parity.

## Results — REVERTED (Gate 2 failed at 1.0008; the alloc-count target was a mirage)

**Gate 1 passed** (54/54 bit-identical vs `precompile/d3261a6` — the
persistence + the learned-ledger doomed scan are behavior-preserving,
including the retire-order argument). **Gate 2 failed**: elimination-class
geomean **1.0008** (g2-slp 1.0023, g2-ak128 ×2 exactly 1.0000 — no
eliminate activity there at the cap), controls 1.0040 (all within noise,
slightly positive). Below the pre-registered 1.02 bar and inside the
neutrality band → reverted per the letter (same disposition as
watcher-8byte and shrink-retention).

**Why the 77 % allocation count bought ~0.2 % of cost**: ~3.5 M growth
reallocs were eliminated, but a glibc fastbin alloc+free pair is
~30–100 cycles and the occurrence-list growth is amortized — ≈ 0.3 G
cycles on a ~30 G-instruction run. The counting-allocator number
(alloc **count**) was real but alloc count ≠ alloc **cost**; the
perf-annotate view that seemed to confirm allocator dominance was an
aggregation artifact (interleaved inlined frames). Recorded as a
measurement lesson: allocator counts must be priced (cycles/alloc
× count) before they name a lever.

## What this session-segment actually established (kept knowledge)

1. **Gent's saved-position port is dead**: scan instrumentation shows
   `iters/miss` = 2.38 / 2.11 / 2.82 on circuit / noL / si2 (len/miss
   12.9 / 20.2 / 19.1) with 58–65 % of examined literals false — the
   false-prefix Gent would skip is worth ≤ 1 % end-to-end on the best
   file, for a divergence-class change plus header surgery. frb45
   (7.2 iters/miss, 86.6 % false) and worker (52.5 iters/miss, 99.1 %)
   have bigger skippable fractions but negligible propagate shares
   post-landings.
2. **Fresh profile ranking** (`cycles`, no-LTO symbols build,
   `MAXC=20000`): propagate 33.3 % / 6.2 % / 26.0 % and eliminate_phase
   10.2 % / 4.8 % / **29.4 %** on circuit / worker / g2-slp; worker's
   shrink/minimize walk 37.3 % stands as recorded.
3. **g2-slp's eliminate cost is not resolutions** (~10 %, comparable to
   cadical's whole elimination) **and not the allocator** (this study):
   the inclusive tree puts ~10 % in the `ps×ns` pair-loop plumbing and
   6.6 % in backward subsumption; the round structure pays a full
   789 k-clause reconnect + watch rebuild per round for
   triple-digit yields in rounds 2+ (`NIXIE_LOG_ELIM` transcript
   recorded). The next eliminate lever, if anyone takes it, is the
   **round-2+ economics** (schedule/schedule-gating — heuristic class,
   matched-null required), not data-structure capacity.

## Disposition

Code reverted (experiment preserved briefly on `elim-persist-exp`, then
deleted; this study is the artifact). The private target dir and the
profiling worktree were cleaned up.
