# Worker-class memory, slice 3: the BIG as an exact-size CSR + deferred parse attach (2026-09-06)

Slice 3 of the worker-class memory thread (`2026-09-05-worker-class-memory-landing.md`,
`2026-09-06-worker-class-memory-slice2.md`). Slice 2 ended 12.5 MB short of
the −25 % KR on worker_550 (736.5 MB vs ≤723.75) and 4.4 % short on the
worst-ratio KR (2.61× vs ≤2.5×), with the residual attributed to the
pre-search elimination phase's standing heap. This slice removes the two
standing-heap components the attribution named and lands both KRs with
~100 MB of margin.

## Where the peak actually was (heaptrack + phase instrumentation)

Phase-boundary `VmHWM`/`VmRSS` instrumentation (env-gated, removed before
landing) plus a symbolized heaptrack pass on `MAXC=0` (parse only) gave the
first complete account of worker_550's 736.5 MB peak:

| moment | hwm | rss | composition |
|---|---|---|---|
| after parse | 631.8 | 629.9 | arena 247.5 used / **268.4 cap** + BIG **164.7 live / 250.0 cap** + refs 41.2 + ~70 misc |
| after solve-start `shrink()` | 631.8 | 629.9 | BIG shrunk to 164.7 exact — **rss does not drop**: ~85 MB of freed per-literal Vec chunks stay resident in glibc bins |
| elim phase entry (conflicts=2000) | 675.4 | 645.5 | +10.7 MB learned clauses in arena; a ~30 MB transient (hwm−rss) came and went in between |
| elim round 1 | **736.4** | →647 | round-1 occurrence CSR + scratch ≈ +91 MB of net-new pages, freed at round end |

heaptrack's parse-only run attributed the allocations exactly:
**268.44 MB** from `ClauseArena::ensure_capacity` (the arena buffer, 12
realloc calls) and **125.17 + 124.84 = 250 MB** from the two
`BinaryImplicationGraph::add` directions in `attach_watchers` — the
per-literal `Vec<Vec<(Lit, ClauseId)>>` growing by doubling to ~1.5× live.

Two structural facts follow, and they are the whole study:

1. **The BIG's parse-time doubling overshoot (~85 MB) never leaves RSS.**
   The per-literal lists are ~190 k separate small allocations; the
   solve-start `shrink_to_fit` frees them to *allocator bins*, and the
   elimination round's occurrence CSR is one 82 MB `mmap` that cannot reuse
   bin chunks. The dead slack rides under the peak forever.
2. **`VmHWM` is monotone**: the parse-time 632 MB is a floor under
   everything later. Any real cut must prevent the overshoot from ever
   existing, not reclaim it after the fact (the slice-2 `shrink` could not).

## The changes (all trajectory-neutral, identity-gated)

| # | change | where | mechanism |
|---|---|---|---|
| J | **BIG as an exact-size CSR**: `Vec<Vec<(Lit, ClauseId)>>` → `span_end`/`live` CSR + flat `edges` array + per-literal overflow `Vec` for post-build appends | `solver/mod.rs` | full rebuilds (`rebuild_watches_and_binary_graph`, `refresh_binary_graph`) use a two-phase count→layout→fill build (the `RoundOccs` pattern), so the flat buffer is exact-size by construction and one allocation. Incremental appends (learned binaries, gate-congruence sentinels, factoring products) go to lazily-allocated overflow lists keyed *after* the primary froze — ids are append-only, so primary-then-overflow is globally id-ascending, exactly the chronological order the old single per-literal `Vec` held. Deletions compact the span in place (order-preserving memmove) / `retain` the overflow, keeping the walk's by-id merge contract intact |
| K | **deferred parse attach**: `begin_deferred_big`/`finish_deferred_big` wrap the DIMACS parse; `attach_watchers` suppresses BIG edges while the latch is set and the flush materializes the graph from the arena in one exact-size build | `dimacs.rs`, `solver/mod.rs` | during parse the BIG is write-only (first read is solve entry's propagate; parse-time units defer via `pending_parse_unit_flushes`), so the per-literal doubling churn of 20.6 M edge pushes never happens. The flush reproduces the incremental attach's content and order exactly (ids ascending, two edges per live binary) — pinned by a dedicated differential test |
| L | **propagate binary loop** rewritten from take/put-back of the per-literal `Vec` to index-based iteration over the CSR span + overflow snapshot | `solver/propagate.rs` | no borrow held across the `&mut self` trail calls (the old take/put dance existed only for that); the documented invariant (nothing appends under `lit` during its own propagation; no deletions inside propagate) makes the snapshot sound. Conflict-path requeue semantics unchanged |
| M | **`refs` reserve from the DIMACS header**: `p cnf <vars> <clauses>` now reserves the id→ref table up front (bounded `min(C, 2^27)`) | `dimacs.rs`, `clause.rs` | the table's doubling growth transiently held up to 2× live (a 41 MB table peaking ~66 MB); untouched reserve pages cost no RSS, so an inflated header is harmless |

Supervisor lever (1) (wire `trim_slack` into BVE entry) was measured dead:
the arena's slack at elimination entry is 268.4−258.2 = **10 MB**, far under
the trim gate (≥ max(16 MiB, used/2)) — nothing to trim, documented here so
it is not retried. Levers (3) (chunk the eliminator CSR) and (4) (packed
binary tier) were not needed once (2) landed with the correct mechanism —
the edge encoding was already 8 B; the *layout* (per-literal `Vec` doubling
+ bin-retained slack) was what cost the memory.

## Why this is identity-preserving

- Every consumer sees the same per-literal *sequence*: the old structure
  was one `Vec` per literal in chronological push order; the new combined
  view is primary (the rebuild snapshot, ids ascending = chronological at
  freeze time) then overflow (strictly later ids, chronological). A fold at
  the next rebuild re-establishes the same invariant. Both new unit tests
  pin this: `binary_graph_matches_vec_semantics` (randomized
  build/add/remove vs a reference `Vec<Vec<..>>` model, content **and
  order** after every step) and `deferred_big_materializes_incremental_attach`
  (same clause stream through the deferral pair vs plain incremental
  attach — identical views at every literal).
- `rebuild_watches_and_binary_graph`'s phantom tick accounting (the
  BIG-authoritative BCP parity contract) bumps exactly once per live-binary
  direction in the count pass; the parse-time bumps are re-derived by the
  flush's `phantom_reset` + bump. Watch entries, blockers and per-list order
  are reproduced (ids ascending, `[0]/[1]` watch positions).
- The deferral flush runs at parse end on success **and** error paths (the
  wrapper function shape guarantees it), plus defensively at `solve` /
  `solve_with_assumptions` entry, so no path can propagate with an
  unmaterialized graph (a missing BIG edge is a lost binary implication —
  a soundness bug, not a style issue).

**Identity gate: 54/54 corpus files, verdict AND conflict counts
bit-identical** old (`8cb75c0`, itself identity-chained to `cb9f05c`) vs
this tree, re-run with the final committed binary. Full-counter spot checks
on worker_550: conflicts 106143, decisions 717649, propagations 88486164,
restarts 208, walk ticks 9172946 — all bit-identical.

## Memory result (per-child VmHWM, 100 s cap, canonical corpus, all four arms)

| file | slice 2 | slice 3 | Δ | cadical | kissat | nixie/kissat |
|---|---|---|---|---|---|---|
| noL-11-14 | 28.9 | 29.3 | +1.4 % | 15.9 | 20.8 | 1.41× |
| frb65-12-2 | 22.1 | 24.0 | +8.6 % | 16.9 | 12.2 | 1.97× |
| FmlaEquivChain | 83.5 | 86.2 | +3.2 % | 99.2 | 53.6 | 1.61× |
| mrpp_4x4 | 15.2 | 16.0 | +5 % | 13.1 | 12.3 | 1.30× |
| g2-slp | 162.4 | 161.8 | 0 | 115.4 | 73.2 | **2.21×** |
| **worker_550** | **736.5** | **621.7** | **−15.6 %** | 1919.1 | 288.4 | **2.16×** |
| si2-b03m | 110.7 | 110.7 | 0 | 178.2 | 105.4 | 1.05× |
| shuffling-2 | 491.8 | 493.6 | +0.4 % | 927.1 | 275.4 | 1.79× |

- **KR2.1: worker_550 965 → 621.7 MB = −35.6 %** (target ≥25 %, i.e.
  ≤723.75 MB) — **met**, with 100 MB of margin.
- **KR2.2: worst nixie/kissat ratio 2.61× → 2.21×** (g2-slp; worker_550
  itself is 2.16×) — **met** (target ≤2.5×).
- The small-file +1–3 MB moves are the CSR's fixed per-literal overhead
  (`span_end` + `live` + the overflow `Vec` header ≈ +8 B/literal-code over
  the old `Vec<Vec>` header) on instances whose whole footprint is 15–90 MB;
  absolutely small, reported honestly.

## Wall neutrality

Identity is the proof (bit-identical trajectories cannot cost search
work); two confirmations:

- worker_550 end-to-end 33.3 s → 30.8 s on the same machine layout (the
  exact-size CSR rebuild replaces ~190 k per-literal Vec doublings and the
  take/put-back dance in the hot propagation loop);
- a clean paired A/B (11 corpus files, 2 rounds, alternating arms, pinned
  cores, fixed `MAXC=60000` budget — equal work by identity): per-file
  new/old 0.979–1.041, **geomean 1.0063×** — inside the ±5 % neutrality
  band, i.e. the CSR propagate loop is constant-factor neutral.

The standing table recorded at `8cb75c0` therefore transfers to this
commit by construction: identical verdicts, conflict budgets and
trajectories (54/54 gate), wall within noise.

### A measurement-environment note for the next agent

One full identity-gate run reported a single mismatch
(`Timetable_C_392…`: old=Unknown/60000 vs new=Sat/32841) that vanished on
re-run and never reproduced standalone (6/6 reps, both arms identical).
The corpus file was canonical before and after; the only consistent
explanation is `/tmp/sc24f` being rewritten *while the old arm read it*
(shared scratch — the same signature as slice 2's worker_550 drift). The
protocol used for the recorded 54/54 runs: sha-verify all 54 files against
`precompile/corpus-sc24f/` immediately before AND after the gate.

## Gates

- `cargo build --all-features` clean; release builds warning-free.
- `cargo nextest run --workspace --all-features`: **10473/10473** + doc tests
  (10471 pre-existing + the two new BIG tests).
- `cargo clippy --all-features --all-targets -- -D warnings`: zero warnings.
- `cargo fmt --all -- --check`: clean.
- `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features`: clean
  (the literal `-- -D` spelling after `cargo doc` is rejected by this
  cargo's argument parser — toolchain artifact, recorded in both prior
  iterations).
- Z3 parity: 170 benchmarks, 169 agree + 1 Z3-Unknown inconclusive,
  **0 mismatches**.
- Identity: 54/54 verdicts+conflicts vs `8cb75c0` (chained to `cb9f05c`),
  re-run with the final binary.

## What is still open

The worker_550 residual (621.7 MB vs kissat's 288.4) now decomposes as:
arena 259.6 (live binaries at 16 B/slot + non-binaries) + BIG CSR 164.7
(live edges, exact) + refs 41 + eliminator round CSR ~91 transient + ~65
misc. The next structural levers, in the order the numbers suggest:
the supervisor's lever (4) — a packed 16–24 B binary tier replacing the
44 B arena slot + BIG edge pair (kissat's shape: binaries live *only* in
its packed tier; we pay arena slot + BIG edge ≈ 24 B/binary) — and the
eliminator occurrence CSR chunking (lever 3). Both are larger ports;
neither is needed for the KR targets anymore.
