# CSR watch lists: design kickoff for the multi-session architecture item (2026-09-13)

Round-10 handoff item 3.  The ELS rewatching study
(`2026-09-12-els-rewatching.md`) closed in-place watch surgery as
architecturally unprofitable at the current representation and named
the exit: CSR/arena watch lists, where **rebuild = memcpy and surgery =
sorted splice**.  This document is the next session's entry point: the
measured access inventory, the layout, the migration slices, and the
stop-gates.  Nothing here is implemented yet.

## What the payoff is (and is not)

The target is the ELS rewrite cluster on si2-class walls: the full
watch/BIG rebuild sweeps the clause arena clause-major once per ELS
round (~6 rounds on si2; already allocation-free and −0.9 % from the
2026-09-12 landings).  CSR does **not** remove the BIG rebuild — only
the watch half — so the realistic ceiling is a few percent of
si2-class walls, and the ELS surgery that unlocks must beat the
memcpy-rebuild it replaces.  The ELS study's surgery lost by 9.7 %
*because* normalization at `Vec<Vec<Watcher>>` is entry-major; at CSR
the same normalization is span-local.

## Slice 1 result (landed same day, `1c8a1a99`)

`CsrWatchBuild` (the `RoundOccs` pattern adapted to `Watcher` entries)
plus a per-rebuild shadow behind `NIXIE_CSR_SHADOW=1`.  Validation
across 6s167-opt, j3037_10_mdd_b and si2-b03m: **every rebuild
compares equal, order included** (21.7k literals, up to 740k entries
on si2), `mismatched=0` throughout.  Standalone two-sweep build cost:
90-160 µs (6s167), 0.5-1.4 ms (j3037), 12-18 ms (si2) — the upper
bound for slice 2's merged build, which shares the rebuild's existing
sweep (≈ half).

The stop-gate itself resolves **analytically**, recorded here because
it upgrades slices 2-4 from "semantic risk" to "representation
switch": the drifted `Vec` list is always *(prefix survivors in order)
++ (arrival-ordered appends)* — in-place compaction, `retain`-removal
and append are all order-preserving on that decomposition — and that
is exactly *CSR primary ++ overflow*.  No mutation interleaves primary
and overflow entries, so the two representations are order-isomorphic
at every point of the search.  The empirical bar stays (trajectory
identity per slice), but no semantic change is expected.

## Reference check (done first, per AGENTS)

Neither reference uses CSR watches: cadical `internal.hpp` has
`typedef vector<Vector<Watcher>> Watches`, kissat scans per-literal
stacks.  **This is novel territory** — no port target, so the burden of
proof is the bit-identity + screen bar at every slice, and the design
must lean on the one in-house precedent: `RoundOccs`
(`solver/eliminate.rs`) — a CSR primary + per-literal overflow + exact
combined-view contract, built for exactly this reason (glibc bin
retention) and trajectory-neutral by construction since 2026-09-10.

## Measured access inventory (`watches.<method>` counts across the crate)

| site | count | CSR shape |
|---|---|---|
| `len` | 16 | `starts[lit+1]-starts[lit]` (+overflow len) — **phantom tick parity reads list sizes; the counters must stay byte-identical** |
| `get` (read) | 13 | combined view slice |
| `remove_clause(lit, r)` | 8 | scan span for `r`, tombstone or span-compaction |
| `add(lit, w)` | 8 | overflow append (`attach_watchers` ×2 per learned clause — the hot mid-search insert) |
| `get_mut` | 7 | needs a combined-view cursor abstraction (two arrays) |
| `phantom_len/bump` | 9 | unchanged (own arrays) |
| `as_mut_ptr` (BCP cursors) | 3 | primary span gives the same `&mut [Watcher]` shape; overflow must be drained-after or scanned-second |
| `truncate/resize/restore/snapshot/compacting/clone` | 11 | mechanical ports |
| `reset_lists_in_place` (rebuild) | 1 | **the memcpy**: count → `layout` → sequential fill (RoundOccs's exact pattern) |

The BCP's per-literal scan (`list_kernel::scan_list`) is an in-place
read/write prefix compaction over a borrowed `&mut [Watcher]` that also
**moves** entries to other literals' lists (watch moves append).  In
CSR: the compaction runs inside the span (entries are contiguous),
survivors keep `[start, write)`, and moves append to the *destination*
literal's overflow — the same primary-sorted-plus-arrival-overflow
order the current code drifts to between rebuilds.

## The critical semantic to pin (the stop-gate)

Today a search-drifted list is one array in mixed order; the rebuild
re-sorts by `ClauseRef`.  CSR's combined view is *sorted primary, then
arrival-ordered overflow* — **not** the same array order.  If any
consumer's behavior depends on the interleaving (BCP visit order is
trajectory-load-bearing: it decides which conflict fires first), the
representation change is not trajectory-neutral and must be gated as a
semantic change with the full screen — or the overflow must merge
in-order at a cadence that reproduces the drift pattern.  Slice 1
exists to answer exactly this, with the ELS study's check-mode pattern
(`NIXIE_ELS_REWATCH_CHECK`): end-state equality is insufficient; the
bar is **full-solve trajectory identity** on the 54-file corpus at
conflict caps, then the 60 s screen.

## Migration slices (each independently landable)

1. **Shadow build** (no search-path use): construct the CSR beside the
   `Vec<Vec<Watcher>>` at every rebuild, assert combined-view equality
   with the built lists per rebuild.  Cost: transient memory + build
   time; default-off behind a feature/env.  Answers the order-parity
   question with zero risk.
2. **Read paths** switch to the combined view (`get`, `len`,
   subsume candidate scans).  Trajectory-identity gate.
3. **BCP scan** switches to spans (`propagation_parts` returns
   `(&mut [Watcher], &mut [Vec<Watcher>])` pairs or the scan splits
   primary/overflow passes — the cursor machinery in
   `list_kernel`/`watch_cursor` keeps its borrowed-slice shape).
   Trajectory-identity gate.
4. **Write paths**: `add`→overflow, `remove_clause`→span compaction,
   `attach_watchers` hot path profiled (the per-learned-clause insert
   must not regress BCP).
5. **The payoff**: re-implement ELS rewatching on CSR (the surgery the
   2026-09-12 study built and removed — its design carries over
   verbatim once the representation holds) and A/B it against
   memcpy-rebuild on the si2 class.  If the flip does not materialize,
   the item closes negative with the measurement.

## Stop-gates

- Slice 1 finds order-parity that cannot be reproduced without
  semantic change → re-evaluate (either accept a screen-gated semantic
  change or close the item).
- Slice 4's `attach_watchers` overflow path regresses the BCP measurably
  (learned-clause attach is the highest-frequency insert) → the
  overflow must batch (e.g. attach into a pending buffer drained at
  conflict boundaries) before proceeding.
- Phantom tick parity (`bin_phantom` sizes drive restart/stable
  schedules) breaks anywhere → fix before any trajectory claim.

## Infrastructure inherited for this item

- `RoundOccs` (`solver/eliminate.rs`) — the CSR+overflow precedent with
  `layout`/`connect`/`push`/combined-view; generalizing it to
  `Watcher` entries is the natural implementation vehicle.
- The ELS study's check-mode pattern and its surgery design (steps 1-5
  in that study) — reusable verbatim for slice 5.
- The 54-file trajectory-identity harness + 60 s screen runners under
  `docs/studies/assets/inproc-amplitude-2026-09-12/`.
