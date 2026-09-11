# Unsafe BCP arms: what −30 % cycles is not (2026-09-11)

Mandate: close the wall/conflict gap; narrowly-scoped unsafe Rust allowed.
This round built and measured four unsafe/ILP arms against the standing
anchors. **None meets a landing bar; the patch is preserved as an asset at
`data/2026-09-11-unsafe-bcp-arm.patch`.** The measurements re-prove, with
fresh arms, where the cycle cost lives — and where a −30 % move would have
to come from.

## Arms and verdicts (paired PMU, pinned core, ASLR off where noted)

| arm | instructions | cycles | verdict |
|---|---|---|---|
| subsume kernel: unchecked mark/payload (`mark_read`/`mark_write`, unchecked `ConnectedPayloads::get`) | **−4.1 % crn**, −0.6…−3.3 % 7/7 anchors | −0.3…−1.7 % | real, small |
| + guarded normalize stores (skip no-op pair stores on re-fired parked watchers) | **−2.9 % geomean, 8/8 negative** | **−0.45 % geomean** (crn −0.35, si2 −1.9, mrpp −0.7, break +0.4, constraints +0.35) | below band; not landed |
| ILP group probe (8-wide independent value loads in the saved-pos replacement scan) | **+13…+27 %** on 3-SAT corpora | worse | reverted |
| `PropagationQueue::append` re-inline | confounded with the probe arm | — | reverted with it |

The instruction-only win repeats the PGO lesson at smaller scale: the
propagate loop is **stall-bound** — the removed compare/branch/store
instructions were executing inside stall slots, so cycles barely move.
PGO already measured −7 % instructions → 0 % cycles; the repo rejected it
for exactly this reason, and the same reasoning rejects this arm's unsafe
surface at −0.45 % cycles.

## The ILP probe failure mechanism (worth recording)

1. First form: the new scan helper de-inlined (`#[inline]` size heuristic;
   its nested `unsafe fn` counts) — a **real call per miss visit**, and the
   two-segment closure was outlined into one shared callable:
   `find_saved_pos_hit_values::{{closure}}` alone = **12.3 % of whole-run
   samples** on crn (+12–14 % instructions).
2. `#[inline(always)]` + closure→`fn` cut that to +2.8…+5.9 % — still
   positive: the modal saved-pos scan is **1–2 steps** (that is what Gent's
   saved position records) and 3-SAT tails are one literal; there is no
   dependency chain left to overlap.
3. An `n < 4` serial fallback gate did not recover it: the hybrid's mere
   presence in the scan body perturbs layout/register allocation (+~5 %
   gross on files whose every execution took the serial path).
4. Conclusion: the serial saved-pos scan is already near-optimal for this
   workload shape; ILP overlap has nothing to overlap. The one apparent
   large win (6s167-opt "−25 % cycles") was a measurement artifact — see
   the traps below.

## Measurement traps found (both bit us)

- **`precompile/corpus-sc24f/6s167-opt.cnf` solves in ~80 ms** on current
  HEAD (pre-search passes collapse it). Its cycle/instruction percentages
  are startup- and layout-dominated and swung −25 %…+41 % across runs. It
  must not be used as a throughput anchor at full solve; the campaign-era
  1.2 s / 62 k-conflict reference no longer holds.
- **ASLR layout luck** moves stall-bound runs by double-digit percentages
  run-to-run. Paired PMU comparisons on this codebase need
  `setarch -R` (fixed layout) + repeated interleaved runs + medians; the
  `cpu_atom/<not counted>` line must be excluded when parsing `perf stat`
  on this host (hybrid PMU).

## So where would −30 % cycles come from?

Every engineering pool is now measured to sub-band: per-visit codegen
(eight arms + PGO), density (8-byte watcher +0.7 %), single-pass BCP
(built, lost), analysis scratch (reverted), this round's four arms. The
cycle cost that remains is:

1. **branch misses**, ~18/propagation × ~17 c ≈ 23 % of the loop's cycles —
   scaling with *visit count* and per-entry branch structure (the
   deliberate half: id+ref watcher, two-pass BIG, phantom ticks);
2. **visit count itself** (17.4/prop on the old 6s167 shape; ~5.9 on
   j3037): a search-state property (watch placement, blocker quality, DB
   retention);
3. **IPC/register pressure** (~1.25×): fewer live values per entry — only
   a different *entry format* changes this, and both density variants
   measured negative.

A −30 % cycle move therefore requires doing **less work per conflict**,
not the same work faster: visit-count policy (blocker refresh, watch-move
policy, retention) or fewer conflicts — both heuristic-class (trajectory-
changing), both owned by the matched-null program in
[`docs/BENCHMARKING.md`](../BENCHMARKING.md) and the conflicts program of
the 2026-09-07 campaign (median 2.6× conflicts gap vs cadical, seed-
matched — the single pool where a ≥2× lives).

## Disposition

- Worktree reverted; nothing landed. The patch (subsume unchecked kernel +
  guarded stores: −2.9 % instructions, 8/8 non-negative, trajectory-
  identical, debug-assert-guarded) is preserved above for reuse if a
  future change makes the loop instruction-bound (e.g. a colder memory
  hierarchy or a density win that changes the stall mix).
- `Trail::values()` accessor, `find_saved_pos_hit_values` and the oracle
  test are part of the patch, not main.
