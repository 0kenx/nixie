# ELS substitution scratch reuse + the 2026-09-11 throughput re-profile (2026-09-11)

Round goal: the per-conflict throughput gap to kissat visible in the 20-file
3-arm table (break 2.0×, crn 1.7×, j3037 2.0× per-conflict wall vs kissat).
Profiled six files (`break`, `crn`, `mrpp`, `si2`, `j3037`, `constraints`)
with the `profile.perf` build — first profiles on *this* corpus; the
2026-09-07 campaign's closures were measured on `6s167`/`crypto1`.

## What the profiles said (and what was already closed)

| share | break | crn | mrpp | si2 | j3037 | constraints |
|---|---|---|---|---|---|---|
| `list_kernel::scan` (2 entries) | 58% | 49% | 57% | 17% | 44% | 73% |
| `propagate` outer frame | 8% | 2% | — | — | **23%** | 2% |
| `subsume_round` | 4% | **14%** | 9% | 10% | 2% | 5% |
| inprocess/ELS/elim cluster | — | — | — | **~35%** | — | ~4% |

BCP per-visit codegen, watcher density, arena locality, the analysis walk and
the inline-bins restructure are all closed by the six 2026-09-07 closures
plus `2026-09-07-bcp-inline-bins.md` — re-confirmed, not retried. The
remaining items this round:

1. **j3037 anatomy** (`bcp-stats`): 5.87 watch visits and 1.42 BIG edges per
   propagated literal, 950 propagations per conflict, 76 % of propagations via
   the BIG. The 23 % outer-propagate frame is the per-*literal* fixed cost
   (queue, CSR probe, assign) over 330 M literals — spread thin, mined class.
   Kissat shape comparison: 1.73× props/sec; the conflicts gap (1.24×) and
   the throughput gap compound.
2. **`subsume_round` budget vs cadical** — reference check: nixie clamps
   `cum_search ∈ [1e6, 1e9]` checks; cadical's actual defaults
   (`options.hpp`) are `subsumemineff = 0` (floor `max(δ, 2·active)`) and
   `subsumemaxeff = 1e8`. The nixie comment's "1e6/1e9" reference values are
   wrong. Measured impact on this corpus: none actionable — crn/j3037 rounds
   are *schedule*-limited (36 rounds × ≤11 k scheduled clauses), not
   budget-limited; only sub-1e6-prop early rounds overspend, and the pass is
   the measured-net-positive effort schedule (`2026-09-07-inproc-effort-
   schedule.md`, 0.83× conflicts at 5 seeds). Not changed.
3. **`eliminate.rs` `doomed` full-DB scan** (the `from_iter<ClauseId,
   Filter<Map<Range>>>` 3.7 % frame on si2): cadical's
   `mark_redundant_clauses_with_eliminated_variables_as_garbage` is the same
   full scan with the same early-break flag check (`elim.cpp:736`). Shape
   parity — not a defect. Not changed.
4. **si2 inprocess cluster (~35 %)**: ELS substitution + eliminate phase +
   watch/BIG rebuilds + arena compaction, all reference-shaped O(live) passes
   over a 600 k-clause DB. Rebuilds are each consumed by a following
   propagate (no coalescing). The one *defect* found in there is the landed
   fix below.

## The landed fix: ELS per-clause allocation churn

`substitute_equivalent_literals_round` allocated **two heap buffers per live
clause per round**: the `SmallVec<[Lit; 8]>` mapped-literals collect (spills
its inline 8 on wide-uniform clauses — si2's width-20 originals) plus
`Vec::with_capacity` for the rewritten clause. On si2: 600 k clauses × 6
rounds > 1 M malloc/free pairs, visible as the `_int_malloc`/`realloc`/
`memmove` cluster. Both hoisted to clear-and-refill scratch outside the loop.

Trajectory identity: **54/54 standing-corpus files bit-identical**
(conflicts/decisions/propagations/verdict; the two "differs" cells in the
first parallel screen were a runner artifact — 8 workers pinned to one core —
and are identical solo). Paired PMU instructions (pinned core 3, both arms):

| file | instructions | Δ |
|---|---|---|
| si2-b03m-m800-03 | 24.335 G → 23.920 G | **−1.71 %** |
| break_unsat_06_07 | 8.387 G → 8.376 G | −0.13 % |
| mrpp_4x4 | 32.249 G → 32.231 G | −0.06 % |
| constraints_17 | 50.211 G → 50.195 G | −0.03 % |
| j3037_10_mdd_bm1 | 241.953 G → 241.907 G | −0.02 % |
| crn_11_99_u | 12.600 G → 12.600 G | −0.00 % |

Uniformly non-negative, concentrated exactly where ELS rewrites wide clauses.
Landed under the zero-complexity rule (removes per-iteration allocations,
adds no structure): same rationale as the 2026-09-07 probe-fold landing.

Gates: workspace nextest 10 928/10 928; clippy/fmt/rustdoc clean; Z3 parity
4.16.0 — 175 files, 0 wrong (1 z3-Unknown inconclusive).

## Where the constant-factor program now stands

Nothing above ~2 % remains in the engineering class on this corpus. The
compounding 1.4–1.7× per-propagation instruction gap vs kissat/cadical is
spread across per-literal fixed costs (j3037's shape) and per-visit bodies —
both closed to sub-1 % levers by the 2026-09-07 campaign and re-confirmed
here. Further gains are heuristic-class (visit counts, blocker quality,
inprocessing schedule density on binary-dense formulas) and need the
matched-null machinery, or architectural (incremental ELS rewatching instead
of rewrite-all + full rebuild — a soundness-sensitive refactor of the ELS
pass, recorded as the largest single remaining si2-class lever at ~8 % of
that file's wall).
