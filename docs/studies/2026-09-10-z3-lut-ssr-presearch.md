# Z3 LUT-cube SSR: CaDiCaL one-watch never connects the 8-lit encoding (2026-09-10)

Follow-up to [SAT-caching](2026-09-10-z3-sat-caching-circuit.md). Z3 4.16.0's first
inprocess (`sat.inprocess.out`) shrinks `circuit_48in64out` from **168,064** clauses
(64 units + 168,000 width-8) to **68,948** (173 units, 249 binary, 11k ternary,
29k width-4, 6.5k width-5, **21,633** width-8). Nixie on that dump: 108k conflicts
(vs 232k on the original). The remaining Z3 search on the dump is 17k.

## Root cause

CaDiCaL one-watch subsumption connects a clause only on its minimum-occurrence
literal, and only if that list is ≤ `subsumeocclim` (100). A 4-in-4-out LUT cube
has ≥240 occurrences per variable, so **none of the 168k original cubes ever
connect**. `self_subsumed` stayed ~5k (learned-clause noise). Z3
`back_subsumption1` walks every occurrence of the min-occ variable, both
polarities — 465k self-subsuming resolutions.

Pre-search elim is also off by default (`presearch_collapse`, cadical conflict
scheduling). That is a separate, measured-negative full-elim lever
(`2026-08-inprocessing-schedule.md`); this pass is SSR-only.

## Fix

`presearch_backward_simplify`: Z3-shaped backward SSR over original clauses,
small-first, 1e8 check cap, **one round by default**. Auto-runs when the original
CNF is wide-uniform (modal width ≥6 covering ≥75% of size≥3 originals, ≥1000 such
clauses). `NIXIE_PRESUB=1` forces; `NIXIE_PRESUB=0` skips;
`NIXIE_PRESUB_ROUNDS=N` overrides the cap.

## Cells (seed 0, CaDiCaL preset, `stats_solve`)

| arm | circuit_48in64out | constraints_17 (sat) | j3037 (unsat) |
| `NIXIE_PRESUB=0` | 231,596 | 85,245 | 366,030 |
| auto (wide-uniform, fixpoint) | **110,180** | 85,245 (did not fire) | 366,030 (did not fire) |
| auto + failed-literal probe, 3 rounds | **65,539** | (did not fire) | (did not fire) |
| auto + probe, **1 round (default)** | **44,894** | did not fire (44,381 on this tree) | — |
| auto + `SAT_CACHING=1` | 128,573 (fixpoint) | — | — |
| Z3 4.16.0 | 23,149 | 19,381 | 272,037 |

`self_subsumed` on circuit: 5,084 → **547,517**. Auto did not fire on the two
collateral files (identical conflicts). SAT-caching on top of this pass is
trajectory-negative here; leave it off.

## Verdict

This closes the **simplify half** of the 7× gap (232k → 110k, matching Nixie on
Z3's dumped CNF). A post-SSR failed-literal probe (Z3 assigned 16, we get 1)
plus **stopping after one SSR round** moves the same binary **179k → 45k**.
Residual formula is actually *smaller* than Z3's first inprocess (57k vs 69k
clauses, 4k vs 22k width-8); Z3 SAT-caching on *our* dump is 50–662k depending
on round count, so the leftover **1.94×** (45k vs 23k) is search on a
differently-shaped residual, not missing SSR. Do not default-on SAT-caching; do
not raise CaDiCaL `subsumeocclim` globally; do not run extra SSR rounds on this
family. The auto gate keeps the pass off the standing corpus except LUT-cube
encodings. `NIXIE_PRESUB_TRACE=1` / `NIXIE_DUMP_POSTSSR=path` dump the residual.

## Negative: circuit PI-first (2026-09-10, same day)

`domain_priority` on the rarest original variables (occ = 240 = one 4-in-4-out
gate pin) is the textbook circuit-SAT PI order. Measured:

- **After SSR:** residual modal width is 4, so a post-SSR occ ranking is not
  the PIs (2 vars at occ 13–14). Forcing that ranking: 66k → 111k.
- **On original occ, after SSR:** PI-first via `domain_priority` (every
  decision is a remaining pin until they are all assigned) **timed out at
  180s**. Flattening already destroyed the LUT BCP that would make PI
  assignments useful; the search then spends a long prefix on variables that
  barely appear in the residual.
- **Without SSR (cubes intact + PI-first):** also timed out at 180s.

Do not seed `domain_priority` from occurrence on this family. Walk's printed
`minimum=0` is an uninitialized counter, not a found model.

## Extra SSR rounds are trajectory-negative (2026-09-10)

Round 0 does the work (102,060 subsumed, 540,747 strengthened). Further rounds:

| `NIXIE_PRESUB_ROUNDS` | conflicts |
| 1 (default) | **44,894** |
| 2 | 96,572 |
| 8 (fixpoint, rounds 0–2) | 65,539 |

Leftover vs Z3 23,149 is **1.94×**. Extra rounds reshuffle CDCL without matching
Z3's residual (Z3's first inprocess is one simplify). Default cap is 1.

## Negative: Z3 both-polarity intersection probing

CaDiCaL `probe_round` only schedules binary-implication roots; after SSR the
residual is width-4 and that queue is almost empty (1 failed literal). Z3
`process_core` probes every variable both ways and forces the Stålmarck
intersection. Implemented as `probe_both_polarities` (`NIXIE_PRESUB_Z3PROBE=1`).
On this family it assigned 4 units (trail 72 vs 67) and **raised** conflicts
66k → 117k. Sound, not useful here. Unit tests cover intersection and failed
literals. Leave off.

Other search copies on the 1-round residual are also worse: `SAT_CACHING=1`
95k, `VSIDS=1` 80k, `NO_STAB=1` 321k, `ELS_PRE=1` 82k. The 23k is Z3 search
× Z3 residual; neither side copies onto the other.
