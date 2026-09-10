# Z3 SAT-caching on `circuit_48in64out` — real lever, does not close the 7× gap (2026-09-10)

Z3 4.16.0 solves `circuit_48in64out` SAT with **23,149** conflicts (0.63 s).
Nixie/Kissat sit at ~163k / ~277k (n/z conf **7.02×**). Z3 has no circuit/LUT/XOR/ANF
solver on this DIMACS path (`cardinality.solver` forced off; `xor_solver` hardcoded
false; `sat.anf` off; `lut_finder` is a dead friend). Ablating Z3 itself:

| Z3 config | conflicts |
| `sat.phase=caching` (default) | **23,149** |
| `sat.phase=basic_caching` | 218,200 |
| `sat.subsumption=false` | 206,523 |
| `sat.probing=false` | 121,315 |

The 7× is search quality. This study ports Z3's `PS_SAT_CACHING` two-phase
search (sticky longest conflict-free prefix during the SAT period; 400-conflict
periods growing 400/800/800/1200/…) as `SolverConfig.sat_caching` (0 off, 1 on,
2 matched null that complements the sticky polarity). Default stays **off**.

## Cells (seed 0, CaDiCaL preset, `stats_solve`, this tree)

Input `satcomp2024/bench/303480ca7e8322d771c94caf4ebd4e95-circuit_48in64out_with_700gates_4in4out_dist128_seed1.sanitized.cnf`
(2,848 vars, 64 units + 168,000 width-8 LUT cubes).

| arm | verdict | conflicts | T/N |
| off (`sat_caching=0`) | sat | 231,596 | — |
| treatment (`=1`) | sat | **153,716** | **0.70×** vs null |
| matched null (`=2`) | sat | 219,116 | — |

Collateral, same binary:

| file | off | treatment | note |
| `constraints_17_0.4_1` (sat) | 85,245 | **28,074** | Z3 is 19,381 |
| `j3037_10_mdd_bm1` (unsat) | 366,030 | 429,325 | 1.17× worse |

## Verdict

- **Not a specialized circuit solver.** The CNF is a 4-in-4-out LUT circuit;
  Z3 never reconstructs gates.
- SAT-caching is a **real SAT-finding lever** (circuit T/N 0.70; constraints
  0.33× vs off) and **hurts UNSAT** (j3037 1.17×). It does **not** close the
  7.02× conflict gap (153k vs Z3 23k). Remaining distance is Z3's VSIDS-only
  core plus 465k self-subsuming resolutions vs Nixie's ~5k.
- Default stays off. Knob: `SAT_CACHING=1` / `NIXIE_SAT_CACHING=1`. Do not
  default-on without a multi-seed corpus; the UNSAT regression is already
  visible at n=1.
