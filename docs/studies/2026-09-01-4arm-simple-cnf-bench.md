# Four-arm simple CNF benchmark: main vs upstream 0.3.3 vs CaDiCaL vs Kissat (2026-09-01)

A standing-table-style snapshot (score = solved at cap), not a heuristic A/B —
no improvement claim is made, so no matched null applies (`docs/BENCHMARKING.md` §2
governs *claims*; §12 requires reference arms on SAT-side tables, which this carries).

## Why a 9-file set

The 261-file standing corpus (`satcomp2025/main_easy_mid` + the 108-file
`satcomp2024/bench`, untracked-by-design per the v0.3.3 port) is **no longer on
disk** — only 4 `satcomp2024/bench` files survive, plus 5 CNF fixtures in-repo.
Per instruction, this run uses **every CNF file currently in the repository**
(9 files) rather than re-downloading corpora:

| instance | vars | clauses | verdict (cross-agreed) |
|---|---|---|---|
| `sat_simple` | 10 | 30 | sat |
| `break_unsat_06_07` | 1 101 | 5 037 | unsat |
| `noL_11_14` (standing-gap hard-trio member) | 1 419 | 7 835 | sat |
| `crn_11_99_u` | 1 287 | 2 332 | unsat |
| `summle_x4044` | 93 724 | 198 976 | sat |
| `j3037_10_mdd_bm1` | 14 400 | 63 952 | unsat |
| `circuit_48in64out_…_seed1` | 2 848 | 168 064 | sat |
| `constraints_17_0.4_1` | 2 720 | 58 990 | sat |
| `si2-b03m-m800-03` | 10 862 | 472 588 | sat |

## Arms

| arm | binary | sha256[:16] | role |
|---|---|---|---|
| `nixie-main` | `precompile/5665273/cnf_solve` (CaDiCaL preset, default) | `e6d128b1a9fd154f` | treatment |
| `nixie-upstream-0.3.3` | `precompile/e7c7bca/cnf_solve_upstream` (CaDiCaL preset; minimal harness added uncommitted in a throwaway worktree of tag `v0.3.3` = `e7c7bca`) | `b63ca04d285caff4` | baseline |
| `cadical` 3.0.1 | `../temp/cadical/build/cadical` | `015dafc87f3ecf1e` | reference (parity) |
| `kissat` 4.0.4 | `../temp/kissat/build/kissat` | `e08eddf914bbd918` | reference (goal) |

Protocol: **serial** (one run at a time, quiet machine), **60 s wall cap** via
external `timeout -k 2` on all arms alike, single deterministic run per cell
(all four solvers are deterministic at default seed). Verdict parsed from the
`s …` line; cadical/kissat SAT models checked against the original CNF.

## Result — solved at 60 s (serial)

| instance | nixie-main | nixie-upstream-0.3.3 | cadical 3.0.1 | kissat 4.0.4 |
|---|---|---|---|---|
| sat_simple | sat 0.0 s | sat 0.0 s | sat 0.0 s | sat 0.0 s |
| break_unsat_06_07 | unsat 0.7 s | unsat 2.8 s | unsat 0.5 s | unsat 0.4 s |
| noL_11_14 | sat 33.9 s | **TO** | sat 4.4 s | sat 19.1 s |
| crn_11_99_u | unsat 1.0 s | unsat 17.2 s | unsat 0.4 s | unsat 0.7 s |
| summle_x4044 | sat 6.9 s | **TO** | sat 4.6 s | sat 4.2 s |
| j3037_10_mdd_bm1 | unsat 34.2 s | **TO** | unsat 21.9 s | unsat 14.8 s |
| circuit_48in64out | sat 9.2 s | **TO** | sat 5.8 s | sat 2.2 s |
| constraints_17_0.4_1 | sat 7.0 s | **TO** | sat 1.0 s | sat 4.4 s |
| si2-b03m-m800-03 | sat 1.7 s | **TO** | sat 2.2 s | sat 2.5 s |
| **solved / 9** | **9** | **3** | **9** | **9** |

- **Verdict mismatches: 0** across every decided (instance, arm) pair.
- All cadical/kissat SAT models re-verified against the CNF (0 failures).
  The nixie arms print no model (`cnf_solve` prints the `s` line only), so their
  SAT verdicts rest on the 4-way agreement — with both references model-checked.
- Conflict counters were not captured in this run (cadical/kissat emit them in
  solver-specific stat blocks; kept out of scope for a score-only snapshot).

## Reading

1. **main ≥ upstream 0.3.3 decisively**: 9/9 vs 3/9, and on every decided
   instance upstream is 4–17× slower (0.7→2.8 s, 1.0→17.2 s). This is the
   2026-08/09 SAT-core arc (BIG-authoritative BCP, write-elision, shrink
   fallback fix, RANDPOL landing …) doing exactly what the individual studies
   measured — here visible end-to-end on one table.
2. **main is competitive with the references on this set but not faster**:
   cadical sweeps 9/9 with the best time on 6 files; main's slowest solves
   (`noL_11_14` 33.9 s vs cadical 4.4 s, `j3037_10_mdd_bm1` 34.2 s vs 21.9 s)
   are the standing-gap study's known hard-class members — no surprise and no
   new information beyond consistency.
3. `constraints_17_0.4_1`, which `docs/BENCHMARKING.md` §12 cites as the
   kissat-counter-completeness example (230.9 M search ticks), solves in
   1–7 s for all arms — the counter lesson stands, the instance is not a
   discriminator at a 60 s cap.

## Caveats (explicit)

- **9 files, single seed, wall-clock cap** — a score snapshot in the standing-
  table tradition, not a §2/§5 measurement. No effect size should be read off
  it; the upstream-vs-main margin (6 files + 4–17× on the rest) is far outside
  any noise band, but fine ordering *within* the leaders is not resolvable.
- The corpus situation is a standing problem: re-downloading
  `satcomp2025/main_easy_mid` (GBD `track=main_2025`) and `satlib` is a
  prerequisite for the real 261-file table with its kissat column
  (`docs/BENCHMARKING.md` §12 "What to re-measure").
- Upstream 0.3.3 was run through a minimal equivalent harness
  (`ConfigPreset::CaDiCaL`, same parse/solve path) built uncommitted in a
  throwaway worktree; the binary is cached at `precompile/e7c7bca/`.
