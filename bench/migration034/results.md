## Results

All 264 registered cells completed. Counts below are decisive answers consistent
with available corpus labels and references, not model/proof certification.

| Sample | Solver | Solved | SAT / UNSAT | Unknown | Timeout | Error | Total elapsed (s) | PAR-2 (s) |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| SAT (24) | before | 24 | 12 / 12 | 0 | 0 | 0 | 17.13 | 0.714 |
| SAT (24) | after | 24 | 12 / 12 | 0 | 0 | 0 | 17.02 | 0.709 |
| SAT (24) | z3 | 24 | 12 / 12 | 0 | 0 | 0 | 13.85 | 0.577 |
| SAT (24) | kissat | 24 | 12 / 12 | 0 | 0 | 0 | 5.64 | 0.235 |
| SAT (24) | cadical | 24 | 12 / 12 | 0 | 0 | 0 | 8.39 | 0.350 |
| SMT (48) | before | 24 | 6 / 18 | 13 | 9 | 2 | 365.91 | 31.233 |
| SMT (48) | after | 24 | 6 / 18 | 10 | 13 | 1 | 471.18 | 31.252 |
| SMT (48) | z3 | 35 | 11 / 24 | 2 | 11 | 0 | 370.44 | 17.052 |

Whole-process instruction ratios are paired geometric means; lower is cheaper.
Only jointly solved, agreeing cells enter a ratio. Different rows can have different
pair sets, so their ratios must not be combined transitively.

| Sample | Ratio | Pairs | Instructions | Elapsed diagnostic |
|---|---|---:|---:|---:|
| SAT | after/before | 24 | 1.0016 | 0.9733 |
| SAT | after/z3 | 24 | 3.2599 | 1.3308 |
| SAT | after/kissat | 24 | 1.2921 | 1.0797 |
| SAT | after/cadical | 24 | 2.5089 | 1.1455 |
| SMT | after/before | 23 | 1.3678 | 1.2670 |
| SMT | after/z3 | 24 | 4.8360 | 2.2098 |

SAT/UNSAT split for the migration pair:

| Kind | Answer | Pairs | After/before instructions |
|---|---|---:|---:|
| SAT | sat | 12 | 1.0016 |
| SAT | unsat | 12 | 1.0017 |
| SMT | sat | 5 | 1.7574 |
| SMT | unsat | 18 | 1.2758 |

Per-family solved counts (Nixie columns are before/after):

| Kind / family | N | Before | After | Z3 | Kissat | CaDiCaL |
|---|---:|---:|---:|---:|---:|---:|
| SAT / uf100-430 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uf150-645 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uf200-860 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uf250-1065 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uf50-218 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uf75-325 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uuf100-430 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uuf150-645 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uuf200-860 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uuf250-1065 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uuf50-218 | 2 | 2 | 2 | 2 | 2 | 2 |
| SAT / uuf75-325 | 2 | 2 | 2 | 2 | 2 | 2 |
| SMT / AUFLIA | 4 | 1 | 1 | 1 | — | — |
| SMT / QF_ANIA | 4 | 1 | 1 | 3 | — | — |
| SMT / QF_AUFLIA | 4 | 4 | 3 | 4 | — | — |
| SMT / QF_BV | 4 | 2 | 3 | 3 | — | — |
| SMT / QF_IDL | 4 | 3 | 3 | 3 | — | — |
| SMT / QF_LIA | 4 | 1 | 1 | 4 | — | — |
| SMT / QF_NIA | 4 | 0 | 0 | 2 | — | — |
| SMT / QF_UF | 4 | 4 | 4 | 4 | — | — |
| SMT / QF_UFIDL | 4 | 2 | 2 | 3 | — | — |
| SMT / QF_UFLIA | 4 | 3 | 3 | 3 | — | — |
| SMT / UF | 4 | 1 | 1 | 2 | — | — |
| SMT / UFLRA | 4 | 2 | 2 | 3 | — | — |

Migration gains and losses at the cap:

| Instance | Before | After | Z3 |
|---|---|---|---|
| `smt-lib/non-incremental/QF_AUFLIA/array_benchmarks/misc/pipeline-invalid.smt2` | sat | timeout | sat |
| `smt-lib/non-incremental/QF_BV/brummayerbiere4/unconstrained05.smt2` | error | sat | sat |

Largest observed SMT instruction ratios among agreeing completed pairs:

| Instance | After/before instructions | Before (s) | After (s) |
|---|---:|---:|---:|
| `smt-lib/non-incremental/QF_UFLIA/mathsat/Wisa/xs-10-18-2-2-5-3.smt2` | 12.433 | 2.123 | 27.190 |
| `smt-lib/non-incremental/QF_UF/20190906-CLEARSY/0016/00194.smt2` | 10.156 | 0.017 | 0.032 |
| `smt-lib/non-incremental/QF_UFLIA/wisas/xs_8_13.smt2` | 4.698 | 0.970 | 4.332 |
| `smt-lib/non-incremental/QF_IDL/mathsat/fischer/FISCHER7-8-ninc.smt2` | 1.595 | 0.116 | 0.166 |
| `smt-lib/non-incremental/QF_IDL/planning/plan-16.cvc.smt2` | 1.461 | 0.115 | 0.115 |

Verdict disagreements: **0**.


Errors are retained as non-solves:

- before: `smt-lib/non-incremental/QF_BV/pspace/shift1add.29940.smt2` (exit 134); see `precompile/af14b6d2f800685b2737b02189cdae44d23f5459/benchmark/migration034-satlib-smtlib-30s/5ebcaa73c508cfd5d6ee2498`.
- after: `smt-lib/non-incremental/QF_BV/pspace/shift1add.29940.smt2` (exit 134); see `precompile/862c6d948f73133f1229831a0240f2558e8dbfe5/benchmark/migration034-satlib-smtlib-30s/5595ff8a8f106e613faae845`.
- before: `smt-lib/non-incremental/QF_BV/brummayerbiere4/unconstrained05.smt2` (exit 134); see `precompile/af14b6d2f800685b2737b02189cdae44d23f5459/benchmark/migration034-satlib-smtlib-30s/f8686b405669fbe70bde073a`.
