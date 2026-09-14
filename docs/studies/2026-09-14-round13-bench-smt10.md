# Round-13 entry benchmark: nixie / kissat / z3 over 10 random SMT-LIB instances

The round-13 handoff executed with its precondition restored: the machine
had lost its `smt-lib/` corpus (handoff trap 2), so it was refetched from
the official SMT-LIB release 2025 (non-incremental) Zenodo record 16740866
— 12 logics, 108 659 files, 53 GiB, layout
`smt-lib/non-incremental/<LOGIC>/<FAMILY>/...` exactly as the tests and the
differential sample expect (provenance + refill recipe: `smt-lib/PROVENANCE.md`).

## Design

- **Sample**: 10 instances drawn uniformly with `seed=20260914` from the
  QF_BV division (46 191 files, size ≤ 20 MB; largest picked 3.3 MB).
  QF_BV is the only division where all three solvers can meet: nixie and
  z3 solve the `.smt2` directly; kissat solves the DIMACS CNF produced by
  z3's `apply (then simplify bit-blast tseitin-cnf)` — the equisatisfiable
  tseitin encoding z3 itself would feed its SAT core (converter:
  `bench/differential/smt2_to_dimacs.py`).
- **Gates**: kissat(cnf) must equal z3(smt2) — converter fidelity;
  nixie(smt2) must equal z3(smt2) — the soundness canary. 60 s timeout,
  single run, wall clock (cross-binary capability view, SMT-COMP style —
  not a heuristic A/B; the AGENTS matched-null discipline does not apply
  to a fixed-seed one-shot verdict check).
- Binaries: nixie = HEAD build (flip-A CSR default path), z3 4.16.0,
  kissat = `../temp/kissat/build/kissat`.

## Results — 10/10 three-way agreement

| instance | z3 | kissat | nixie | cnf (vars/clauses) |
|---|---|---|---|---|
| sage/app8/bench_316 | unsat 0.05 s | unsat | unsat 1.76 s | 0/1 |
| sage/app11/bench_128 | unsat 0.12 s | unsat 0.01 s | unsat 0.37 s | 0/1 |
| stp_samples/…cond_029234 | unsat 0.02 s | unsat | unsat 0.42 s | 0/1 |
| sage/app7/bench_300 | unsat 0.44 s | unsat 0.01 s | unsat 0.73 s | 0/1 |
| sage/app9/bench_351 | unsat 0.12 s | unsat 0.01 s | unsat 0.24 s | 0/1 |
| spear/…bin_eventlogadm | sat 8.32 s | sat 0.27 s | sat 20.67 s | 306 868 / 1 295 352 |
| sage/app7/bench_8104 | sat 0.01 s | sat | sat 0.01 s | 8 / 8 |
| stp_samples/…cond_025585 | sat 0.02 s | sat | sat 0.03 s | 299 / 1 215 |
| Sage2/bench_13880 | unsat 7.12 s | unsat 2.31 s | **unsat 0.21 s** | 679 039 / 2 880 315 |
| MCMPC/millionaires.t1.i31 | sat 0.03 s | sat 0.01 s | sat 0.02 s | 636 / 1 799 |

Reading notes (one shot, no distributional claim):
- Five `0/1` CNFs: z3's `simplify` decided them before any search — the
  kissat leg is the empty clause; those cells say nothing about search.
- nixie's QF_BV stack is currently behind z3's on the spear/sage cells
  that survive preprocessing (≈2–2.5× z3) — consistent with the
  QF_BV-tier roadmap — while **bench_13880 inverts the picture** (0.21 s
  vs z3 7.12 s / kissat 2.31 s on the 2.9 M-clause encoding), so the
  gap is structure-specific, not uniform.
- Verdict-wise the canary is clean: 0 disagreements, 0 timeouts.

Raw data: `outputs/smt10/results.json` (untracked); converter landed at
`bench/differential/smt2_to_dimacs.py` for reuse (it handles z3's `k!N`
tseitin names *and* declared free Booleans, unit clauses, `true/false`
collapse, multi-goal output).
