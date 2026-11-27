# The linear core answers a consistent system – eight pinned variables of 𝔽₇ read `sat` in 6 M instructions where the cascade ran for minutes and gigabytes with no verdict (2026-11-27)

The finding the previous record left open ("a *consistent* linear system
is not answered by the linear solver"), landed as the next slice, on
`9b3982d7` (the five slices of `2026-11-27-nested-booleans-ff-skeleton-closure-class-members.md`
in). `linear_core` already reduced a goal's linear generators to rows
with their literal provenance and returned a certified UNSAT for an
inconsistent one; a consistent one fell through to enumeration (seven
variables of 𝔽₇, 7⁷ points) or to the Gröbner cascade (eight and more:
pⁿ > 2²²), where the field equations make the quotient ring pⁿ-dimensional.
Eight variables pinned to constants ran for minutes and grew past the
gigabytes without a verdict; through the `QF_UFFF` combination, four
applications of one function answered `unknown` after 6 s. Both are
decided in one pass now.

One file (`nixie-theories/src/ff_theory.rs`), three tests, two
regressions. Nothing outside the finite-field procedure changes: the
25-cell probe, the pure-SAT gates and the nonlinear cascade are
bit-identical.

## The change

`check_conjunction` encodes the goal once. If every generator is linear
(`is_linear`: total degree at most one per term), `linear_core` runs and
its two outcomes are final: `Inconsistent` is the certified UNSAT it
always was; `Rewritten(rows, _)` hands the pivot rows to `linear_point`,
which reads a point off them and returns the model. Otherwise the
enumeration-eligible goals take the old route (the core for its
refutations, then enumeration), and the rest go to the cascade – which
now takes the encoding made here instead of encoding again
(`grobner_path(field, f, enc, generators, budget)`).

`linear_point`. The core's output for an all-linear goal is its reduced
pivot rows, `c_p·x_p + Σ c_v·v + c₀`, `x_p` the row's smallest variable,
and no `v` another row's pivot (each pivot was eliminated from every
other row). So the variables no row pivots on are free and take 0, and
each pivot reads `−(c₀ + Σ c_v·value(v)) / c_p`. The reading rests on a
check, not on that shape: the point is evaluated into every ORIGINAL
generator as a polynomial and the model is returned only if all vanish;
anything else falls through to the old route. Every variable of the
goal enters the point explicitly – `MPoly::eval_all` reads a variable
missing from the assignment as 1, not 0, so a sparse point would verify
the wrong thing. The model gives each field-sorted term of the goal its
variable's value: the encoder's disequality witnesses and bitsum sums
are not terms and stay out, as in every model here, and compound terms
are folded from their parts by the validator. A bitsum's definition row
(`s − Σ 2ⁱ·bᵢ`) is linear and joins the system.

What stays off the path: a disequality `(not (= a b))` encodes as
`(a − b)·w − 1` with a fresh witness `w` – quadratic – so a goal with one
takes the old route, as before. A nonlinear generator that becomes
linear after the core's substitution does not return to the linear path
either; the route it took is the one it always took.

## Method

Paired whole-process instruction counts (`perf stat -x, -e
cpu_core/instructions/u`, one pinned P-core), base `precompile/9b3982d7/nixie`
(the previous landing's candidate, sha256 `5b93b0b3…`) against the
candidate (the standing recipe on this tree, sha256 `8b2142f8…`). The base
arm is run under `RLIMIT_AS` of 6 GB and a wall cap on the inputs it
cannot finish: uncapped, it reached 4.7 GB of resident memory six seconds
into eight pinned variables and was still running ten minutes later when
the session's memory monitor aborted the run (the first attempt; its
solver process outlived the abort and was killed by pid). The caps are
the measurement, not a gate: "no verdict" below means the base spent the
instructions shown and then failed its next allocation, or hit the cap.
One repetition where an arm dies, the median of three where both finish.

## What it decides

Pure `QF_FF`, whole process:

| input | base | candidate |
|---|---:|---:|
| 6 variables pinned to constants, 𝔽₇ – the base's enumeration | 157.5 M | **6.0 M** (0.038) |
| 8 variables pinned, 𝔽₇ | 17.0 G in 31 s, no verdict | **6.3 M**, 0.05 s |
| 16 variables pinned, 𝔽₇ | 17.0 G in 40 s, no verdict | **7.3 M** |
| 64 variables pinned, 𝔽₇ | 17.0 G in 33 s, no verdict | **15.3 M** |
| 256 variables pinned, 𝔽₇ | 17.1 G in 25 s, no verdict | **99.6 M** |
| 8 variables pinned, 𝔽₆₅₅₃₇ | 18.0 G in 41 s, no verdict | **6.5 M** |
| a chain of 16 sums, 𝔽₉₇ – the cascade decided this one | 10.3 M | 9.6 M (0.934) |

`QF_UFFF`, n applications of one function, every argument 1 and every
result 0 (the family the function-hood scan was measured on):

| n | base | candidate |
|---|---:|---:|
| 4 | `unknown`, 16.3 G, 7.1 s | **`sat`**, 6.6 M, 0.05 s |
| 5 | `unknown`, 16.3 G, 10.5 s | **`sat`**, 7.0 M |
| 64 | `unknown`, 16.9 G, 10.0 s | **`sat`**, 81.3 M |
| 200 | `unknown`, 18.8 G, 9.3 s | **`sat`**, 747 M, 0.10 s |
| 800 | 35.7 G in 19 s, no verdict at the cap | **`sat`**, 19.0 G, 1.3 s |

The candidate's cost at n = 800 is still superlinear – the per-literal
DAG walks of the combination layer (the previous record's "remaining
quadratic terms") – but it answers. The congruence chain `(= x y)` with
`(distinct fⁿ(x) fⁿ(y))`, whose case tree holds all-linear nodes, gets
cheaper too: n = 1,000 3.82 G → 3.03 G (0.79), n = 2,000 20.7 G → 18.6 G
(0.90), `unsat` in both arms.

## What it does not touch

Nonlinear goals on the cascade's own path, whole-process instructions:
a goal of products over 8 variables of 𝔽₇ 26.72 M → 26.72 M (1.0000);
`bench/ff`'s goldilocks planted instances 13.78 M → 13.78 M (0.9997),
48.90 M → 48.90 M (0.9999), sparse 16x24 50.65 M → 50.65 M (1.0000),
sparse 64x96 186.69 M → 186.65 M (0.9998) – verdicts identical. A first
form of the slice encoded the goal up front and left the cascade to
encode again: +2.1 % to +4.9 % on these, inside the band and still a
cost the cascade need not pay; the cascade takes the encoding now and
the rows read 1.0000.

The standing probe, against the same base: all 25 cells bit-identical,
instruction geomean **0.9999**; `paired_instructions.sh` **1.0000** over
12 cells; `run_gate.sh` vs the pinned `28e82c65` **PASS**, conflicts
1.000 / decisions 1.000 / wall 0.96 (n = 9). No finite field is on any of
them; they are the proof that nothing outside the procedure moved.

## Tests

`nixie-theories/tests/ff_linear_point.rs`:

* `pinned_variables_are_decided_at_any_count` – 2n variables, n = 4, 8,
  64, 256 over 𝔽₇ and n = 1, 8, 64 over 𝔽₆₅₅₃₇: a model, validated by
  `validate_model`, every value as pinned.
* `an_inconsistent_linear_system_is_a_certified_unsat_at_any_count` – one
  contradiction among 2, 8 and 256 pinned variables: UNSAT with a
  certificate and a core.
* `random_linear_systems_agree_with_an_independent_elimination` – 144
  random sparse systems, one to twelve variables and one to twenty
  equations over 𝔽₇ and 𝔽₆₅₅₃₇: every verdict equals a Gaussian
  elimination written for the test; every model validates; every UNSAT
  carries a certificate, except the one whose `0 = c₀` the term builder
  folds to `false` (no field certificate by design).
* `compound_linear_terms_read_their_parts` – a sum, a product by a
  numeral and a bitsum on the left of an equation; a free variable takes
  0.
* `a_disequality_is_still_decided`, `no_generators_is_the_all_zero_model`.

The solver's own: `eight_pinned_variables_read_sat` (n = 8 and 256,
`(get-value (x0 x1))` reading 0 and 1) and
`four_applications_of_one_function_with_equal_results_are_sat` (n = 4 and
64), both in the FF regression suites, both `unknown` or verdictless
before. The standing FF suites – the oracle, the planted fuzzer, the
window split, the binary oracle – are unchanged and green.

## Bar

Run on the final tree, the candidate built with the standing recipe
(sha256 `8b2142f8…`), the base `precompile/9b3982d7/nixie`.

* `cargo fmt --all -- --check`; `cargo clippy -p nixie-theories -p
  nixie-solver --all-features --all-targets -- -D warnings`: clean.
* `cargo nextest run -p nixie-theories -p nixie-solver --all-features
  --no-fail-fast` (dev profile, `opt-level = 1`, debug assertions on):
  **5,330 run, 5,318 passed (3 slow), 12 skipped**, 7 failed, 5 timed
  out – the documented non-passes only (the 5 `SIGABRT` stack canaries,
  the 2 sets tests, the 5 slow releases).
* `bench/perf_gate/run_gate.sh` vs the pinned `28e82c65`: **PASS**,
  conflicts 1.000 / decisions 1.000 / wall 0.96 (n = 9).
* `bench/perf_gate/paired_instructions.sh` vs `precompile/9b3982d7/nixie`:
  geomean **1.0000** over 12 cells, conflicts identical.
* `bench/perf_gate/smt_probe_ab.sh` vs the same base, strict: 25 of 25
  cells bit-identical, instruction geomean **0.9999**.
* The pinned differential (`bench/differential/bench_diff.py`, 270
  instances, τ = 10 s, z3-validated models), candidate arm: **179 solved /
  179 agree / 0 disagree**, every `sat` with a valid model (90 and 89).
  No finite-field instance is in the sample, so the four flips against the
  base's own run (`RF-00`, `bench_134`, `bench_315` solved at 6.4–9.3 s
  where the base timed out; `super_queen97-1` the other way at 10.8 s)
  are the cap's noise, on a box at load 15–30.
* `bench/z3_parity` (in process, `--out` to a scratch file; z3 4.16.0):
  **171 Correct / 0 Wrong / 6 Inconclusive** – the standing result.

## Traps recorded

* **An aborted command leaves its solver running.** The first A/B of
  this slice was killed by the session's memory monitor while the base
  ground eight pinned variables; the tool reported the command aborted,
  and the solver kept going – 4.7 GB six seconds in, still allocating
  ten minutes later. Kill by pid from a script that holds the patterns
  (`killab.sh`), and run an arm that may not finish under `RLIMIT_AS`.
* **`RLIMIT_AS` under 6 GB kills the solver at start.** mimalloc reserves
  its arena in virtual address space, and the limit counts reservations:
  a 2 GB cap produced a verdictless 1.6 M-instruction run in both arms –
  the allocation failure, not the algorithm.
* **A peak-RSS sampler around `perf stat` did not sample.** Reading
  `VmHWM` of perf's child through `/proc/<pid>/task/<tid>/children`
  reported 11 MB for a process at gigabytes; the memory numbers here are
  from `ps`, not from that sampler.
* **A test's reference must model the term builder.** `0 = c₀` with c₀ ≠
  0 never reaches the procedure as an equation: `mk_eq` folds it to
  `false`, and that UNSAT carries no certificate by design. The random
  oracle's first form demanded one and failed on its first system.
* **The encode is not free just because it is linear.** Encoding twice
  for the cascade read +2–5 % on small nonlinear goals; measured, then
  removed by handing the cascade the encoding. A "cheap" extra pass still
  gets a row.
