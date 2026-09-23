# Audited theory performance protocol

Registered before measurement, 2026-09-22. Baseline: 345ecfec01ae615b514452d68f61c6ff4b7b9b12.
Measure the standalone APIs added by the theory completeness audit: symbolic
FP format conversion, finite/cofinite set witnesses, alternative EUF/arithmetic
arrangements, and decoded array equality atoms. These are constructed API
workloads, not a claim about overall SMT-LIB performance.

Each cell constructs its problem, checks SAT, pushes a contradictory extension,
checks UNSAT, pops, and checks SAT again. The driver verifies every accepted
witness. The same driver emits equivalent SMT-LIB for installed Z3; record its
actual version and binary hash. FP circuits are requested before input constants
are asserted; Z3 can simplify the complete formula before bit blasting. For sets,
`card(A)=n` plus n distinct required members is equivalent to the explicit finite
array used in Z3. Its complement is a cofinite array. Array cases isolate decoded
equality chains rather than general store/select reasoning. Arrangement cases
require pairwise distinct Real values. Report these representation differences.

Grid: FP half/single, single/half, double/single (1 and 4 conversions); sets
(4,16,32 members); arrangements (3,5,7 terms); array atoms (16,64,256 terms).
Seeds 0..9 select candidates; 10..19 are held out until implementation is frozen.
Seeds vary input data, rounding modes and declaration order, not hidden SAT
settings: the standalone APIs do not expose a search seed. Every paired arm uses
the exact same inputs. Do not present this as evidence about stochastic search
policies. Any proposed search-policy change requires a separate matched-null
experiment with actual solver seeds and is outside this initial protocol.

Primary cost: whole-process user instructions, CPU 0, `perf stat -x, -e
instructions:u`, sum counted hybrid PMU rows, require >=99% coverage. Includes
startup, encoding, solving, Nixie witness validation, output and destruction.
Python checking of Z3 responses is outside its measured process; disclose this
asymmetry. Wall time is diagnostic only; 120s external safety cap, never solver
policy. Unknown/error/timeout are not solved cases and remain recorded evidence.

Use immutable benchstore records under precompile/<source>/benchmark, preserving
raw stdout/stderr and generated SMT-LIB. Reuse existing cells; never overwrite
failed attempts. Pin driver, compiler, lockfile, build profile, binary, host and
input hashes. Both Nixie arms use the same external Cargo package/profile
(`release`, debug=1) to permit building the driver against the baseline revision.

First measure and profile. Prefer removal of redundant exact computation with
identical clause/variable order and observable search trace; the original
computation is its control, with no heuristic placebo. If a candidate changes
search, register an appropriate matched null before measuring that candidate.
Accept only held-out geometric-mean instruction ratio <=0.95 on the targeted
family, no untargeted family >1.05, identical verdicts, and all correctness gates.
Report distributions, per-family Nixie/Z3 and treatment/control, solved-at-cap,
all failed cells, and limits. Do not extrapolate constructed workloads.

## Candidate selected after baseline profiling

The 150 selection cells all answered correctly. FP costs 1.17–6.51 times Z3;
all other families cost less than Z3 on this grid. The FP64-to-FP32 profile
attributes 2.61% of samples to packed watch snapshot construction and 5.22%
to its memmove, in addition to clause snapshot and allocation costs.
Candidate: omit lucky rollback snapshots only when root propagation has
assigned every variable. All strategies, validation scans, variable/clause
order and counter updates remain identical. There can be no speculative
assignment in that state, hence no watch/clause mutation to restore. Keep
the original forced-snapshot computation in unit tests and compare complete
state across complete/partial trails, conflicts and scopes. This is an
allocation/copy change, not a search policy. The acceptance target is the
FP family geomean; apply the originally registered 5% bar and held-out seeds.

## Reproduction

The external package contains the example as `src/main.rs`, path dependencies
on `nixie-core` and `nixie-theories`, `num-rational = "0.4"`, edition 2024,
and `[profile.release] debug = 1`. The actual manifest, Cargo.lock, driver,
profile and binary are retained under each measured revision's `theory-perf/`
cache directory. Use that lockfile, the recorded compiler, and identical
package/build paths for both arms. The workspace's LTO release profile is
different; do not mix its instruction cells with the external package cells.

Example commands (substitute the recorded full revisions and cached binaries):

```sh
python3 bench/theory_perf/run.py --binary precompile/BASE/theory-perf/audited-theory-perf \
  --driver-binary precompile/BASE/theory-perf/audited-theory-perf \
  --driver precompile/BASE/theory-perf/driver.rs --sha BASE --role baseline \
  --root precompile --lock precompile/BASE/theory-perf/Cargo.lock
python3 bench/theory_perf/run.py --binary /path/to/z3 \
  --driver-binary precompile/BASE/theory-perf/audited-theory-perf \
  --driver precompile/BASE/theory-perf/driver.rs --sha BASE --role reference \
  --root precompile --lock precompile/BASE/theory-perf/Cargo.lock
python3 bench/theory_perf/run.py --binary precompile/CAND/theory-perf/audited-theory-perf \
  --driver-binary precompile/BASE/theory-perf/audited-theory-perf \
  --driver precompile/BASE/theory-perf/driver.rs --sha CAND --role treatment \
  --root precompile --lock precompile/BASE/theory-perf/Cargo.lock
python3 bench/theory_perf/report.py --root precompile --baseline BASE --treatment CAND --csv paired.csv
python3 -m unittest discover -s bench/theory_perf -p 'test_*.py'
```

Add `--first-seed 10` to all three run commands and the report for held-out
confirmation. `report.py` rejects missing/ambiguous pairs, differing Nixie
configurations, hosts, input hashes, verdict transcripts, or failed validation.
It reports failure/censoring rather than treating Unknown as a matched answer.
The three-check transcript is one benchmark cell; successful cells certify two
SAT witnesses and a contradictory scoped extension, not three independent inputs.
