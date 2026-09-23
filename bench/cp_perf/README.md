# Optional cumulative performance experiment

Pre-registered 2026-09-22, before collecting baseline or treatment cells.
Baseline source: 591f9e69 (the optional-task implementation is fa8c0675).

The candidate under investigation eliminates whole-model domain copies when
forcing one cumulative start candidate. Static inspection found copies both
in value filtering and inside nested presence-support tests. First collect an
instruction profile of the baseline; reject this target if copying is not a
material cost. Keep the propagation rules, visits, trial order, explanations,
BigInt arithmetic, independent validators, and proof contract identical.
Do not add cache state or change the SAT search policy.

Use pinned CPU 0 and `perf stat -x, -e instructions:u`, summing counted hybrid
PMU rows and rejecting missing counters. This covers process startup, model
construction, callbacks, domain copies, timetable construction, allocation,
validation, printing and destruction. It excludes kernel instructions; no
kernel-dependent mechanism is changed. Wall time is diagnostic only. Each
cell has a 120-second external safety cap, never a solver policy input.

Seven callback families: unknown independent admissions, all present, all
absent, shared admission, individually blocked admissions, 141-bit start
values, and four unrelated start variables per scheduled task. Sizes are
8 tasks x 8 starts and 32 tasks x 16 starts, with two scoped rounds each.
Public solver and certified solver cases use 4 tasks x 4 starts for each
family and two scoped rounds. Seeds 0..9 rotate value declaration order and
set the SAT seed; reserve 10..19 for fresh-seed confirmation after selection.
All solver cases have a known SAT witness; unknown callback results are
partial propagation states and never counted as solved SAT instances.

Gate: every paired output byte must agree (callback result, all consequences
and full ordered explanations; solver verdict and conflicts/decisions/
propagations). Also require the existing exhaustive optional-schedule oracles
and full repository verification gates. No heuristic is introduced, so the
unchanged implementation is the exact-computation control; a randomized
heuristic placebo would test a different claim. If trajectory identity fails,
stop and investigate; do not interpret an instruction ratio as an optimization.

Go bar: callback instruction geomean treatment/control <= 0.90, no family
geomean > 1.05, and public ordinary/certified geomeans <= 1.05. Report per-family
and per-mode ratios, baseline distributions, solved-at-cap, and all failed
cells. Within 5% is neutral. Do not generalize constructed CP workloads to
whole-solver speed. Fresh seeds must confirm the same bar. Performance cells
are immutable: use benchstore records, source/binary/harness hashes, host,
explicit compiler/build settings, command line, and the exact generated case
identity; reuse an existing cell. Baseline and treatment use the same driver,
external Cargo manifest, lockfile, build directory, release settings and CPU.
The external package allows compiling the driver against clean baseline
sources before this new example exists there; retain its manifest and lock
with the binary. Final example source is the identical measured driver.

## Reproducing and inspecting the stored experiment

The checked-in client is `nixie-solver/examples/cp_scheduling_perf.rs`:

```sh
cargo run --release -p nixie-solver --example cp_scheduling_perf -- callback present 32 16 0 2
```

That workspace release profile differs from the external measurement build;
use the cached external manifest and lockfile when comparing with this study.
For new experiments, hold the profile constant between arms and include the
profile change in `run.py`'s config flags. The driver uses the public API only.
An external Cargo package can point `nixie-core`, `nixie-theories` and
`nixie-solver` at a clean source checkout, depend on `num-bigint = "0.4"`, and
use `[profile.release] debug = 1`; copy the driver into its `src/main.rs` and
the retained lockfile into that package. Build both revisions with the same
package path, lockfile, compiler and `CARGO_INCREMENTAL=0`; cache each binary
before changing the source revision. The stored manifests record exact paths.

The runner requires an explicit immutable source revision and corresponding
binary. It records the driver hash in config identity; callers must supply
the driver actually compiled into that binary. Example (substitute real SHAs):

```sh
python3 bench/cp_perf/run.py precompile/BASE/cp-scheduling-bench \
  --sha BASE --role baseline --source . --root precompile \
  --driver nixie-solver/examples/cp_scheduling_perf.rs
python3 bench/cp_perf/run.py precompile/CAND/cp-scheduling-bench \
  --sha CAND --role treatment --source . --root precompile \
  --driver nixie-solver/examples/cp_scheduling_perf.rs
python3 bench/cp_perf/report.py precompile BASE CAND
```

`run.py` consults the canonical benchstore index before every cell and records
through `benchstore.py`; it refuses to rerun failed/unrecorded raw attempts.
Fresh-seed replay adds `--first-seed 10` to both runner and report commands.
Reports reject incomplete pairs, differing host/config identity, differing
verdicts, and differing full-output hashes. Raw output and counter stderr are
retained next to the canonical JSON records. No callback `unknown` is counted
as a successful SAT solve. The solver cases exercise admission and cancellation
with ample capacity; these small cases measure integration overhead, not hard
resource-packing search or scalable proof enumeration.

## Z3 performance reference and the next optimization

The [bounds/replay protocol](bounds_protocol.md) extends the grid to 8x16
end-to-end cases and uses installed Z3 4.16.0 as the external performance
reference. `reference.py` emits equivalent exact QF_LIA schedules, checks both
returned Z3 models independently, records immutable instruction cells and
reports Nixie/Z3 ratios separately from Nixie before/after ratios:

```sh
python3 bench/cp_perf/reference.py run --binary precompile/BASE/cp-scheduling-bench \
  --sha BASE --arm baseline --source . --root precompile
python3 bench/cp_perf/reference.py run --binary /path/to/z3 \
  --sha BASE --arm reference --source . --root precompile
python3 bench/cp_perf/reference.py run --binary precompile/CAND/cp-scheduling-bench \
  --sha CAND --arm treatment --source . --root precompile
python3 bench/cp_perf/reference.py report --root precompile \
  --baseline BASE --treatment CAND --reference BASE --csv paired.csv
```

Add `--first-seed 10` to runs and report for held-out confirmation. The Z3
record's source revision identifies the benchmark-driving Nixie checkout;
Z3 itself is identified by its actual version and binary hash. See the
[study](../../docs/studies/2026-09-22-cp-scheduling-bounds.md) for limitations,
model-check accounting and results. Run harness tests with
`python3 -m unittest discover -s bench/cp_perf -p 'test_reference.py'`.

## Larger-case investigation

`reference.py run` and `report` accept repeatable `--shape TASKSxWIDTH` and
`--family FAMILY` selectors. Defaults remain the original two shapes and all
seven families. For the larger-case grid use:

```sh
--shape 8x32 --shape 16x16 --shape 16x32 --shape 32x16 \
--family unknown --family present --family sparse --first-seed 10
```

The [larger-case study](../../docs/studies/2026-09-23-cp-larger-cases.md)
records all source/binary identities, reused cells, profiles and per-seed data.
For its baseline-only Z3 comparison, pass the same frozen Nixie revision as
both `--baseline` and `--treatment` to the existing report command; the
current/previous column is consequently 1 and is not an optimization result.
The extended harness has a new content hash; do not rerun the existing small
grid simply to refresh that hash.
