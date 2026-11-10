# Upstream 0.3.4 differential tools

These 30 Python tools come from `cool-japan/oxiz` commit
`41439c5194ebbb80649505a1116ef4ea2716dd0b`. They provide seeded finite-BV,
array, datatype and mixed-theory generators; incremental fuzzers; verdict and
model replay against Z3; corpus comparisons; reduction; and deterministic
response checks. The original [tool catalog](UPSTREAM_README.md) and
[historical reconstruction notes](UPSTREAM_REBUILD.md) are preserved as evidence,
not instructions to install old solver releases or claims about Nixie's results.

Use Python 3.10+, GNU `timeout`, and installed Z3 (currently 4.16.0 for the
migration verification). `fuzz_pushpop.py` also requires NumPy. Pass an absolute
release CLI path to `--probe`, `--a`, or `--b`; no probe crate is necessary.
Named probes still resolve below `$NIXIE_ROUND4_SCRATCH/probes` (default
`target/round4/probes`). CLI runs have no probe-specific elapsed-time field;
that field is optional and wall time is only a diagnostic.

For example, with `REV` set to the cached commit SHA and `RUN` to a new result
directory under `precompile/$REV/benchmark/round4/`:

```bash
python3 scripts/round4/gen_dt.py --seed 19 --count 20 --out "$RUN/corpus"
python3 scripts/round4/camp14.py "$RUN/corpus" \
  --probe "$PWD/precompile/$REV/nixie" --out "$RUN/results" --jobs 2
```

Every judged report records the actual Z3 version. Unknowns and timeouts are
inconclusive, not agreements. Preserve results and seed manifests; do not rerun
an existing measurement cell. Follow [the benchmarking guide](../../docs/BENCHMARKING.md)
for experiments, including matched nulls for heuristic comparisons. Campaigns
use at most two workers and must run after builds and test suites finish.

`sweep.py` retains the historical default of 217 inputs. For the fork's larger
corpus, explicitly pass `--expected-count N`; a mismatch refuses to report.
Reports include a digest of corpus paths and contents. Do not compare historical
sweep totals with a different corpus.

The Python finite oracle covers generated, well-sorted Bool/BV/array formulas.
It is not a general SMT solver. Unsupported operators fail or remain unresolved;
unsupported sorts and incremental commands are explicitly rejected by the static
conjunction oracle. The incremental fuzzers and Z3 judge handle scopes separately.
Model values must have the expected sort. Large finite domains and external
S-expressions deeper than 128 levels decline before compilation; the tools do
not claim to certify arbitrary deep models. Run the focused tool checks with:

```bash
python3 -m unittest discover -s scripts/round4 -p 'test_*.py'
```

A model omitting declared symbols is only a partial assignment. A satisfiable
Z3 replay of its pins is reported as `model_partial_consistent`, never
`model_ok`: existence of some extension does not validate an absent function
interpretation. Complete-model and partial-model outcomes remain separate.
