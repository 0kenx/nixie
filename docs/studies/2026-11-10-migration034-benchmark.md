# Upstream 0.3.4 migration: SATLIB / SMT-LIB 30-second snapshot

## Registered protocol (before measurements)

Request: benchmark before/after the migration on SATLIB and SMT-LIB samples,
with a 30-second timeout, against Z3 and Kissat.

- Before: `af14b6d2f800685b2737b02189cdae44d23f5459`.
- After: `862c6d948f73133f1229831a0240f2558e8dbfe5`; the subsequent final
  migration commit `5c2b6bed` changes only Python tools and documentation.
- Both cached Nixie binaries use standard release, default features, LTO and
  one codegen unit. The before-cache build-equivalence note is retained;
  the after binary is `nixie-parity`, not the faster-to-build non-LTO test binary.
- References: installed Z3 4.16.0 on SAT and SMT; Kissat 4.0.4 and CaDiCaL 3.0.1
  on SAT. Kissat/CaDiCaL do not accept general SMT-LIB.

The committed `bench/migration034/manifest.json` pins every instance, binary
hash, source revision, host, CPU and command configuration before measurement.
There are 72 instances and 264 solver cells:

- **24 SATLIB instances:** two path-hash-selected members of each SAT/UNSAT
  pair at 50, 75, 100, 150, 200 and 250 variables. Official source archives:
  [SATLIB benchmark catalog](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html).
  Archive hashes and original member hashes are in `satlib-provenance.json`.
  Only the historical `%` terminator and trailing zero are removed for a
  common strict-DIMACS input. Header, literal ranges and clause count are
  checked; every solver receives identical normalized bytes.
- **48 SMT-LIB instances:** four from each of the 12 locally available logics,
  selected without running a solver. Files at most 1 MiB with exactly one
  check-sat are eligible. Families and paths are ordered by salted SHA-256;
  family round-robin selection limits domination by a large submission.
  The local corpus is the official 2025 non-incremental release documented
  in `smt-lib/PROVENANCE.md`. No expected verdict or prior runtime is used
  to pick the sample. This is a bounded sample, not the whole SMT-LIB corpus.

Run one default-configuration observation per cell. The result store's seed
index zero denotes that default observation, not an injected random seed.
This is an observational comparison of a large correctness/feature migration;
there is no single semantic heuristic treatment or meaningful matched null.
Consequently, do not infer a general speedup, heuristic merit or statistical
neutrality from these single-seed results. A causal heuristic comparison would
require a separate matched-null, at-least-ten-seed study.

Two serial lanes run on physical CPUs 2 and 5. Each instance's arms share a
CPU, with rotated arm order. All runs have an external GNU timeout of 30 seconds
(TERM, one-second KILL fallback), and an 8 GiB address-space limit. No internal
wall-clock solver policy is enabled. Inherited Nixie/OxiZ/Z3 experiment variables
are cleared. No solver builds or test suites run during measurement.

Primary cost: whole-process user-space retired instructions from `perf stat`,
including inherited children and the identical timeout/prlimit launcher. Require
one active hybrid PMU and at least 99.9% counter coverage. This covers parsing,
preprocessing, theory/model work and search; SAT conflict counts alone do not.
Timed-out costs are censored and excluded from completed-pair instruction ratios.
Report solved-at-cap, failures/Unknown/timeouts, per-family results, SAT/UNSAT
breakdowns, gained/lost cases, and geometric mean after/before instructions on
jointly solved, agreeing cases. Wall time and PAR-2 (60 seconds for a non-solve)
are secondary diagnostics; this shared host is not an isolated timing rig.

Correctness classification compares decisive answers with declared corpus status
and independent reference answers. Disagreements must be listed, never counted
as successful solves. Agreement is not a checked model/proof. `benchstore.py`
therefore retains unverified responses in `metrics.secondary.raw_answer`, with
its certification verdict honestly set to Unknown. Raw stdout/stderr and perf
output survive for every run. No existing cell is rerun; incomplete cells require
explicit diagnosis before superseding. Z3's reference records use the after
revision as their storage owner, not as a claim about Z3's source revision.

The harness has four focused tests for verdict parsing, hybrid PMUs, unavailable
or multiplexed counters, and preservation of Nixie's native DIMACS route.
No solver source or search policy is changed by this benchmark.

## Results

Pending the registered run. Raw evidence will live under the pinned revisions'
`precompile/<sha>/benchmark/migration034-satlib-smtlib-30s/`, with canonical
records in `benchmark/runs/migration034-satlib-smtlib-30s/`.

## Harness corrections during collection

The initial CaDiCaL command used Kissat's `--statistics` spelling; CaDiCaL
requires `--stats`. Those 24 invocations rejected the command before solving.
Z3 also interprets a bare filename containing `=` as a parameter assignment;
the affected SMT-LIB filename requires `--` before it. These are invalid harness
invocations, not solver performance failures. Their raw records remain archived.
Corrected argument lists have distinct content-addressed configurations. Only
those corrected cells are measured; all valid completed cells are reused.
Five harness tests now cover these CLI boundaries as well as PMU/verdict parsing.
Do not retry the incorrect commands or include their errors in solver totals.
