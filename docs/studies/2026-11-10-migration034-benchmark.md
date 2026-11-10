# Upstream 0.3.4 migration: SATLIB / SMT-LIB 30-second snapshot

These results describe the migration **before the subsequent policy rollback**.
The [protocol audit](2026-11-10-migration034-protocol-audit.md) withdraws two
default search policies that lacked the required matched-null/multi-seed
evidence. This snapshot does not waive those requirements or establish the
rollback's performance.

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

Completed 264 final cells. The corrected reference pass reused 239 valid cells
and executed only the 25 corrected configurations; the initial 25 command errors
remain archived and are excluded from solver totals. All 264 result-store records
and instance hashes validate. All 24 available SAT witnesses from Kissat and
CaDiCaL satisfy their input clauses. No decisive verdict disagrees with the
available corpus labels or references; this is not a proof of general soundness.

| Solver | SATLIB solved / 24 | SMT-LIB solved / 48 |
|---|---:|---:|
| Nixie before | 24 | 24 |
| Nixie after | 24 | 24 |
| Z3 4.16.0 | 24 | 35 |
| Kissat 4.0.4 | 24 | — |
| CaDiCaL 3.0.1 | 24 | — |

Observed after/before instruction ratios are **1.0016** on all 24 SAT pairs
and **1.3678** on the 23 jointly solved, agreeing SMT pairs. SAT conflicts,
decisions, propagations and restarts are identical on all 24 pairs. The SMT
solved total hides one gain and one loss: `unconstrained05.smt2` changes from
memory exhaustion to Sat, while `pipeline-invalid.smt2` changes from Sat to a
30-second timeout. Both references' relevant decisive answers are Sat.

The largest observed SMT increase is `xs-10-18-2-2-5-3.smt2`: **12.433 times**
the instructions, with diagnostic elapsed time rising from **2.123 to 27.190 s**.
This is a concrete cost finding, not a claim about a specific heuristic's merit.
The one-seed sample does not establish statistical neutrality or a general
speedup. It also does not establish that migration procedures were compliant.

SMT non-solves before/after are 13/10 Unknown, 9/13 timeouts and 2/1 errors.
The errors are address-space-limit allocation failures; `shift1add.29940.smt2`
fails this way in both revisions. Total diagnostic SMT elapsed time is
365.91/471.18 seconds; mean PAR-2 is 31.233/31.252 seconds. Short wall timings
include process-wait granularity and should not be treated as precise latency.

The [full tables](../../bench/migration034/results.md) include per-family and
SAT/UNSAT breakdowns, paired reference ratios, all gained/lost cases and errors.
The [CSV](../../bench/migration034/results.csv),
[summary](../../bench/migration034/summary.json), and
[record/model validation](../../bench/migration034/validation.json) are committed.
Raw stdout/stderr/perf evidence remains under the pinned revisions'
`precompile/<sha>/benchmark/migration034-satlib-smtlib-30s/`, with canonical
records in `benchmark/runs/migration034-satlib-smtlib-30s/`.

Reproduce the report without remeasuring:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 bench/migration034/summarize.py
PYTHONDONTWRITEBYTECODE=1 python3 bench/migration034/audit.py
```

The runner reuses completed cells. Do not regenerate the manifest or replace
cached binaries to obtain a different result.

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
