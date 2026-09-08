# Exact sparse-word subsumption: rejected cost screen

The target is cycles per conflict, including inprocessing charged to the whole
solve. Existing profiles attribute 13.2% of si2-b03m time to subsumption. This
experiment replaces repeated signed-byte membership checks on dense connected
clauses with exact sparse 64-bit literal masks. It changes no search policy.

## Mechanism and invariants

Group literal codes by `code >> 6`. For each connected-clause word, subtract
the candidate's positive-literal mask. Zero missing bits means inclusion;
exactly one missing bit across the entire clause permits strengthening only
if its complement is present. Otherwise the check fails. Complementary codes
differ in their low bit, so they share a word. This implements the existing
scalar check and CaDiCaL `src/subsume.cpp:subsume_check` semantics exactly.

Pack only clauses with at least four literals per distinct word. Two u64s
store each word index and mask, so this fixed threshold does not expand the
literal payload. Repeated variables (either polarity, including duplicates)
fall back to the scalar path to preserve its multiplicity behavior. Candidate
mask updates must reproduce signed marks' last-write behavior on opposite
polarities. Sparse clauses and unrepresentable optional-cache offsets also
use the original matcher.

Build masks only upon connection, after any strengthening. Already connected
clauses are not rewritten during this round; check arena liveness before
using a row. Preserve schedule sorting and ties, occurrence order, budget
increments and stopping points, binary processing, dirty-set/RNG updates,
proof events, and scratch-buffer lifetimes. Debug builds compare every packed
match against the scalar result. Tests also compare explicit clause payloads
and metadata, models and proof transcripts; a database's abbreviated Debug
output is not a state oracle.

## Static evidence, before solver runs

A scan of original clauses of length 3 through 100 counts exact word groups:

| input | literals | words | eligible literals | eligible words |
|---|---:|---:|---:|---:|
| si2-b03m | 5,958,086 | 792,532 | 5,914,871 | 778,844 |
| circuit | 1,344,000 | 582,480 | 94,080 | 23,280 |
| j3037 | 88,328 | 72,174 | 0 | 0 |

These are input counts, not dynamic work or a speedup estimate. The target
is si2; circuit guards sparse-case overhead. j3037 gets no new cost cell.
Input SHA-256 values:

- si2: `8e24efbf17294a0fe9a2f7681d5cbb615f7f3417cc04258debb6c2ee498192ee`
- circuit: `d3338c04e29f5c8b7e75686fa30fd9927babb7b34b9f7c87785397662f59d8e2`
- j3037: `7672cb34e4b32cf83292630f1155b7e564bdcf4b2eedd60f7f25cf59b4b5bcc7`

## At most four new cells, no tuning

Use a clean committed control based on main `a43ee41`, and its direct
descendant containing only this implementation/tests. Pin both source and
binary hashes. Build both with the same compiler, lockfile, release profile
and ordinary features. Explicitly set `NIXIE_SWEEP=0` in both arms because
main now defaults sweep on. Clear all other study overrides.

First run si2 scalar then packed, seed 0, MAXC=40000, CPU 10, CaDiCaL preset,
model output enabled. Measure whole-process user instructions, user cycles
per conflict, branches/misses, conflicts, verdict and secondary wall time.
Require one active PMU with at least 99.9% scheduling coverage. Store every
cell once in the canonical result store; reuse exact existing cells. A
300-second emergency timeout is not a policy input or permission to rerun.

Stop immediately unless both si2 instruction and cycles/conflict treatment
/ scalar ratios are at most **0.95**, with byte-identical complete stdout.
Only on passing run circuit packed then scalar with the same settings;
neither circuit cost ratio may exceed **1.03**. Any trajectory discrepancy
fails the engineering comparison. No density-threshold or inline tuning
after seeing these cells. Budget Unknown is an unsolved prefix observation,
not an independently verified answer. Report solved-at-cap for each pair.

This is a small rejection screen, not a broad or multi-seed performance
claim. Positive production landing additionally requires full workspace
build, nextest, doc tests, clippy, formatting, docs and fresh Z3 parity.
Failure archives the candidate source and records the finding on main.

## Result: neutral, below the registered bar

The control is **`490756d`** (registration-only descendant of `a43ee41`),
binary SHA-256
`593cb3a22a6ccab0adaeb5a750e66c94304c0c677ebfef1a9a488b595d4a3a1b`.
The direct-descendant candidate is **`bf0994e`**, binary SHA-256
`3bb01207c4aeeb026e543cc87d4d4e573b984879e663ba16f5662dfae42bda4d`.
Both builds used Rust 1.96.0 / LLVM 22.1.2, the same lockfile, ordinary
features and release settings, from clean committed source.

Only the first **two cells** ran. Both solved si2 SAT at **39,246 conflicts**;
the complete stdout, including the model and all printed counters, is byte
identical. Both models were independently checked against the input CNF.
Solved-at-cap is **1/1 in each arm**. This is a completed solve, not a
conflict-budget prefix.

| metric | scalar | sparse words | treatment / scalar |
|---|---:|---:|---:|
| user instructions | 27,416,023,886 | 27,676,768,714 | **1.009511** |
| user cycles | 10,954,208,363 | 10,754,348,127 | **0.981755** |
| cycles / conflict | 279,116.56 | 274,024.06 | **0.981755** |
| branches | 6,509,361,018 | 6,519,455,619 | 1.001551 |
| branch misses | 41,999,779 | 36,507,023 | 0.869219 |

Secondary wall times were 2.571 s scalar and 2.520 s packed; they are not
the advancement metric.

The 13.08% branch-miss reduction does not yield a qualifying whole-solve
gain: instructions increase 0.95%, and the measured cycle reduction is only
1.82%. Both whole-solve differences are within the neutrality band; the
registered advancement gate fails. The runner stopped before either circuit
cell. No thresholds were tuned and no cells were repeated.

Static literal density was insufficient evidence of removable dynamic work.
The measurement includes mask construction, candidate bitmap writes, larger
occurrence entries and all fallback paths; it does not isolate which of these
costs offsets the branch-miss savings. Do not retry this same sparse-word
matcher or tune its density cutoff on these observations. A successor needs
new dynamic evidence that its avoided work exceeds construction and storage
costs. This result does not close the Kissat gap.

Canonical record IDs are **e45297cb1743dd83** (scalar) and
**1976b4223ba4fa74** (packed). Each uses one active `cpu_atom` PMU with 100%
event scheduling coverage. Records, raw outputs, perf counters, runner,
conditional manifest and summary are in the respective
`precompile/<sha>/benchmark/` directories. The candidate cache also retains
its source patch/bundle and build/test logs.

## Correctness coverage and disposition

All **759 SAT library tests** passed with all features. Six focused tests
cover 361,584 exhaustive scalar/mask comparisons, omitted literals, unique
and multiple flips across word boundaries, duplicate and opposite-polarity
fallback, checked offset limits, last-write candidate marks, and equal inline
occurrence-list footprint. Paired real rounds exercise strengthening before
connection, repeated dirty rounds and budget exits.

Twenty-four eight-variable formulas are exhaustively classified by truth
table, then solved in both arms with proof recording off and on. Explicit
literal order and clause metadata (including deleted slots), trail, watches,
binary graph, statistics, dirty sets, elimination marks, models and LRAT
transcripts agree. SAT models and UNSAT LRAT proofs are checked independently.
The focused tests also pass in separate full-schedule and recency/hot-literal
processes. All-target SAT clippy, formatting and committed release builds
passed.

The candidate code is **archived, not landed**. Its cost gate failed, so no
full workspace or SMT parity qualification is claimed. Main receives this
negative finding only; the temporary checkout and branch are removed.
