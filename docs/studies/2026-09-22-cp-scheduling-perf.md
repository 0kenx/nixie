# Borrowed cumulative start trials: measured CP cost reduction

The optional cumulative producer was copying every current finite domain for
one hypothetical start assignment, both during start filtering and inside
presence-support tests. A cumulative trial now borrows a singleton slice for
the chosen variable while reading other domains unchanged. Every task sharing
that variable sees the same singleton. Constraint membership also uses a
borrowed scan instead of allocating a list of variables. Non-cumulative
globals keep at most one materialized domain copy per candidate, shared among
all such globals visited for that candidate.

This is a representation change, with identical feasibility rules, callback
visit order, presence trials, consequences and ordered explanations. The
producer still rebuilds the exact BigInt timetable; it introduces no search
cache, propagation-strength change, heuristic, policy input or proof shortcut.
The independent model validator and finite lemma checker are untouched.

## Protocol and provenance

The [protocol](../../bench/cp_perf/README.md) was written before measurement;
the original preregistration SHA-256 is
`c5629d2d0c2d97c806cae13011b8ef94af9bcc8bbaf0702174a58991163fc607`.
Its original bytes are retained with the baseline binary. The protocol's
later reproduction instructions do not change the preregistered cells or bar.
Baseline is `591f9e693691aee153613285bdb5e06179607ff3`, including the original
optional implementation `fa8c0675`. The optimization snapshot is `be1440ca`;
`46a99e23` merges the concurrent heap-default landing, which does not execute
in these CP workloads. Both were measured against the same baseline.

The immutable external driver is also checked in as
[`cp_scheduling_perf.rs`](../../nixie-solver/examples/cp_scheduling_perf.rs),
SHA-256 `e15f17e802fccad51603c6e7dc2921bd32263e6578297be4eed7889be9834797`.
A standalone Cargo package points to the source checkout and permits the
same driver to build against the clean baseline, where the new example did
not yet exist. Both arms use default library features, identical lockfile,
release optimization with debug level 1, default system allocator, package
path, target directory and compiler. This differs from the workspace's LTO
CLI release profile; the numbers describe this public-library workload and
build, not all release configurations.

Primary metric is whole-process user instructions from `perf stat`, pinned
to CPU 0, summing counted hybrid PMU rows and requiring 99% coverage or better.
It includes model construction, allocation/copying, timetable computation,
callbacks, solver work, validation, output and destruction. No changed work
is hidden behind a SAT-conflict-only counter. An initial instruction-sampled
profile of `callback present 32 16 0 2` attributed approximately 27% of samples
to vector cloning, plus allocator/free and destruction costs; the sample is
bottleneck evidence, not an instruction-accounting decomposition. Its raw
profile and report are retained with the verification evidence.

The baseline is the exact-computation control. No heuristic decisions are
changed, so a randomized heuristic placebo is inapplicable. The structural
substitution argument, exhaustive soundness checks, and exact paired output
identity address trajectory reshuffling. The protocol would reject a trace
mismatch before interpreting its cost ratio. Ten seeds per cell vary declared
value order and the SAT seed; seeds 10..19 are held out for confirmation.
No wall-time speed claim is made on this shared, loaded host.

## Results

Every one of 280 selection pairs (seeds 0..9), 280 fresh-seed pairs (10..19),
and 280 combined-revision fresh-seed pairs has identical output bytes. This
includes every callback result and full ordered consequence/explanation,
and each solver result plus conflicts, decisions and propagations. Each
experiment has 140/140 verified SAT solver/certified cells within the external
120-second cap, with no lost or censored samples. The other 140 cells are
partial callback states: their `unknown` is never counted as solved SAT.
There are no UNSAT solver instances in this cost study; exhaustive SAT/UNSAT
and checked-refutation evidence belongs to the correctness gates below.

Ratios are treatment instructions / baseline instructions, paired geomeans.
Values inside 5% would be neutral. All modes pass the preregistered bar
(callback <= 0.90; ordinary/certified <= 1.05; no family > 1.05).

| Mode | Selection | Fresh seeds | Combined revision, fresh seeds |
|---|---:|---:|---:|
| CP callbacks | 0.1829 | 0.1820 | 0.1820 |
| Ordinary solver | 0.5976 | 0.5975 | 0.5975 |
| Certified solver | 0.6137 | 0.6135 | 0.6134 |

Combined-revision fresh-seed family ratios:

| Family | Callback | Ordinary | Certified |
|---|---:|---:|---:|
| Unknown independent presence | 0.2647 | 0.7570 | 0.7740 |
| All present | 0.4653 | 0.7940 | 0.8076 |
| All absent | 0.1051 | 0.7586 | 0.7797 |
| Shared presence | 0.3182 | 0.7753 | 0.7908 |
| Forced absence, demand > capacity | 0.2871 | 0.8310 | 0.8419 |
| 141-bit start values | 0.0896 | 0.5655 | 0.5863 |
| Four unrelated variables per task | 0.0623 | 0.1636 | 0.1718 |

The [paired CSV](2026-09-22-cp-scheduling-perf.csv) records every combined
fresh-seed instruction count, including the ten-point baseline distribution
for each instance. `bench/cp_perf/report.py` reproduces min/median/max by
instance and family and rejects missing pairs or transcript differences.
Canonical per-machine records for all 1,400 measured cells, raw stdout/stderr,
binaries, build manifests and lockfiles live in `precompile/<sha>/benchmark/`.
Existing cells were reused when comparing the merged revision.

These are deliberately constructed, mostly permissive scheduling workloads:
8x8 and 32x16 callback shapes, 4x4 solver shapes, two scoped rounds each.
Sparse models benefit most because the old code copied unrelated domains.
This does not measure difficult resource packing, variable durations/demands,
stronger cumulative filtering, or scalable proof enumeration. Those remain
separate work. No whole-solver speed claim follows from these CP numbers.

## Soundness and verification

A new exhaustive substitution regression checks 524,880 borrowed-versus-
physical singleton trials, including shared start variables, unsorted/holey/
empty domains, 141-bit values, optional polarities and unknown presence,
negative capacity, zero duration/demand, and unrelated trial variables.
The existing independent scheduling oracles remain the semantic reference:
43,740 partial callback states with every emitted implication checked against
concrete schedules and the independent lemma checker, plus 4,860 public
scoped solver verdicts with checked exported/imported refutations for UNSAT.

The production audit followed domain reconstruction, constraint membership,
value filtering and first-witness selection, presence trial discharge,
shared-start substitution, BigInt half-open events, scope rollback, independent
model replay, and the checked CP/CNF/LRAT proof chain. Only producer domain
access and allocation changed. No trial writes the callback domains; zero-
size and absent tasks are skipped before reading their start. No cache state
can survive push/pop. Non-cumulative candidate materialization is lazy and
shared across constraints, preserving the original copy bound on mixed models.

The documentation gate also exposed a pre-existing Cargo output collision:
the auto-discovered `nixie-tla` executable and `nixie_tla` library both wrote
`target/doc/nixie_tla/index.html` (also present in the optional-feature gate
logs). The executable now has an explicit `doc = false` target, matching the
main CLI convention and preserving the library's API documentation. This
changes documentation output only, not its build, tests or solving behavior.

Final verification on the combined source (with the documentation-only target
fix):

| Gate | Result |
|---|---|
| `cargo build --all-features` | Passed |
| Full workspace/all-features nextest | 12,244 passed; 17 configured skips |
| Focused CP producer/proof/public-oracle tests | 12 passed |
| All-features/all-targets Clippy, `-D warnings` | Passed |
| Workspace formatting check | Passed |
| All-features API docs, warning-denying rustdoc | Passed cleanly after the target-collision fix |
| Workspace/all-features doctests | 114 passed; 31 ignored |
| Z3 4.16.0 differential parity | 176 decisive agreements, zero wrong, one inconclusive |

The inconclusive parity case is `array_unique.smt2`: Nixie UNSAT, Z3 Unknown;
it is not counted as agreement. Compiler is rustc 1.96.0, LLVM 22.1.2; host is
an Intel Core Ultra 7 265K running Linux. Test builds use no incremental cache,
no dev/test debug info, four build jobs and four test workers. A temporary
nextest config increases outer runner termination to at least ten 60-second
periods under shared-host load, following the existing documented practice;
assertions, solver budgets and seeds are unchanged. The convergence test
completed in 396.913 seconds; the full suite completed in 593.718 seconds.
The config and complete logs are retained with the landing's cached binary.

The first general performance-gate invocation printed PASS, but a separate
package-only release build replaced its mutable target executable with a
different feature-unification build during the run. That invocation is
**discarded as landing evidence** and its log is retained. The final workspace
release rebuild restores SHA-256
`de3f02187f5a4dfeb16b6048154ca3000e74d9f1b68dca629820655b9253c6c1`,
identical to the frozen executable used for the replacement gate. The new
gate configuration uses that frozen artifact and a 601-second external cap;
no solver setting changes. CP experiments already used immutable cached
artifacts, so none of their 1,400 cells is affected or rerun.

Final frozen-artifact performance gate: **PASS**, twelve matching verdicts,
nine nontrivial counter pairs and three trivial cases, with no lost samples.
Conflict and decision geomeans are both **1.000** against pinned `28e82c65`.
The printed wall ratio is observational only. The final rebuilt workspace CLI
is byte-identical to the frozen gate artifact.
