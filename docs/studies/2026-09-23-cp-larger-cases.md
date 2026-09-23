# Investigating larger CP scheduling cases

The larger gap is real and grows most sharply with domain width. At 16 tasks
with 32 possible starts, ordinary Nixie uses **17.2847× Z3's instructions**
for all-present tasks and **45.2950×** for the sparse family. All new cells
are decisive checked SAT, and Nixie records zero conflicts in every run.
This is callback/explanation overhead on easy schedules, not evidence of a
search-quality deficit or hard packing performance. No production solver
optimization is implemented in this investigation.

## Protocol

Pre-registration, 2026-09-23. Baseline is landed `7ab18362` (source of
its cached binaries: `f43db048`). Z3 4.16.0 remains the external reference.
The previous 8x16 ordinary ratios are 6.8371 for sparse and 2.3328 for
all-present. Investigate before changing propagation or search policy.

First collect instruction-sampled profiles from frozen binaries, pinned to
CPU 0. Profile invocations use extra rounds for sampling and are diagnostics,
not new comparable performance cells. The sparse family has four unrelated
finite-domain variables per task; inspect domain/callback and explanation
overhead separately from the all-present cumulative sweep. Existing all-family
2-round performance cells are reused, not rerun.

Sampling totals appear inconsistent with the existing process-counter totals.
Before interpreting new measurements, compare the generic `instructions:u`
and explicit `cpu_core/instructions/u` events in the same diagnostic process
(50 rounds, seed 10, all-present 8x16), then check sampled-period accounting.
This is counter calibration, not a performance claim or a replacement cell.
Record the outcome and any invalidated evidence explicitly.

After that, preregister the scaling grid and any candidate before running its
performance comparison. Require independently checked models/proofs, exact
BigInt/half-open semantics, no absent-task scheduling restrictions, and the
existing certificate contract. Any optimization must retain exact transcripts
and be measured on ten paired seeds plus ten confirmation seeds; a policy
change instead needs its own matched null. No wall-time performance claim.

## Scaling grid (before measurement)

Keep the driver, profile, two pushed rounds and 120-second external cap. Add
8x32, 16x16, 16x32 and 32x16 task/domain shapes, in unknown, all-present and
sparse families: ten seeds 10..19, ordinary/certified Nixie and Z3. The sparse
family still adds four unrelated finite-domain variables per task. These are
240 Nixie and 120 Z3 cells. They are a diagnostic baseline distribution, not
optimization selection or confirmation. No production solver change is made
in this investigation. Existing 8x16 cells are reused for the starting point.

The existing reference harness now accepts explicit shape/family selectors;
default workloads and encodings are unchanged. Its new hash identifies new
measurements; do not rerun existing small-grid cells merely for the new hash.
Use source `f43db048` for the frozen Nixie binary and this harness commit for
the Z3 records. Every returned Z3 model is independently validated as before;
Nixie's internal model and certificate checks remain enabled. Report each
family/shape/mode's Nixie/Z3 geometric mean and ten-seed min/median/max, all
solved-at-cap outcomes and Nixie's search counts. Avoid an overall scalar
which lets small cases hide a growing gap.

Counter calibration gave 3,087,105,858 instructions for both generic and
explicit-core events in the same pinned process, with 100% coverage and an
identical transcript. The initial 1M-period profile had 156 throttle events;
20M sampling still throttled. Use 100M-period profiles with extra rounds and
verify zero throttle/lost events. These profiles locate costs; their sample
fractions are approximate and are not end-to-end improvement measurements.

## Results

The grid completed 240/240 new Nixie and 120/120 new Z3 cells, with no cap,
Unknown, failed model or missing counter. All counters had 100% coverage.
The reused 8x16 slice contributes 60 Nixie and 30 Z3 cells; reference cells
serve both ordinary/certified modes, so the paired CSV's 300 comparisons
are not 300 independent Z3 samples. Every Nixie run has zero conflicts.

Geometric means of paired **Nixie/Z3 user instructions** (lower is better):

| Tasks × start values | Unknown presence | All present | Sparse |
|---|---:|---:|---:|
| 8 × 16 (reused) | 1.0134 | 2.3328 | 6.8371 |
| 8 × 32 | 3.4071 | 8.1585 | 23.3969 |
| 16 × 16 | 1.1608 | 4.7154 | 10.9535 |
| 16 × 32 | 4.9123 | 17.2847 | 45.2950 |
| 32 × 16 | 1.0873 | 4.8360 | 8.5042 |

These are ordinary-mode results. At 16x32 the certified equivalents are
4.9695, 17.3512 and 45.3653: certified/ordinary ratios of 1.0116, 1.0039 and
1.0016, all neutral. Both modes retain the ordinary independent model gate.
The full distributions and modes follow below; the [per-seed CSV](2026-09-23-cp-larger-cases.csv)
also records decisions, propagations and conflicts.

Doubling width from 16 to 32 at 16 tasks multiplies Nixie's instruction
cost by 4.40 (unknown), 4.08 (present) and 5.92 (sparse). Z3's corresponding
factors are 1.04, 1.11 and 1.43. Task count alone has a different effect:
Z3 also gets more expensive, so a lower ratio at 32x16 does not mean Nixie
gets cheaper. Sparse Nixie's median rises from 3.23 billion instructions at
16x16 to 16.13 billion at 32x16, while the ratio drops from 10.95 to 8.50.

## What the profiles and source establish

Profiles use the same frozen binary, ordinary mode, seed 10, with additional
rounds for sampling. The accepted 100M-period profiles have zero throttle
or lost events. They are single-seed diagnostics, not statistical estimates
of a proposed optimization's gain. Source locations were resolved from the
frozen executable's DWARF with LLVM addr2line; the generic iterator symbols
were traced to their actual callers.

| Profile component | Sparse 8x16 | Sparse 16x32 |
|---|---:|---:|
| `CpModel::run` self | 26.82% | 15.62% |
| `CpModel::domains` snapshot fold | 20.90% | 10.83% |
| `add_theory_reason_clause` | 8.46% | 31.70% |
| Model replay's per-premise truth checks | 4.06% | 17.08% |

1. **Long explanations expose a quadratic SAT loop.** CP exclusions retain
   the complete snapshot reason list, including unrelated finite-domain
   variables. `UserCallback::consequences` validates and translates that
   entire list. In `nixie-sat/src/solver/learn.rs`,
   `add_theory_reason_clause` scans the growing output vector for each input
   reason to deduplicate by SAT variable. The 16x32 sparse profile assigns
   more than 96% of that function's samples to this duplicate scan. This
   places approximately 30% of total sampled instructions on an avoidable
   quadratic loop. That fraction is a diagnostic ceiling, not a measured
   speedup. The sparse shape has 80 finite-domain variables and 2,560
   indicators despite only 16 tasks using the resource.
2. **Every fixation rebuilds and scans the full CP snapshot.**
   `CpModel::on_fixed` calls `run`; `domains` looks up every indicator and
   reconstructs every domain/reason list. Candidate filtering then looks
   up the indicators again. The independent model gate notifies each watch
   before final checking, exercising this same callback path during replay.
   The anonymous `Map::fold` hotspot resolves to `CpModel::domains` and
   `PropagatorContext::get_fixed_value`; the `Iterator::all` hotspot resolves
   to the model gate's repeated premise validation, not cumulative filtering.
3. **All-present cost is mostly rebuilding timetables.** At 16x32, about
   77% of samples are in `cumulative_feasible`, BigInt addition and BTreeMap
   insertion/iteration (roughly 71% at 8x16). Each candidate start rebuilds
   an exact mandatory-part event map, repeated as each indicator is fixed.
   BigInt and half-open endpoint semantics are required; unnecessary repeat
   work is the target, not narrower arithmetic.
4. **These resource constraints are redundant.** In every family measured
   here, each demand is one and capacity equals the number of tasks. Hence
   even simultaneous presence of all tasks cannot overload the resource.
   This follows directly from the declarations, independent of profiles.
   The corpus measures integration/exactly-one overhead. It cannot establish
   industrial scheduling performance or justify stronger propagation.

The established presolve precedent is OR-Tools'
[`CpModelPresolver::PresolveCumulative`](https://github.com/google/or-tools/blob/stable/ortools/sat/cp_model_presolve.cc#L6820):
it removes a cumulative constraint when the sum of maximum demands does not
exceed minimum capacity. Its
[cumulative implementation](https://github.com/google/or-tools/blob/stable/ortools/sat/cumulative.cc#L67)
retains presence and nonzero-size conditions for individual demand checks.
Sources inspected 2026-09-23. Z3's local user-propagator implementation was
also inspected for its premise validation, justification construction and
scoped replay contract; none of those contracts should be bypassed here.

## Ranked follow-ups, not implemented

1. Replace the quadratic SAT reason deduplication with order-preserving
   membership tracking. Preserve first occurrence **by variable**, the
   propagated-variable exclusion, resulting literal order, watch choices,
   LBD and proof output. A local scratch structure avoids adding scope state.
   This is the most direct large-sparse target and affects all theories, so
   measure short-reason and SMT workloads too and run the full landing gates.
2. Recognize exact redundant-capacity bounds in the CP producer, following
   the reference presolve rule. Keep original declarations in independent
   model/proof validation; retain negative-capacity, malformed-input, zero-size
   and absent-task behavior. Measure genuine capacity-binding workloads before
   treating a win on this deliberately redundant corpus as a general gain.
3. Reuse the unknown-indicator positions already discovered during one
   snapshot, avoiding the second fixed-value hash lookup. Preserve event and
   consequence order. A persistent incremental snapshot would address more
   of the quadratic scaling, but is a separately scoped change needing
   callback/model/push/pop rollback proofs and exhaustive stale-state tests.
4. Compact exactly-one explanations only as a separate experiment. The
   independent domain checker already needs just the fixed positive indicator,
   but shortening learned clauses can alter search. Do not fold it into an
   allegedly trajectory-identical engineering patch; preregister the relevant
   controls and recheck complete proof export/import.

Add capacity-binding SAT/UNSAT packing families and resource contention before
selecting stronger cumulative propagation. Variable durations/demands and
stronger propagation remain unimplemented, separately scoped feature work.

## Verification and provenance

This change touches benchmark selectors, harness tests, study text and data;
no Rust solver or checker source is changed. Five Python harness tests pass,
including checked Z3 models for all four new shapes and malformed selector
rejection. Rust formatting and `git diff --check` pass. The measured solver
is the already fully verified `f43db048` source recorded in the preceding
[landing study](2026-09-22-cp-scheduling-exclusions.md); no new solver build,
Rust-suite run or solver landing-gate result is claimed for this investigation.

Nixie binary SHA-256:
`8216d4d828f40d88e7b7a544c05d01df19adf9121e8ff178fc86b545725a3e5d`.
Z3 4.16.0 SHA-256:
`e01bc8bcd4d487be9666873545532ff4cd705ad4cd746f616290fac756f12c46`.
New Nixie records are stored under `precompile/f43db048…/benchmark/`; new
Z3 records under `precompile/6973d94e…/benchmark/`. The reference field's
revision identifies the benchmark harness, not Z3's Git source. Existing
8x16 reference records remain under `df564313…` and were not rerun.
The 360-cell manifest was checked missing before measurement and complete
afterward; record IDs, paths, raw counter totals and coverage were audited.
Profiles (including throttled attempts), calibration, manifests and logs
are archived under the final study commit's `precompile` directory.

## Ten-seed distributions

Instruction counts are in millions. There are ten seeds in every row;
Z3 rows are reused between Nixie modes.

| Mode | Family | Tasks × values | Nixie/Z3 | Nixie instructions min / median / max (M) | Z3 instructions min / median / max (M) |
|---|---|---|---:|---:|---:|
| certified | present | 8 × 16 | 2.3657 | 122.8 / 126.7 / 133.1 | 51.3 / 52.8 / 62.4 |
| certified | present | 8 × 32 | 8.2358 | 482.5 / 538.8 / 581.7 | 63.7 / 64.4 / 66.5 |
| certified | present | 16 × 16 | 4.7407 | 690.4 / 766.0 / 796.3 | 147.7 / 158.4 / 189.8 |
| certified | present | 16 × 32 | 17.3512 | 2919.3 / 3114.1 / 3264.2 | 168.6 / 175.4 / 192.9 |
| certified | present | 32 × 16 | 4.8453 | 4820.0 / 5224.0 / 5537.8 | 843.2 / 1004.1 / 1482.8 |
| certified | sparse | 8 × 16 | 6.9078 | 673.2 / 737.0 / 838.9 | 102.5 / 107.3 / 114.0 |
| certified | sparse | 8 × 32 | 23.5446 | 3787.7 / 3989.7 / 4766.7 | 169.3 / 172.4 / 179.2 |
| certified | sparse | 16 × 16 | 10.9697 | 2970.8 / 3233.2 / 3506.4 | 250.5 / 269.4 / 560.8 |
| certified | sparse | 16 × 32 | 45.3653 | 15396.2 / 19390.1 / 22996.0 | 390.5 / 412.3 / 486.5 |
| certified | sparse | 32 × 16 | 8.5276 | 13382.7 / 16162.1 / 17901.7 | 1072.5 / 1578.4 / 5454.4 |
| certified | unknown | 8 × 16 | 1.0460 | 53.2 / 54.2 / 58.6 | 50.8 / 52.4 / 55.4 |
| certified | unknown | 8 × 32 | 3.4822 | 193.9 / 229.3 / 260.2 | 62.8 / 65.8 / 68.7 |
| certified | unknown | 16 × 16 | 1.1784 | 207.9 / 220.4 / 234.8 | 150.7 / 175.4 / 431.2 |
| certified | unknown | 16 × 32 | 4.9695 | 870.1 / 980.4 / 1048.5 | 182.3 / 193.4 / 221.1 |
| certified | unknown | 32 × 16 | 1.0994 | 995.0 / 1031.4 / 1135.4 | 698.4 / 840.0 / 3460.1 |
| solver | present | 8 × 16 | 2.3328 | 121.0 / 125.0 / 131.2 | 51.3 / 52.8 / 62.4 |
| solver | present | 8 × 32 | 8.1585 | 478.2 / 533.2 / 576.0 | 63.7 / 64.4 / 66.5 |
| solver | present | 16 × 16 | 4.7154 | 686.7 / 762.1 / 792.7 | 147.7 / 158.4 / 189.8 |
| solver | present | 16 × 32 | 17.2847 | 2911.7 / 3101.5 / 3249.8 | 168.6 / 175.4 / 192.9 |
| solver | present | 32 × 16 | 4.8360 | 4811.4 / 5213.5 / 5529.3 | 843.2 / 1004.1 / 1482.8 |
| solver | sparse | 8 × 16 | 6.8371 | 668.9 / 729.6 / 830.4 | 102.5 / 107.3 / 114.0 |
| solver | sparse | 8 × 32 | 23.3969 | 3767.8 / 3963.5 / 4724.6 | 169.3 / 172.4 / 179.2 |
| solver | sparse | 16 × 16 | 10.9535 | 2975.1 / 3230.3 / 3495.5 | 250.5 / 269.4 / 560.8 |
| solver | sparse | 16 × 32 | 45.2950 | 15437.5 / 19354.7 / 22914.6 | 390.5 / 412.3 / 486.5 |
| solver | sparse | 32 × 16 | 8.5042 | 13339.5 / 16131.1 / 17879.9 | 1072.5 / 1578.4 / 5454.4 |
| solver | unknown | 8 × 16 | 1.0134 | 51.5 / 52.5 / 56.7 | 50.8 / 52.4 / 55.4 |
| solver | unknown | 8 × 32 | 3.4071 | 189.6 / 224.9 / 254.9 | 62.8 / 65.8 / 68.7 |
| solver | unknown | 16 × 16 | 1.1608 | 205.0 / 216.8 / 231.7 | 150.7 / 175.4 / 431.2 |
| solver | unknown | 16 × 32 | 4.9123 | 863.0 / 969.0 / 1033.7 | 182.3 / 193.4 / 221.1 |
| solver | unknown | 32 × 16 | 1.0873 | 987.3 / 1017.7 / 1123.7 | 698.4 / 840.0 / 3460.1 |
