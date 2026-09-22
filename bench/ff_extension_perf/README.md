# Binary extension-field arithmetic performance

Pre-registration, 2026-09-22. Production baseline: `df564313` (the CLI is
byte-identical to cached `4ce171d8`). No measurements have been collected.

Inspect a sampled baseline instruction profile of the F256 two-variable
case before editing arithmetic. The candidate replaces heap-backed scalar
operations in the existing shift-and-reduce multiplication with checked
machine-word operations for degrees <=32. The same coefficient loop,
assignment order, AST walk, work charges, and budget boundary must remain.
Degree >32 retains the exact BigUint implementation. The independent core
convolution/division evaluator remains unchanged. No heuristic is proposed:
the unchanged implementation is the exact-computation control; introducing
a randomized search placebo would test a different claim.

Measure complete CLI invocations on CPU 0 with `perf stat -x, -e
instructions:u`, summing active hybrid PMU rows and requiring >=99% counter
coverage. This covers construction, parsing, field validation, arithmetic,
allocation, solving, model verification/readback, output and destruction.
Kernel instructions are excluded; no kernel-facing mechanism changes.
Wall time is diagnostic only. The external safety cap is 120 seconds and
never a solver policy. No quiet-machine wall-time claim is planned.

`cases.json` fixes the workload matrix. Seeds 0..9 choose independently
planted witnesses (and set NIXIE_SAT_SEED); reserve 10..19 for confirmation.
The matrix includes F4/F16/F256 square roots, both F8 representations,
shared squaring DAGs, two-variable systems, no-root quadratics, an exhausted
budget, certified SAT, and unaffected prime/wide-field controls. No Z3 FF
reference exists. The harness independently evaluates binary arithmetic by
coefficient convolution and polynomial long division. SAT models are checked
against every generated equation; the UNSAT quadratic has its complete root
set independently checked. Unknown is not counted as solved or verified.

Go/no-go: every paired full output must agree, all arithmetic/budget oracles
and repository gates must pass, the non-control instruction geomean must be
<=0.85, at least three non-control cases must improve >=10%, and no case may
regress >5%. Controls within +/-5% are neutral. Fresh seeds must meet the
same bar. Report baseline min/median/max, per-case ratios, SAT/UNSAT/Unknown
counts and lost cells. Do not extrapolate these generated workloads to all
SMT solving. A failed candidate is documented and not enabled.

The baseline and candidate use the same workspace release build, compiler,
lockfile, harness and CPU. Records pin source/binary/harness/instance hashes
and are recorded through `bench/suite/scripts/benchstore.py`. Existing cells
are reused, never rerun; unrecorded failed raw attempts also block reruns.
A generated manifest is saved before each arm starts. No verdict is marked
verified unless the independent harness check succeeded.

```
python3 bench/ff_extension_perf/run.py precompile/BASE/nixie --sha BASE \
  --role baseline --root precompile
python3 bench/ff_extension_perf/run.py precompile/CAND/nixie --sha CAND \
  --role treatment --root precompile
python3 bench/ff_extension_perf/report.py precompile BASE CAND
```

Add `--first-seed 10` to each command for fresh-seed confirmation. The runner
needs permission to use perf hardware counters. Raw SMT-LIB, stdout, perf
stderr and manifests live beside the canonical benchstore records.

## Z3 reference amendment (before reference cost collection)

At the user's request, additionally compare the same fixed 13 cases and
seeds 0..19 with installed Z3 4.16.0. Its upstream release tag is
[`ddb49568`](https://github.com/Z3Prover/z3/releases/tag/z3-4.16.0);
the binary path and hash pin the actual installed Nix package. No native Z3
finite-field syntax is assumed. `z3_reference.py` emits exact QF_BV:
addition is XOR, multiplication is coefficient convolution followed by
monic polynomial long division, and squaring directly encodes the F2-linear
Frobenius map. This last specialization avoids an artificially weak generic
multiplier for the square-heavy workload. The prime control uses bounded
integers with exact modular multiplication. Encoding generation is outside
the measured invocation, as is Nixie's input generation; both include parsing,
solving, and printing the complete generated input.

Before collecting cost, the reference translation passed exhaustive product
checks in F4, both F8 representations and F16, exhaustive square checks through
F256, and functional checks on all 13 seed-zero cases. These are untimed
checks, not repeated performance cells. Returned models are checked by the
independent coefficient-array oracle. No-root UNSAT is checked exhaustively.
The budget case has a planted solution: Nixie's Unknown is reported as
unsolved, while the reference is allowed to solve it. The certified-SAT case
has the same equations and an independently checked model; this comparison
does not claim interchangeable proof formats or certified UNSAT support.

Use the same CPU, instruction counter, coverage rule and 120-second cap.
Set both Z3 `sat.random_seed` and `smt.random_seed` for each seed. Record
reference cells once under suite `ff-extension-z3`, role `reference`, with
translated input hashes and original logical-instance hashes for joining.
Report per-case instruction distributions, Nixie/Z3 ratios on jointly solved
cells, and solved/Unknown counts separately. No acceptance bar requires
beating Z3; the original optimization bar remains unchanged. This comparison
measures two complete solvers with different input representations, not a
native-FF Z3 implementation or isolated arithmetic throughput.

```
python3 bench/ff_extension_perf/z3_reference.py /path/to/z3 --self-test
python3 bench/ff_extension_perf/z3_reference.py /path/to/z3 --root precompile
python3 bench/ff_extension_perf/z3_reference.py /path/to/z3 --root precompile --first-seed 10
```
