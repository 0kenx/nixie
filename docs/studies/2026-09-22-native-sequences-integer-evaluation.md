# Integer evaluation cost in native sequence histories

## Pre-registration

Baseline: `097ca4ad4773f27acd37927afbf567b616b38acd`, cached symbolized release
binary SHA-256 `1b82996ba06c3ec34448638bebfd26c4bfb528f65236a82a1112982f10558e2c`.
A pinned CPU 6 instruction profile of history-512 (20M sampling period,
550 samples, zero lost samples) attributes 30.9% to num-rational checked
multiplication, 12.0% to checked addition, and 5.1% to rational reduction.
The hot callers are simplex assignment recomputation and bound accumulation.

Try integer-only fast paths at these checked evaluation operations. With
both denominators exactly one, checked i64 numerator arithmetic gives the
same canonical result and the same overflow failure as num-rational. Keep
the original trait operation for all fractional inputs. In particular, do
not replace it with the existing wider-intermediate simplex helpers, which
can change where overflow is reported. Retain exact row recomputation,
wide-value handling, explanation collection, and independent native model
validation. This is a mechanical cost change, not a search policy change.

Z3 `src/util/mpq.h:231-247,295-303` similarly dispatches integral addition
and multiplication directly to integer arithmetic and resets denominator
one; CVC5 `src/util/rational_gmp_imp.h:243-276` delegates exact operations
to its GMP rational representation. Nixie keeps pure Rust and its checked
fixed-width / exact-fallback contract. The actual fixed-width oracle is
num-rational's CheckedMul implementation and checked_arith_impl macro.

Accept a >5% history instruction reduction, no lost decisive results, and
all correctness and performance landing gates. Reuse both prior Nixie
measurement sets and original Z3 4.16.0 cells. Measure every candidate cell
once on the same 22-case, ten-requested-seed corpus, CPU/event/cap settings.
Report paired ratios and coverage, including neutral or regressing cases.
The native child solver still drops the requested seed; report this known
limitation rather than calling those ten independent trajectories. Require
complete history-512 diagnostic trace identity in addition to the structural
same-operation argument. Any trajectory-changing experiment requires a
separate matched-null design and is outside this plan.

## Soundness and scope audit

The only production changes are two private, stateless scalar helpers and
eight call sites in `Simplex::update_assignment` and `Simplex::delta_acc`.
No caches, trails, counters, scheduling flags, sort handling, or AST walks
are introduced. Integer multiplication in the old trait first divides by
`gcd(n, 1) = 1`, checks the numerator product, then normalizes denominator
one. Integer addition computes lcm one, checks the numerator sum, then
normalizes. The fast paths perform precisely the potentially failing
operation and directly construct the already canonical result. This also
holds for zero, negative values, and `i64::MIN`; overflow returns None.
All other operands call the exact original trait implementation.

The caller audit checks both the successful and failing paths:

* Assignment recomputation still bypasses narrow values for wide-point
  references, preserves row order and component-write order, and retries
  the whole row with BigRational on either product or sum overflow. An
  unrepresentable final still migrates the row to the wide store. Existing
  wide-row migration and bound-change regressions cover these paths.
* Delta accumulation still computes both products before writing either
  component and may write the real component before a failing delta sum.
  A new regression compares both the Option result and this partial state
  against the old operations. Its bound-derivation caller still replaces
  the whole accumulated sum on exact retry and collects every remaining
  antecedent without double counting. The existing
  `basic_bound_exact_retry_does_not_double_count` regression protects this.
* Bound writes and rollback still use their existing trails. The helpers
  have no state that can survive push/pop. Scope and incremental arithmetic
  tests exercise the unchanged callers.
* Native reduction, model completion, and independent interpretation of
  original sequence assertions are unchanged. Solver-level parity and
  native sequence differentials test the final answer boundary.

New primitive tests compare 4,900 integer operand pairs against both the
old checked traits and exact BigRational results. Fractional pairs compare
values and rejection points, including an intermediate-overflow sum whose
reduced final fits: the fast path must preserve None here. The independent
oracle ensures agreement is not merely two copies of the same arithmetic.

## Measured result

All 220 candidate runs completed: **190 decisive, 30 Unknown, zero wrong
answers, errors, or timeouts**, matching both prior Nixie binaries. All
190 decisive pairs have valid 100%-enabled instruction counters. The
unsupported symbolic-length/index/word-equation probes remain Unknown.
Ten requested seeds per case repeat the existing default native child
trajectory; these are instruction distributions, not ten independent
search trajectories.

| History length | Previous instructions, median [min–max] | Candidate instructions, median [min–max] | Paired candidate/previous |
|---:|---:|---:|---:|
| 8 | 5.259M [5.257–5.262] | 5.190M [5.184–5.193] | 0.9868 |
| 32 | 13.443M [13.442–13.450] | 13.143M [13.138–13.150] | 0.9776 |
| 128 | 95.691M [95.684–95.713] | 85.631M [85.626–85.644] | 0.8949 |
| 512 | 11005.940M [11005.844–11006.773] | 8100.095M [8099.984–8100.309] | 0.7360 |

History-512 uses **26.4% fewer instructions** than `097ca4ad`, and 71.9%
fewer than the original 28.86B-instruction implementation. The four-history
geometric ratio is **0.8928** (10.7% less work). The length-8 and length-32
changes are inside the ±5% neutrality band. Across all 19 commonly solved
cases the ratio is **0.9759**, also neutral; the material gain is in larger
histories. The SAT-only ratio is 0.9133 over five cases, and UNSAT-only is
0.9993 over fourteen. Append, tail and split family ratios are respectively
0.9989, 0.9993 and 0.9974. Every other supported case is neutral.

Against the reused Z3 4.16.0 results, the ratio over the 15 commonly solved
cases is **0.04990** (20.04× fewer instructions). This remains a conditional
comparison on the fixed-shape synthetic corpus: four Z3 timeouts are
censored, while Z3 solves the three symbolic probes Nixie declines. Z3 and
historical Nixie cells were reused, not rerun or selectively replaced.

The complete history-512 trace retains all 462,672 decision events, 671
conflict events, and 1,536 variable legend lines. The canonical trace is
byte-identical to the prior trace (464,880 lines), SHA-256
`6749ea7391c6b7128e47a2e81e923ab6635d76d37434f5ae5246e58dd72284d5`.
Both captures concatenate stdout followed by stderr, preserving every
byte and the full ordering within each stream. The improvement
removes arithmetic work on the same search, not a lucky change of trajectory.

The final 20M-period profile contains 405 samples (~8.10B instructions),
with zero lost samples or throttle/unthrottle events. The old out-of-line
checked rational routines cease to dominate; `propagate_bounds_in` now accounts for 32.1% of samples, followed
by small-vector copies, rollback and hash-map work. This records the next
bottleneck, not an additional unmeasured optimization in this landing.

## Reproduction

The candidate was measured using the existing
`bench/native_sequences/compare_optimization.py` with the original
`native-sequences-z3-perf` records as `--baseline`. The saved candidate
cells were then joined by case and seed to `097ca4ad`'s `comparison/`
records; `previous-comparison.json` retains every distribution and paired
ratio. No candidate cell was rerun. The runner fingerprints the executable,
host, baseline manifest, CPU/event/cap and environment (hash only; no secret
values). The historical original environment-fingerprint limitation remains.

The run-once sequence schema is used rather than asserting benchstore's
`verified_model_or_proof` field for unsupported native UNSAT proofs; this
is the same explicitly documented constraint as the original study. Native
SAT models are independently validated; UNSAT relies on the reduction and
scalar solver, screened against the reference, without claiming a proof.

Release optimization/LTO/codegen settings are unchanged; symbols are retained
with `CARGO_PROFILE_RELEASE_STRIP=none`. Measured executable SHA-256:
`e4e76cbc4f6f8c5e00d13553089f4b6f4336b4f77679b299c9cb4f187f25c2bf`.
The binary, raw measurements, profiles, traces and verification logs will
be cached under the landed commit's `precompile/` directory.

### Binary isolation correction

An initial `cargo build --release -p nixie-cli` produced a CLI-only artifact
with hash `a46bb0f46ae566e59075a478d6fde3448951ff46b0afc0fd62742b67069aa122`.
Its 220 cells are retained separately as preliminary; history-512 used
7.974B instructions. The parity script subsequently ran the default workspace
release build, whose Cargo feature unification produced the final binary
above. The prior `097ca4ad` baseline was also a workspace release build.
The executable path was mutable: the workspace build replaced
`target/release/nixie` while the initial standing gates were running.
Those mixed-artifact gate logs are retained but are **not landing evidence**.

The corrected procedure copies the final workspace executable to an immutable
path before any measurement. Its distinct hash receives its own 220 cells,
trace and full standing gates; no existing same-hash cell is rerun. All
numbers above use that final artifact. Future runs must pass cached/frozen
binaries to comparison and gate scripts, never a target executable that a
concurrent Cargo command may replace. Keep build selection and feature
unification aligned with the baseline. This administrative failure and both
measurement sets are retained so it cannot be mistaken for selective reruns.

## Verification

The final frozen executable passes Z3 4.16.0 parity: **176 Correct, 0 Wrong,
1 Inconclusive, 0 Timeout, 0 Error**, over 177 inputs. The known
`AUFLIA/array_unique.smt2` remains Nixie Unsat versus Z3 Unknown and is
excluded from decisive parity.

The final performance landing gate passes with conflict and decision ratios
both **1.000** over all nine nontrivial cases; three configured external
cases also retain their verdicts. The separate whole-instruction standing
comparison is **1.0011** over all 12 cells, with identical verdicts and
conflicts: neutral outside the motivating sequence history family. Its
baseline is the standing `28e82c65` executable, not the sequence baseline.

The initial full workspace test run stopped after 9,173 passes when the
600-search scope-convergence regression hit its unchanged 300-second limit;
3,037 tests were not run. All logs are retained. Concurrent compilation and
standing performance gates made this a loaded run. Among 35 completed tests
in unchanged core/math/SAT crates taking >1 second in the prior landing,
the median wall ratio was 1.574; the unchanged finite-field identity test
went 102.096s to 168.968s. The timed-out scope test took 198.263s at the
previous landing. This supports a load explanation but does not substitute
for passing the regression and the complete suite. No timeout budget or
assertion is weakened.

The isolated scope-convergence regression passed in **247.114s**, with its
original 300-second limit. The subsequent full rerun uses two test workers
pinned to performance cores (`taskset -c 0-7`), with no concurrent benchmark
or build processes from this task. All source and test assertions are
unchanged between these verification attempts. Three new primitive tests
also passed separately, including the independent BigRational checks.

During that rerun, the scope-convergence test passed in **206.024s**. Main
then advanced to `6723d2ac`, a heap-definition optimization. The pre-integration
run was deliberately stopped after more than 10,000 passing tests, and that
commit was fast-forwarded into the worktree; the termination log is retained.
All build/lint/doc/test gates restart on the combined tree, including the
new heap tests. This avoids claiming pre-integration tests as a complete
verification of the landing tree.

The integrated workspace release build is **byte-identical** to the frozen
measured CLI (`e4e76cbc4f6f8c5e00d13553089f4b6f4336b4f77679b299c9cb4f187f25c2bf`).
Consequently the existing native-sequence cells, diagnostic trace and CLI
performance-gate records apply unchanged and are reused rather than executed
again under another label. Z3 parity uses a separate executable that links
`Context` directly; its build identity is checked separately. Heap changes remain their own main
commit; this change adds only the checked evaluation fast paths and tests.

The separate parity runner changed from
`b319313076ac3a20a861309b3d0599e14f9c884f194fd0150353a9bcee73ba48` to
`51db0a0f2cbce4187384985de459d67808fb9dba5575ee1006c22993fd20b3e4`.
Therefore the full Z3 4.16.0 parity gate was rerun on the integrated runner:
again **176 Correct, 0 Wrong, 1 Inconclusive, 0 Timeout, 0 Error**.
The CLI's identical hash was not used as evidence about this distinct binary.

Completed integrated static and workspace gates:

* `cargo build --all-features`: passed.
* `cargo nextest run --workspace --all-features --build-jobs 4
  --test-threads 2`, pinned to CPUs 0–7: **12,214 passed, 0 failed,
  17 skipped**, 640.654s. The scope-convergence regression passed in 208.086s.
* `cargo clippy --all-features --all-targets -- -D warnings`: passed.
* `cargo fmt --all -- --check`: passed.
* `cargo doc --no-deps --all-features`: passed with repository rustdoc
  warnings denied.
* Separate workspace doctests: **114 passed, 0 failed, 31 ignored**.

Debug/test builds use `CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
CARGO_INCREMENTAL=0`, retaining assertions and the existing timeout limits.

The explicit ignored congruence canary
`pete_cxs_bp_is_unsat_on_every_trajectory` passed in **131.660s**. Native
sequence tests passed **14/14** (two core tests and twelve solver tests),
including **214 decisive Z3 4.16.0 differential agreements**. Both existing
CVC5 **1.3.4** heap differential tests also passed on the integrated tree,
checking the newly landed heap reduction with the modified shared arithmetic.

Main's subsequent `b3b760dd` heap benchmark-analysis/report commit was also
fast-forwarded. It changes no Rust source, Cargo configuration, or solver
test input; the solver binaries and Rust verification remain unchanged.
Its Python analysis unit tests passed after integration.
