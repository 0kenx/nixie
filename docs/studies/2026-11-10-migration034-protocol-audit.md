# Migration 0.3.4 protocol audit and policy rollback

## Trigger and findings

The user challenged compliance with `AGENTS.md` after the migration benchmark.
The benchmark is preserved in commit `1605a116` and
[its study](2026-11-10-migration034-benchmark.md). Its before/after numbers are
observations, not the matched-null evidence required to justify a heuristic.
Calling that single-default run a snapshot does not make it a compliant
heuristic-acceptance experiment; it cannot be used to approve these activations.

The migration's claim that all required gates passed was too broad as a statement
of protocol compliance. The archived release build, full nextest/doctest, Clippy,
formatting, documentation, trajectory-canary and Z3 logs establish those checks;
they do not establish adherence to the heuristic experiment protocol.

Two default activations lack that required evidence:

1. `7034f149` added MBQI guard-boundary proposals with a new pivot schedule,
   bounded tuple enumeration, and candidate ordering. The study called this a
   completeness feature, but its optional speculative search policy still changes
   the path under a finite budget. It has neither a matched-null comparison nor
   an at-least-ten-seed distribution covering its work.
2. `93fcd2ce` expanded datatype model repair from the existing right-class numeric
   increment to retries on either side, offsets +1 through +8, and alternative
   constructors. Its pinning/validation fixes are correctness work, but those
   extra choices are optional search policy. The same controls are missing.

A further measurement gap affects the migration's broader performance claims.
Its DIMACS conflict/decision gate does not cover the SMT combination, completion,
or model-publication work it changed. The historical audit itself recorded a
large `memory_alias` cost increase while retaining the change for correctness.
That is not a passing measurement of the changed work. Incremental gate comparisons
also used the preceding slice as their explicit baseline rather than establishing
whole-migration cost against the pinned baseline. Neither fact is concealed by
successful tests or by the final SAT ratio of 1.002.

The new complete-work sample measures a 1.368 after/before instruction ratio on
23 shared SMT solves, one gained solve, and one lost solve. It does not identify
which policy caused the increase, and this rollback makes no such attribution.
In particular, the large quantified-free UFLIA cost cannot simply be blamed on
an MBQI guard sampler.

## Corrective scope

Withdraw the unsupported default policy activations instead of reverting the
entire migration and restoring known wrong-answer defects:

- Remove the MBQI guard sampler from production enumeration. Keep its isolated
  arithmetic/budget tests under `cfg(test)` for a possible future controlled
  study; it is not enabled by a feature, environment variable, or default path.
- Restore the datatype repair's single numeric +1 proposal on the right class.
  Remove opposite-side retries, +2 through +8 guesses, constructor alternatives
  and the new ordering of disequality pairs.
- Preserve exact BigRational arithmetic, all original/encoded/constructor pin
  checks, whole-equality-class updates, bounded work, clone-before-trial behavior,
  monotonic violation checks and final interpretation certification.
- Preserve the independent SAT scope, proof, allocator, namespace, wide-number,
  finite-domain theorem, type, model-publication and rollback correctness fixes.
  There is no evidence that reversing those fixes would be a safe correction.

The policy rollback is not presented as an optimization experiment or a solution
to the measured SMT cost increase. It withdraws unsupported behavior. Re-enabling
it requires a separately registered matched-null study with at least ten seeds,
complete-work counters and the required soundness checks. The existing
`NIXIE_SAT_SEED` CLI hooks are in the DIMACS paths; an SMT experiment must
explicitly seed/verify its relevant search and null perturbations rather than
assuming `GATE_SEEDS` exercises MBQI or datatype repair.

Coverage tests now distinguish the withdrawn capability from correctness. The
original enum scope/model regression remains unchanged and passes; a quantified refutation
may return Unknown rather than fabricate Sat. Scope restoration still must not
publish stale models. Unit tests independently retain wide +1 arithmetic, refusal
of a new numeric collision, encoded-root pinning, and equality-class protection.
The encoded-root regression uses numeric fields so removal of enum search cannot
make its pin check pass vacuously.

## Independent checks around the rollback

The removed MBQI call only proposed additional evaluated falsifiers and updated
proposal statistics. It did not establish exhaustive coverage. The generator's
finite-domain/ground metadata, `mbqi/sat_certify.rs` coverage checks, integration
certification, and final published-interpretation checks remain in place. An
empty proposal list is not promoted to a satisfiability certificate.

Datatype repair still gathers pins from original assertions, certificate roots
and encoded ground instances; moves proven equality classes together; checks
literal constructor ownership; computes exact offsets; and evaluates a cloned
trial interpretation. The violation-set check can refuse the retained +1 proposal
without falling through to a wider search. A direct constructor-pin assertion
and the numeric encoded-root regression prevent the reduced search space from
masking those two checks. Scope/model invalidation code is unchanged, and the
original public datatype get-value/push/pop test is retained unchanged.

The dependency/cache inventory also confirms that all 25 migration commits which
changed solver Rust code have cached CLIs. The only changed Cargo manifest was
the isolated SAT formal harness; no solver dependency manifest or `deny.toml`
was changed. These facts establish those specific obligations, not universal
compliance or a proof of the solver.

## Verification

Verification uses Rust 1.96.0 and the repository's standard release profile
(`lto = true`, `codegen-units = 1`), without the earlier fast-link overrides.
The four changed Rust files are hash-checked against the final verification
inputs. Completed checks:

- `cargo build --release --all-features`: pass.
- Full workspace/all-feature nextest: **12,791 passed, 20 skipped**.
  The slow array-convergence regression passed in 99.374 seconds.
- Workspace/all-feature doctests: **117 passed, 31 ignored**.
- Release/all-feature/all-target Clippy with `-D warnings`: pass.
- Workspace formatting: pass.
- Release/all-feature documentation: pass, with `-D warnings` supplied by
  `.cargo/config.toml`.
- Explicit ignored trajectory canary: **1 passed** in 37.329 seconds.
- Official differential suite with installed **Z3 4.16.0**: **176 decisive
  agreements, zero disagreements, one inconclusive**. The inconclusive
  `array_unique.smt2` has Nixie Unsat and Z3 Unknown; it is not counted as agreement.

The pinned performance gate **passed**: all 12 verdicts agree, with nine
nontrivial pairs and three trivial cases. Geometric-mean conflict and decision
ratios are both **1.000**; the secondary wall-time ratio is 1.00. Its baseline
remains `bench/perf_gate/BASELINE` (`28e82c65`); no baseline, timeout or seed
override was applied. This SAT gate cannot establish the cost of changed SMT
work, and no claim is made that this rollback fixes the benchmark's SMT regression.

An earlier build was stopped before the final pair-ordering correction and is
not final verification evidence. Final full-suite linking was resumed with 16
build jobs after stopping an eight-job compilation before any tests began;
completed artifacts were reused. Preliminary focused runs, including failed
test-authoring attempts, are retained as superseded evidence. The final full
suite above tests the resulting source without weakening the existing public
datatype scope/model regression.

The landing's default-feature, standard-release CLI is retained as
`precompile/<rollback-commit>/nixie`. Final and superseded verification logs,
source hashes, the verification driver, and the parity JSON are archived beside
it under `benchmark/protocol-audit/`. The original 264-cell benchmark remains
unchanged and reusable under its recorded endpoint revisions. No temporary
branch or worktree was created for this correction.
