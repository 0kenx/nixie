# Correctness-only reconstruction and per-capability gates

The user rejects the remaining 1.28973x cost and requests rollback of the
migration, reapplication of correctness patches only, measurement of that
baseline, and an apply/drop decision for each additional change under the gate
protocol. This supersedes the earlier all-capabilities migration decision.

## Registered reconstruction

Start from pre-migration source `af14b6d2`, not from the assumption that a whole
migration commit is a correctness patch. Preserve historical measurements,
regression evidence and unrelated baseline work. Use an isolated worktree whose
parent is current main; the eventual landing is a forward commit, never a reset
or rewrite of main. Do not land the bare old source with its known wrong answers.

Retain a change in the initial baseline only for an identified invalid verdict,
invalid model/proof, memory unsafety, exact-arithmetic defect, state/scope defect,
or invalid resource-result contract in existing behavior. Record the reproducer
and independently examined layers. Necessary representation/API dependencies
must be named as dependencies, not silently counted as standalone features.
A known missing certificate may produce Unknown or a model error; it must not
be replaced by a successful-looking default. Improving Unknown to Sat/Unsat is
additional solving coverage, not on its own a correctness justification.

The audit inventory is `bench/migration034/rebuild-plan.json`. Each original
slice must end with an explicit split/retain/drop decision. Source-level
subtraction is checked against the old and rejected trees so optional features
cannot survive merely through a dependency-heavy commit.

## Baseline verification and measurement

Use standard release builds, all required workspace/all-feature checks and
separate doctests, installed Z3 4.16.0 parity, and the unchanged pinned perf gate.
Preserve tests that expose incorrect existing behavior. Tests for withdrawn
capabilities belong to their candidate patches, rather than being silently
weakened to declare the old feature present. Record any deliberate loss of
solving coverage separately from soundness.

Measure the same 24 SATLIB and 48 SMT-LIB inputs, 30-second caps, 8 GiB, CPU
assignment and complete-process instruction counter. Reuse existing before,
migrated, rollback, cost-fixed, Z3, Kissat and CaDiCaL cells. Record all outcomes,
solved-at-cap and the original common-solve cohort. No task-owned build/test
runs overlap performance measurement. Every new cell is recorded once.

## Additional-capability decision protocol

Before measuring each candidate, register its exact source, intended user
benefit, targeted correctness/coverage cases, affected paths and acceptance bar.
Compare it with the measured correctness-only baseline and with the cumulative
accepted tree. Run the applicable release, differential and pinned performance
gates before landing. For any search-policy change, use a matched null, at least
ten effective common seeds, complete-work counters, baseline distributions and
fresh-seed replay; the single-default snapshot cannot authorize it.

Require zero wrong answers and no lost standing solves. Treat aggregate cost
within the documented 5% band as neutral, never as evidence of a speedup. A
feature needs a concrete coverage/API benefit even when cost-neutral. A cost
outside that band requires specific benefits and family-level accounting; the
rejected aggregate regression cannot be reintroduced by approving individually
small slices. Prefer dropping an optional feature or restricting it to its
explicitly requested use over charging unrelated inputs. Invalid controls,
unverified behavior or benefit-free complexity fail the decision gate. Record
negative results and apply/drop reasons on main as well as successful changes.

No source rollback or correctness-only performance result is claimed yet.
