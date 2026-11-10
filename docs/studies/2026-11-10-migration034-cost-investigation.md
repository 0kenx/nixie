# Migration 0.3.4 SMT cost investigation

## Registered investigation

The user requires an explanation for the observed 1.3678 geometric-mean
instruction ratio, accepting increased cost only where directly required for
correctness. The prior policy rollback is `507ce04c`. No assumption is made that
it removes the measured cost.

First measure that cached, standard-release binary on the unchanged 72-instance
sample using `bench/migration034/rollback-manifest.json`. Retain the existing
suite identity, instance bytes, CPU assignment, clean environment, 30-second
external timeout, 8 GiB limit and whole-process instruction metric. Reuse all
264 completed migration/reference cells; execute only the 72 new rollback cells.
The original manifest and results remain historical evidence.

Next localize the changes using cached intermediate release binaries and
instruction sampling. The initial diagnostic cases are the five largest
completed-pair instruction increases (Wisa, CLEARSY, wisas, FISCHER and plan-16)
and the lost `pipeline-invalid` solve. Selection is explicitly retrospective:
these are fault-localization inputs, not a held-out performance claim. Freeze
each additional binary/configuration manifest before executing it; store each
measurement once and reuse it. Sampling runs have their own configuration and
do not replace the original cost observations. Check build-profile provenance
before using intermediate costs for attribution.

For each localized change inspect callers, generated constraints, theory state,
model validation and scope restoration. Classify the cost as required correctness
work, avoidable implementation overhead, or unsupported search-policy change.
An existing correctness test justifies its obligation, not arbitrary execution
cost on unrelated inputs. Preserve the obligation while removing repeated or
irrelevant work where equivalence can be established.

No heuristic optimization is authorized by a favorable single-default number.
Any proposed search-policy change requires a separately registered matched null,
at least ten effective seeds, complete-work counters and fresh-seed replay under
`AGENTS.md`. A correctness fix requires a reproducer and independent inspection
of the affected invariants. A semantics-preserving implementation change must
establish what is preserved, including budget accounting and generated order;
if it changes search policy, it enters the heuristic protocol instead.

Acceptance requires the full release verification gates, current Z3 4.16.0
parity, and the pinned SAT gate, plus the same full SMT sample for any resulting
binary. Report all gained/lost solves and disagreements alongside costs. Never
justify the aggregate increase solely by saying the migration contains soundness
fixes. Record unresolved costs and negative experiments explicitly.
