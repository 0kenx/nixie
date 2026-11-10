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

## Initial localization

The rollback snapshot completes all 72 new cells and reuses all 264 existing
cells. SAT remains 24/24; SMT remains 24/48 (18 Unsat, 6 Sat, 10 Unknown,
13 timeouts, one allocation failure). There are no decisive disagreements with
available labels/references. On the same 23 common SMT solves the instruction
ratio is **1.36965**. The policy rollback therefore does not explain or fix the
1.3678 observation. The SAT ratio is 1.00208 on 24 pairs.

Cached adjacent revisions localize the large UFLIA costs and pure-arithmetic
overhead to slice nine, `1106bd4d` → `c8abf146`. Wisa rises from about 32.0 to
393.7 billion instructions; wisas rises from 14.25 to 66.30 billion. FISCHER
and plan-16 retain identical SAT decisions/propagations/conflicts/restarts while
their instruction costs increase. A scan-based `EufSolver::has_app_nodes` is now
called on every assignment, even on graphs containing only leaves. Tracking the
first live application can answer the exact same question without scanning;
this implementation change is under verification, not yet a landed result.

Separate, registered dump configurations show byte-identical initial CNF and
term-to-variable sidecars on both UFLIA cases across the adjacent interface
commits. Their changed search therefore begins after that initial encoding.
The new shared-interface bookkeeping and theory facts still require attribution;
the existence of correctness regressions in that slice does not settle it.

CLEARSY's increase is separate: `029ce7ad` costs 11.25 million instructions and
the next slice, `8ca3622a`, costs 110.36 million, with unchanged SAT counters.
That slice introduces published-model certification. The pipeline timeout is
already present at `68c36c44`, before the interface changes. Neither is attributed
to slice nine. Exact diagnostic costs and artifact paths are recorded in
[`cost-localization.json`](../../bench/migration034/cost-localization.json).
