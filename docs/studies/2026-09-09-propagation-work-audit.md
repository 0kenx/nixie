# Propagation work behind the Kissat wall gap

The qualified residual-cache landing `f9d6714` improves circuit seed-1
wall from 9.63 to 8.81 seconds, with identical Nixie state/output, while
the requested mode-matched Kissat takes 1.88 seconds. Nixie reports
19391470 processed trail literals and 186114 conflicts; Kissat reports
6684415 and 167929. Similar conflicts do not establish similar work.
See [the preceding result](2026-09-09-connected-residual-payloads.md).

## Questions and audited instrumentation

Separate propagation inside scheduled inprocessing from the remaining
work before blaming search/restart replay or elimination. Nixie's default
CaDiCaL preset runs effort-budgeted vivification, whereas the requested
Kissat flags explicitly disable it. Keep those policies and comparison
flags unchanged; this is a diagnostic attribution, not an ablation or a
heuristic enablement claim.

The existing `NIXIE_INPROC_TRACE=1` captures cumulative propagation deltas
around scheduled `inprocess` calls and each of its five passes. Its timers
are output only and do not feed policy. `NIXIE_LOG_ELIM=1` records phase
entry conflicts, original-clause counts, round completion, units and
cumulative resolution counts. The latter does not record all internal
propagations, and neither directly measures replay after restarts or the
final root queue reset. These coverage limits must survive the analysis.
Root rewinds have soundness obligations: pending root implications consumed
under temporary vivify assumptions must be rediscovered after backtracking;
do not remove queue resets based on timing alone.

The initial elimination audit also checked CaDiCaL `src/elim.cpp`: hitting
the round limit leaves a phase incomplete, exactly as Nixie's current
bound-growth rule does. Merely seeing no bound growth after two rounds is
not evidence of a porting bug. Eligibility (raw occurrence limit 100 vs
Kissat's default 2000) and definition extraction differ and deserve a
work-volume audit, rather than a blind threshold/default flip.

## Registration: one cached-binary diagnostic invocation

Use qualified `precompile/f9d6714/stats_solve`, measured binary SHA-256
`d1fbf1afa2c333b27d9ae4ba324878f1772d7043c917ccaa907717148abdd52e`,
source-equivalent to `a64b285`. Original circuit SHA-256
`d3338c04e29f5c8b7e75686fa30fd9927babb7b34b9f7c87785397662f59d8e2`,
seed 1, CPU 15, MAXC=10000000, `NIXIE_SWEEP=0`, printed model and
300-second emergency cap. Clear other study variables. Enable only the
two trace flags above. Capture stdout/stderr in anonymous tmpfs files,
record start and completion immediately, and write the canonical result
once. No automatic retry, new control, new Kissat run or performance claim
from traced elapsed time. Confirm no constrained competing userspace
thread includes CPU 15 before execution.

Require complete stdout identity with candidate record `ee11cd60c342c2fb`
and a model checked against the original CNF. Report all phase counts,
aggregate pass propagations, total eliminated variables and whether each
elimination round completed. Reconcile summed deltas with the terminal
counter; leave unmeasured phase/replay costs unassigned. Prefer existing
source/counter evidence over an additional observation run. The next
implementation, if justified, needs its own costed registration and
correctness argument; this trace cannot establish a policy win.


## Result: most propagation is outside scheduled inprocessing

The one registered invocation completed with byte-identical stdout and an
independently checked original-CNF model. Canonical record
`92ce14f418cbd4ab` is stored under `precompile/f9d6714/benchmark/runs/`;
raw trace, command, hashes, affinities, starts/completions and reconciled
analysis are under `benchmark/propagation-work-audit/`. Its elapsed time
is diagnostic only and is not a new wall benchmark.

| Scheduled work | Processed trail literals |
|---|---:|
| Vivification | 895469 |
| Transitive reduction | 13787 |
| ELS, BVA, pure/subsumption | 0 |
| **Sum over 33 scheduled rounds** | **909256 (4.69%)** |
| **Outside those calls** | **18482214 (95.31%)** |

Every round's five pass deltas sum exactly to its whole-call delta. There
are 12 elimination phases and 24 rounds; **all 24 rounds complete**, with
228 variables eliminated and 3501242 total attempted resolutions. Increasing
the elimination resolution budget does not address an observed exhaustion
on this run. Round-limit phase completion still follows CaDiCaL's semantics.

The final reset after each of the 33 scheduled calls can replay at most
33 x 2848 = **93984 existing literals** (0.485% of the aggregate), even if
the whole variable set were at root each time. This bounds only those exit
resets, not other rewinds or newly derived consequences. The trace does not
separate the remaining total into ordinary search, elimination, pre-search
work and other replay. Do not call the remaining 95.31% pure search or infer
that every root rewind is negligible. `stats.shrunken` counts literals
removed from learned-clause analysis, not propagation-head resets.

## Eligibility and the already available representation repair

A read-only recount of the original input gives 64 unit clauses and
168000 width-eight clauses over 2848 variables. Among its 2834 two-sided
variables, **zero** have heavier polarity occurrence count <=100; **all
2834** are <=2000 (maximum 844). This is before root propagation/subsumption,
not a dynamic rejection count: those passes make some candidates eligible,
as the 228 observed eliminations demonstrate. The trace's `orig` field is
also not an independently counted live database size: raw retirement and
promotion preserve historical ClauseDatabase accounting, so use it only
with that qualification.

This confirms the relevance of the [existing exact relation transformer](2026-09-08-relation-factorization.md),
not a new discovery of the relation structure. That implementation already
recognizes all 700 groups, emits the equivalent 44864-clause formula, checks
all local assignments and produces a resolution proof prefix. Its historical
one-seed feasibility result is not a default-enablement result. Reimplementing
the same recognizer or blindly raising the occurrence threshold would waste
that work. Missing cheap definition detectors are another option, but a
high occurrence limit without cheap definition handling can expose a much
larger cross product.

The next concrete step is an explicit in-memory solving mode using the
existing exact transformer, with the same clause order and bounded fallback.
Preserve ordinary defaults, retain the original formula for SAT model
validation, and include transformation/loading/validation in its wall time.
This makes the existing algorithm usable in one input-to-verdict invocation;
it does not establish factorization's general merit or authorize a hidden
policy flip. Ordinary watch-loop work remains relevant on the transformed
representation and on inputs without these relations.
