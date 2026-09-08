# Learned-clause traffic and later direct use

## Registered question

This is the next stage of idea 3 in `2026-09-07-nixie-propagation-redesign.md`.
The region census already found learned clauses responsible for 55–90% of
sampled visits. Previous usage-versus-glue and retention-percentage studies
did not establish a useful policy. The new question is whether **recurring
propagation cost per clause** supplies information those scores miss.

Add a compile-time `clause-traffic` observer, absent from ordinary builds.
Select clause IDs with a fixed hash and stride 16, independently of their
traffic, size, glue, tier, use or solver RNG. For every selected learned
clause, count all actual binary/long visits, blocker hits, payload accesses,
replacement-tail inspections, unit propagations, conflicts and clauses
expanded in the main first-UIP resolution loop. Keep separate 4,096-conflict
epochs and record the observed length, glue and tier when each row starts.
Track sampled original/deleted traffic separately. Do not call a clause
"unused": the census does not price minimization, proof traversal, or the
search it might prevent without ever becoming a direct reason.

Counter storage is bounded, with explicit omitted-event and overflow flags.
IDs are append-only inside one observation session. Starting a solve,
push/pop and full reset clear the session; reports describe only the current
session. The observer must not alter clauses, trail values, RNG, watch order,
tick schedules, proof IDs or any solver budget. Compare full diagnostics and
proof transcripts in tests. The semantic reference is the existing Nixie
propagation/resolution loops and Kissat `proplit.h`, `analyze.c`, `reduce.c`.

Exactly **two new observation runs**: circuit_48in64out and j3037_10_mdd_bm1,
seed 0, 40,000-conflict cap, CPU 10. Reuse the clean `2202f0e` scalar outputs
from the persistent-blocker screen as exact trajectory controls; do not rerun
them or Kissat. Use a committed portable release binary. Instrumented time
and PMU cost are not performance estimates. Record every cell once through
`benchstore.py`, with source/binary/input hashes and raw reports.

For each completed adjacent epoch pair, rank sampled learned clauses by
prior-epoch payload accesses plus tail inspections (ties by clause ID).
Report the top quarter's fraction of next-epoch measured work, and the part
of that work belonging to clauses with zero next-epoch direct units,
conflicts or first-UIP uses. Separately report all-clause work/use
concentration, tier/glue/length strata, and observations censored by deletion
or missing future rows. Missing rows are **not** zero future use. Exclude the
partial final epoch from prediction. This is a prospective prediction check
on the existing trajectory, not a counterfactual deletion experiment.

Advance to a cost-aware active-set policy only if both inputs have at least
1,000 sampled learned rows, no observation omissions/overflow or trajectory
difference, and the previous epoch's most expensive quarter accounts for at
least 25% of next-epoch work with zero observed direct use in at least half
the eligible epoch pairs. Otherwise close this signal at this screen. No
parameter/stride/epoch-width search follows the result.

A later policy needs a matched null with identical physical accounting,
selection counts, timing and code paths, but cost histories assigned to
different eligible clauses. It must include accounting/reactivation work and
compare total work and solved-at-cap, not just cycles/conflict. This census
does not license changing solver defaults or claim a speedup.

Before landing the observer: targeted count, tail, lifecycle, capacity and
exact proof/search-identity tests; full workspace build, nextest, doctests,
clippy, formatting and strict docs; fresh available-Z3 parity. Retain the
source, toolchain and all evidence in the binary/result cache.
