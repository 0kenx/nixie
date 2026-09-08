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

## Observation interface

Build `stats_solve` with `--features clause-traffic` and set
`NIXIE_CLAUSE_TRAFFIC=16`. Library callers use
`Solver::enable_clause_traffic(NonZeroU64)` and
`Solver::write_clause_traffic(writer)`. The JSON schema is
`nixie-clause-traffic/1`; each row identifies one clause in one epoch. Its
`counts[channel][metric]` uses binary/long channels and metrics visits,
immediate blocker hits, payload accesses, tail inspections, unit assignments,
conflicts, and main first-UIP expansions. The initial conflict clause also
counts as one first-UIP expansion when that loop reads it. Consequently these
are event counts, not counts of distinct semantic uses.

Length/glue/tier are observed at the row's first event, not necessarily at
learning or the epoch boundary. Tier values are Local=0, Mid=1, Core=2.
`final_status` is the clause's status when the report is written, not a
retirement timestamp. Original and deleted clauses have separate aggregate
counters. Literal order, strengthening and arena relocation cannot alias
IDs; a promoted original stops adding learned rows. Reset clears records
before IDs restart.

The storage cap is 250,000 clause/epoch rows; the ID index cannot exceed the
row count. Exceeding it reports omitted events by channel/metric. Counter
overflow is also explicit. Neither failure influences solving. The analysis
script refuses either kind of incomplete census. A shared diagnostic session
guard prevents nested public solve calls from clearing outer preprocessing
counts; all early returns release it, and it preserves Solver's Send/Sync
traits. The observer remains enabled after push/pop/reset but starts with
empty records. Re-enabling explicitly also starts a fresh session.

`bench/suite/scripts/clause_traffic_probe.py` checks the exact cached control
stdout and applies the registered analysis. Top-quarter selection uses the
prior epoch only, descending work with clause-ID tie breaks, taking
`max(1, floor(prior_rows / 4))` clauses. Its future-work denominator includes
all learned rows in the next epoch, including newly observed clauses.
Missing future rows remain censored even if the clause is deleted at report
time. Four independent Python tests cover hindsight selection, partial
epochs, missing future rows, direct uses, and invalid observation reports.

The standalone parity harness has a `clause-traffic` feature.
`NIXIE_CLAUSE_TRAFFIC_PARITY=1` explicitly activates stride-one collection in
every constructed SAT solver, including Context's private cores. This is
only available in instrumented builds and is cleared for ordinary parity
and benchmark runs.
