# Predicting watch-trigger pressure without changing search

## Registration

The fixed-trail scanner boundary failed its cost screen. Prior profiles put
substantial cost in repeated long-watch visits and data-dependent misses; the
failed bulk-blocker representations did not make those visits cheap enough.
This study asks whether an online signal could choose less frequently triggered
watches. It measures a prerequisite for a policy, not another loop rewrite.

At an ordinary watch move, the first undefined tail literal is always the real
choice. A passive observer examines at most eight tail positions beginning at
that literal, retaining the first four undefined literals. For each candidate,
the online score is its cumulative number of false-literal long-list triggers
since observer activation. Predict with the minimum score, breaking ties by
original candidate order. The matched semantic null permutes the very same
score multiset among those candidates, then uses the same minimum/tie rule.
Use a separate fixed-seed observer RNG; never consume or modify search RNG.
This preserves the number of options and score distribution at each decision.
CaDiCaL `src/propagate.cpp` supplies the semantic reference: any undefined tail
literal is a valid replacement; the solver here still chooses the original one.

Sample every 256th actual long-watch move. Increment exact per-literal counters
when a false literal's long-watch list is about to be scanned, after BIG and
budget exits. After the next 1,024 such triggers, label each chosen literal by
the increase in its own counter. Report the summed label for the original
choice, score prediction and shuffled-score null, plus the uniform-candidate
expectation, event counts, ties, candidate counts and inspected tail positions.
Also split samples by whether they began before or after conflict 16,384.
Resolve due samples before new samples at the same trigger; current-trigger
work is excluded from the future window. End-of-solve pending samples are
censored explicitly, never assigned a zero label. Reset history and censor
pending samples at solve/scope boundaries; ordinary backtracks preserve it.

The label is future **literal trigger frequency on the unchanged search**.
It is not an observed reduction in clause visits: clauses may be changed or
deleted, and a different watch can change later propagation/search. This proxy
can reject an uninformative signal; success licenses a separately registered,
fully costed policy/null comparison, never a default flip or a speedup claim.

Require at least two candidates for a comparison. Report eligible sampled moves
over all sampled moves; also report all actual moves and visited watcher entries
(excluding unvisited conflict tails). Capacity limits: two million literal
counters, 200,000 pending samples. Reject activation/growth or explicitly count
lost samples on exhaustion. No inference from omitted data. The observer is
feature-gated and does not change clauses, watched positions, blockers, reasons,
budgets, ticks, schedules, model/proof state or ordinary output.

Exactly TWO new observer runs: circuit and si2, seed 0, MAXC=40000, CaDiCaL preset,
CPU 10, model output, explicit `NIXIE_SWEEP=0`, all other study overrides cleared.
Use clean committed source descended from this registration, identical compiler
and lockfile to the existing `19d4d47` scalar binary. Reuse its cached complete
stdout for identity; independently validate any SAT model. No measured comparison
of observer time/instructions/cycles, no new control or Kissat runs. Record each
cell once with source/binary/input hashes, raw report, immediate completion,
and independently recomputed metrics in the result store.

Advance only if BOTH inputs have at least 25% eligible sampled moves, at least
1,000 complete eligible samples overall and 250 in the late bin, and prediction /
shuffled-null future-trigger totals <=0.75 both overall and late. Null totals
must be nonzero; no capacity omissions or output differences are acceptable.
Report prediction / uniform expectation too; require it <=0.75 overall and late
to guard against an unusually poor shuffled draw. These are two-run telemetry
gates, not a multi-seed causal comparison. No horizon, candidate width, history
decay or tie-break tuning follows the observed data.

Before observation: focused tests of sampling, future-window boundaries,
zero/tied/unequal scores, score shuffling, censoring, limits and scope resets;
paired exact-state/model/LRAT comparisons; all SAT tests, strict SAT clippy,
formatting and the committed release build. Archive the passive prototype and
land its evidence. Any later production source landing requires all workspace
gates and fresh installed-Z3 4.16.0 parity.
