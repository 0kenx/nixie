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

## Result: predictive signal below the registered gate

Both registered observer cells completed, with no new control/reference runs
or repeated cells. The score predicted lower future literal-trigger counts
than the shuffled-score null, but the reduction was only 15–16% overall and
13–16% in late search. Neither input meets the required 25% reduction, against
either the shuffled null or the exact uniform-candidate expectation. No active
watch policy, timing comparison or parameter sweep follows this screen.

| Input | Eligible / sampled moves | Complete eligible samples | Censored | Complete late samples |
|---|---:|---:|---:|---:|
| circuit | 28,105 / 38,440 = 73.11% | 28,046 | 59 | 23,648 |
| si2 | 63,889 / 72,698 = 87.88% | 63,815 | 74 | 36,420 |

Coverage and sample-count gates pass. Censoring includes history resets and
the unfinished final future windows. Censored samples contribute no labels,
and eligible = complete + censored in each conflict bin. No capacity omissions
occurred; peak pending samples were 76 / 3,663, below the 200,000 limit.

The following totals include only complete eligible samples. Each label counts
the chosen literal's triggers in its next 1,024 long-list trigger events; the
uniform column is the exact mean over that sample's two to four candidates,
summed across samples. Different samples can have overlapping future windows.

| Input / epoch | Original choice | Prediction | Shuffled-score null | Uniform expectation | Prediction / null | Prediction / uniform |
|---|---:|---:|---:|---:|---:|---:|
| circuit, all | 63,424 | 51,228 | 60,932 | 61,284.750 | 0.840740 | 0.835901 |
| circuit, late | 52,445 | 42,442 | 50,561 | 50,495.583 | 0.839422 | 0.840509 |
| si2, all | 802,484 | 646,084 | 760,105 | 757,255.667 | 0.849993 | 0.853191 |
| si2, late | 487,481 | 402,092 | 460,984 | 459,921.750 | 0.872247 | 0.874262 |

Prediction / original-choice totals are 0.807707 / 0.805105 overall and
0.809267 / 0.824836 late on circuit / si2. These are observed proxy differences,
not cycle savings or estimated reductions in actual clause visits. A clause
can change or disappear within a window; different watch choices can alter
later propagation and search. The strong overlap between windows also prevents
treating the sample count as independent solver replications.

The observer examined a mean 3.56 / 6.26 tail positions and retained 2.52 / 3.21
undefined candidates per sampled move on circuit / si2. An active implementation
would pay its own counter-update and selection costs on the selected scope;
those costs are not priced here. The two observed searches made 9,840,737 /
18,610,688 actual watch moves and visited 100,167,701 / 161,699,940 watcher entries.
The visit totals match the independently implemented, previously cached entry
census exactly. They include all visited entries and exclude unvisited conflict
tails; they are not just the sampled candidate cohort.

**Disposition:** archive this cumulative-trigger predictor. Do not tune its
horizon, candidate width, tie rule or history decay against these results as
fresh evidence. The finding establishes a modest predictive relationship on
these unchanged trajectories, while failing this study's required magnitude.
It neither qualifies a policy nor rules out other sources of watch-selection
information. Nixie's production solver and the measured Kissat gap are unchanged.

## Verification and retained evidence

All **1,018 SAT tests passed, one skipped**, including nine new targeted tests.
They cover exact sampling/window boundaries, inspection limits, tied scores,
score permutations, counter growth and explicit capacity failures, censoring,
history resets, conflict-tail/BIG/budget exits, solver scopes, inprocessing, and
24 paired generated formulas with exhaustive truth classification, checked
models, identical clause/trail/watch/BIG/counter state and independent LRAT
verification. Strict SAT clippy with all features/targets, workspace formatting
and the clean committed release build passed. This archived observer has not
undergone full workspace or fresh Z3 qualification; no solver source is landed.

Complete stdout matches the cached `19d4d47` control in both cells. Circuit is
**Unknown at 40,000 conflicts**, solved-at-cap 0/1; si2 is **SAT at 39,246
conflicts**, solved-at-cap 1/1, with its model independently checked against
every original clause. Unknown is not a verified verdict. The stdout hashes
are `abf7160aba5efe114034ca76964f868cd3191a7c0d969bf4db887ad225368b4d`
and `c25ba0a9a391a198ca92943e0e5f07eab463efa505980699e3245d712173d30f`.

Registration: `f1960f3a4f490c902ff9cd0bddf056cff2798034`.
Observer: `66269138c9feb64da9a9b9f34dc56532a5b68f0b`, binary
`precompile/6626913/stats_solve-watch-trigger`, SHA-256
`4bc8eda9d3a879c934b91e4dae4003f2e256927599ea74c140a8bc51218b0fc6`.
Build: portable release, `bcp-watch-trigger`, Rust 1.96.0 / LLVM 22.1.2,
lock SHA-256 `3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
The control's relevant compiled SAT sources and Cargo configuration match the
registration before adding observation. No observer timing is used as evidence.

Canonical records are **`a04dac6eadf7b69a`** (circuit) and
**`8bfb893c5f81d9f1`** (si2), under
`precompile/6626913/benchmark/runs/watch-trigger-shadow/`. Its sibling
`watch-trigger-shadow/` directory retains the manifest, runner, raw reports,
immediate subprocess completion, summary, exact-fraction independent audit,
source patch/bundle, build identity, copied lockfile and qualification logs.
The bundle requires the registration commit on main. The temporary worktree
and its experiment/result branches were removed after archival.

Report schema `nixie-watch-trigger/1` has two `bins` rows: before conflict 16,384
and at/after it. Columns are sampled moves, eligible moves, completed windows,
original label, predicted label, shuffled label, uniform label multiplied by
12, tied minima, differing prediction/null choices, candidate count, inspected
positions and censored eligible windows. Scores reset at activation and the
registered solve/scope boundaries; report counters accumulate across resets.
