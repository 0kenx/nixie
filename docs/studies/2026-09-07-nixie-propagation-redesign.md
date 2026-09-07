# Reducing Nixie's work per conflict

## Objective and scope

The mode-matched panel at `0263862` measured 2.22× cycles/conflict and
2.14× instructions/conflict against Kissat. Reaching that panel's throughput
parity requires about 55% less cost. Search quality is a separate target:
the `noL_11_14` median hit the ten-million-conflict cap while Kissat's median
was about 770,000. See [the measured breakdown](2026-09-07-mode-matched-throughput.md).

The user explicitly permits new architectures tailored to Nixie, beyond
mechanisms in Kissat, and requests fewer experimental runs. Reference solvers
remain semantic checks. Negative micro-optimizations do not prove that the
current representation has reached a performance floor. The recently landed
[eager normalization](2026-09-07-eager-watch-normalization.md) is useful within
its measured component scope but does not close the overall gap.

These are research hypotheses, not demonstrated speedups or established claims
of global novelty. Keep pure Rust, exact explanations, scope consistency, and
the repository's full correctness gates.

## 1. Shared satisfaction across watcher groups — first experiment

**Current status:** the opportunity gate passed, but the subsequent
[order-preserving tile kernel failed its registered cost screen](2026-09-07-watch-tiles-prototype.md).
It skipped 25.64% and 17.57% of logical visits on break and circuit, yet used
1.818× instructions and 1.744× cycles/conflict in the two-input geometric mean.
The kernel was removed; its source and four-cell evidence are archived. No
holdout or parameter search followed the rejection. Another representation
must eliminate per-entry traversal and maintenance costs, rather than add
cached groups around the existing flat vectors. The registration and earlier
opportunity evidence below remain as historical context.

Within a trigger's watch list, group clauses sharing a blocking literal. If
that literal is true, one check can establish satisfaction for the whole
group. Unlike the rejected four-watcher prefix experiment, the proposed
representation can avoid individual blocker loads, branches, and visits.
Keep recently inserted/moved entries in an ordinary delta list and measure
the cost of rebuilding or maintaining groups.

The premise is exact: the blocker must belong to every clause in its group.
A true blocker stays true throughout a forward propagation pass. A blocker
that was false or unassigned can become true during that pass; a previously
negative check cannot authorize a later skip. Backtracking invalidates cached
truth, while clause strengthening/removal can invalidate membership. These
conditions must be represented explicitly in any production implementation.
Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp` provide the reference
semantics for individual blocker checks and conflict-prefix preservation.

First measure the opportunity without changing watch choice, visit order,
stored clause order, budgets, ticks, proof state, or search. Start from
`4a9b87f`, whose solver code is the eager-normalization baseline.

### Registered feasibility measurement

Add opt-in, compile-time-gated observation of actual watch-list visits:

- Select one in 256 nonempty lists by deterministic list ordinal. Sample
  across the whole invocation, including preprocessing and inprocessing.
- Snapshot blocker identities and truth at list entry; record actual blocker
  hits in visit order. Only the visited prefix counts if propagation conflicts.
- Count duplicate true-blocker checks, distinguish those already true at
  entry from those becoming true later, and report satisfied-group sizes.
- Count blocker changes and removed/moved entries in the sampled visit.
  Compare membership with the preceding sampled visit of the same trigger,
  reporting the sampling gap. This is sampled persistence, not a claim about
  every intervening visit.
- Bound snapshot/history memory and explicitly report any omitted coverage.
  Group identity and membership comparisons are exact, not hash-only matches.
- Observation state belongs to one solver; scope/solve boundaries invalidate
  persistence history. It never influences a solver decision or result.

The main feasibility statistic is
`(entry-true hits - distinct entry-true blockers) / sampled visited entries`.
It is an optimistic count of removable checks, not a cycle saving: it assumes
free grouping/maintenance and does not account for the cheaper cost of a
blocker hit relative to a clause miss. Also report the visited-entry fraction
in entry-true groups of at least four members, adjacent repeated hits, and
churn. These expose whether a large-group implementation has work to remove.

Advance to a shadow grouping/replay prototype only if **at least two of the
three inputs** have **at least 30% duplicate entry-true checks** and **at least
20% of visited entries in entry-true groups of size four or more**, with no
unexplained observation loss or trajectory difference. Those are feasibility
thresholds, not a landing bar. If they fail, record the narrower conclusion
that grouping the existing blockers lacks the registered breadth/opportunity;
do not silently replace this with a watch-selection heuristic.

Initial measurement cells: CaDiCaL preset, seed 1, `break_unsat_06_07` and
`circuit_48in64out` to completion under the existing ten-million-conflict cap;
`noL_11_14` capped at 100,000 conflicts. Three instrumented runs. Reuse cached
unobserved stdout for trajectory checks wherever available; at most one new
unobserved noL control if an exact current-binary cell is absent. No new Kissat
or CaDiCaL sweep, no seed/configuration tuning. Store every cell once using
`bench/suite/scripts/benchstore.py`, including source/binary/input hashes,
capture configuration, raw reports and diagnostics. Instrumented timings
cannot be used as a throughput comparison.

The first observation format need not replay full CDCL. Any later kernel
replay must additionally preserve assignments, backtracks, clause mutations,
reasons and conflict boundaries. Replay is an implementation-cost screen;
changed search requires a small paired full-solver panel and an untouched
holdout. Heuristic changes additionally require a matched null. Total solve
cost, solved-at-cap, conflicts and cycles/conflict are reported together.

## 2. Native propagation blocks for structured regions

The [three-cell traffic screen](2026-09-07-structured-region-traffic.md) found
no recognized AND/XOR groups and rejected that subset. Its offline follow-up
identified 700 eight-variable relations in circuit, each with 16 allowed rows.
An exhaustively checked factorization would reduce that input's non-unit
literal slots sixfold; runtime benefit is unmeasured. Proof-emitting relation
factorization is the next circuit-specific candidate. Learned clauses dominate
traffic on break and noL, providing a broader lead for idea 3.

Preserve SMT expression structure and recover verified structure from DIMACS
where possible. Compile suitable gate networks, parity systems and cardinality
regions into compact propagation blocks. A block consumes changed inputs,
computes consequences, and retains an explanation recipe; conflict analysis
expands the necessary explanation. Keep ordinary clauses for unsupported
regions and interactions with learned clauses.

Nixie already has gate detection, XOR reasoning and theory explanation support.
The proposal is to combine regions and reduce auxiliary assignments and clause
events, not duplicate those existing modules. Maintain complete explanations,
proof emission, backtracking and fallbacks for exposed internal variables.
The general explanation-producing approach has precedent in
[lazy clause generation](https://www.cs.bgu.ac.il/~mcodish/Papers/Sources/cp07.pdf).
Assess recovered-CNF benefits and native-SMT benefits separately.

First falsification: measure the fraction of actual propagation work covered
by eligible regions, including boundary interactions and explanation cost.
Do not implement a broad compiler when coverage alone rules out a material win.

## 3. Learned-clause usefulness relative to propagation cost

The [region traffic census](2026-09-07-structured-region-traffic.md) measured
learned clauses at 89.90% / 55.29% / 87.55% of sampled visits on break / circuit /
capped noL, and 94.04% / 70.66% / 88.82% of replacement-tail inspections. This
supports collecting cost/use per learned clause; it does not establish that
the clauses are dispensable or qualify a deletion policy.

Measure each eligible learned clause's recurring watch/scan traffic alongside
its use as a propagation/conflict reason. Explore an active set and dormant
storage with bounded reactivation, preserving live reasons, proof dependencies
and scope guards. Nixie already uses activity, glue and usage; the added signal
is the cost paid to retain that information in active propagation.

The hypothesis is fewer expensive active clauses without losing useful learned
information. Excess deactivation can increase conflicts and lose overall.
Before a policy comparison, construct a matched null with the same activation
or deletion counts and timing, scrambling the proposed utility signal. Include
all scoring/reactivation work in deterministic counters. Reject a favorable
cycles/conflict ratio if total cost or solved-at-cap worsens materially.

## Verification and status

The agenda and feasibility criteria were committed before measurement in
`d907929`. The observer and reproducible runner landed in `603ff9b` after
the correctness gates below. Tests cover repeated blockers, conflict tails,
mid-visit truth transitions, membership churn, history invalidation and
bounded coverage. The completed first experiment and next decision follow.

### Observation implementation

The `bcp-groups` feature adds a per-solver collector and is absent from
ordinary builds. `Solver::enable_watch_group_stats(NonZeroU64)` starts/resets
collection; `write_watch_group_report` writes `nixie-watch-groups/1` JSON.
`stats_solve` exposes this as `NIXIE_WATCH_GROUPS=256` and writes the report
to stderr, preserving the existing stdout diagnostics/model format.

Memory limits are 262,144 entries per snapshot, one million retained history
entries and 65,536 retained trigger lists. Both entry and list limits are
needed because an empty post-compaction list still occupies a history record.
Omitted snapshot/history coverage is counted. History compares sorted exact
`(clause id, blocker)` multisets; it clears at solve entries and push/pop.
The membership denominator includes complete lists, while opportunity counts
and histograms include only actual visited prefixes. Those denominators must
not be interchanged.

`group_counts` and `group_entries` use size bins 1, 2, 3, 4–7, 8–15, 16–31,
32+. `by_conflicts` uses conflict bins 0, 1–1023, 1024–16383, 16384+ and
columns `[visited, entry_true, duplicate_entry_true, large_group_entries]`.
`removed` covers moves/deletions from this trigger's list, not destruction of
the clause. `history_gap_sum / history_pairs` is a gap in global nonempty
list visits between sampled observations; it is not a number of restarts.

The reproducible runner is `bench/suite/scripts/watch_group_probe.py`. After
building and caching `stats_solve` with `--features bcp-groups` at a committed
source revision, pass `--binary precompile/<sha>/stats_solve-groups --sha <sha>`.
It writes per-input benchstore manifests, refuses to repeat existing or
incompletely recorded cells, checks SAT models, reuses two cached release
controls and allows the registered missing noL control. Timing of the
instrumented solver is intentionally not reported as a performance result.

### Implementation verification

All required gates passed on the integrated implementation, including the
seven new observation tests: workspace all-features build; nextest (10,637 passed,
12 skipped); doctests (111 passed, 29 ignored); all-targets/all-features
clippy with warnings denied; formatting; and all-features documentation with
warnings denied. The 100,000-case SAT differential found zero mismatches and
zero invalid models. Fresh Z3 parity against the user-authorized available
Z3 4.16.0 gave 169 agreements, zero disagreements and one unresolved case
out of 170. That unresolved case is not counted as an agreement.

An additional, non-required native `cargo check -p nixie-sat
--no-default-features` check stops at the pre-existing frozen-clock assertion
in `nixie-math/src/lib.rs:111`. It is not a passing configuration. The new
observer explicitly requires `std` and is excluded when its feature is off.
The initial verification (10,630 tests) is retained under
`precompile/d907929/benchmark/shared-satisfaction-verification/`. Source
auditing then detected the concurrent `4689d14` library changes, so the full
gates and fresh differentials were repeated on the integrated code. The final
logs, exact source fingerprint and parity report are under
`precompile/603ff9b/benchmark/shared-satisfaction-integration-verification/`.
The subsequent `27b27f6` landing only changed documentation and the independent
`cnf_solve` example; all-targets clippy was rechecked for that example. Library
sources and the measured `stats_solve` binary were unchanged by it. No
measurement cell was repeated during integration verification.

## First experiment: opportunity gate passed on two of three inputs

The registered seed-1 measurements used four new solver cells: three observed
runs and the missing capped noL control. The break and circuit controls were
reused. There were no repeat cells, new reference-solver benchmark runs, seed
sweeps or configuration searches. All three observed stdout reports matched
their controls byte for byte, including every printed search counter and the
circuit model. The circuit model also satisfies every original input clause.
No snapshot or history observations were omitted by the memory limits.

| Input | Reported result / conflicts | Sampled visited entries | Duplicate entry-true checks | Entries in groups of size ≥4 | Gate |
|---|---|---:|---:|---:|---|
| break_unsat_06_07 | UNSAT / 33,293 | 348,456 | 141,822 / **40.70%** | 127,767 / **36.67%** | pass |
| circuit_48in64out | SAT / 186,114 | 3,086,423 | 1,188,116 / **38.49%** | 1,066,460 / **34.55%** | pass |
| noL_11_14 | Unknown at cap / 100,000 | 721,938 | 160,691 / **22.26%** | 91,302 / **12.65%** | fail |

Percentages use sampled visited entries as the denominator, not all original
list entries or just blocker hits. The sampled-list counts are 14,373,
75,122 and 15,275 respectively. The 100,000-conflict noL prefix is an
opportunity measurement, not a solved case or a full-search result. Break's
reported UNSAT is trajectory-checked here, without a newly checked proof;
the canonical record therefore does not mark that verdict proof-verified.

The passing results are not caused only by the initial search prefix. Among
visits at conflict counts ≥16,384, duplicate fractions are 46.85% for break
and 37.81% for circuit; large-group fractions are 43.30% and 33.72%. Capped
noL remains below both gates in that bin (22.84% and 13.12%). This checks
where the measured opportunity occurs; it is not an independent replication.

### Maintenance cost is the next uncertainty

| Input | Adjacent repeated hits / visits | Entries moved or removed / visits | Blocker updates / visits | Retained old membership between sampled visits | Mean sampling gap in global list visits |
|---|---:|---:|---:|---:|---:|
| break_unsat_06_07 | 20.64% | 23.15% | 9.17% | 25.71% | 174,731 |
| circuit_48in64out | 17.44% | 16.39% | 15.93% | 27.75% | 656,570 |
| noL_11_14 | 10.11% | 22.80% | 10.80% | 20.70% | 139,555 |

Adjacent repeated hits alone expose less opportunity than grouping across
the whole list. The move/removal and blocker-update counts also show real
maintenance work within observed visits. Membership persistence uses a
different denominator: the exact intersection divided by the preceding
sampled post-visit membership. Its large sampling gaps prevent interpreting
it as immediate per-visit group survival or a rebuild schedule.

**Decision: advance idea 1 to an order-preserving shadow representation and
cost replay.** The feasibility screen is complete; a production grouped
propagator is not implemented by this step. The next prototype must preserve
the original order of unsatisfied watcher visits, retain an ordinary delta
for mutations, and account for group checks, skipped watcher traffic,
compaction, blocker changes and rebuilding. Reconstructing every group by
walking every watcher on every visit would recreate the traffic it aims to
remove. A negative group check must still allow later truth transitions;
only a currently true shared blocker certifies skipping its members.

A concrete candidate is a fixed-size tile of watchers with a small set of
`(blocker, membership mask)` headers. A true header clears its members from
the work mask; visiting the remaining set bits in increasing position keeps
the original order. Members skipped as satisfied still have to survive any
compaction, and a false header cannot suppress later individual checks.
Tile boundaries can split the measured whole-list groups, so retained
opportunity and mask/compaction traffic both need measurement. This is a
prototype design, not an implemented representation or a proven cost win.

Keep scheduler accounting separate from cost measurement in that prototype.
The current propagation ticks deliberately charge logical list size using
eight bytes per watcher and include phantom binary entries, despite a
twelve-byte physical watcher. Preserving those ticks can preserve search;
they cannot then establish the new representation's physical saving. Record
actual group checks, visits, copies and rebuild work separately, followed by
instructions and cycles per conflict in a bounded comparison.

This result establishes removable *check counts* on two registered inputs.
It establishes no cycle reduction, does not cover binary propagation or
conflict analysis, and assumes free grouping when computing the opportunity.
NoL's capped prefix gives weaker support. A single seed and three inputs
do not establish benchmark-wide benefit, and the existing Kissat throughput
gap remains unclosed by this diagnostic implementation.

### Reproducibility and stored evidence

Observer source: `603ff9be3cb9446acf9f8035198442e31d04c36c`.
Probe binary: `precompile/603ff9b/stats_solve-groups`, SHA-256
`4923f7e325c4799a113c8dd1535877e93b10095e4213cdb3599881ee311b1235`.
Control binary: `precompile/eb3a62d/stats_solve`, SHA-256
`76a883a819c437d1e8dd4c43828975b860212027b13554219f4b8f5cde119332`.
Both use the same dependency lock, SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
The intervening `3a4622f` and `4689d14` changes concern SMT/BV solving.
`4689d14` also adds an explicit level-zero propagation API, which these
DIMACS runs do not call. The observation binary and its controls use the same
underlying SAT search implementation.

| Input | Observation record | Reused/control record | Input SHA-256 |
|---|---|---|---|
| break_unsat_06_07 | `aa076232602d9693` | `50fa8316e92aed2a` | `8c94b7be135467462330cd4819c1d2acdbabd2c7f9290a6c53409186021a4bbf` |
| circuit_48in64out | `6a37f1404f1a6e5b` | `a6b0151744a458c1` | `d3338c04e29f5c8b7e75686fa30fd9927babb7b34b9f7c87785397662f59d8e2` |
| noL_11_14 | `582f3db2286905aa` | `4e70e8d19a55d4c0` | `04fa242c31eb4b487c776adb647f03cc2486afbc7a4bbdc902b227ba96dc8b68` |

The runner's manifests, raw reports and complete summary are under
`precompile/603ff9b/benchmark/shared-satisfaction-probe/`; canonical
observation records are under that commit's `benchmark/runs/` directory.
Canonical control records are under `precompile/219bed6/benchmark/runs/`
(break/circuit) and `precompile/eb3a62d/benchmark/runs/` (noL).
The binary build manifest records the compiler and build recipe. The
measurement used CPU 2, stride 256, the CaDiCaL preset and the registered
conflict caps. All report arithmetic and record identities were independently
checked from saved data without additional solver runs.
