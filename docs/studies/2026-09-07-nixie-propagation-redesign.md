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

Documentation and feasibility registration are the first landed step. The
observation implementation must have tests for repeated blockers, conflict
tails, mid-visit truth transitions, membership churn, history invalidation,
and bounded coverage. Before landing shared-solver changes, run the complete
workspace build/tests/doctests/clippy/fmt/docs checks and fresh Z3 parity with
the user-authorized available version. Exact diagnostic and SAT-model checks
accompany the three measurement cells. Results and the next decision will be
appended here; no speedup is claimed by the registration.

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

All required gates passed on the implementation, including the seven new
observation tests: workspace all-features build; nextest (10,630 passed,
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
Logs and command results are retained under
`precompile/d907929/benchmark/shared-satisfaction-verification/`.
