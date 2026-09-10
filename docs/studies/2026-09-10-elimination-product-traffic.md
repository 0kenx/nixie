# Propagation traffic from elimination products

## Registration

The retained residual-prefix census rejects sharing executed false prefixes,
but leaves a distinct hypothesis: process elimination parent cofactors instead
of their expanded resolvent pairs. Before implementing that native engine,
measure how much actual long-watch traffic belongs to those pairs. Default
bounded elimination often admits no more resolvents than parent clauses, so
large product compression must be established, not assumed.

Extend the existing opt-in `bcp-groups` observer with passive provenance for
every output actually inserted by `elim_add_resolvents`: output ID, parent IDs,
insertion width and batch identity. A batch is one accepted pivot's insertion
call, not an assertion that its surviving outputs form a complete Cartesian
product. Eager units, skipped/satisfied pairs and other clause constructors
are not mislabeled as inserted resolvents. Record proof-mode insertions too.
Never change resolution, clause order, IDs, budgets or propagation decisions.

On existing sampled lists retain only the visited prefix's clause IDs and
blocker outcomes. Join those visits to birth provenance offline. Count all
sampled visits in denominators, including original inputs, learned clauses,
deleted hits, singleton families and conflict prefixes. Retain provenance
after shrink/deletion: this deliberately overestimates directly born clauses
eligible for a native product. It does not classify copied descendants or
quantify traffic through binary edges. These are explicit scope limits.

For each batch within a visited list, compare visited outputs with the number
of distinct left plus right parents. Report `max(outputs - left - right, 0)`
as a limited, optimistic consumer-count screen: evaluating each participating
cofactor once and paying zero join, maintenance or explanation cost. Also show
one-side sharing separately; it requires suitable cofactor states and is not
an implementable saving. Neither metric establishes persistent event savings.
Report insertion shapes and overall/post-16384-conflict strata independently.

Advance this direct-output, within-trigger product design only if provenance
covers >=20% of all sampled long-watch visits and the cofactor-consumer screen
reaches >=10% of those visits, overall and after conflict 16384. Require >=1000
sampled lists, no capacity omissions and exact stdout identity. Failure stops
the native implementation for this scope; no threshold/stride tuning or
extra input follows. A pass requires a separate executable design and cost
registration; it is not a speedup claim or license to change search defaults.

Budget: ONE new observer invocation on original j3037, seed 0, CPU 15,
MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0, NIXIE_DEFINITIONS=0,
NIXIE_WATCH_GROUPS=4096, all other study overrides cleared. Portable release,
Rust 1.96.0 / LLVM 22.1.2 and retained lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Emergency 300 s, no timing input to the solver. Reuse production stdout from
`0ec1f4bfcfe8f5f9`, prior census `41fc24ef457c85bd`, and requested-mode Kissat
`45a3c8f2e3057841`; no new controls/references or repeated starts. Store source,
binary/input hashes, raw report, immediate completion and canonical record.
Primary is explicitly sampled long-watch visits, not complete solver cost;
instrumented elapsed time is not throughput evidence. Unproved UNSAT remains
unknown/unverified in the canonical record.

Before capture: tests for actual insertion provenance, signed parent IDs,
proof/no-proof paths, visited conflict prefixes, duplicate visits, capacity
and writer errors, scope/reset ID lifetime, plus ordinary/all-feature SAT
tests, strict SAT Clippy and formatting. Independent offline implementations
must reproduce the joins and arithmetic. Archive a rejected observer and
land its finding. Full workspace gates and installed-Z3 4.16.0 parity remain
required before production solver changes. Local Kissat `resolve.c`, CaDiCaL
`elim.cpp` and Nixie's existing resolver specify pair/retirement semantics.

## Result: enough provenance coverage, no two-side consumer saving

The single capture completed with **52,159 sampled lists and 506,812 visited
entries**, with no omissions. Complete stdout is byte-identical to retained
production: reported UNSAT, 330,565 conflicts, 323,390,316 propagations and
695,639,361 ticks. Every existing watch-group counter also matches the previous
census. All 52,159 list ordinals, conflict strata, visited clause IDs and blocker
outcomes match its independently captured residual trace, including the visited
prefixes of its 47 conflict samples. This is stronger observation-identity
evidence than equal aggregate counters alone.

| Quantity | All search | After conflict 16384 |
|---|---:|---:|
| Sampled lists | 52,159 | 49,363 |
| All long-watch visits | 506,812 | 493,262 |
| Direct elimination-output visits | 125,133 | 118,494 |
| Coverage of all visits | 24.6902% | 24.0225% |
| Two-side consumer-count screen | **0** | **0** |
| One-side count, states unverified | 58,182 | 54,827 |
| One-side count / all visits | 11.4800% | 11.1152% |

Both coverage gates pass; both consumer-count gates fail. The registered
direct-output, within-trigger native-product implementation **does not
advance**. No threshold change, extra input, performance comparison or
flamegraph invocation follows. There is no implemented product engine whose
runtime could yet be profiled, and the instrumented capture is not a timing
comparison. This result does not close persistent or conditional cofactor
sharing, narrower cofactor representations, binary-edge traffic, or a changed
elimination policy.

## Why this candidate fails, and what combinations would have to change

The eliminator inserts **57,154 outputs in 6,246 batches**. Of those, 5,559
batches and 54,311 outputs have only one participating parent on one side.
Only seven batches have more outputs than the sum of their distinct parent
counts, exceeding that sum by just one each. Even those small static excesses
do not occur together in a sampled visited list.

Actual traffic is more decisive: 124,932 of 125,133 directly generated visits
belong to within-list groups with one parent on a side. Only 58 visited groups,
containing 201 visits, involve multiple parents on both sides; none has more
visited outputs than participating parents. A one-to-many batch with k outputs
needs k+1 participating cofactors if both sides are reevaluated. Merely
replacing expanded output consumers with both sets of parent consumers cannot
reduce their count here. Counting repeated visits preserves multiplicity;
unrelated clauses and singleton groups remain in every denominator.

The 58,182 one-side count is **not a realizable saving**. Skipping the other
side requires a suitable cofactor state; the report does not record those
states or their maintenance. A satisfied shared cofactor can discharge its
pairs, while a false one activates the opposite side. Matching singleton
unassigned literals across both sides also require a join, as explained in
the [residual-family study](2026-09-10-residual-family-census.md). Neither the
formula equivalence nor birth membership supplies this state machine, valid
reasons, or propagation order.

Joining the retained executed-tail trace gives 234,596 visit/payload/tail
operations for directly born outputs and **764,409 for learned clauses**,
out of 1,083,277 total. This proxy charges one per visited watcher, one per
blocker miss and one per inspected tail literal; it is not cycles. Learned
clauses account for 70.56% of it and are outside this provenance class. Of
the direct-output visits, 77,975 already hit their individual blocker and
only 47,158 reach the payload path. Dropping all output traffic is not
possible, and treating every covered visit as expensive resolution work
would greatly overstate this mechanism's opportunity.

The earlier negative blocker certificates, kept spans and delayed moves do
not supply free parent-state maintenance. Combining their bookkeeping with
this product representation does not remove the remaining k distinct leaf
consumers. The prior structural-definition experiment generated more
resolvents and increased propagation work; it could change family shapes,
but this fixed-policy capture supplies no evidence that it creates enough
useful sharing. That would need a separate registration with a matched null
and fresh seeds, not an inference from this result. Do not retry the present
two-side within-list design with a different stride or timing window.

The measured Kissat gap remains the target. Retained j3037 complete-process
counters separate it into **1.282x propagations per conflict and 1.702x user
cycles per propagation** (2.182x cycles per conflict). This capture changes
neither factor. A large next lever must reduce the learned-clause traffic
dominating the trace, remove a dependent access paid by that traffic, or
establish a cheaper conditional state mechanism with its full maintenance
and reason cost included. Fewer instructions in unrelated bookkeeping do
not establish that benefit.

## Verification and retained artifacts

Observer candidate: `2d26b2ae5953b19c063a67002623635574bc7475`, based on
registration `3aa7994681f27a0c268da57d2d447429bbd40450`. The implementation is
feature-gated and never consulted by search. Before capture, ordinary SAT
tests passed **1,013/1,013**, all-feature SAT tests **1,044/1,044**, with one
existing ignored test in each run. Two doctests passed, one ignored. Strict
all-feature/all-target SAT Clippy, formatting and four Python tests passed.
An initial Clippy warning about an unused LRAT test handle was corrected;
the final affected test and Clippy both passed. These are scoped observer
checks, not full-workspace or Z3 production qualification.

The provenance tests cover actual insertion, satisfied-output skipping,
both pivot polarities and proof/no-proof paths. Generated paired SAT/UNSAT
tests compare observer and ordinary search state, models and independently
checked LRAT proofs. Prefix/multiplicity, capacity/writer errors and ID
lifetime have focused tests. The ID audit checks append-only clause slots,
arena relocation preserving identity, scope retirement, and full database
reset. The candidate resets the observer on full reset because clause IDs
restart there; this is an observer-lifetime change, not a discovered wrong
SAT/UNSAT result. Ordinary scope changes retain birth membership deliberately.

The [offline analyzer](../../bench/suite/scripts/elimination_product_analyze.py)
and its tests are landed. Dictionary/set grouping and an independent sorted
merge join with run-length counting agree on every aggregate and histogram.
Validation rejects omissions, missing samples, duplicate output IDs, invalid
parent ordering/hit flags and mismatched visit totals. A separate comparison
checks every sample against the previously retained trace. Early and late
strata and both gate thresholds have explicit tests.

Canonical observation **`ca7641bfa225b7e7`** is under
`precompile/2d26b2a/benchmark/runs/elimination-product-census/`. The sibling
`elimination-product-census/` directory retains raw stdout/stderr, manifest,
start/completion, runner, analysis, structural summary, preflight logs,
build identity and source patch/bundle. Reported UNSAT remains canonical
unknown/unverified because this invocation did not check a proof. Its
44.316 s instrumented elapsed time is only completion evidence.

Binary: `precompile/2d26b2a/stats_solve-products`, SHA-256
`64226216881037d5d1ca84062f25656aad2fe3f6e84dc15f488e28618c54b56a`.
The portable release uses the registered compiler and lock, with no native
flags or PGO. The [archived patch](assets/2026-09-10-elimination-product-census.patch)
applies to registration `3aa79946`; a temporary Git index reconstructs exact
candidate tree `e3aaad669b8998eb9cc0e97fa4941950cfc1bba3`. The solver observer
is archived, not promoted. No control, Kissat reference or performance cell
was repeated. Owned temporary checkout, branch and build artifacts are
removed after landing; cached binaries and measurement records remain.
