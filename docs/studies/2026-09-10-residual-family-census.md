# Shared residual scans: opportunity and representation costs

**Result: reject within-list residual-prefix sharing.** One passive solver
capture, no new performance/control/reference runs. Ordered sharing saves
only 0.0172% of sampled operations under the optimistic cost model; the
sorted-prefix variant saves 0.0936%. No propagation mechanism or speedup is
landed from this result.

## Registration

The structural-elimination screen left j3037 at 2.55x Kissat wall with
definitions disabled. Its on-arm profile attributes 72.87% of cycles to
propagation. Adding more resolvents did not help. This step investigates
whether repeated propagation can share work across real clause identities.
It does not claim that smaller formulas or more eliminated variables help.

Existing blocker and per-clause traffic reports do not retain the literal
sequences actually inspected. Add a passive extension to the `bcp-groups`
observer that records those sequences on every 4,096th nonempty long-watch
list. Preserve actual visit order, clause identity, original/learned status,
clause length, blocker outcome, other-watch value, and each inspected tail
literal/value pair. Capture only visited entries, including the conflicting
entry but excluding its unvisited tail. Mid-list assignments remain visible
at their actual observation time. Never read extra literals into the scan
count or use any observation as a propagation certificate or policy input.

Exactly one new solver observation: j3037_10_mdd_bm1, seed 0, CaDiCaL preset,
MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0, NIXIE_DEFINITIONS=0, CPU 15,
portable release. All other study overrides are cleared. Compare complete
stdout with the retained `54dd3ad` definitions-off cell; reject inference if
the search counters differ. The current production source differs by qualified
elimination safety fixes, so identity is checked rather than assumed.
Reuse its requested-mode Kissat reference; run neither control again.
Observation wall/cycles are not solver throughput measurements. Store the
committed source, binary/input hashes, trace, completion and canonical record.

Analyze false tail prefixes within each sampled list. Forward propagation
does not unassign literals, so an observed false literal stays false through
the list; this permits an optimistic shared-prefix opportunity calculation.
For each actual scan, count already observed prefix edges of length at least
four. Price at least one family lookup per beneficiary scan. Report ordered
prefixes and an optimistic sorted-prefix variant separately, along with a
looser unique-literal bound. Include singleton scans, blocker hits, payloads,
short prefixes, original/learned strata, conflict bins and observation limits
in denominators. No sum across unrelated scopes is a certificate.

Advance to an executable representation only if net saved checks reach 20%
of sampled long-watch visits + payload accesses + tail inspections, both
overall and after conflict 16,384, with at least 1,000 sampled lists and no
omissions/overflow/output differences. This is a deliberately optimistic
event-count gate, not a cycle estimate or a statistical heuristic comparison.
The sorted variant cannot justify an order-preserving implementation. A
negative closes this within-list prefix design; it does not rule out temporal
sharing, shared satisfaction, or a representation with different semantics.
No stride, minimum length, or threshold tuning follows the observation.

Before observation, test exact scan capture, assignments, conflict tails,
classification, writer/capacity errors, and unchanged clause/trail/watch/proof
state; run all SAT tests, strict SAT Clippy and formatting. Archive the passive
prototype and land the evidence. Full workspace gates and installed-Z3 parity
remain required before any solver source enters production.

The semantic references are Nixie's current `propagate.rs`/`watch_kernel.rs`,
Kissat `src/proplit.h` and CaDiCaL `src/propagate.cpp`. Reasons must remain real
clause IDs. A future persistent certificate must cover backtracking,
strengthening, deletion, relocation and scope reset; a transient prefix
observation does not establish those invariants.

## Observation and independent audit

Prototype `73dcc31b41654ca2c842de461ce858db7cab0ad6`, based on registration
`4674abe`, produced exactly the complete stdout of cached control
`58792bf989fa9dc7`: 330,565 conflicts, 323,390,316 propagations, 28,358
restarts, and 695,639,361 solver ticks. This includes every printed counter,
not just the conflict count. The reported answer is UNSAT; neither capture
nor control generated an independently checked original-CNF proof, so the
canonical capture verdict remains unknown/unverified.

The trace contains 52,159 sampled lists, 506,812 visited entries and 383,359
actual tail inspections. All sample ordinals, entry counts and list counts
agree with the independent existing watch-group collector. There are no
skipped lists, skipped entries, history omissions, trace capacity errors or
writer failures. An independent tuple-set implementation reproduces all
prefix savings computed by the trie analyzer. Observed assigned values never
change or become undefined within a captured list.

Here **work** means visits + payload accesses + tail inspections. These are
event counts, not weighted instruction/cycle estimates; no profile percentage
is multiplied into them to invent a wall-time prediction.

| Quantity | Whole capture | At/after conflict 16,384 |
|---|---:|---:|
| Sampled lists | 52,159 | 49,363 |
| Work events | 1,083,277 | 1,054,979 |
| Ordered-prefix beneficiaries | 55 | 55 |
| Ordered checks saved before lookup | 241 | 241 |
| Ordered net after one lookup per beneficiary | 186 (0.0172%) | 186 (0.0176%) |
| Sorted-prefix beneficiaries | 214 | 213 |
| Sorted net after one lookup per beneficiary | 1,014 (0.0936%) | 1,011 (0.0958%) |

Both registered 20% gates fail by a wide margin. Sorting is an order-relaxed
variant, not an order-preserving optimization or an exhaustive subset-sharing
oracle. The finding is scoped to sharing previously observed false prefixes
within a watch-list visit. It does not estimate lifetime reuse across lists.

## Why the mechanism is too small, and what its costs would be

The expected large repeated residuals rarely appear in the actual scan:

- 61.90% of entries exit on their existing true blocker.
- Of 186,225 scans, 48.47% encounter no false tail literal at all, and
  91.81% encounter fewer than four. The mean inspected tail is 2.059
  literals overall and 2.529 for learned clauses.
- 108,251 scans visit clauses wide enough to contain a four-literal tail,
  but only 15,257 actually traverse four false literals. Clause width is
  therefore a poor proxy for the work that could be shared.
- Even an unrealistically free individual-literal cache could remove only
  60,613 repeated false checks within these lists: 5.60% of work events.
  This looser bound still pays no lookup, construction or invalidation cost.

The ordered trie constructs 199,238 distinct prefix edges to find 55
beneficiaries. Charging just one lookup for every scan whose false prefix
reaches four changes its net from +186 to **-15,016** checks. Sorted sharing
similarly gives -14,029. These remain optimistic: eligibility itself is not
known without scanning or a maintained index, and persistent indexing needs
clause membership, watch-move/strengthening updates, and backtrack validity.
Reusing allocations, hashing faster, or changing trie layout cannot rescue
such little reusable work. Do not tune the minimum prefix or stride against
this trace and call the result fresh evidence.

Learned clauses account for 73.33% of sampled payload accesses plus tail
inspections (70.56% when visits are included). The relevant retained
[flamegraph](assets/2026-09-10-structural-elimination-j3037.svg) is the prior
definitions-on profile, where propagation is 72.87% inclusive, watch scans
49.41% self and the driver 21.59% self. Its different trajectory is explicit:
it identifies the broad cost center, not the exact cycle weights of this
definitions-off trace. No extra flamegraph of instrumented observation code
would price a prefix-sharing implementation that was never built.

## Underlying algorithm and combinations

This falsifies a premise of the previous proposal: overlapping clause
contents do not imply overlapping *executed scans*. Most scans stop before
reading a large common part. The next representation needs to remove entire
clause visits or propagation events, rather than make a small repeated tail
cheaper. The negative kept-span, delayed-move and blocker-cache mechanisms
would still pay their own maintenance; adding this nearly empty prefix
signal supplies no demonstrated complementary benefit.

The more specific lazy-elimination product remains a different hypothesis.
For pivot-erased parent clauses A_i and B_j, ordinary resolution forms all
A_i OR B_j. Their conjunction equals `(AND_i A_i) OR (AND_j B_j)`. A compact
product could process cofactor events instead of each expanded pair, yielding
the real pair's resolvent as its reason. This can share **fan-out events**
even when the literal orders of executed scans have no common prefix.

There is a critical additional obligation: **false-side activation alone
does not reproduce unit propagation**. For parents `(x OR u)` and
`(NOT x OR u)`, neither pivot-erased cofactor is false while u is unassigned,
but the deduplicated resolvent is the unit u. Kissat `resolve.c` and Nixie's
`elim_resolve_clauses` explicitly deduplicate shared literals. For unsatisfied
cofactors with unassigned-literal sets U and V, the exact test is the size of
`U union V`: zero means conflict and a singleton means unit. Thus a complete
product propagator must handle both false/unit side activation **and matching
unit literals across the two sides**. A satisfied cofactor already satisfies
its pairs. Tracking only all-false cofactors with one watch is insufficient;
the extra unit-state joins and witness maintenance belong in its cost model.

That is a candidate algorithm, not an implemented or validated propagator.
It needs exact duplicate/tautology handling, eager unit/fixpoint behavior,
backtrackable false-side witnesses, live reason materialization with stable
IDs, proof ordering, deletion/strengthening/scope handling and model extension.
Retaining hidden cofactor state is not free elimination. Before implementing
it, quantify actual generated product sizes, activations and repeated fan-out;
the current trace does not retain parent-product provenance. Its potential
interaction with structural recognition is specific: keep the generated
product compact instead of expanding extra resolvents. No benefit follows
merely from combining two independent optimizations.

The retained complete-process counters also separate two substantial targets:
Nixie has 1.282x as many propagations per conflict and 1.702x as many user
cycles per propagation as requested-mode Kissat on this cell. Their product
is the 2.182x cycles/conflict gap. The latter ratio includes all process work,
so it is not a pure BCP timer. Index/header layout can address part of the
second factor; a successful event-sharing algorithm must address the first
without increasing the total cost. This study establishes neither improvement.

## Verification, artifacts and disposition

Before observation: 1,042 SAT tests passed, one existing test ignored; two
doctests passed, one ignored; six Python analysis tests, strict all-feature
SAT Clippy and formatting passed. The broader test command initially reached
a missing external-corpus symlink in the isolated checkout. Linking the
existing corpus and completing that target plus doctests resolved it; both
the failed setup log and successful completion logs are retained.

The five new Rust tests cover scan ordering/values, capacity, writer errors,
live classification and mid-list assignments/conflict tails. Existing paired
generated SAT/UNSAT tests now activate the trace and compare complete
clause/trail/watch/BIG/counter state, original models and independent LRAT
proofs. The ordinary release build contains no observer code. The passive
prototype did not receive full-workspace qualification and is archived,
not merged into the production solver. Only this finding and the offline
analyzer/tests are landed.

Canonical observation: **`41fc24ef457c85bd`**, under
`precompile/73dcc31/benchmark/runs/residual-family-census/`. The sibling
`residual-family-census/` directory retains the once-only runner, manifest,
start/completion, complete stdout/stderr, raw trace, analysis, independent
audit, preflight logs, source bundle/patch and build identity. Binary:
`precompile/73dcc31/stats_solve-residual`, SHA-256
`60dd18a089ea6d70d59358a0fc54a1e17ecbc7850a1bda8a9a8db84c08afa6c9`.
The source bundle requires registration `4674abe`, already on main.

Portable release, Rust 1.96.0 / LLVM 22.1.2, lockfile SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`;
no native flags or PGO. Reused requested-mode Kissat record:
`45a3c8f2e3057841`, Kissat 4.0.4. No benchmark cell was repeated and no
new wall-performance result is claimed.
