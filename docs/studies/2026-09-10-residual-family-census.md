# Shared residual scans: opportunity and representation costs

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
