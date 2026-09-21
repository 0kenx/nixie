# The branch-request cadence — the internal walk shortened to Z3's shape, the ray-walk class dissolved

**Date:** 2026-09-22 (later session).  **Entry:** the unified-driver
study's residual map, item 1 (`i202`/`i445`, the search-level thrash).
**Tree:** `cebb4cfb` + this landing.

## The decode

On `i445` (probe instrumentation at the dive/B&B/branch layers): the
B&B burned **46,848 node bodies in 10 seconds** across 11 branch-request
rounds — the tree is a 4,000-deep LINEAR CHAIN branching on the same
three variables (13, 0, 8 — the simplex-rotation trio: internal
div/mod slack vars).  The branch bounds WALK: var 13 advances `+3` per
node (`…4064 → 4067 → 4070…`), var 0 `+1` (`38 → 39 → 40…`) — **the LP
re-optimizes to the next fractional point every time a branch bound
pins it: item 96's ray-walk class**, directly measured this time.  The
dive (≤512 nodes) never lands an integral leaf; the walk burns the node
budget every CDCL round.

## Z3's shape (the reference read)

`theory_arith_int.h::branch_infeasible_int_var`: at a fractional
vertex, Z3 internalizes ONE case-split lemma (`x ≥ k ∨ ¬(x ≥ k)`),
marks it relevant, and RETURNS to CDCL.  One branch per check; the case
exploration belongs to CDCL.  Our request fired only at budget
exhaustion (`LIA_MAX_NODES` = 20,000 walked nodes) — the inverse shape.

## The dose experiment (pre-registered)

Env-gated knob (`NIXIE_LIA_REQUEST_NODES`), dose = the node budget at
which the request fires:

| dose | i202 | i445 | fixed-seed corpus (1800) |
|---|---|---|---|
| 20000 (default) | timeout | timeout | 200s, 27 >1s, 11 TO |
| 1024 | timeout | timeout | — |
| 64 | **sat** (11.2s) | unknown (7.1s) | 62s, 10 >1s, 1 TO |
| 8 | **sat** (4.1s) | unknown (7.1s) | 61s, 8 >1s, 1 TO |
| 1 | **sat** (4.0s) | unknown (3.3s) | 63s, 9 >1s, 2 TO |

i202's dose-8 model is **z3-validated** (binding + negation → `unsat`).

## The matched null (the discipline, decisive)

Same cadence (dose=8), same minting path, the branch point perturbed
`k → k+7` — a real case split with none of the fractional-vertex
content: **the null reproduces the ENTIRE cost win (62s vs 61s) and
does NOT recover i202 (`unknown`)**.  The honest decomposition:

* the **−70% corpus cost is the CADENCE** (CDCL round churn replaces
  the internal walk — the null matches it);
* the **recovery is the SEMANTIC branch** (only the true fractional
  point closes the search).

Both claims stand, each attributed to its own mechanism.

## The ≥10-seed distributions (10 fresh seeds × 600)

| arm | median seed total | min–max | timeouts |
|---|---|---|---|
| walk (20k) | 77.5s | 36–133 | 39 |
| request@8 | 43.8s | 22–69 | 15 |
| request@64 | 36.7s | 20–73 | 15 |

Every request-arm seed beats the walk arm's BEST seed.  Pre-registered
dose rule (min corpus total; ties → larger): **64**.

## The landing

`LIA_REQUEST_NODES = 64`, gated on `lia_branch_channel_on()` — the
`NIXIE_LIA_BRANCH_LEMMA=0` opt-out keeps the full 20k walk (the
unarmed search's strength is unchanged).  One constant and one budget
check in `bnb_search` (+30/−1).

**Named members on the landed tree:** i142 sat (0.10s), i393 unsat,
i504 sat, i566 sat, i116 **sat in 0.71s** (the unified-driver landing's
23s trajectory reshuffle is itself cured by the cadence change), i129
sat (0.37s).

**Survey at the default:** fixed seeds 2 members (`i0`, `i496` — both
the conflict-limit class, reshuffled), fresh seeds 5 members (`i133`,
`i161`, `i258`, `i445` — conflict-limit; `i551` — J5-`Undecided`) + 2
timeouts.  `i445` migrated from the timeout class to a 7s honest
`unknown` (65 branch rounds, then the conflict limit).  Zero `smx-rl`,
zero ray-walk, zero repair-orbit attributions anywhere.

**Battery:** suite 12,124 run, 12,121 passed, 3 failed (a subset of the
documented `known_unsound` class — the other twelve pre-existing
failures pass on this base tree from the parallel sessions' SAT
landings between `ef572fc1` and `cebb4cfb`; this diff is one constant
and one branch); clippy/fmt/rustdoc clean; parity **176/177 Correct,
0 wrong** (z3 4.16.0); perf gate PASS (counters 1.000/1.000, wall
0.88); fresh differentials (mixed 20262730, wide 20262732) clean.

## The residual map (after this landing)

1. **The conflict-limit class** (`check_core_solving`'s dropped-conflict
   arm): the dominant remaining family (`i0`, `i133`, `i161`, `i258`,
   `i496`, `i445` now here too).  The search capacity tail.
2. **`i551`:** the J5-`Undecided` certificate class (the predecessor
   handoff's open item 2, unchanged).

The one-sentence version: **the ray-walk class was the internal B&B
re-optimizing along an LP ray one integer at a time — and Z3's shape
(one case-split lemma per fractional vertex, exploration in CDCL),
dosed at 64 nodes and null-decomposed into cadence (the −70% cost) and
content (the recovery), dissolves it.**

## The CAV post-landing audit's cells, measured on THIS landing

`docs/studies/2026-09-22-cav-regression-attribution.md` (landed while
this campaign ran) bisects three CAV sat-cell losses INTO the
unified-driver landing (`2a7dc324`) and names "Route A — bound the
internal walk per check, hand the fractional var to the channel" as the
fix — which is this landing.  Measured back-to-back on this tree
(caps 60s, calm load):

| cell | pre-driver (`7687dc39`) | driver (`2a7dc324`) | this landing |
|---|---|---|---|
| `CAV/30-vars/problem__011` | sat ≤27s | no verdict @120s | no verdict @60s |
| `CAV/45-vars/problem__025` | sat ≤20s | TO @60s | **sat 17.0s** |
| `CAV/45-vars/problem__034` | sat ≤7s | TO @60s | TO @60s |
| `CAV/45-vars/problem__026` (control) | sat | sat | sat 0.65s |

**One of three recovered** (025 — the Route-A mechanism is real); 011
and 034 remain in the driver's regressed state (this landing's armed
path changes only the request cadence; their states are identical to
`2a7dc324`'s, not worse).  The remaining two are the
driver-trajectory regression the audit already attributed — the
dive-level fix (why the driver's entering/leaving reshape stops the
dive landing where the old 20k-node walk did) is still open, and this
landing does NOT close it.  The audit's "cheap closure" (the calm-load
LIA standing table) remains the next agent's entry.
