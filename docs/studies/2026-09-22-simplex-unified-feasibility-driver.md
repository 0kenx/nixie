# The simplex unified feasibility driver — the pivot-cap/resource-limit family retired

**Date:** 2026-09-22.  **Entry:** the successor handoff
(`docs/handovers/2026-09-21-arithmetic-arc-simplex-family-handoff.md`),
open item 1: *classify and fix the simplex pivot-cap / resource-limit
family (6 fresh-seed members + i129)*.  **Tree:** `80f1ac58` + this
landing (rebased over the integer-tableau Phase 1/2 landings; the six
fix anchors applied cleanly on both trees).

## The classification (measure before believing)

All 7 members attributed on `ef572fc1` with the rebuilt item-67 probe
(auto `fn:line` tags at every statement-position Unknown return and
`resource_limit` write in the arith solver, the simplex, and
`solver/mod.rs` — the inserter recipe is recorded below):

| member | attribution | class |
|---|---|---|
| `gap_s20261000_i129` (fixed) | `smx-rl:check` → the wide-repair BUDGET arm | repair orbit |
| `gap_s20262601_i445` | `smx-rl:check` → budget arm | repair orbit |
| `gap_s20262601_i144` | `smx-rl:check` → budget arm | repair orbit |
| `gap_s20262601_i202` | budget arm + the arith relay | repair orbit |
| `gap_s20262600_i492` | `smx-rl:make_feasible` (the 100k PIVOT CAP) | pivot-cap stall |
| `gap_s20262602_i361` | `smx-rl:make_feasible` (pivot cap) | pivot-cap stall |
| `gap_s20262601_i551` | the big-const gate's `Undecided` (no simplex tag) | **J5-(b1), NOT this family** |

Not a budget problem, not a NOCOL problem: two stalls of the SAME
composite operator.

## The root cause, three layers deep

**Layer 1 — the split driver.**  Wide rows (exact `BigRational` tableau
rows that do not fit `Rational64`) were repaired by a SEPARATE loop in
`check` (one wide repair, then a full narrow re-feasibilization per
round), while the narrow `make_feasible` ran its own DdM loop.  Two
operators with no common progress measure can orbit: measured on i445,
the narrow driver's entering choice immediately re-entered the column a
wide repair had just parked (`MF:65:Upper:13` right after
`REPAIR:13:...`), a period-1 composite cycle.

**Layer 2 — `crash_basis` re-preferences positioned nonbasics.**  A wide
pivot clears `assignment_current`; the next re-derivation runs
`crash_basis`, which re-snapped EVERY nonbasic to its preferred (lower)
bound — including ones the search had parked at their UPPER bound.
Measured on i129: the wide repair parked `x204` at its upper bound `0`
— **exactly the feasible corner** (the 2×2 subsystem over `x9`/`x204`
is satisfiable only with `x9` at its upper and `x204 ∈ [−49/20, 0]`); the
crash re-snapped `x204: old=0 → lower=−2664529699535823903/4`, erasing
the repair; the state returned bit-identically — a period-2 limit cycle
until `MAX_WIDE_REPAIRS` (32) declined the check.

**Layer 3 — `update_assignment` has the SAME re-snap loop, one call
deeper.**  Fixing layer 2 alone recovered only 2 of 6 members: a
write-site trace (`W@snap` tags on every `assignment[x]`/`wide_points`
writer for the cycling pair) showed the value still moving with NO
tagged caller — `update_assignment` (called BY `crash_basis` at its end)
opens with its own lower-preferred unconditional re-snap of all
nonbasics.  The layer-2 fix preserved the position and the very next
call relocated it.

Z3's `lp_primal_core_solver` never re-preferences a positioned column:
nonbasic entries are written by their own writers (the pivot's leaving
snap, the guarded bound writers) and stay; the staleness flag's contract
covers BASIC entries (wide pivots defer their rows' re-derivation), not
the free coordinates.

## The fix (six pieces, all in `simplex/mod.rs`)

1. **`wide_row_violated_bound`** — the violated bound (kind + reasons)
   of a wide basic, refactored out of `wide_row_violated` so the driver
   and the classification share ONE exact comparison.
2. **`find_violating` scans the wide store too** — the wide basics join
   the SAME smallest-index leaving rule: one feasibility driver over
   both stores, the shape of Z3's single exact tableau
   (`one_iteration_tableau_rows` leaves by `find_smallest_inf_column`,
   store-agnostic).  Undecidable evaluations are skipped (the
   classification owns their honest decline).
3. **`make_feasible` handles wide leaving basics** — the exact-row
   entering rule (`find_wide_pivot_col`, smallest eligible index);
   `pivot` already solves wide leaving basics exactly.  The no-column
   arm: the interval refutation (`wide_row_refuted_by_bounds` —
   bounds-only reasoning, sound whatever the assignment says) either
   returns a Farkas conflict or the honest `resource_limit` decline.
4. **`check`'s classification keeps refutation/undecidable only** — the
   repair role moved into the driver; the interleaved repair loop is
   gone.  Classification order is the VARIABLE order (the verdict must
   not depend on hash layout).
5. **`crash_basis` preserves resting nonbasics**
   (`nonbasic_rests_at_bound`): a nonbasic already parked at one of its
   current bounds (narrow entry == bound, or wide point == wide bound)
   keeps its value; only genuinely unpositioned variables (fresh,
   popped, transient) snap.
6. **`update_assignment`'s entry loop — the same preserve rule** (the
   layer-3 site).

## Measured

* **Recoveries (verdicts z3-agreeing, models z3-validated by binding +
  negation, the ledger empty):** `i129` (0.36s), `i144` (0.20s), `i492`
  (0.04s — the pivot-cap class now instant), `i361` (0.07s).  All four
  models validate `unsat` on the negated conjunction.
* **The family is gone:** zero `smx-rl` attributions remain anywhere.
* **Survey delta (fresh seeds 20262600–02 × 600):** 6 members → 3
  (`i133`, `i551`, `i566` — all the CONFLICT-LIMIT class or J5, see the
  residual map); fixed seeds: 1 member (i129 → recovered; a reshuffled
  `i285` appeared, conflict-limit class).  The timeout tails moved
  (8 fresh / 12 fixed) — `i202`/`i445` migrated from unknown-members to
  the timeout class (their simplex cycles are gone; the search-level
  thrash remains).
* **Aggregate theory-path cost (1800 fixed-seed instances, nixie-only
  wall):** total 262s → 206s (−21%), >1s instances 39 → 27, timeouts
  18 → 11, median 7ms → 7ms; p90 28ms → 46ms (the exact wide-row scan
  per driver iteration — the wide-heavy tail pays; the aggregate
  improves because recoveries remove long `unknown` grinds).  One named
  member slowed by trajectory reshuffle: `i116` 2s → 23s (same `sat`).
* **Battery:** workspace suite 12 124 run, 12 109 passed, 15 failed =
  the documented pre-existing corpus class (verified identical on the
  clean `ef572fc1` tree: `si2_b03m` + `known_unsound` ×7 + `qfidl_dl` ×5
  + `iso_brn1083` ×2); clippy/fmt/rustdoc clean; **parity 176/177
  Correct, 0 wrong (z3 4.16.0)**; perf gate PASS (counters 1.000/1.000,
  wall 0.99 — the SAT-side corpus; the theory path is covered by the
  corpus timing above); 3×400 mixed + 3×300 wide fresh differentials
  (20262700–02 / 20262710–12) — zero disagreements, zero refuted models;
  timeout counts match the baseline on the same seeds.
* **Named-member audit (i142, i116, i504, i393, i566) on the landed
  tree:** all z3-agreeing (`sat`/`sat`/`sat`/`unsat`/`sat`); i116 23s
  (was 2s — reshuffle, same verdict).

## The regression pin (and one pin revision)

`rederivation_preserves_nonbasic_parked_at_upper_bound` — a nonbasic
parked at its upper bound by a tighten-then-loosen bound sequence keeps
its value through `update_assignment` AND `crash_basis`.  Revert-checked:
fails on the clean tree (`x: 0 ≠ 10`), passes with the fix.
`rederivation_preserves_wide_point_at_wide_bound` pins the `cmp_big`
arm (contract pin; not revert-discriminating).

`bnb_snapshot_survives_scope_pop_at_any_width` was revised: it froze
the OLD trajectory's model value (`xi = -49806208999015789358`); the
unified driver's leaf now rests at `xi = -3` — BOTH models z3-validated
(binding + negation).  The pin now asserts the trajectory-independent
property (`sat` + a genuine integral non-default publication).

## The residual map (the next campaign)

* **`i202`/`i445` (timeout class):** the simplex no longer cycles, but
  the SEARCH thrashes — decoded on i445: a 3-phase rotation
  (`MF:13:Lower:8` → `MF:0:Lower:13` → `MF:8:Upper:0`) at the CHECK
  level across B&B dive nodes, ~18k `make_feasible` calls of one pivot
  each, 25+ branch requests fired, node budget (20k) burned repeatedly.
  The dive's per-node bound pushes recreate the same violated slack each
  round.  This is item 89's dive-leaf/branch-channel territory.
* **`i133`/`i285`/`i566` (conflict-limit class):** `check_core_solving`'s
  "a real theory conflict was dropped at the conflict limit" arm — the
  search-capacity tail.
* **`i551`:** the J5-`Undecided` class (the certificate declines; not
  refuted, so not block-and-retried) — the handoff's open item 2.

## The instrument recipes (session-local, rebuilt per campaign)

* **The probe inserter** (`.session/probe_insert.py` in the campaign
  worktree; the recipe): auto-tags at every statement-position Unknown
  return (`return SolverResult::Unknown` / `return Ok(TheoryResult::Unknown)`)
  in `nixie-solver/src/solver/mod.rs`, `nixie-theories/src/arithmetic/solver.rs`,
  and every `self.resource_limit = true` in the simplex — each an
  env-gated (`NIXIE_GAP_PROBE=1`) `eprintln!("[[TAG:{fn}:L{line}]]")` with
  ORIGINAL line numbers.  The survey's `.err` capture then attributes a
  member in one probe run.  Hand tags for the three wide-decline arms
  (`smx-wide:repair-budget` / `nocol` / `undecidable`).
* **The write-site trace:** env-gated prints on every
  `assignment[x] = …` / `wide_points` mutation for the cycling pair,
  plus per-pivot `(leaving, bound.kind, entering)` and the pair's exact
  values (`eval_big_raw` for wide basics, entry for the rest), a
  `[[MF-CALL]]` marker per `make_feasible` entry, and a `[[REST]]` dump
  inside `nonbasic_rests_at_bound`.  The layer-3 discovery needed the
  WRITE-SITE tags specifically — value movement with no tagged caller
  is the signature of an uninstrumented store writer one call deeper.
* **Model validation:** `get-model` → the `(model …)` block balanced out
  verbatim → the original `declare`s minus the model-defined names →
  `assert (not (and <assert-bodies>))` → z3 `unsat`.  (The naive regex
  forms fail twice: the `(model` wrapper must be included, and each
  assert body is already a balanced s-expression — do not re-parenthesize.)
* **Corpus timing:** generate the fixed seeds' 1800 instances once,
  `subprocess.run` with the survey's 10s timeout, and compare total /
  median / p90 / >1s / timeout counts — the theory-path cost gate the
  perf gate does not cover (its corpus is SAT-side).

The one-sentence version: **the family was never a budget problem — it
was three stacked value-continuity breaks (a split driver, and two
lower-preferred re-snap loops, the second hiding one call inside
`crash_basis`), and one unified driver plus a position-preservation rule
retires the class outright, with every recovery z3-validated and the
wrong-verdict ledger still empty.**
