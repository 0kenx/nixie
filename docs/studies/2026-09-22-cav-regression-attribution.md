# The CAV sat-cells lost at the unified feasibility driver — a bisected attribution

**Date:** 2026-09-22 (small hours).  **Recorder:** the Route-B session
that landed `35ea8786` (the division-first joint-reduction walk —
bit-identity, counters identical base-vs-candidate on every probe named
here, so this regression is present identically with and without it).

**Why this record exists:** the driver's campaign
(`2a7dc324`, study `2026-09-22-simplex-unified-feasibility-driver.md`)
measured the fuzz corpus (aggregate −21 %, 4 z3-validated recoveries,
survey family retired) but NOT the SMT-LIB CAV family; the standing LIA
table that would have caught it was load-blocked all day.  This is the
missing post-landing audit, executed with cached binaries so the next
agent does not re-diagnose from scratch.

## The bisect (back-to-back, same load on both sides of every row)

| cell | `795abb8f` (pre-window) | `7687dc39` (last good) | `2a7dc324` (driver) | `35ea8786` (landing tree) |
|---|---|---|---|---|
| `CAV/30-vars/problem__011` | sat ≤27 s | sat 17.2 s | **no verdict @120 s** | unknown @100 s cap |
| `CAV/45-vars/problem__025` | sat ≤21 s | sat ≤20 s | **TO @60 s** | TO @60 s |
| `CAV/45-vars/problem__034` | sat ≤7 s | sat ≤7 s | **TO @60 s** | TO @60 s |
| `CAV/30-vars/problem__026` (control) | sat | sat | sat | sat |
| `CAV/45-vars/problem__022` | churns | churns | churns | churns (pre-existing) |

All three losses appear AT `2a7dc324` and stay.  `problem__025`'s
first-sweep TO on `7687dc39` was load noise (load 73; it re-ran `sat`
calm) — the 60 s back-to-back rows are the trustworthy ones.

Channel-independence: `2a7dc324` on `problem__011` with
`NIXIE_LIA_BRANCH_LEMMA=0` still has no verdict at 120 s — the branch
channel is not the differentiator; the driver's own trajectory is.

## The putative mode (not re-instrumented this session)

The driver study's own residual map names the class for `i202`/`i445`:
a 3-phase `make_feasible` rotation at the CHECK level across B&B dive
nodes (~18 k single-pivot calls, branch requests fired, the 20 k node
budget burned repeatedly — "item 89's dive-leaf/branch-channel
territory").  The CAV cells fit: pre-driver, `problem__011`'s cost was
ONE theory check's internal B&B (~20 k nodes, ~80 k pivots — the
LIA-floor handoff's words) that reached an integral leaf; the driver's
entering/leaving rule changes (wide rows join the smallest-index
leaving rule; `crash_basis`/`update_assignment` preserve resting
nonbasics) reshaped that internal trajectory so the dive no longer
lands.  Confirming this needs the campaign's own instruments (the
write-site trace + `[[MF-CALL]]` recipe, recorded in their study) —
rebuild them per that recipe rather than re-deriving.

## What NOT to do

* **Do not revert `2a7dc324` blind:** it retired the pivot-cap /
  resource-limit survey family with 4 z3-validated recoveries; the
  trade is real.  The fix is dive-level (Route A of the LIA-floor
  handoff: bound the internal B&B per CHECK and hand the fractional
  variable to the CDCL-visible channel — the architecture the floor
  handoff already sized).
* If a piece-level bisect is attempted: the commit is six pieces in
  `simplex/mod.rs` (the wide-store joining `find_violating`, the
  driver rewrite of `make_feasible`, the two preserve-resting-nonbasics
  loops, the `check` repair-loop deletion).  Build the intermediates in
  throwaway worktrees, cache binaries to `precompile/<sha>/`, delete
  the worktrees.

## Instruments used (all cached)

`precompile/795abb8f`, `precompile/7687dc39`, `precompile/2a7dc324`,
`precompile/35ea8786`.  Verdict + wall at fixed caps, back-to-back A/B
under matched load; load-noise cells re-run calm before believing them
(the 025 first-sweep flip is the worked example).

## The next agent's cheap closure

The calm-load standing table (LIA leg) — blocked on machine load this
whole arc — is the instrument that prices this class honestly
(par-2/geomean readout per `docs/BENCHMARKING.md`); run it before any
fix lands, so the dive campaign's counterfactual has a baseline.

## Addendum (same night): the piece-level bisect — executed

Two subset builds over the driver commit's six pieces (rebuild recipe:
worktree at the base, apply the named hunks verbatim from `2a7dc324`):

* **S1 = `7687dc39` + the preserve-resting-nonbasics pair ONLY**
  (`nonbasic_rests_at_bound` + the two `continue`s in `crash_basis` and
  `update_assignment`): `problem__011` sat 13.9 s, `problem__025` sat
  22.8 s, `problem__034` sat 5.1 s — **pre-driver behavior; the preserve
  rules are INNOCENT solo**.
* **S2 = `2a7dc324` with the preserve rule neutralized** (fn body :=
  `false`): all three cells TO @60 s — **the regression is the
  unified wide-driver rewrite ALONE** (the wide basics joining
  `find_violating`'s smallest-index leaving rule + `make_feasible`'s
  exact wide pivots + the `check` repair-loop deletion).

These cells genuinely go wide: no input literal exceeds ~14 digits, but
the pivot accumulation builds the 120-bit denominators the
integer-tableau studies measured — the canonical `Rational64`
materialization declines and the exact store takes over.  The old
architecture (narrow `make_feasible` + `check`'s interleaved one-wide-
repair-then-narrow-re-feasibilization loop, 32-budget) carried the CAV
trajectory; the unified driver's leaving/entering order for wide basics
does not.

**Fix options this leaves open** (for the dive campaign or the smx
successor):  keep the preserve rules and the survey recoveries, and
either restore the interleaved repair shape for wide-heavy trajectories,
or land the Route-A dive bound (the per-CHECK node budget + CDCL-visible
channel) so the internal trajectory difference stops deciding these
cells.  The `rederivation_preserves_*` pins are NOT in conflict with
either (S1 shows the preserve pair passes alone).
