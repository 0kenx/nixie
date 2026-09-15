# Branch-variable selection for the chain frontier: the lever is inapplicable — measured

**Date:** 2026-09-16
**Scope:** the lever recorded as next by
`docs/studies/2026-09-16-ff-untraced-fast-path.md`: chain ≥128×192 via
round-robin branch-variable selection, per `docs/BENCHMARKING.md`.
**Verdict:** **negative result — the experiment cannot run as designed.**
The pre-registered lever targets FindZero's round-robin brancher; on the
frontier goals FindZero never executes, because the nonlinear Gröbner
cascade over the full chain cannot complete at any measured budget. The
real blocker is the cascade, and the real next lever is the design doc's
actual §6.5 — the variable-SUBSET split (window decomposition) — or F4.
No heuristic was changed; nothing ships beyond three diagnostic
`[ff-stats]` lines.

## Why the lever's precondition fails

The chain corpus's fate per goal (instrumented runs, this study):

| goal | path taken | round-robin? |
|---|---|---|
| chain 16×24/32×48/64×96 | monolithic untraced cascade **completes** (64×96: basis of 63 from 96 gens) → FindZero solves via the univariate brancher | never reached |
| chain 128×192/256×384 | monolithic budget-out → split fallback → **split's nl-GB budget-out** → honest `unknown` | never reached |

No corpus goal reaches the round-robin brancher. Selecting its branch
variable better cannot move any measured outcome.

## The measurements (release, quiet load ~8)

`bn254_chain_planted_128x192` (192 generators = 64 linear + 128
nonlinear, one variable-sharing component):

| total budget | nl-GB(128 gens) | wall |
|---|---|---|
| 2^24 (default) | `Err(Budget)` | 3 s |
| 2^26 (4×) | `Err(Budget)` | 9 s |
| 2^28 (16×) | `Err(Budget)` | 29 s |

The exhaustion is genuine (the bloat breaker does not fire — the basis
stays under 8×inputs+64 elements and elements under 512 terms; the
monomial-op budget simply runs out). The 128-constraint nonlinear
cascade is intractable for plain Buchberger at any budget that keeps
the honest-refusal time in seconds; this is the same MQ hardness the
original handoff named, now with the frontier moved from 8×6 to 128×192
by the arc's landings (grevlex fix → split-GB → budget honesty →
untraced fast path).

For contrast, 64×96 completes monolithically with budget to spare
(2^22 of 2^24 left), and the sparse corpus completes at every size —
the boundary is specific to the chain's coupling density, not to size
alone.

## What the real next levers are

1. **The variable-subset split (the design's actual §6.5)**: the landed
   split is cvc5's 2-way linear/nonlinear split — it does NOT decompose
   the chain (one component; the nl side sees all 128 quadratics at
   once). The handoff's original phrasing — "maintain bases over
   variable SUBSETS in the original space, exchange only
   support-fitting consequences" — describes a window decomposition:
   the chain's sliding windows each form a small basis (a handful of
   variables), and only consequences whose support fits a neighbouring
   window cross. That attacks the cascade itself, which is where 128×192
   dies. This is a real build (overlapping clusters, exchange
   fixpoint, soundness argument via ideal containment per cluster).
2. **F4** — batched linear-algebra reduction; orthogonal to (1),
   replaces the S-pair loop wholesale.
3. The round-robin brancher MAY matter after (1) or (2) land — if the
   cascade completes and FindZero's positive-dimensional round-robin
   becomes the binding constraint, the pre-registered matched-null
   experiment (branch-variable ordering vs a permuted ordering, same
   distribution of choices, ≥10 seeds per cell, tick counters only)
   becomes runnable. Re-issue it then; do not run it against a
   brancher the corpus never executes.

## What shipped

Three `[ff-stats]` diagnostic lines (split partition, split l/nl-GB
sizes-or-budget-out, bloat-breaker firing) and one `[fz]` round-robin
marker — all behind the existing `NIXIE_FF_STATS` env, all
deterministic step/size counts, never policy inputs. They are exactly
the instrumentation this study needed and the next study will need. The
temporary `NIXIE_FF_BUDGET` override used for the 2^26/2^28
measurements was **removed** — an env-var budget is a policy input and
does not ship.

Corpus verdicts unchanged (chain 128×192/256×384 honest `unknown` in
~3 s; 64×96 `sat` 1.4 s; sparse 128×192 `sat` 0.2 s).
