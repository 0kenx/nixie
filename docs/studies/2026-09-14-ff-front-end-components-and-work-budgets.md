# FF front end: connected components, min-degree branching, work-proportional budgets

**Date:** 2026-09-14
**Scope:** `docs/FF_THEORY_DESIGN.md` §6.4 (connected components), §5 Step 3
(brancher selection), §4.5 (budget semantics). Completes the Phase-5 item
list and its exit criterion ("measured on `bench/ff/`; step-count reductions
reported").

## What changed

Three deterministic changes to the 𝔽_p procedure. None alters the answer
space: they change what the procedure *does* (per `docs/BENCHMARKING.md`,
such changes report solved counts and step counts; no matched null is
required — there is no stochastic baseline to null out, the procedures are
deterministic and the oracles pin the verdicts).

1. **Connected components (§6.4).** After the linear core, the generator
   set is partitioned by the variable-sharing graph (union-find; components
   ordered by smallest generator index). Each component gets its own
   Gröbner + FindZero with its own budget; UNSAT of any refutes the whole
   (core = that component's origins), SAT needs a point per component.
   `FindZero` now takes the component's variable list — zero-dimensionality
   and completion are per-component questions.

2. **Min-degree brancher selection.** Among super-linear univariate
   elements of the GB, branch on the one of *smallest degree* (the root
   count is the branching factor). First-found order once picked a
   degree-8 element sitting beside a degree-2 one.

3. **Work-proportional budget units.** `GrobnerBudget` charges one unit
   per **monomial operation** (a reduction between s-term polynomials
   costs ~s), not one per step. Step-counting made a 2^24 budget mean
   *hours* on big-polynomial cascades: the budget never noticed the
   polynomials growing, so a goal that should have refused in principle
   ground in practice — a refusal that never arrives is no refusal.

## Measurements (bench/ff/, debug build, 3 runs, median)

| goal | before | after | verdict |
|---|---|---|---|
| bn254 sparse planted 8×12 | sat, ~0.1 s | sat, ≤1.3 s | held |
| bn254 sparse planted 16×24 | **no verdict in >200 s (grind)** | honest `unknown`, ~11 s | capacity fixed |
| bn254 sparse planted 32×48 | **no verdict in >200 s (grind)** | honest `unknown`, ~14 s | capacity fixed |
| bn254 sparse planted 64×96 | sat, ~6 s | sat, ~7.5 s | held |
| bn254 sparse planted 128×192 | **no verdict in >200 s (grind)** | honest `unknown`, ~18 s | capacity fixed |
| bn254 planted (dense) 4×6…8×14 | sat, ≤0.1 s | sat, ≤0.1 s | held |
| bn254 planted (dense) 12×20 | `unknown`, ~10 s+ | `unknown`, ≤0.15 s | faster refusal |
| goldilocks sparse 16×24 / 64×96 | sat | sat, ≤0.3 s / ≤1.6 s | held |
| goldilocks (dense) 4×6 / 8×14 | sat | sat, ≤0.02 s | held |
| planted-witness fuzz suite (`ff_planted_fuzz`) | 103 s | **2.4–3 s** | all pass |

(Times are debug-build medians of 3; the machine is shared, so treat
cross-run deltas under ~2× as noise — the load-stable facts are the
verdict column and the >200 s → seconds class change.)

The dominant effect is (3): honest refusals that used to take minutes of
grinding (or never arrive) now land in seconds, and the whole fuzz oracle
runs 43× faster because its refusal-exercising rounds stopped subsidizing
undercounted big-polynomial work. (1) and (2) matter on decomposable or
low-degree-structured goals; the dense corpus (every constraint mentions
every variable — unrealistically dense for R1CS) stays one component by
construction, which is why its 12×20 goal still refuses: that case needs
split-GB (Phase 7), and the corpus keeps it as the capacity marker.

## Why the remaining `unknown`s are honest

Every refusal names its site (`OutOutOfBudget { where_ }`): Gröbner basis
(component) on the sparse 16×24/32×48/128×192 and dense 12×20 goals. The
planted-witness invariant held throughout — no planted-satisfiable goal was
ever answered `unsat` (§10.3 oracle), and every `sat` model validated
exactly.

## Verification

- exhaustive tiny-prime oracle: 10/10
- planted-witness fuzz (Goldilocks/BN254/BLS12-381): 5/5
- solver regressions incl. certified-mode certificates: 24/24
- instrumentation: `NIXIE_FF_STATS=1` prints generator/component counts,
  per-component basis sizes, and residual budget (2^k) — deterministic,
  never a policy input.
