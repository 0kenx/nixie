# The assertion fold pass wired (flag-gated): the ctx-simplify fold pass reaches `check-sat` (2026-09-21)

**Date:** 2026-09-21. **Item:** the Bareiss handoff's remaining-map
item 1 — *"the ctx-simplify fold pass (the prp/nec 47×-wall class) —
untouched, own-session"* — executing on the foundation the
`solve_eqs` landing laid (`2026-09-20-solve-eqs-guard-elimination.md`:
the fold power exists in `TermManager::simplify`/`ctx_simplify`; the
wiring into the solving path was the open half).

## What landed

`Solver::assert`/`assert_named` gain a flag-gated fold stage
(`NIXIE_ASSERT_FOLD=1`, OnceLock, default OFF — the rung-3 precedent:
land gated, campaign decides the default): after `expand_lets` and
before the encode-depth guard, every let-expanded assertion runs the
two passes that carry the guard-equality solve rules (bottom-up
`simplify`, then `ctx_simplify`).  Placement contract (in the code):

* **after `expand_lets`** — the passes do not descend into `Let`
  nodes; the let-expanded DAG is where the select-chains become
  solvable;
* **before the depth guard** — the nec-smt spines (2537-deep) fold to
  a constant here, so the guard measures the folded term and never
  refuses them;
* **inside the pipeline, after `certificate_term` is captured** —
  certified mode keeps the EXACT user assertion as its trust base; the
  fold is one more equivalence stage among the pipeline's existing
  rewrites (`flatten_eq_ite_tables`, `eliminate_nonbool_ite`, …), so
  named-assertion core mapping (index-aligned) and scope consistency
  (the fold is a pure term function) are untouched.

Both passes are explicit-stack and fuel-bounded — the deep spines are
stack-safe by construction, and on fuel exhaustion the fold degrades
to the identity, never to a wrong answer.

## The armed evidence (measured at 2026-09-21, load 9–15 disclosed)

`check-sat` verdicts, every one cross-checked against z3 4.16.0:

| class | unarmed (main) | armed | wrong verdicts |
|---|---|---|---|
| nec-smt small (37) | 12 solved | **17 solved** | 0 (17/17 agree) |
| nec-smt med (30 sampled) | 0 solved | 1 solved | 0 |
| nec-smt large (6) | 0 solved | 1 solved (checkpass `unsat` in 136 ms) | 0 |

The five small-class flips are the fold members the ninth-session
study predicted: the fuel-exhausting residual folds at assert time and
the solver answers `unsat` in milliseconds (e.g. `prp-3-21`:
unarmed = 30 s timeout, armed = `unsat` in 12 ms).  The honest cost:
on members whose residual does NOT fold, the armed pipeline replaces
an instant (spurious) `unknown` with a real search that can time out —
the deep-split study's documented unknown→timeout conversion (wall
cost at caps ≥ the search's runtime; both are non-solves on the
table).

## Verification

* Workspace nextest `--all-features`: 12 093 run, all green (the three
  `scope_rebase` timeouts at load ~15 are the documented flake class —
  re-run at `-j1`: 9/9 pass).
* **Armed Z3 parity** (177 benchmarks, z3 4.16.0): **176 agree, 0
  wrong-verdict pairs** (the one difference is the standing nixie-
  `unsat`/z3-`unknown` inconclusive).
* **Perf gate** (BASELINE `86846e39`): **PASS, 1.000/1.000, wall
  1.01** — the default path is bit-identical (the flag is off unless
  set).
* clippy/fmt/rustdoc clean on every touched file.

## The default stays OFF (the flip campaign is the follow-up)

The flip needs the standing table at calm load (≤8 sustained) —
unavailable this session (load 9–15 throughout, another campaign
running), and per the repo's own discipline a default-path flip wants
a paired unarmed/armed table snapshot (counters primary, par-2 and
geomean secondaries, the LIA leg first).  **The campaign's named
bar**: QF_LIA solved-count up (the nec-smt cells), zero disagreements,
both-solved median not regressed, and the unknown→timeout wall cost on
the unconverted members accounted against the cap.  z3's own default
is to run its rewriter on every assertion — the flip aligns with the
reference solver's shape, but the table decides, not the analogy.

## Traps this session

- The shared `target/` hit ENOSPC again mid-session (the 163 GB
  debug-info accumulation); a `git add && commit` failed with a
  HALF-WRITTEN INDEX (status clean-but-nothing-staged) — after freeing
  space, re-`add` before retrying the commit, don't trust the first
  post-ENOSPC status.
- Worktree liveness under load: a `cd` into a live worktree failed
  transiently ("No such file or directory") while `git worktree list`
  showed it — re-check before concluding a purge.
- Commit WIP early: uncommitted work in a worktree is one purge away
  from gone; the shared object store is the durable place.
