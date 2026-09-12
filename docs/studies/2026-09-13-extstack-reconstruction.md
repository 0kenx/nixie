# The extension-stack port: eliminating the false-witness class (2026-09-13)

> Trigger: the round-10 wide-cap portfolio screen's model-check gate
> fired 138 times — `Sat` verdicts whose printed models falsified
> original clauses of the input file.  The verdicts were right (cadical
> agrees on every affected file); the exported *witnesses* were wrong.
> For a solver whose output is consumed as proof-carrying evidence, a
> bogus model is the same bug class as a false `sat`: downstream users
> replay the assignment and it fails.

## The reproducer (exact command form)

```
DIAG=1 PRINT_MODEL=1 SEED=2 <binary> \
  precompile/corpus-sc24f/1009c791cee542cdf19651fe25e6881a-summle_X4053_steps8_I1-2-2-4-4-8-25-100.cnf
```

Pre-fix (any binary 8082e335…3e25802e): `result=Sat` at 44 702 conflicts,
model line omits 656 of 112 049 variables, and 63 original clauses are
**all-false** under the printed assignment (e.g. `(9309 ∨ ¬9487)`,
`(10178 ∨ ¬11017)`).  Post-fix (`32c88866`): total model, all 234 322
clauses satisfied, identical conflicts counter (the search is untouched).

The bug was *not* new: the 8082e335 baseline cells already contained
these cells as downgraded `unknown`s — the class was hiding inside the
"0/5-at-60 s" classification itself (summle_X4053 seed 2 solves in
6.5 s and was recorded as `unknown`).

## Root cause — the layers (AGENTS principle 2 ledger)

| # | layer | finding |
|---|---|---|
| 1 | `save_model`'s BVE rule | reconstructs from `bve_def[v]` = the **positive-side** clauses present in the occurrence lists *at retirement*.  Three obligation leaks: (a) clauses of `x` retired earlier by *another* variable's elimination are recorded nowhere (only positive sides are kept, and only once); (b) eliminations whose positive clauses were strengthened away mid-scan record an **empty** side and defaulted `v = false` on the false premise "retired as satisfied by unconditional units" — measured: `BVE_ORDER_PUSH v=10178 defs_recorded=0` while `(10178 ∨ ¬11017)` was retired at 11017's step; (c) side tests read `Undef` as not-satisfied, so a missing value was indistinguishable from a false one. |
| 2 | ELS representative pass | valued substituted variables from `equiv_substitution`, but chains through **unconstrained** representatives never resolved (`1268 ≡ ¬1267`, 1267 never branched, both defaulted independently → `(1267 ∨ 1268)` falsified).  Running the pass before vs after the BVE pass each broke a different subclass (305 vs 4 711 falsified clauses measured). |
| 3 | Undef semantics | cadical's walk is proven under the `vals` convention (unassigned = `false`); our clause test read `Undef` as "not satisfied" while the flip guard read `Undef`-negatives as true — inconsistent, producing toggle-back chains that re-falsified already-repaired entries (the `(251 ∨ ¬233 ∨ ¬250)`/`(250 ∨ ¬251)` pair over an unassigned 250). |
| 4 | retirement paths audited (no defect) | lucky fail-path `shrink` (content-identical restore), vivify/subsume strengthening (subset clauses: satisfying the shrunk clause satisfies the original), satisfied-at-round-time retirements (level-0 units are permanent), learned-clause retirements (entailed).  The one genuine obligation set is exactly "clauses retired at eliminations" + "ELS implications" — both now pushed. |
| 5 | `reset()` lifecycle | elimination/ELS bookkeeping (`ext_stack`, `bve_def`, `bve_order`, `equiv_substitution`) was never cleared; stale obligations from a previous formula would poison a re-solve's reconstruction.  Cleared now. |

## The fix (cadical `External::extend`, Sörensson/IJCAR'12)

* Every clause retired at a variable's elimination is pushed on a flat
  extension stack `[witness, lits…, SENTINEL]` — both sides, witness =
  the pivot literal the clause contains (`elim_retire_pivot_clauses`).
* Every ELS equivalence pushes its two implications as witness clauses
  (the composed representative is transitivity-safe), making
  reconstruction **uniform** across mechanisms — no separate
  representative pass, no cross-pass ordering problem.
* `save_model`: trail values → pure literals → **default every remaining
  `Undef` to `false`** (the convention the walk is proven under) → walk
  the stack backward, flipping the witness variable of each falsified
  entry.  No per-variable side rule, no defaults over partial records.
* `bve_def`/`bve_order` survive as branching-skip markers
  (`var_eliminated`, VMTF) — the search path is bit-identical.
* `debug_verify_model` now also checks extension-stack obligations in
  debug builds: the retired-clause class was invisible to the live-DB
  net, which is why 11 k tests stayed green while corpus models were
  broken.

Measured sizes: Timetable-class runs push ~766 k entries (~9 MB) —
the walk is one linear pass at `Sat` time.

## Verification

* Regression: `nixie-sat/tests/elimination_model_reconstruction.rs` —
  planted-model structured formulas (implication chains + equivalences,
  lucky disabled, pre-search collapse so the mechanisms fire on test
  sizes).  **Fails pre-fix** (`original clause #2 [-37, 45] falsified`)
  and passes post-fix; asserts the mechanisms fired so it cannot
  vacuously pass.
* Reproducer + siblings: summle X4044/X4053/X11112 × seeds 0-4 →
  15/15 total models, 0 falsified clauses.
* Workspace: 11 115/11 115 nextest; clippy/fmt/rustdoc(-D warnings)
  clean; Z3 parity 4.16.0 — 175 files, verdicts identical to the
  tracked record.
* Trajectory identity vs `4f51efd7` default path: 8/8 conflict-counter
  cells bit-identical (si2/j3037/crn/worker/Timetable, seeds 0/3,
  MAXC=8000).

## The lesson for the corpus screens

The 2026-09-12 screens' "model-checked SAT cells" gate is what caught
this — but the failures were silently *downgraded to unknown* rather
than escalated.  A downgrade that hides a real solve (summle s2 at
6.5 s!) also corrupts the conversion accounting of any portfolio
study built on it.  The 300 s wide-cap screen (same day) had 138 such
cells across 9-10 files.  Rule adopted: a model-check failure is a
loud event, never a silent downgrade — the runner now prints
`!!! MODEL CHECK FAILED … investigate` and the study must account for
every one of them before reporting conversions.

Also note for future screens: cadical's `-P` preprocessing default is
**0** — cadical's default trajectory runs *no* pre-search elimination
(verified in `cadical.cpp`'s usage text and `init_preprocessing_limits`).
Our `presearch_collapse: false` default matches that; the handoff's
"pre-search fixpoint" framing for item 2 refers to schedules cadical
only enters under `-P > 0`.
