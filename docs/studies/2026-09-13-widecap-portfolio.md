# Wide-cap portfolio screen: the 0/5-at-60 s class converts on plain default at 300 s (2026-09-13)

Round-10 handoff item 1.  Question: at a 300 s budget, does a
`default@X → comb@(300−X)` sequential portfolio (comb = `NIXIE_OTFS=1
NIXIE_EAGER_SUB=1`) convert the 13-file 0/5-at-60 s class that the
amplitude arms could not reach?  Conversion bar from the handoff: the
comb arm converting ≥3 files beyond default makes the `SEEDS=` token
take it as a late arm.

## Screen

13 files (the measured 0/5-at-60 s class) × seeds 0-4 × 3 arms,
harness-staged chains (stage 1 = default, `X` s; stage 2 = comb,
`300−X` s; both stages `SEED=<seed>`; binary `4f51efd7`; cadical 3.0.1
references at 600 s).  Records under
`precompile/4f51efd7/benchmark/runs/sc24f/` (config ids
`default-300s`, `def60-comb240`, `def120-comb180`); runner committed at
`docs/studies/assets/inproc-amplitude-2026-09-12/sc24f-widecap-portfolio-runner.py`.

## Result: the premise dissolves — default alone converts the class

| arm | files with ≥1 Sat | Sat cells (of 65) |
|---|---|---|
| default-300s | **12 / 13** | 53 |
| def60→comb240 | 12 / 13 | 51 |
| def120→comb180 | 12 / 13 | 52 |

Every file except `170058440` (the one cadical itself does not solve
in 600 s) produces `Sat` verdicts at 300 s **on the plain default
path** — including circuit_64in64out (5/5; it simply needs >60 s on
default) and all three summle files (5/5 each, ≤33 s single-shot on
re-verification).  The "0/5-at-60 s class" was overwhelmingly a *cap
artifact*, not an algorithmic gap.  The portfolio arms add nothing and
subtract a little: combined-crypto1 loses 1-2 cells (5/5 default vs
3/5, 4/5) because the comb restart burns budget the default trajectory
was going to use.

**Verdict: the portfolio route at 300 s is dead** — there is no
conversion residue for a late arm to capture.  Item 1 of the round-10
handoff closes negative.  (The comb arms' 60 s circuit-class wins from
the 2026-09-12 program remain real, but they are speed, not
conversions, at any cap ≥300 s.)

## The screen's real finding: 138 model-check failures (fixed in 32c88866)

138 of the 195 cells finished with `result=Sat` whose printed models
failed the harness model check — across summle×3, j3037, si2,
circuit_48×2, crypto1, 64_25, g2-slp (9-10 files; every one
cadical-confirmed SAT; 0 verdict disagreements).  Root cause and fix:
`2026-09-13-extstack-reconstruction.md` (the `bve_def` positive-side
reconstruction exported false witnesses; verdicts were always right).
Re-verification with the fixed binary (`precompile/32c88866/`), all 10
affected files × seed 2, default-300s arm: 10/10 `Sat` with valid total
models.

Two measurement-integrity notes for future screens:

1. The 2026-09-12 baseline cells already contained this bug's
   fingerprints as silently-downgraded unknowns — summle_X4053 seed 2
   was recorded 0/5-class while solving in 6.5 s.  Any class
   definition built on downgraded cells inherits the corruption.
2. Model-check failures are loud events (`!!! MODEL CHECK FAILED …
   investigate` in the runner) and must be accounted before conversion
   claims — a downgrade is for the record's schema, not for the
   narrative.

## Residual state for the next session

- The comb/OTFS/eager-sub arms stay available infrastructure
  (soundness-netted, default-off, bit-identical); their *value* is
  confined to sub-60 s budgets on the circuit class.
- `170058440` remains the only genuinely-unsolved sc24f file at 300 s
  (cadical 600 s ref: unknown) — an endurance file, not a class.
- Handoff item 2 (Timetable elimination schedule: phase-timing
  restructure / saturated-occurrence gating) and item 3 (CSR watch
  lists) are untouched by this screen; the elimination-side
  instrumentation (`NIXIE_LOG_ELIM`) is unchanged.  One prior worth
  carrying: cadical's default runs **no** pre-search elimination
  (`-P 0`); a "pre-search fixpoint" arm would be exploring
  non-default cadical territory, so measure against `-P>0` references
  if that route is taken.
