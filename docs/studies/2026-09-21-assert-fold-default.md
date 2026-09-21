# The assert-fold campaign: the default flips, refute-only — the nec-smt class solves

**Date:** 2026-09-21 (the small-hours session executing the
`2026-09-20-smt-perf-arc-executed.md` handoff's step 3, reconciled with
the assert-fold session's landing).  **Landed:** `NIXIE_ASSERT_FOLD`
default **ON** with a kill-switch, **refute-only adoption** at the call
sites, the ite structural cost gate, a depth-aware composition contract,
and the depth-guard's fold-rescue ladder — **69 nec-smt instances flip
`unknown → unsat` with zero z3-disagreeing flips; `prp-3-18` (the 47×
wall cell) decides at 41-102 ms / 0 conflicts (was 880 ms / 1015
conflicts); `problem_2__014` (the 42× cell) flips timeout →
`sat`/905 ms; the standing LIA slice gains the cell (33/60) with par-2
9429 → 9088 ms and both-solved median vs z3 0.55 → 0.52.**

## The reconciliation (two sessions, one feature)

The assert-fold session landed `assert_fold` (`a6349641`, flag-gated
`NIXIE_ASSERT_FOLD=1`, "probe-only until the measurement campaign flips
the default") — composition `simplify` + `ctx_simplify` per assertion
after `expand_lets`, before the depth guard.  This session's independent
probe (the same idea, independently measured) was clobbered by their
landing's checkout (their addendum documents the incident — the item-96
precedent applies: same feature, hand off).  What lands here is the
CAMPAIGN their landing named, plus the safety corrections the campaign
exposed:

1. **Refute-only adoption (the campaign's core verdict).**  Their pass
   REWRITES every ite-bearing assertion.  Measured at calm load, the
   rewrite regressed the standing LIA slice's mid-band hard: median wall
   37 → 305 ms, geomean 144 → 256 (the sixth session's "may reduce
   locally but increase globally" caveat, at verdict-cost scale — the
   fold's residual encodes worse than the original ite structure).
   Adopting ONLY decided constants (`false` → the native
   `has_false_assertion` routing; `true` → the native drop) keeps every
   win at zero cost: non-refuting goals keep their original encoding
   verbatim, so the search is bit-identical up to unused interning.
   Post-fix slice: no cell worsened >2.5×, the small-cell direct A/B
   (fold vs pre-fold, back-to-back) is faster-or-equal.
2. **The depth contract.**  Their placement runs `ctx_simplify` BEFORE
   the depth guard — but `ctx_walk` is mutually-recursive NATIVE code
   (the ninth session's own record), so a 2500-deep spine on a 128 KiB
   encode thread is a stack-overflow hazard.  The call sites now skip
   deep terms entirely; the depth-guard's rescue LADDER owns them:
   rung 1 `fold_ground` (as before), rung 2 the explicit-stack bottom-up
   `simplify` — which carries the same guard-equality solve rules
   (`eq_ite_rules` fires in `simplify`'s `Eq` arm) and collapsed every
   deep spine the campaign measured (that is where the 69 flips come
   from; `deep_fold_rescue` in `encode_guards.rs`, both guard sites).
   Deep-term ADOPTION there stays rewrite-shaped deliberately: the
   alternative is refusal (`Unknown`), so a worse encoding is strictly
   better than no search.
3. **The ite structural gate.**  `subtree_has_ite` (explicit-stack,
   early-exit) — non-ite goals never pay the fold at all.
4. **Default ON, `NIXIE_ASSERT_FOLD=0` to disable.**  The kill-switch
   verified: the 1015-conflict search path round-trips exactly.

## Evidence

* **Campaign:** 120-file nec-smt prefix, fold vs pre-fold binary:
  69 flips, ALL `unknown → unsat`, ZERO flips disagreeing with z3
  4.16.0 (every flipped member cross-checked).  Full-corpus sweep
  earlier: zero false verdicts anywhere (all gaps honest
  `unknown`/`timeout`).
* **Standing table** (calm load): LIA 33/60 (was 32), disagreements 0,
  par2 9088 (was 9429), both-solved median 0.52 (was 0.55), conflicts
  4502 (was 5517 — the fold's refuted cells).  BV leg load-contaminated
  (z3's own set moved 55→52); the nixie BV counters match the
  fold-off baseline modulo the two known drift cells (millionaires:
  sat held, 0→10-38 conflicts, wall equal-or-better).
* **Bit-identity:** perf gate PASS (conflicts/decisions 1.000/1.000 —
  the SAT corpus never enters the fold); the LIA slice's non-fold cells
  hold verdicts and counters (5517 − 1015 = 4502 exactly: prp-3-18's
  refutation is the whole delta).
* **Z3 parity:** 176/177, 0 mismatches.  **Workspace suite:** 11 865
  green.  Pins updated to the new contract: the audit's 3000-deep
  same-condition `ite` nest now collapses and answers its TRUE `sat`
  (the overflow-discipline invariant unchanged); the deep-neg chain
  rescued to `sat`; an unfoldable UF-application chain still refuses
  `unknown`; the module's unit pins under the default; the end-to-end
  refute pin.

## The class boundary after this landing

* The nec-smt UNSAT members: closed (fold-refuted at assert time).
* `prp-5-23`-shaped members: timeout → `unsat`/55 ms.
* The remaining `unknown`/`timeout` mass: the SAT-side members z3 also
  times out on, plus the deep spines whose residual is NOT
  value-decided (the fold leaves a real search; those now SEARCH rather
  than refuse — some solve, some time out honestly).
* `problem_2__014`-class SAT cells at 0 conflicts: preprocessing
  encoding cost on our side — the refute-only fold does not touch
  non-refuting goals; that cell's win here came from the ladder (deep
  spine → collapsed → searched to `sat`).

## Traps recorded

* **`MM` in a shared tree is someone's live work** — the assert-fold
  session's checkout clobbered this session's uncommitted encode.rs
  probe (their addendum).  This session then re-derived the same
  feature's MEASUREMENTS in reconciliation — the net cost was one
  wasted build+measure cycle and one confusing hour of "why did my code
  revert".  Commit WIP or expect the clobber.
* **The shared `target/` and `/tmp` stayed volatile all night** (two
  purges, one stale test binary that passed a pin the source could not
  pass — always distrust a surprising PASS right after target churn;
  re-run before believing it).
* **geomean_all on a corpus of ms-floor cells is load-noise-dominated**
  — a 3 ms cell at load 12 measures 15 ms; use par2 + both-solved
  median + per-cell direct A/B for landing decisions (the operator's
  standing instruction, now with a documented mechanism).

## Addendum: the conj-level probe's demand pool (text-level scan)

The removed check-time conj-level fold (cross-assertion context) has a
pool of **9 312 multi-assert ite-bearing scripts (10.1 % of the
92 377-file corpus)** — dominated by QF_BV (7 750), then QF_UF (614),
QF_NIA (506), QF_LIA (341).  Whether cross-assertion context actually
folds a measurable subset is unmeasured (needs solver runs: re-express
the goal as `(assert (and …))` + `(simplify …)` on a sample and compare
against the per-assertion outcome) — the owning session's first probe,
cheap and single-threaded.
