# Root fix: quantified-UF constant args pinned into arithmetic; quantified exit-gate backstop removed (2026-08-24)

## Sequence (the removal protocol working as designed)

Following the arrangement-round root-cause fix (`a5f97b9`), the last
remaining backstop of the class was the **quantified-path exit gate**
(`28a8ac1` pr30#3 congruence half + `1051647` ground-assertion half).
Per the review direction — backstops hide real bugs; certified mode
verifies `sat` — the removal was run as a probe: remove, then re-run
every surface the gate ever guarded.

- 168 parity files: **0 fires**.
- 971 quantified tests (`pr30`/`pr28`/`pr29`/quant/mbqi/model filters): **0 fires**.
- Full suite: **1 failure** — `test_pr30_quantifier_trigger_function_ground_diseq_is_not_sat`.
  The gate had been masking a **reachable false `sat`**:

```
(forall ((z Int)) (>= (f z) 0))   ; f is quantified → un-purified (per-function gate)
(= x 2) (= y (+ x 1))             ; ⇒ y = 3 entailed by arithmetic
(not (= (f y) (f 3)))             ; refutable by congruence — answered `sat`
```

## Root cause (three layers deep)

1. **Why no congruence**: `purify_numeric_uf_args` skips quantified
   functions (purification breaks `mbqi::model_certify`'s clean ground
   pins).  Un-purified, `f(3)`'s argument `3` never becomes an
   *arithmetic interface term* — `interface_terms()` only contains terms
   arith has interned, and `3` appears solely inside an EUF-owned
   application.  Every interface-equality mechanism (model-equal probe,
   arrangement round) selects candidates from
   `interface_terms ∩ uf_args`; the pair `(y, 3)` could never be
   generated, `entailed_equal_reason` never ran, EUF never merged,
   congruence never fired.
2. **Why encode-time pinning failed**: pinning at encode is wiped by
   `rebase_theory_state`/model-block resets (`arith.reset()` clears
   `term_to_var`) — the pin is not a SAT-trail fact, so no replay
   re-asserts it.  Measured: pin present at encode, absent at the probe.
3. **Why value reads went stale**: `ArithSolver::pop` keeps
   `term_to_var` (search-global) while bounds are popped —
   `is_interned` cannot distinguish a live pin from a popped one, and
   the tableau assignment lags the re-pin until the next solve.

## The fix

- **encode.rs** (`pin_quantified_uf_const_arg`): collect the constant
  numeric args of *skipped* (quantified) functions into
  `quant_uf_const_pins`, evaluated in **closed form** by the atom
  parser's linear extractor — literals, negated literals (`(- 4)`, not
  parser-folded), compound constants (`(- 8 2)`).  `div`/`mod`/`ite`
  stay opaque terms in the extractor (never folded), so the
  empty-`terms` test skips them — no integer/rational
  division-semantics hazard.  Variable-bearing compounds skip the same
  way.
- **theory_manager.rs** (`nelson_oppen_combine` top): re-pin
  **unconditionally every round** — `assert_eq(&[(t,1)], v, t)` on the
  cached row plus `derived_reasons.record(t, vec![])`.  The pin row is
  a tautology (`c = c`); the reason tag names no literal and the EMPTY
  `DerivedReasons` explanation is exactly the documented semantics for
  "holds structurally, rests on no assertion" — a certificate citing
  the pin contributes nothing to the conflict clause instead of losing
  justification (`terms_to_conflict_clause` case 2/3).
- **Pins-aware value reads** (`arith_value_with_pins`): grouping and
  the model-equal prefilter report the pin value for pinned terms (true
  by construction) instead of a possibly-stale tableau assignment.

## Verification

| shape | nixie | z3 |
|---|---|---|
| UFLIA literal `f(3)` (pr30#3 case) | `unsat` | unsat |
| negative literal `g(- 4)` | `unsat` | unsat |
| compound constant `g(- 8 2)` | `unsat` | unsat |
| UFLRA real constants | `unsat` | unsat |
| nonlinear quantifier body (`ALL`) | `unsat` | unsat |
| sat controls (y = 4 ≠ 3) | `sat` | sat |

Gate-removal side: the exit gate and both helper predicates are
deleted; pr30 test updated to expect the now-correct `unsat`; new
regressions added (negative, compound, sat controls).  Full bar: 10 086
tests, clippy/fmt/doc, differential **0 wrong / solved 160 (unchanged —
corpus is QF, pins map empty, trajectories identical)**, canaries
unchanged (pete/cxs-bp unsat, 25s unsat, wisas unsat, sorted_list sat),
Z3 parity 168/168.

## Follow-ups

- `UFNIA`/`UFNRA` are missing from the `LogicSpec` registry (rejected
  as unknown at `set-logic`); the nonlinear-quantified path is currently
  only reachable via `ALL`/`NIA`.
- `div`/`mod` constant args of quantified functions stay unpinned
  (opaque in the extractor) — same shape as before this fix, not a
  regression; needs an exact-division evaluator if it ever fires.
