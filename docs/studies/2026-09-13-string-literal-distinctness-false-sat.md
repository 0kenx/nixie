# A string equality that is not a top-level assertion was not decided — false `sat`

**Date:** 2026-09-13
**Severity:** **wrong `sat`.** The solver reported a model for formulas that have none.
**Status:** **FIXED.** Two independent gaps, both closed. Reproducer:
`cargo run -p nixie-tla-check --example strite` (terms built directly on `nixie-core`, no
TLA+ involved); regressions in `nixie-solver/tests/finite_sets_decision.rs`.

## The title is wrong, and that is the point

This study was first written as *"a string equality used as an `ite` condition is not
decided"*, because that is the shape the TLA+ arena's `Cardinality` encoding produced. Two
hypotheses were wrong before the real cause appeared, and both are recorded here because the
controls that killed them are what located the bug.

**Hypothesis 1 — `ite`.** Killed by a reproducer with no `ite` in it at all:

```
x="a" /\ y="b" /\ (x=y -> v=1) /\ (~(x=y) -> v=0) /\ v # 0     Sat  <-- WRONG
```

**Hypothesis 2 — "the atom is not registered with the string theory".** Killed by looking:
**there is no string theory in `nixie-solver`.** `nixie-theories::string::StringSolver` exists
and is referenced by nothing outside its own crate — exactly the situation
`2026-09-13-set-theory-not-reachable-from-solver.md` found for `SetSolver`. Nothing was
failing to consult the string solver, because nothing ever consulted it.

## The real cause: two gaps, and preprocessing hiding both

Every *working* case worked because the simplifier folded it. Every case where the atom
survived to the SAT layer was unconstrained. Two independent reasons:

### Gap 1 — `mk_eq` did not fold distinct string literals

`nixie-core`'s `mk_eq` folds constant comparisons for `IntConst`, `True`/`False` and
`BitVecConst`. `StringLit` was simply absent from the match, so `(= "a" "b")` built an atom
instead of `false`:

```
("a"="b" \/ p) /\ ~p                 Sat  <-- WRONG
```

Two distinct string literals are distinct values by construction, exactly as two `IntConst`
terms are. One arm alongside the existing three.

### Gap 2 — EUF did not mark string literals as distinguished values

With gap 1 closed, a literal-vs-literal equality folds away — but an equality between two
*variables* pinned to different literals does not:

```
(x="a" \/ p) /\ ~p /\ (x="b" \/ q) /\ ~q      Sat  <-- WRONG
```

EUF merges `x` with `"a"` and `x` with `"b"`, and the resulting class holds two distinct
literals with nothing objecting.

The mechanism for this already existed and strings were simply never registered:
`EufSolver::declare_value_const` — *"declare that `term` denotes one element of a family of
pairwise-distinct distinguished values"* — with **floating-point literals already using it,
keyed by bit pattern**, for the identical false-`sat` class. String literals now get a mark
keyed by their text, so every spelling of `"a"` shares one id and merges freely while `"a"`
and `"b"` can never land in one class. One mark per literal, O(k), rather than the C(k,2)
pairwise disequality edges the big-`IntConst` path needs.

## Why only strings

| sort | why it was already safe |
|---|---|
| `Int` | the arithmetic solver knows `1 != 2`; `emit_big_const_distinctness` covers the abstracted wide constants |
| `BitVec` | interned per `(value, width)` with a distinguished-value mark |
| floats | `declare_fp_const`, keyed by bit pattern |
| uninterpreted | no constants to confuse; disequalities are stated by the user |
| **strings** | **nothing** — no theory, no mark, no folding |

## Scope of the bug

Far wider than the shape that surfaced it. **Any** string equality reaching the solver as
something other than a foldable top-level assertion — under a disjunction, an implication, an
`ite` condition, a quantifier body — was a free Boolean. `(or (= x "a") p)` is an ordinary
thing to write.

## Why the TLA+ front end found it

`nixie-tla-check::arena` encodes `Cardinality(S)` as a sum of indicators, each guarded by "no
earlier candidate is present and equal to this one". With string elements those guards are
string equalities under an `ite`, reached as a matter of course. Nothing in the existing
suites built one, because no existing front end produced one — the same pattern as
`2026-09-13-lia-wide-literal-arithmetic.md`.

## What was deliberately not done

The `Cardinality` encoding was never reshaped to avoid the `ite`. It could have been, and the
blocked test would have gone green while the solver stayed wrong. It was left as an
`#[ignore]`d test naming this study instead, and it now passes on its own.

## Both directions are checked

A fix that made the unsatisfiable cases pass by assuming equalities false would be worse than
the bug. The reproducer therefore ends with a genuinely satisfiable case
(`ite(p=q,1,0) # 0` over uninterpreted `p`, `q`), and the regressions include
`equal_string_literals_still_merge` and `an_open_string_equality_is_still_satisfiable`.

## Still open

Whether other condition theories have the same shape. `ite(bv1 = bv2, ...)` and
`ite(fp1 = fp2, ...)` are covered by their existing distinguished-value marks, and
uninterpreted sorts have no constants — but the check is two lines each in
`examples/strite.rs` and has not been done exhaustively.
