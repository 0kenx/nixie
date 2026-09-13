# A string equality used as an `ite` condition is not decided — false `sat`

**Date:** 2026-09-13
**Severity:** **wrong `sat`.** The solver reports a model for a formula that has none.
**Reproducer:** `cargo run -p nixie-tla-check --example strite` — terms built directly on
`nixie-core`, no TLA+ involved.
**Status:** reported, not fixed. The defect is in `nixie-solver`, which was under active edit
by another agent when this was found.

## The observation

Every line below asserts an **unsatisfiable** formula, so every line should print `Unsat`.
The last is the exception and is included deliberately.

```
x="a" /\ y="b" /\ x=y                 [asserted atom]       Unsat  ok
"a"="b" /\ TRUE                       [boolean connective]  Unsat  ok
i=1 /\ j=2 /\ ite(i=j,1,0) # 0        [int condition]       Unsat  ok
x="a" /\ y="b" /\ ite(x=y,1,0) # 0    [int branches]        Sat  <-- WRONG
x="a" /\ y="b" /\ ~ite(x=y,F,T)       [bool branches]       Sat  <-- WRONG
1 + ite("b"="a",0,1) # 2              [cardinality shape]   Sat  <-- WRONG
ite(p=q,1,0) # 0, p q uninterpreted   [really Sat]          Sat  ok
```

## What the controls establish

The controls matter more than the failures, because they place the defect precisely and rule
out three plausible causes:

| Control | Rules out |
|---|---|
| `x="a" /\ y="b" /\ x=y` is `Unsat` | "the string theory cannot decide literal disequality" — it can, and through variables, so this is not constant folding |
| `"a"="b" /\ TRUE` is `Unsat` | "the atom never reaches a theory at all" — under ordinary Boolean structure it does |
| `i=1 /\ j=2 /\ ite(i=j,1,0) # 0` is `Unsat` | "`ite` conditions are broken generally" — the identical shape over `Int` is decided, with variables, so no folding there either |
| the bool-branch case also fails | "this is an arithmetic interaction" — **it is not.** The same `ite` feeding a purely Boolean consumer fails identically |

So the failure is specific and narrow: **a string equality appearing as the condition of an
`ite` is not decided**, whatever the `ite`'s branches are and whatever consumes it. The same
equality asserted directly, or placed under `and`/`or`/`implies`, is decided correctly.

The final line is a genuine `Sat` — `p` and `q` are uninterpreted and may or may not be equal —
and is there so that a fix cannot be a blanket "assume the condition is false".

## What was *not* established

An earlier draft of this study asserted a cause: that `nixie-solver`'s `nelson_oppen.rs`
classifies `TermKind::Ite` by its result sort, putting the `ite` in `Arithmetic` while its
condition belongs to `String`. **That is wrong** — `Ite` is classified `TermTheory::Shared`,
alongside `Eq` and the Boolean connectives. The bool-branch control kills the arithmetic
framing independently.

The real mechanism is not identified here. What is established is the boundary: asserted atom
and Boolean connective work, `ite` condition does not, and the `Int` analogue of the same
`ite` does. Somewhere between the `ite` condition becoming a SAT literal and the String solver
being told about that literal, the connection is lost.

## Why the TLA+ front end found it

`nixie-tla-check::arena` encodes `Cardinality(S)` as a sum of indicators, one per candidate
member, each guarded by "no earlier candidate is present and equal to this one". With string
elements those guards are string equalities under `ite` — the fourth and sixth lines above,
reached as a matter of course rather than by looking for trouble.

Nothing in the existing suites builds an `ite` with a string condition, because no existing
front end produces one. Same pattern as `2026-09-13-lia-wide-literal-arithmetic.md`: a new
front end exercising an old core along a path its own suites do not cover.

## Direction of the error

**Observed:** false `Sat`. In bounded model checking that manufactures a counterexample — a
violation the specification does not have.

**Not established:** whether the same gap can produce a false `Unsat`. An un-propagated
disequality makes a formula *easier* to satisfy, which points at false `Sat` only; but this is
a theory-interface failure, and those are not reliably one-directional. Do not assume
`NoViolationWithin` is unaffected until the connection is fixed and checked both ways.

## What was done in the front end

Nothing was worked around. `Cardinality` could be encoded without an `ite`, and deliberately
was not: the shape is legitimate, and removing it would hide a live soundness bug rather than
fix it.

`nixie-tla-check/tests/arena.rs` carries the affected case as an `#[ignore]`d test naming this
study, so it turns green on its own when the defect is fixed. Integer-element cardinality —
including the duplicate-candidate cases the encoding exists to get right — is tested normally
and passes.

## What to check when fixing

- How an `ite` condition becomes a SAT literal, and whether that literal is registered with
  the theory that owns its atom. The `Int` path works, so compare the two.
- Whether other condition theories are affected: `ite(bv1 = bv2, …)`, `ite(fp1 = fp2, …)`,
  `ite(f(x) = f(y), …)` over uninterpreted sorts. Each is a two-line addition to
  `examples/strite.rs`, and the pattern is not obviously string-specific.
- Both directions, using the final control: a fix that made the unsat cases pass by assuming
  the condition false would break it.
