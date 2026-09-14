# Membership as an uninterpreted predicate: right idea, wrong plumbing

**Verdict:** tried and reverted, 2026-09-14. The idea is sound and the
mechanism it depends on **works**; what stops it is model reconstruction, not
the reasoning. Worth retrying when that is addressed. Do not re-derive the
first three steps.

## The problem it was attacking

`200b3eab` fixed a wrong `sat`: an opaque set's membership atoms were
independent Booleans, so `x = y` said nothing about `x \in S` and `y \in S`.
The fix states congruence **as axioms**, and that has two costs it cannot shed:

* **Incomplete.** It can only speak about equalities the formula spells out
  (closed over chains), never about one the solver derives.
* **Expensive.** The corpus went from roughly four minutes to 8:33. Earlier,
  cruder versions of the same axioms reached 19:55.

Both are inherent: a ground reduction has to *say* what a theory solver
*decides*.

## The idea

Do not say it. Define `e \in S` to be `@in_S(e)` — an ordinary uninterpreted
Boolean application — and let **EUF's congruence closure** relate equal
elements. That is complete (it covers every equality the solver derives, not
only the written ones) and costs one extra term and one axiom per
(element, set) pair the definition loop already visits: no quadratic anything.

It is a cross-domain move rather than a new mechanism: the congruence we were
restating by hand already exists one layer down.

## What was verified

**EUF closes Boolean applications.** Probed directly before building anything:

```rust
let fx = tm.mk_apply("f", [x], bool_sort);
let fy = tm.mk_apply("f", [y], bool_sort);
solver.assert(fx);  solver.assert(tm.mk_eq(y, x));  solver.assert(tm.mk_not(fy));
// Unsat — congruence closes it.
```

The reduction change is small: in the membership-definition loop, emit
`(= (set.member e S) (@in_S e))` alongside the shape axiom, and delete the
congruence block, the element-equality survey field and its closure entirely.
With that in place `nixie-solver`'s 37 finite-set tests pass, including the
three congruence regressions from `200b3eab`.

## Why it was reverted

**The model stops answering about `set.member`.** Two of `nixie-tla-check`'s
tests fail with *"a set membership the model did not decide"*: a trace decoder
reads a set's value from the `set.member` atoms the query built, and once the
atom is one half of an equivalence, the SAT assignment may sit on the *other*
half — or on neither, if preprocessing collapsed them to a single
representative.

Propagating across true Boolean equalities in `build_model` — the same trick
that fixed the string and array cases — was tried and **did not help**, which
says the atom is not merely unassigned but gone: rewritten away, with no
equality left in `var_to_constraint` to copy along.

Chasing that is a model-reconstruction project in its own right, and there was
already a correct, measured fix in hand. Trading a working answer for a faster
one that cannot be read back is the wrong direction.

## What to do instead, and what to keep

The remaining cost is the price of axioms over congruence, and the real repair
is the one `docs/studies/` has been recording: a finite-set theory solver keyed
on equivalence classes, as CVC5 does (`theory_sets_private.cpp`), which decides
membership rather than defining it and can answer for its own model.

`nixie-theories/src/set/` already holds 8366 lines shaped like that solver —
propagators for membership, subset and cardinality, a `Theory` impl, equality
notifications. It is **not wired in**, and it is not ready to be: nothing
translates `TermKind::SetUnion` and friends into its constraints, `can_handle`
returns `true` for every term, `theory_id()` returns `TheoryId::Bool` with a
comment saying it should not, and `get_model` returns nothing. The missing
front end is most of the work, and the model is the part that matters here.

Two things from this attempt are worth keeping when that is done:

1. EUF congruence over Boolean applications is available and closes exactly the
   property in question.
2. Whatever represents membership must be **readable back from a model**. That
   is not a detail to leave until last: it is what killed this attempt, and it
   is what `nixie-tla-check`'s trace replay — which found the original wrong
   `sat` — depends on.
