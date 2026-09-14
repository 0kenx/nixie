# An array-sorted variable has no value in the model

**Status:** **fixed** 2026-09-14, same day. Kept because both halves are
worth having on record, and because the second half is subtler than it looks.
**Severity:** `(get-value)` on an array term cannot answer; the `sat`/`unsat`
verdict is unaffected.

## What happens

```rust
let arr = tm.sorts.array(int, int);
let f    = tm.mk_var("f", arr);
let base = tm.mk_var("base", arr);
let s2   = tm.mk_store(tm.mk_store(base, one, one), two, two);
solver.assert(tm.mk_eq(f, s2), &mut tm);
assert_eq!(solver.check(&mut tm), SolverResult::Sat);

let m = solver.model().unwrap().clone();
m.get(f)                       // None      — nothing assigned
m.eval(f, &mut tm)             // Var("f")  — evaluates to itself
m.eval(tm.mk_select(f, one), &mut tm)
                               // Select(f, 1) — unreduced
```

`f` is pinned by an assertion to a two-store chain over `base`, and the model
says nothing about it. Two separate things are missing:

1. **The array theory produces no model value** for an array-sorted variable.
   There is no store chain, no `FuncInterp`, no default — `Model::get` returns
   `None`.
2. **`Model::eval` has no case for `select` or `store`.** Even given a store
   chain it could not reduce `select(store(b, j, v), i)`, so a `(get-value
   (select f 1))` cannot be answered from the terms either.

## Why it matters here

`nixie-tla-check` now decodes the counterexample behind a reported violation
and replays it through `nixie-tla`'s evaluator (`src/trace.rs`). A TLA+
function is encoded as an SMT array plus a companion domain term, so a
function-valued state variable is exactly this shape. The decoder works around
(2) by reading the `select` terms *the query itself built* — the same tactic it
uses for sets, whose ground reduction likewise leaves no model value — but that
only recovers points something asked about. A function `Init` pins with a store
chain and the invariant never selects from is unrecoverable, and its trace
cannot be replayed.

Measured cost at the time: **none on the corpus** — all 19 reported violations
were over scalar state. The cost was on the shape rather than the count, which
is exactly why it was worth fixing before the shape arrived: sequences made it
the difference between a trace and no trace.
`nixie-tla-check/tests/traces.rs::a_function_built_by_init_decodes` and
`a_sequence_valued_variable_decodes` are the regressions.

## The fix

Both halves, in `nixie-solver`:

* **Array model construction.** `build_model` already reads values out of
  asserted equalities whose SAT variable is true; it now does so for an
  array-sorted equality too, recording the `store` chain as the name's value.
  The equality holds in this model, so the two sides denote the same array and
  this states only what the query already forced. An occurs check declines a
  name that appears in its own value.

* **`Model::eval` learned `select` and `store`**, with the reduction walking a
  chain: a write at an index *equal* to the one being read is the answer, a
  write at a *different* index is skipped, and anything else stops the walk and
  returns the `select` as itself — which is the honest answer for a point
  nothing constrained.

Two things about that walk were not obvious and cost a round each:

1. **The chain's own indices must be evaluated as the walk reaches them.** A
  chain that came from a model *assignment* is the raw term the assertion
  pinned, so an index arrives as arithmetic — `Len(h) + 1`, not `2` — and would
  match nothing.

2. **The links must be resolved through the model too.** A chain is not one
  nested `store`: each `Append` writes onto the *previous* sequence's graph, so
  the base of one link is a name whose own chain is another model assignment.
  Following those is the walk. Neither step recurses through the chain, because
  `Model::eval` returns an assignment without descending into it.

## What it unblocked

TLA+ sequences, which are a length and a `store` chain, and with them the
counterexamples of the specifications `intent` generates — where every
behaviour carries a `history : Seq(Str)` grown by `Append`. Before this a trace
for one of those could not be read back at all.

## Related

`docs/studies/2026-09-14-model-completion-overrides-datatype-fields.md` is a
second model-construction defect found by the same replay, in the same area:
there a datatype field *is* assigned, and assigned a value contradicting the
assertion that pinned it. Both are worth fixing together by whoever owns model
construction.
