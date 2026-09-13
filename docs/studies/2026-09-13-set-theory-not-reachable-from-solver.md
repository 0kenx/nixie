# `nixie-theories::set` is not reachable from the solver — what O3 actually costs

**Date:** 2026-09-13
**Verdict:** O3 (*"hand set operations to a set theory instead of expanding them"*) is
**not** a wiring task. The set module exists but is not a CDCL(T) theory, and nothing
in the term language can name a set. O3 must build the sort, the term kinds and the
Nelson-Oppen dispatch before any of the existing propagators can be used at all.
**Milestone 3's naive encoding must therefore not wait on it.**

## Why this was checked

`docs/TLA_FRONTEND_DESIGN.md` §2 justifies a deliberate divergence from Apalache:
Apalache's Keramelizer expands `\cup`, `\cap`, `\`, `SUBSET` and `UNION` into
comprehensions and quantifiers, because its backend is *"an opaque SMT solver with no
set theory"*. Nixie keeps them in the KerA kernel instead, on the stated grounds that
*"Nixie has `nixie-theories/src/set`"*.

That divergence is load-bearing: it is the reason the kernel carries five set
constructors it would otherwise not need, and the reason the encoder declines them by
name rather than expanding them. Before building the encoder's set support on top of
it, the premise was checked.

## What is actually there

`nixie-theories/src/set/` is real and substantial — `membership.rs`, `cardinality.rs`,
`subset.rs`, `powerset.rs`, `finite_sets.rs`, `operations.rs`, `solver.rs`, with
propagators and statistics for each. What it is *not* is a theory of the solver:

| Checked | Result |
|---|---|
| `SortKind::Set` in `nixie-core/src/sort/mod.rs` | **absent** — the enum has Bool, Int, Real, String, BitVec, FloatingPoint, Array, RoundingMode, Uninterpreted, Parameter, Parametric, Datatype |
| Set term kinds in `TermKind` | **absent** — no membership, union, intersection or cardinality node |
| `TermTheory::Set` in `nixie-solver/src/nelson_oppen.rs` | **absent** — the dispatch covers Shared, Arithmetic, BitVector, Array, String, FloatingPoint, Datatype, Uf, Binder |
| References to `SetSolver` outside `nixie-theories` | **none** — only `nixie-theories/src/lib.rs`, the module itself, and `nixie-theories/tests/c4_theories_deep_recursion.rs` |

So the module has its own expression language (`SetExpr`, `SetVar`, `SetVarId`) and its
own `check()`. It is a standalone decision procedure sitting beside the solver, not
inside it. Nothing a `TermManager` can build reaches it.

## What O3 therefore costs

Four pieces, in dependency order, *before* the first existing propagator runs on a real
query:

1. `SortKind::Set(SortId)` in `nixie-core`, plus sort inference and printing.
2. Set term kinds in `TermKind`, plus builder methods, rewriting, substitution and
   model completion — every walk that matches exhaustively on `TermKind` must grow an
   arm, which is exactly the closed-enum discipline working as intended.
3. A `TermTheory::Set` arm in Nelson-Oppen, with shared-variable extraction across the
   Set/Arithmetic and Set/Uf boundaries (cardinality is the hard one: it couples set
   structure to integer arithmetic, so the combination is not simply disjoint).
4. A bridge from `SetExpr` to `TermId`, or a rewrite of the propagators against the
   term language directly.

`docs/TUTORIAL_CUSTOM_THEORY.md` documents the plug-in path, so step 3 is charted. None
of that changes the *conclusion* of O3 — eager encoding to lazy theory is still the
right transfer, and it is still the one bit-vectors and arrays already made here. It
changes the *cost estimate*, and it changes what milestone 3 should do first.

## Consequence for milestone 3

Milestone 3 is the **naive** encoding, and the design doc already says why it comes
first: *"the naive encoding is what gives us an oracle to test the clever ones
against."* Building it on an unwired theory would invert that — the oracle would depend
on the optimisation it exists to check.

So the naive encoding takes the route Apalache itself takes, and it is worth being
precise about what that route is, because it is easy to get wrong. Apalache does **not**
hand sets to a set theory and does not encode them as SMT arrays. It computes, before
the solver sees anything, an over-approximation of the elements each set can contain —
the *arena* of cells — and then membership is one Boolean variable per (element, set)
pair. Set operations become propositional constraints over those variables:
`x \in A \cup B` is `x \in A \/ x \in B` over a statically known candidate list.

That is a **static analysis producing a propositional encoding**, which is why it needs
no set theory at all. It is also precisely the structure O3 later replaces with a
propagator — so the naive encoding is not throwaway work, it is the specification the
lazy version must agree with.

The kernel's set constructors stay. Keeping them is what makes *both* encodings
expressible from the same IR, which is the point of the divergence; the premise that
justified it was simply stronger than the evidence supported.

## What not to retry

- Do not reach for `nixie-theories::set::SetSolver` from the TLA+ encoder. It cannot be
  called with `TermId`s and wiring it is items 1–4 above, not an import.
- Do not encode TLA+ sets as `Array(elem, Bool)` as a shortcut to the array theory. SMT
  arrays have no union, intersection or cardinality: every set operation would need
  either a quantifier (which is what the kernel divergence exists to avoid) or a
  pointwise expansion over a candidate element list — and if a candidate list is being
  computed anyway, the arena encoding is the same work with an exact result.
