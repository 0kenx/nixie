# Congruence canonicalization of candidate Sat models (2026-08-24)

## Trigger

The final congruence honesty gate (`04329ea`) closed the non-convex
false-SAT class trajectory-independently, at the cost of one honest
downgrade in the differential: `sorted_list_insert_noalloc1` `sat`→
`unknown` (z3: sat).  This pass recovers such `sat`s whenever a real
model exists.

## The decisive measurement (why "pinned" was the wrong rule)

A first version refused to move "pinned" results (assignments the model
builder recorded for applications).  Instrumenting the downgrade showed
two split groups, both fully pinned — e.g. `t.nxt(t.l)=1` vs
`t.nxt(i1)=0` at model-equal arguments (three pointer constants all at
−7).  The z3 cross-check settled the semantics:

* `F ∧ (= (t.nxt t.l) (t.nxt i1))` → **sat**
* `F ∧ (distinct (t.nxt t.l) (t.nxt i1))` → **sat**

Neither side is entailed — the recorded results are **search-arbitrary
choices**, not assertion obligations.  A pin rule built on "the builder
wrote it" is therefore unsound in the completeness direction: it
preserves exactly the arbitrary collisions the pass exists to repair.

## The landed policy

`Solver::canonicalize_model_congruence` (new module
`solver/model_congruence.rs`): group each function's applications by
their arguments' ground model values; unify every split group's results
to a representative (majority, ties by smallest TermId — deterministic)
as a **trial repair**; the caller post-validates with
`model_refutes_assertions` — the same ground evaluator the
model-refutation gate uses — and **discards the repair wholesale**
(original assignments restored) if it falsifies any ground assertion.
The gate then fires only when *every* congruent choice is inconsistent
with the assertions: the genuinely unsat-shaped candidates.

## Results

| instance | verdict | z3 |
|---|---|---|
| sorted_list_insert_noalloc1 | **sat** (was `unknown`) | sat |
| pete cxs-bp / 5s / family | unsat | unsat |
| wisas xs_8_13 | unsat (400 s, unchanged) | unsat |

Differential: **0 wrong verdicts**; the only verdict flip vs `04329ea`
is the recovered `sat`.  Full suite 10 083, clippy/fmt/doc, Z3 parity
168/168.

## Disposition

Landed with the gate (`04329ea` + this): the `Sat` exit now has both
halves — the trajectory-independent refusal of uninterpretable models,
and the repair of models that differ from a real one only in
unconstrained application results.

## Erratum (2026-08-24): SUPERSEDED

The canonicalizer is REMOVED together with the gate it serviced: the false-model class it repaired is closed at the root (complete arrangement enumeration, `2026-08-arrangement-chain-root-cause.md`), and `sorted_list_insert_noalloc1` answers `sat` with no canonicalizer.
