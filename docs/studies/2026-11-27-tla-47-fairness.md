# Issue #47 – fairness assumptions on the lasso

A `SPECIFICATION` is often `Init /\ [][Next]_vars /\ WF_vars(Next)`, or the
per-process idiom `\A self \in Node : WF_vars(step(self))`. Up to now a
temporal property under such a specification was declined by name (75): a
lasso search that ignored the clause would report an **unfair** lasso as a
behaviour of the specification. It is now assumed.

## What a fairness condition says of a lasso

On a lasso – a prefix, then a cycle repeated forever – `WF_v(A)` and
`SF_v(A)` are statements about the cycle alone:

```text
WF_v(A) violated  iff  A enabled at EVERY cycle state  and  no cycle step is an ⟨A⟩_v step
SF_v(A) violated  iff  A enabled at SOME cycle state  and  no cycle step is an ⟨A⟩_v step
```

`ENABLED ⟨A⟩_v` at `s` is "some next state `s''` has `A(s, s'') /\ s'' ≠ s`
on the subscript's variables"; an `⟨A⟩_v` step is `A` on a step that moves
them. The cycle is positions `l..k` of the trace where `l` is the first
state in which `__InLoop` holds (the ITF `loop` field), the closing step
being `last → first`.

## The one exact statement, and why there is only one

`__fair_taken_i' = __fair_taken_i \/ (InLoop' /\ ⟨A⟩_v)` accumulates over
the unrolling and, at the close, says whether a cycle step took the action.
It is exact: an existential inside `A` is in positive polarity there, which
the skolemizing pass handles, and a model with the accumulator true exhibits
the step.

What a fairness assumption must **exclude** is the negation of such a
statement – "enabled … and taken nowhere" – and `ENABLED` is a statement
about *all* next states: `A(s, s'')` with a free `s''` is satisfied by any
`s''` where the action fails. A first version tried it anyway for `SF`,
redirecting the action's primed reads to a shadow copy of the state and
concluding `¬enabled_somewhere \/ taken` at the close. It excluded nothing:
the solver chose shadows that made the action false at every cycle state,
and 98 consecutive candidates reached the concrete check. Sound (it never
excluded a fair lasso) and useless, and the shadows were removed. The
lesson is the polarity rule the codebase already states for skolemization,
seen from the other side: a free witness stands for an existential in a
position the query must *satisfy*, never for the universal a fairness
assumption needs to *refute*.

## What is built

* [`nixie_tla_syntax::behavior`]: a `FairnessClause` carries its own syntax
  and home module, so a checker can assume it rather than report it.
* [`nixie_tla_check::fairness`]: a clause is decomposed into its `WF`/`SF`
  nodes with the `\A` binders above each; a quantified clause is
  instantiated per candidate of its domain (one instance per member,
  guarded by `c \in P`), the binder bound through the lowerer for the
  lowering of that instance alone and withdrawn again
  ([`Lowerer::unbind_constant`], which forgets the definition cache with
  it). A domain without statically known members is declined by name.
* [`nixie_tla_check::temporal`]: the rewritten `Next` carries each
  instance's `taken` accumulator; nothing else of fairness is symbolic.
* `Bmc`: at a `Sat`, a candidate lasso of a fairness-bearing pass is
  **examined** on its concrete cycle. `taken` by the evaluator on every
  cycle step including the closing one; `ENABLED` by the solver on every
  cycle state – the state's values (sets, functions, records, variants
  included) rebuilt as kernel literals ([`fairness::value_literal`]) and
  pinned into the action's unprimed reads ([`lower::pin_unprimed`]), the
  action skolemized in positive polarity and encoded one step past the
  bound. `Sat` is enabled, `Unsat` is not, `Unknown` is `Unknown`.
  * An **unfair** lasso is ruled out by a clause that generalizes the
    evidence: for `WF`, every lasso of this depth whose cycle stays within
    the states just found enabling the action; for `SF`, every lasso whose
    cycle *contains* one of them; and, in both, that takes none of its steps
    (`¬taken_i` at the close). The prefix, the rotation of the cycle and
    stuttering steps inside it change nothing, so one clause covers a
    family. The precondition is stated in full – every state variable at
    every position the loop may occupy, created if the unrolling never
    mentioned it there – because a clause that left a variable out would
    exclude lassoes it has no evidence about, the unsound direction.
    A clause is asserted at its own depth only.
  * A lasso that cannot be examined, or an unfair one that cannot be ruled
    out, is `Unknown` – never reported, never dismissed.
* The CLI prints `Assuming fairness of the temporal property: …`, keeps
  the invariants' warning (a fairness clause changes nothing a bounded
  safety check sees), and words a passing bound as *no violating lasso
  within the bound satisfies the specification's fairness assumptions*.

The quantified clause's instances are one per **candidate** of the domain,
guarded by membership: the candidate lists are over-approximations (a
filter's base), and the guard, evaluated concretely on the cycle state,
decides whether the instance is an assumption at all.

## Found on the way: the tableau's `Init` contradicted its own step 0

The `WF` acceptance test would not find a fair counterexample it should
have: on `Tick \/ Step` with `Step` enabled only where `x = 0`, the
Tick-only cycle `(0,0) → (1,0) → (0,0)` is WF-fair and violates
`<>[](x = 1)`, and "no lasso of 2 steps or fewer violates" was the answer.

The dumped depth-2 query, pinned to that very lasso, is `unsat` – to z3 as
well. The reason is in the tableau: `Init` fixed `unroll = TRUE` for a `[]`
node, and the step-0 equation says `unroll@0 = prev@0 /\ (¬InLoop@1 \/
arg@0)`. For a lasso whose loop starts in state **0**, `InLoop@1` is true,
so the equation makes `unroll@0` FALSE whenever the box's argument is false
in state 0 (and, for a diamond, TRUE whenever its argument is true) –
against `Init`. Such a lasso is unrepresentable; its violation surfaces one
step later, rotated to start in state 1, and within a bound that reaches
only the shorter form it does not surface at all.

Apalache's `TableauEncoder` has the same `auxVarInitEx` beside the same
step-0 equation, so its `--temporal` has the same blind spot; its 26
integration cells do not contain the shape (a `[]` argument false in the
first state of a loop starting there), which is why the parity harness
never saw it. The fix leaves `unroll@0` to its equation – `prev@0` is the
neutral element the product starts from, so this is exact in every case –
and adds lassoes, never removes one. Effects: `a_box_and_a_diamond_on_a_two_cycle`
and `nested_boxes_and_diamonds` now find the two-step lasso at two steps
(they had recorded three, with a comment that rationalized it), and the two
CLI tests reading the `loop` field read `1` for the two-cycle. On the 26
oracle cells nothing moved (below).

## Stuttering: parity kept, and the gap named

The lasso is built over `Next` as Apalache's `LoopEncoder` writes it
(`addLoopLogicToNext` conjoins the loop logic with `next` as is): **no
stuttering step**. In TLA+ every `Init /\ [][Next]_v` specification has
behaviours that stutter forever, and `WF`'s ordinary role is to rule them
out; here, as in Apalache, they are not behaviours of the encoded system,
and the acceptance scenarios spell a stutter as an explicit action that
leaves the state alone (`x' = x`), which `⟨Next⟩_x` correctly does not
count as taken. Modelling stuttering would be one disjunct in
`temporal::encode` (`Next \/ UNCHANGED vars`) and the fairness machinery is
stutter-agnostic by construction; it would also flip the oracle's
`ManyBoxes`/`LongLoops`/`NoLoopsNoProblems` "Liveness" cells (a behaviour
stuttering in its first state violates them), so it is a semantic decision
about the drop-in contract, recorded as an open question rather than made
here.

## Gates

* `nixie-tla-check::fairness` (7 tests): the issue's four scenarios, the
  quantified clause, the decline, and the tableau regression.
* TLA crates: 703 tests (696 + 7), the three updated expectations above the
  only changes.
* Parity, the 26 `--temporal` cells of Apalache's suite (pinned 0.63.0,
  cached oracle): **Agree-Ok 7, Agree-Violation 7 (lengths equal),
  Declined 10, Inconclusive 2, OracleFailed 0, MISMATCH 0** – the two
  inconclusive are the `Range`-over-`Int` timeouts the #29 landing
  recorded. The tableau fix changes no oracle-comparable length.
* Corpus A/B: see the landing note on the tracking issue.

[`nixie_tla_syntax::behavior`]: ../../nixie-tla-syntax/src/behavior.rs
[`nixie_tla_check::fairness`]: ../../nixie-tla-check/src/fairness.rs
[`nixie_tla_check::temporal`]: ../../nixie-tla-check/src/temporal.rs
[`Lowerer::unbind_constant`]: ../../nixie-tla/src/lower.rs
[`fairness::value_literal`]: ../../nixie-tla-check/src/fairness.rs
[`lower::pin_unprimed`]: ../../nixie-tla/src/lower.rs
