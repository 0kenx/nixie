# Issue #49 – opaque sets equated to unions of singletons: the witness, and where the time went

## The shape

```smt2
(set-logic ALL)
(declare-fun d0 () (Set Int)) … (declare-fun d5 () (Set Int))
(assert (= d0 (set.union (set.singleton 1) (set.singleton 2))))
… six of them
(check-sat)
```

`sat`, of course. On `main` @ `feeabc1c` (release `nixie --stats`), against
z3's 18 ms for the same family spelled as arrays:

| file | sets | `main` | this change |
|---|---:|---:|---:|
| `dom4` | 4 | 781 ms, 15,016 decisions | 51 ms, **0 decisions** |
| `dom5` | 5 | 545 ms, 17,586 decisions | 49 ms, 0 decisions |
| `dom6` | 6 | 38.9 s, 701,781 decisions | 10 ms, 0 decisions |
| `dom8` | 8 | > 60 s (timeout) | 10 ms, 0 decisions |
| `u18` | 1, 18 singletons | 13.1 s, 1.4 M decisions | 10 ms, 0 decisions |
| `eqchain6` | 6, no elements | 19 ms, 52 decisions | 11 ms, 52 decisions |

Through the TLA+ encoder, which gives every function-sorted name a
companion `name$dom` and asserts it equal to a union of singletons (issue
#45's shape): eleven function variables over `1..3`, a trivial invariant,
`--length=0` – **`Unknown` after 2.4 s → `NoError` in 2.8 ms**.

## Where the time is – not the counting axioms

The issue's guess was the implicit-pair witnesses entering the counting
axioms. The first half is right and the second half is wrong, and the
difference is what made the fix small.

* `eqchain6` – six opaque sets equated to each other, **no elements** –
  takes 52 decisions. Six opaque sets with fifteen pairs and no membership
  atom to decide are nothing. So it is not the *pairs*.
* `u18` – **one** opaque set equal to an 18-singleton union – takes 1.4 M
  decisions. One explicit pair, eighteen opaque/singleton pairs.
* `NIXIE_CAPS=set_pair_budget=21` on `dom6` (the six explicit pairs and the
  fifteen opaque–opaque pairs, **no opaque–singleton pair**): 4,699
  decisions; with the singleton pairs too (33): 701,781.

So the trigger is the **opaque–singleton pairs**: `(d_i, {1})` and
`(d_i, {2})`, each with a fresh witness `k` and the clause
`d_i ≠ {1} ∨ (k ∈ d_i) ⊕ (k = 1)`.

The counting pass is not involved at all: it runs only where a `set.card` or
a `set.choose` is surveyed, and there is none here.

## What the search does: a final-check storm

`NIXIE_TRACE_DECISIONS=1` on `dom4`: 248 conflicts, 15,016 decisions,
**0 restarts** – 60 decisions per conflict. The conflicts split 13 `bool`
and **235 `final-check`**, the latter at decision level ~79: the SAT core
reaches a complete assignment, a theory's final check refutes it, and the
clause learned is **two literals long**. `NIXIE_THEORY_CONFLICT_DUMP=1`
writes the first one:

```smt2
(set-logic QF_LIA)
(declare-fun @set_ext!… () Int)
(assert (= w 2))            ; the atom `w = 2`, assigned true
(assert (not (< 1 w)))      ; a case-split atom `w ≥ 2`, assigned false
(check-sat)                 ; unsat
```

An **integer** witness with a disequality on it (`w ≠ 1`, `w ≠ 2`, from the
singleton pairs) is an open arithmetic question; the arithmetic search
mints case-split atoms for it (`w ≥ 2`), the SAT core commits them
inconsistently with the equality atoms, and the inconsistency is noticed
only at the final check – one two-literal clause per complete assignment.
Thirty-three witnesses times two disequalities is a long storm. (It is not
the LIA branch channel: `NIXIE_LIA_BRANCH_TRACE` prints nothing and
`NIXIE_LIA_BRANCH_LEMMA=0` changes nothing.)

## The fix: a confined pair states its disequality among its own elements

Two sets both **confined** to known member lists differ, if they differ, at
an element of those lists. The reduction now reads which opaque sets the
assertion stack **pins** – a top-level, positive `(= d t)` conjunct whose
other side has a support ([`support_with`], the structural support extended
to follow pins, transitively) – and for a pair whose two sides are both
confined emits

```text
(= a b)  ∨  ⋁_e (e ∈ a) ⊕ (e ∈ b)        e over the union of the two lists
```

instead of minting a witness. `(set.subset a b)` gets `a ⊄ b → ⋁_e (e ∈ a ∧
e ∉ b)` in the same case. A pair with an unconfined side keeps its fresh
witness: its difference may lie anywhere.

Three points the fix stands on:

* **Scoping.** The axioms are conjoined onto the assertion being made, and
  `reduce` runs over the whole stack at that moment, so an axiom on
  assertion *k* rests only on assertions at or below *k* – which outlive it
  under `pop`. A pin read from an assertion that is later popped leaves with
  the axioms that read it.
* **Only top-level conjuncts pin.** An equality under a `not`, an `or` or an
  implication is not a fact about the stack, and `pinned_supports` flattens
  nothing but `and`. Axioms of earlier passes are top-level conjuncts too
  and are all valid consequences, so a pin read off one is sound.
* **The pair set and the budget are unchanged.** Every pair still gets its
  agreement clauses (`a = b → e ∈ a ↔ e ∈ b`) and still counts against
  `set_pair_budget`; only the disequality witness changed. The model
  synthesizer reads the same `eq_pairs` as before and works from membership
  atoms alone, so fewer witness variables cannot disturb it.

With the pins read, `dom6` is 173 propagations and no decision: every
opaque–singleton clause folds to `(= d_i {1}) ∨ ¬(1 ∈ d_i) ∨ (2 ∈ d_i)`, and
`1 ∈ d_i`, `2 ∈ d_i` are level-0 units.

## What it does not do

* **Unpinned sets keep their witnesses.** A state variable's set (`s@k`,
  constrained only through the transition relation) has no top-level
  equality, and its singleton pairs still mint. With `Int` elements the
  storm is still there for them – the shape `liveness` specs pay for on a
  lasso with integer sets (seen while testing issue #47: the quantified
  fairness test over `Node = {1, 2}` took minutes in the test profile,
  seconds with model values). The witness is genuinely needed there – "a
  has an element other than `e`" has no named element to offer – so the
  remedy is on the arithmetic side: a disequality on a fresh integer should
  not cost a case split per complete assignment.
* **The budget is still 256 pairs.** Eleven function variables at depth 1
  are 27 `$dom` sets, 319 pairs, and the cap fires (`[cap] set_pair_budget
  actual=257 cap=256`): `Unknown`, honestly. With the cap raised the same
  query runs 8 s and is still `Unknown` – the array/search capacity class
  the PlusCal two-array pins document – so exempting confined pairs from the
  cap buys nothing measurable yet, and was not done.

## Gates

* Set-focused solver tests (`--lib` and the nine set/bag/array-domain test
  targets, 1,598 tests): 1,591 pass; 5 `SIGABRT` are the documented 128
  KiB-stack canaries; `choose_of_ite_picks_the_taken_branch` is the
  documented pre-existing failure (its query has no pin, so the reduction
  is byte-identical; both binaries answer `unsat`/`sat` on its two scripts
  through the CLI).
* Corpus A/B (907 modules, depth 4, 20k conflicts, per-file list diffed):
  see the landing note on issue #49.

[`support_with`]: ../../nixie-solver/src/solver/set_theory/mod.rs
