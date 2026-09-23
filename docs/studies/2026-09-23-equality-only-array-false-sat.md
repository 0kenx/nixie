# Equality-only array contradictions answered `sat` — the missing axiom-1 self-reads

**Status:** **fixed** 2026-09-23, same day. Found by digging past the
symptom named in `docs/handovers/2026-09-22-dom-pair-budget-handoff.md`
(don't-care completion in the TLA+ trace decoder) into the layers below it.
**Severity:** **false `sat`** — the catastrophic class. Two minimized
reproducers, both `unsat` in Z3 4.16.0 and `sat` in nixie before the fix.

## The reproducers

```scheme
;; A: two stores collide through an equated pair; nothing selects at 1.
(declare-fun f () (Array Int Int)) (declare-fun g () (Array Int Int))
(declare-fun b1 () (Array Int Int)) (declare-fun b2 () (Array Int Int))
(assert (= f (store b1 1 1)))
(assert (= f g))
(assert (= g (store b2 1 2)))     ;; forces select-at-1: 1 = 2.  UNSAT.

;; B: the BMC branch shape in isolation.
(assert (= x1 x2))                 ;; the UNCHANGED branch's equality
(assert (= x2 (store x1 1 1)))     ;; the taken branch's update
(assert (= x1 (store (store b 1 0) 2 0)))  ;; the init chain, x1[1] = 0
```

B is exactly the committed-equality set a PlusCal two-array depth-4
unrolling produces when two branch-update atoms go simultaneously true
through no-op writes and nothing in the query reads `x[1]` — the model the
`2026-09-22` handoff decoded into a trace the replay rejected.

## Why the solver said `sat`

The lazy array-axiom engine (`nixie-solver/src/solver/array_axioms.rs`)
is a refinement loop over a *candidate model*: it walks the assertions,
collects array structure, and instantiates the lemma families the
candidate does not already satisfy. Every family was gated on something
observed:

* read-over-write — for observed `select` terms;
* upward read-over-write — for indices the base is *read* at;
* write-index congruence — for indices something already READS
  (`read_indices`);
* extensionality witnesses — for pairs already *separated*
  (Z3's `new_diseq_eh`).

A contradiction that lives entirely in array **equalities** observes
nothing: EUF merges the equated arrays (the equalities are committed
facts), but congruence closure has no `select` terms to close over, the
refinement loop asserts nothing, and the search reports a candidate model
whose equality arrangement the array theory never refuted. Verdict:
`sat`, on an UNSAT formula.

## The fix

Z3's eager **axiom 1** (`theory_array_base::assert_store_axiom1_core`,
confirmed against Z3 4.16.0 source and CVC5's `theory_arrays`): for every
`store(b, i, v)` term, the unconditional unit

```text
select(store(b, i, v), i) = v
```

— one per store term, deduplicated by interned id, bounded by the input's
stores. This is the family that *bootstraps the reads*: with the
self-read minted, the store's written value is pinned in the E-graph, EUF
congruence closes over the merged arrays' self-reads, and two chains
writing different values at the same index collide (`1 ≈ 2`) as an
ordinary congruence conflict. Verified: both reproducers flip to `unsat`;
the neighbouring satisfiable shapes (identical write values; disjunction
taking the store side with the alias side ruled out) stay `sat`, matching
Z3.

Regressions: `store_self_read_tests` in `array_axioms.rs` (two unsat
shapes + two sat controls).

## The layers below the false verdict (the reason the trace decoder saw garbage)

The handoff's named item — "don't-care completion independent of the
taken branch" — was the visible symptom of three stacked defects. Fixing
only the decoder would have hidden all three.

1. **The false `sat` above** (theory). The committed-true equality set
   could be jointly contradictory, so *no* model was coherent.

2. **Model construction** (`model_builder.rs`). Two sub-defects:
   - The EUF-reconcile pass ("overwrite every member's entry with its
     class representative's value") installed values that *mention their
     own key* — `x@0 -> store(x@0, 1, 1)` — on which `Model::eval`
     ping-pongs. Now occurs-guarded, like the recording pass always was.
   - Array **aliases** (`x@2 = x@1`, neither side a store) were never
     recorded at all, so an UNCHANGED variable had no value and every
     read of it defaulted. Now recorded in a second pass (after the
     store pass, so a name's own chain wins), resolved through existing
     entries, with a final dereference pass so `f -> g` prints as `g`'s
     chain. Self-referential shapes fall back to the raw name, which the
     walk follows one hop later.

3. **The chain walk** (`select_in` in `solver/types.rs`). A model
   assignment that is a plain alias broke the walk: the minted
   `select(x@2, i)` matched no query-built select and the point read
   back unconstrained — the decoder then had to invent a value the taken
   branch could disagree with. The walk now follows alias assignments
   (cycle-guarded), which is sound for the same reason the chain walk
   is: the assignment states an equality the query committed to.

With 1–3 fixed, the trace decoder's don't-care points complete *from the
model* (the minted select walks the variable's assigned chain and
aliases, evaluating the chain's indices and values under the same model);
the sort default remains the last resort for points not even the chains
reach, and the replay still has the final word.

Regressions for 2–3: `nixie-solver/tests/array_model_chain_walk.rs`
(alias walks at both ends; the self-referential shape's point readings).

## Measured impact

* `tla_bmc` full corpus (318 specs, depth 4): verdicts **byte-identical**
  before/after, replay tally identical (68 clean / 21 violations — 19
  replayed, 1 not decodable, 1 decoded-not-replayed / 4 undecided). The
  corpus never reaches the new paths; the fixes land on the multiprocess
  PlusCal shapes and the solver-level false-`sat` class.
* The two-array pipeline pin (`a_two_array_pluscal_spec_never_answers_a_
  false_clean`) moves from `Violation{4}` + `NotReplayed` to
  `Violation{4}` + **`Replayed`** — the arc's success criterion.
* DiningPhilosophers `ExclusiveAccess` NP=2: depth ≤ 6 completes clean
  (TLC agrees the property holds); a deliberately false invariant
  decodes a 0-step counterexample, with the documented honest replay
  decline on the free-`Nat` `ASSUME`. Depths 7–8 remain the standing
  capacity wall (unchanged).
* Full bar: 12,353 workspace tests; Z3 parity 100 % (0 decisive
  mismatches, z3 4.16.0); perf gate PASS (conflicts 1.000, decisions
  1.000, wall 1.00); clippy/fmt/doc clean.
