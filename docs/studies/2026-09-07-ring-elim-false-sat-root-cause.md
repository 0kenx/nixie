# The ring-elimination false-`sat`: the full causal chain (four layers)

**Date:** 2026-09-07 (follow-up to stage 4, which found the bug)
**Landing commit for the proximate fix:** stage 4 (`4926f73` lineage).
**This note documents the deeper layers and lands the layer-4 fix.**

The question asked after stage 4: *is the linearity gate the root cause, or
a symptom patch?*  Answer: the gate fixes layer 1 of a four-layer chain,
and the layer that actually let the bug reach users as `sat` – rather than
degrading to `Unknown` – is layer 4, fixed here.

## The chain, with the reproduction of each layer

Reproduced by reverting the linearity gate on the fixed tree and running
the parity-obstruction goal (`3n+3n²+1 = y ∧ y = 4`, unsatisfiable because
`n(n+1)` is always even; z3: `unsat`) through the eager dispatch
(`NIXIE_BV_DISPATCH_UNIFIED=0`, `NIXIE_GATE_TRACE=1`):

```
[gate] assertion TermId(10) UNDETERMINED under the model -> PASSES (fail-open)
[gate] assertion TermId(12) UNDETERMINED under the model -> PASSES (fail-open)
sat
(model (define-fun n () ... #b00000000) (define-fun y () ... #b00000100))
```

1. **Missing domain concept in the polynomial IR** (proximate; fixed in
   stage 4).  `Mono { coeff, factors }` cannot express "the degree of `v`
   in this equation", so the eliminator treated the monomial `3·n` of
   `3n + 3n² = 3` as making the equation *solvable for `n`*, emitted the
   self-referential pseudo-definition `n = 3⁻¹(3 − 3n²)`, and dropped the
   equation.  One-point elimination is sound exactly when the definition
   is `v`-free; that invariant lived in a prose comment ("the equation is
   *equivalent* to..."), not in the code.  **Fix:** the linearity gate –
   the eliminated variable must occur in no other monomial of its
   equation.  (Occurrences in *other* assertions, linear or not, are
   fine: `c·v + P(others) = 0` with `c` odd makes `v` a function of the
   others, and substituting a function is theorem-preserving at any
   occurrence shape.)
2. **Assertion-set collapse.**  Drop + substitute left zero assertions;
   the embedded solve of the empty set is trivially `sat`.
3. **Disabled defense #1 – model reconstruction.**  The eliminated `n`'s
   "definition" is self-referential; reconstruction cannot evaluate it;
   the model ships with `n` unset (printed as the sort default `0`).
4. **Disabled defense #2 – the honesty gate fails open.** *This is the
   deeper root cause of the false `sat` reaching users.*
   `model_refutes_assertions` is a **refutation** gate: it returns `true`
   only on `Bool(false)`/`Unrepresentable`; **`Undetermined` passes**.
   Both assertions evaluated `Undetermined` under the incomplete model,
   the gate passed them, and the dispatch – for which this gate was the
   *sole* `Sat` decider – answered `sat` with a model violating its own
   assertions (`3·0+3·0+1 = 1 ≠ 4 = y`).  That violates the repo's own
   stated rule: *a model you cannot concretely verify yields `Unknown`,
   never `Sat`.*

A fifth, structural observation: the regression test that enshrined the
bug (`ring_solve_eqs_model_regression`) was written from the solver's
output ("sat" with a model) rather than from semantics – the parity
obstruction *looks* like a solvable Diophantine and the author's comment
assumed satisfiability.  Oracles must be independent of the
implementation under test.

## The layer-4 fix landed here

`Solver::model_certifies_assertions` – a **certificate** gate for the
dispatch's `Sat` exit:

- every assertion must re-derive to `true` **from the model's values**
  (`eval_in_model_outcome`), with the same `And`-spine flattening as the
  refutation gate but *never* the SAT core's committed-polarity shortcut
  (a certificate that trusts the thing it is meant to double-check is no
  certificate – the committed-polarity channel is precisely how a holed
  model still passed the general path's variant);
- anything else – `false`, `Unrepresentable`, **`Undetermined`** – means
  "cannot honestly report `Sat` from this model", and the dispatch
  **declines** (`return None`), falling back to the general CDCL(T) path
  exactly like its other cannot-decide failure modes.

The refutation gate's fail-open semantics are deliberately **kept** for
the general path (model blocking, equality graph): there it is a
best-effort blocker among several nets, and legitimate partial-evaluation
domains (algebraic values, interface atoms) would make fail-closed there
both wrong and costly.  The certificate is required exactly where one
gate is the whole story.

`certificate_gate_rejects_unevaluatable_models` pins the semantic
difference: an asserted-but-unmodelled goal is refuted by *neither* gate
and certified by *neither* – so the old dispatch would have printed a
model, and the new one declines.

## Why this class cannot recur as a silent false `sat` (defense in depth)

| layer | net | now |
|---|---|---|
| 1 | eliminator emits only `v`-free definitions | linearity gate (stage 4) |
| 2 | empty-after-elimination is legitimate only with genuine definitions | follows from 1 |
| 3 | reconstruction failure leaves the model incomplete | possible (future bugs) |
| 4 | incomplete model ⇒ no certificate ⇒ no `sat` from the dispatch | this landing |

A future layer-1/3 bug in any preprocessor pass now costs a slower
verdict (general-path re-solve), not a wrong one.

## Verification

Workspace 10689/10689; clippy/fmt/doc clean; Z3 parity 169/169 decisive;
300-file corpus sample vs `precompile/4926f73`: **0 verdict mismatches**
(1 new 35 s timeout under parallel load – wall-only, within the
run-to-run swing documented for this sample; verdicts unchanged).
