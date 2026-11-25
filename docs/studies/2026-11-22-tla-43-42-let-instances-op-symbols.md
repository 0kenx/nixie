# Issue #43 + #42: LET-level INSTANCE, operator-symbol parameters, and the shared-DAG rewrite bugs they exposed

**Date:** 2026-11-22
**Issues:** #43 (lowering remainders), #42 (stdlib remainders)
**Landed from:** worktree `tla-43-remainders`

## What landed

### Issue #43 – the two named remainders

1. **`INSTANCE` inside `LET`** (test59.tla). Three pieces:
   - The loader (`Module::instantiated`) now walks *expressions*, not just
     top-level units, so a `LET M == INSTANCE A` target is loaded. The walk
     is an explicit worklist over the new exhaustive `Expr::subexprs()`
     (nixie-tla-syntax), and `WITH` substitution expressions are walked too.
   - The lowerer registers a LET-scoped `ModuleDef` unit into `instances`
     with save/restore on `PopLetDefs` – a module-level instance of the
     same name is shadowed for the extent and restored after, exactly as a
     LET definition is.
   - A missing target is a hard error at the instance, not a name error at
     the use.
2. **Operator-symbol parameters applied infix** (test42.tla).
   `Foo(a, _--_) == a -- 0` now resolves the infix application through the
   scope binding first (a `Binding::Op` inlines the passed operator; a
   `Binding::BuiltinOp` lowers through the infix table), before the
   module-level symbol-definition check. Scope wins over a module-level
   definition of the same spelling – the rule named parameters already
   follow.

### The deeper root cause the pieces exposed (fixed in the same landing)

Test59's LET binds `x == y+1`, and test59a declares `VARIABLE x`. The
implicit substitution of test59a's `x` must be that same-named LET
definition – but `push_instance_body`'s implicit path minted a **free
kernel variable** for any name it could not resolve, silently reading a
wrong-namespace unconstrained symbol (the exact "silently read the wrong
module's symbol" class). Implicit substitution is now resolved through a
fixed ladder (`resolve_implicit`): enclosing instance substitution →
`.cfg`-pinned constant → visible nullary definition (module- or
LET-scoped) → visible function definition → a declaration of the
instantiating module's closure → **hard error**. Each instantiation
records its declaring module for the declaration check.

Paxos.tla then exposed a **latent shared-DAG bug in the skolem pass**, present on main independent of this issue (main's corpus run fails test211 with "the binder `C#16` occurs more than once"):

- The pass had no Visit memoisation, so a shared subterm containing a
  rewrite was re-rewritten once per occurrence, minting N copies with
  identical binder names.
- `rename_var` had no pointer memo and no unchanged-shortcut, so the
  skolem arm's body copy un-shared the DAG with the same effect.
- The first fix attempt used `rename_var` to "refresh" binders – wrong
  tool: it renames *occurrences* and leaves binder *fields* verbatim
  (`rebuild`'s `var: var.clone()`), detaching occurrences from their
  binders while keeping the collision. The landing adds a true
  α-rename (`alpha_rename`: binder fields and occurrences move together,
  pointer-memoised, unchanged subtrees keep their original `Rc`) and one
  shared name counter per top-level pass (`%`-names, a spelling the
  lowerer never mints), applied at the rewrite arms and at every rebuilt
  binder-carrying node.

### Issue #42 – the three named remainders

1. **`SetAsFun` encode**: `native_set_of` now reifies structural members
   (tuples/records → the datatypes the sorts module already gives them)
   instead of declining, which is the same reification the
   function-constructor arm applies to its keys. The ignored test's two
   claims (`SetAsFun({…})["a"] = 1`, `DOMAIN … = {"a","b"}`) are
   assertions again, plus a wrong-value control.
2. **`FunAsSeq`**: lowered to `Opaque("FunAsSeq", [f, len])` and encoded
   as a **window** (offset 0, length `len`) over the function's own
   array – `s[i]` reads `f[i]` exactly, reads past `len` are dead, and
   `len` may be symbolic (better than Apalache, whose encoding needs a
   literal capacity; ours takes the capacity as an inert hint). The
   evaluator replays it as the `1..len` prefix tuple.
3. **Community-module fold rewiring**: `FoldSet`/`FoldSeq`
   (FiniteSetsExt/SequencesExt) are the kernel folds with the operator
   parameters bound the other way around (they accumulate on the
   **right**: `op(x, acc)`); `FoldFunction`/`FoldFunctionOnSet`
   (Functions) are set folds over the indices whose body reads
   `op(f[x], acc)`, with the collection `DOMAIN f` or the given index
   set. The `ApaFoldSet` AC audit still guards the set folds.

## Corpus A/B (bmccheck, depth 4, 20 000 conflicts, list mode)

Main HEAD `493ef13c` vs this landing, full 905-module corpus (tlaplus-examples + apalache), byte-diff of per-spec verdicts:

- `test42.tla`: blocked (`--` has no encoding) → **no-violation**
- `test59.tla`: blocked (no `INSTANCE` in scope) → **no-violation**
- `test211.tla`: blocked *lowering* ("binder `C#16` occurs more than
  once" – the latent DAG bug, already broken on main) → blocked at the
  later *state sort* stage (`Set([cnum: Int, ..])` has no SMT sort yet):
  the lowering is repaired, the remaining decline is honest and names the
  actual gap.
- Every other spec: byte-identical verdict and cause.

Apalache 0.63.0 oracle on the two issue files (with the type annotations
it requires): test59 `NoError`, test42 `NoError` – nixie agrees on both.

## Layers examined (the causal chain, per AGENTS.md principle 2)

1. Parser: `M == INSTANCE M'` inside LET parses as `ModuleDef` (was:
   silently dropped in the LET handler) – fixed at the LET arm.
2. Loader: `instantiated()` missed expression-level INSTANCE targets –
   fixed with the subexpression walk.
3. Lowerer name resolution: LET-scoped instances invisible – fixed with
   save/restore registration.
4. Lowerer substitution: implicit substitution fabricated free variables –
   fixed with the resolution ladder + hard error.
5. Skolem pass: no memoisation + un-sharing rename_var + binder-field
   renaming gap – fixed with (ptr, polarity) memo, pointer-memoised
   rename_var, true α-rename at both copy sites.
6. Encoder: tuple members in `native_set_of`, no `FunAsSeq` window –
   fixed in `encode.rs`.
7. Evaluator: no `FunAsSeq` replay – fixed in `eval.rs`.
8. Sort plumbing: `FunAsSeq` nodes added to `collect_unsortable` so the
   inferred `Seq(a)` reaches the encoder.

### Issue #41 – the two named remainders (landed in the same worktree)

1. **Field-access vs annotation merge**: `f["b"]` against a settled
   `@type: Str -> Int` annotation now applies the *function* – the
   inference's `apply` rule checks the subject's resolved top first, and a
   subject already settled as `Fun` (by an annotation or an earlier
   functional application) never takes the open-record preference that
   produced the unsortable hybrid. The preference itself is untouched for
   unsettled subjects (unannotated heterogeneous records still type). The
   pinned refusal test now asserts Apalache's settled shape, plus a
   wrong-value control and an unannotated-preference control.
2. **Operator-signature checking**: `(a, b) => c` annotations are parsed
   (`parse_signature1`) and **checked** – the operator's body is lowered in
   a throwaway lowerer, its parameters assumed at the annotated types, the
   body's inferred result unified with the annotation's result. A wrong
   signature, a wrong arity, or a signature naming nothing is a type error
   (exit 120); the "not checked yet" note is gone. This exposed and fixed
   an **attribution defect in the attach pass**: an annotation inside a
   definition body bound to the next *module-level* unit
   (NestedCallByName's `LET F` signature landed on `Init`); the attach pass
   now anchors `LET` definitions too (iterative walk over the new
   `Expr::subexprs`), records the bound declaration's offset on the
   `Annotation`, and the check resolves the operator at that offset
   (`operator_at`), module-level or `LET`-scoped.

## Verification summary (final)

- `cargo nextest run --release --workspace --all-features`:
  **12 906 / 12 908**. The two failures
  (`nixie-solver::finite_sets_cardinality::choose_of_ite_picks_the_taken_branch`,
  `nixie-solver::upstream034_model_interfaces::rejected_set_synthesis_cannot_publish_identical_choices`)
  are **pre-existing at the base commit** – `nixie-solver` does not depend
  on any crate this landing touches (`cargo tree` verified), and the
  failures reproduce from the base tree before these changes.
- `cargo clippy --release --all-features --all-targets -- -D warnings`,
  `cargo fmt --all -- --check`, `cargo doc` with `RUSTDOCFLAGS=-D
  warnings`: clean.
- **Apalache verdict parity** (pinned 0.63.0, 123 cells): 21 Agree-Ok +
  7 Agree-Viol vs the main arm's 20 + 7 on the same cells – `Fix531.tla`
  newly agrees (the SetAsFun/FunAsSeq work), `FunExcept2.tla` moves from a
  sort Declined to an honest solver Unknown (it now *encodes*; main cannot
  reach the solver on it at all). No cell regressed.
- **Corpus BMC A/B** (905 modules, list mode, byte-diff): **no-violation
  67→69, violation 20→20, undecided 20→20, blocked 210→208** – test42 and
  test59 blocked→no-violation; test211's lowering repaired (main fails it
  with the binder-collision error; this tree declines honestly at the
  state-sort stage). The remaining hunks are blocked↔blocked *cause* moves,
  each spot-checked by hand: Bug20201118 and View keep main's verdicts
  (two bugs in the first cut of the signature check – a `TyId` arena leak
  across probe inferences, and unparenthesised single-parameter signatures
  `P => Bool` – are what they exposed); CigaretteSmokersTyped,
  ConstantOperatorImpl and SlidingPuzzlesTyped parse their higher-order
  signatures (`(Set(T), (T) => Bool) => T`) and decline at exactly main's
  cause; Bug20190118 now reaches the `Variant` encode gap (issue #17's
  feature) instead of a sort refusal; PascalTriangle/test25 reach deeper
  encode stages. A signature on an operator this module does not define
  (an `INSTANCE` member substituted by `WITH`) is named in a note and
  skipped, not failed.

## Reproducing

```bash
NIXIE_TLA_LIB=../temp/apalache/test/tla cargo run --release -p nixie-tla-check --example bmccheck -- \
  ../temp/apalache/test/tlaplus-suite/test59.tla ../temp/apalache/test/tlaplus-suite/test42.tla
```
