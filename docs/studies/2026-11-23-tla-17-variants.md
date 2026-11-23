# Issue #17: variant types — rows, datatype encoding, aliases

**Date:** 2026-11-23
**Issue:** #17 (Variant, VariantFilter, VariantTag, VariantGetUnsafe/OrElse)
**Landed from:** worktree `tla-17-variants`

## What landed

The complete variant type system, end to end:

- **Rows**: `Ty::Variant { tags, tail }` reusing the record row algebra via
  a kind-parameterised `unify_rows_as` (the row algebra is shared; the
  constructor merged rows are rebuilt with is *not* — a merged variant row
  that came back as a record would unify with records, the exact confusion
  the issue's soundness note forbids). **A variant never unifies with a
  record or a function**: a dedicated decompose arm refuses it, pinned by a
  test.
- **Kernel nodes** for the five operators, `children`/`rebuild` wired so the
  closed-kernel invariant keeps working (adding a node without extending
  the walks stops compilation — that fired four times here, each a real
  site).
- **Lowering** intercepts the five operators where the application *looks
  like* the typed one — a string-literal tag and the matching arity; a
  computed tag is refused by name (`folds_here`'s rule: a local definition
  that does not look like the builtin keeps its own meaning).
- **Sorts**: a closed row is a **multi-constructor datatype**, one
  constructor per tag with one `@vp` payload selector; an open row closes
  at the tags inference found — sound here because a variant value can only
  come from a `Variant` node whose tag the row would then have absorbed;
  the row *is* its connected component.
- **Encoding**: `Variant` is the constructor application (payload reified
  at the tag's sort); `VariantTag` a tester chain; `VariantGetUnsafe` the
  datatype selector — **on the wrong tag it is underspecified by the
  theory, which is exactly the "fresh unconstrained value, never a fixed
  default" the issue asks for**; `VariantGetOrElse` an `ite` on the tester;
  `VariantFilter` a filter+map over the base's candidates under the tag's
  tester.
- **Evaluator + values**: `Value::Variant(tag, payload)`, all five
  operators evaluated (`VariantGetUnsafe` on the wrong tag **refuses**
  rather than inventing a value — a replay hinging on an invented value is
  not a replay).
- **Trace decoding**: the model's constructor names the tag; the payload
  decodes through the constructor argument or the `@vp` selector with
  testers for the no-constructor case. Violations read back and report.
- **ITF**: the `{"tag": …, "value": …}` shape.
- **`@typeAlias`**: the loader collects `@typeAlias: NAME = TYPE;` comments;
  the type grammar grows `Tag(payload) | Tag2(payload2)` arms and a
  **trailing row variable** in record annotations
  (`{ from: Str, term: Int, a }`, Bug1682's own spelling); `@type:
  Set(NAME)` seeds the resolved row (`assume_with_aliases`, aliases
  resolved recursively with a depth bound).
- **Frames integration** (with #20's candidate universes): the frame's
  `VariantFilter` element reading wraps base candidates in the tag's
  getter, so a binder over a filtered set ranges over concrete payload
  terms; frame elements are built **at the variable's merged-row sort** —
  left at their own, the universe would hold members of several one-tag
  datatypes the set's element sort cannot hold.

## Verified

- `nixie-tla-check/tests/variants.rs` (7 tests): the operators round-trip;
  heterogeneous payloads share one set; variant↔record/function refused;
  the alias closes the row and the framed checks run; a filtered violation
  is found; a computed tag refused; `UNIT`.
- All tla crates: 380/380 (one pre-existing test updated: a comprehension
  over a symbolic base used to *decline*; with #20's frames it now checks
  to the correct verdict — the test's own comment said "the frames work is
  what unblocks those").
- clippy/fmt/doc clean.
- Self-contained acceptance-shaped specs (A3/A5: three tags, two payload
  shapes, a framed set variable, filters and gets) check to `NoError`; the
  wrong-payload invariant reports `Error` with a variant trace.

## The named remainder

**Bug1682 itself still declines at the frame-materialisation step.** The
specification types, lowers and frames — the remaining failure is that one
`MkAppendEntries`-family frame element (whose payload reads
`currentTerm[s]`) reaches the encoder through a path where its node sort is
not yet declared, poisoning the frame; the pre-frames decline comes back
honestly. Paxos's shape (`--length=5 --inv=Inv`) exercises the same
interaction plus the `V!`-prefixed instance members. Both are one
investigation away — the failure is named, reproduced
(`/tmp`-scratch `A5` + a function-read payload), and not papered over.

Bug20190118, which the previous session left declining at
"`Variant` has no encoding yet", now declines *later* — the variant
encodes, and the remaining gap is the trace-side interaction above.
