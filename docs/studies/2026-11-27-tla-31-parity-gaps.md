# Issue #31 – the parity gaps the corpus names: `:=`, the annotations, the temporal walk, and eight cells the harness hid

On `main` @ `cc6eb36e` the full 253-cell run of `bench/tla_apalache_parity`
stood at Agree-Ok 64, Agree-Violation 27, Agree-Refused 3, Declined 58,
Inconclusive 21, OracleFailed 80, MISMATCH 0. This records what the 58
declined and the 80 "oracle failed" cells were, what is fixed, and what the
same run says now:

| class | before | after |
|---|---:|---:|
| Agree-Ok | 64 | 75 |
| Agree-Violation | 27 | 26 |
| Agree-Violation-Shorter | – (counted as Agree-Violation) | 5 |
| Agree-Refused | 3 | 3 |
| Declined | 58 | 43 |
| Inconclusive | 21 | 31 |
| OracleFailed | 80 | 72 |
| **MISMATCH** | **0** | **0** |

109 verdict agreements against 94; no cell moved from an agreement to a
decline, an `Unknown` or a mismatch. The 15 cells that moved are listed in
`bench/tla_apalache_parity/METHODOLOGY.md` ("Standing result,
2026-11-27").

## Two soundness defects, found on the first cells

### Apalache's `:=` is an assignment, and it was lowered as `:>`

`FoldSetInInit.tla` refused with `(Set(Int) -> Set(Int)) and Bool cannot be
the same type`. The spec writes `values := S` in `Init` and `values' := S` in
`Next`; `Apalache.tla` defines the operator for TLC as `__x := __e == __x =
__e`, Apalache reads it as `ApalacheOper.assign` – typed `(a, a) => Bool`
(`ToEtcExpr.scala:854`), rewritten to `lhs = rhs` by
`VCGenerator.removeAssignments` – and the comment that "names an
assignment" in its own documentation.

The lowerer built a one-entry **function** from it, as from `:>`, and a test
pinned that reading (`("a" := 1)["a"] = 1`). Where the surrounding
conjunction had a single conjunct the type checker refused the
specification; where it had more, the assignment was replaced by an inert
term of function type and the state variable stayed **free** – and the
frame analysis never saw the assignment it was named after. The reproducer
in `apalache_stdlib.rs`:

```tla
Init == \E S \in SUBSET {1, 2}: /\ seen := S
Inv  == seen # {3}
```

`seen` is inside `{1, 2}` in every state, so the invariant holds; the old
binary refused the spec with `(Set(Int) -> '2) and Bool`, and with two
conjuncts it would have searched with `seen` unconstrained. `x := S` is
lowered to `x = S` now; a user's own definition of the operator still wins
(`test44.tla` defines `a := b == <<a, b>>`).

### `<<A>>_<<x, y>>` was read as `A /\ x' # x /\ y' # y`

`<<A>>_v` is `A /\ v' # v`, and for a tuple subscript that is *some*
component changing – the negation of `UNCHANGED <<x, y>>`. The fairness
pass's `changed` conjoined the components, so an action that moves one
variable was never "taken" on its own cycle. Enabled at every state of the
cycle and taken nowhere is a definition of a `WF` violation, so the lasso
was ruled out as unfair:

```tla
Tick == x' = 1 - x /\ y' = y
Step == x' = x /\ y' = 1 - y
Spec == Init /\ [][Tick \/ Step]_vars /\ WF_vars(Step)
```

`[](x = 1)` is violated by `(0,0) ->Step-> (0,1)` and Step's own two-cycle,
fair under `WF_vars(Step)`; the main binary answered **NoError at every
length**, this one Error at 2 (replayed). The usual `vars == <<x, y>>` is
the shape every spec writes, so every `WF_vars(A)` whose `A` moves a proper
subset of the variables was affected.

## The annotations the corpus writes

Twelve cells stopped at the type checker, each on an annotation the oracle
reads without remark.

* **`$name`** is a reference to the `@typeAlias` named `name` – Apalache's
  `aliasReference`, the sigil part of its `ConstT1` key. The tokenizer had
  no `$`: `MegaSpec1`, `Invariants`, `Test1182`, `MC_ERC20`,
  `MC3_TwoPhaseTyped` and `TestReqAckVariants` were refused. A reference no
  alias defines is a type constant of its own, `$name`, as it is there –
  never a parse error, never the type variable `name`.
* **`() => T`** is the signature of a zero-argument operator – how the
  corpus annotates a constant written as a definition (`\* @type: () =>
  Set(Int); Empty == {}`). The parameter list demanded one parameter
  (Bug1880, TestBags, EmptyFunctionSet).
* **One comment may hold several annotations.** `TestReqAckVariants.tla`
  annotates a variable with a block comment whose first line is the
  `@typeAlias:` definition and whose third is the variable's own `@type:`;
  read as one, the alias's text swallowed the `@type:` line and the variable
  lost its annotation without a word. The scan follows Apalache's
  `CommentPreprocessor`: an annotation runs from its `@name:` to the `;`
  that closes it, to the next annotation, or to the end; the `@` must follow
  whitespace or a `*`.
* **An annotation may span several `\\*` lines** (`MC_LamportMutexTyped`'s
  alias; `CommentedTypeAnnotation`'s type, `//` comments included): Sany
  hands Apalache a declaration's consecutive comment lines as one text and
  its type lexer skips `//` to the line's end. Adjacent one-line comments
  are scanned as one group now – and each annotation keeps the position of
  **the line it starts on**. The first version gave the group its first
  line's position, which bound a trailing comment on `msgs, \* …` and the
  next declaration's `\* @type: Int;` both to `msgs`: five specs
  (`HandshakeWithTypes` ×4, `Paxos`, `MC3_TwoPhase*`,
  `NeedForTypesWithTypes`) that had passed the type checker were refused
  until that was found. A test pins the interleaved shape.
* **A `LET` definition's annotation is checked, not seeded.** The name is
  inlined away and never reaches inference, so seeding it by name could only
  collide with another `LET` definition of the same name elsewhere:
  `TestBags.tla` annotates `EB == EmptyBag` as `Int -> Int` in one test and
  `Str -> Int` in another, and the second refused the specification. It is
  checked against its own body now, as a signature with no parameters.
* **An alias that does not parse is reported** (Apalache: `Parser error in
  type alias`), where it was dropped silently and every `$name` naming it
  read as an opaque type. This is what found the two comment shapes above:
  made loud, `TestReqAckVariants` and `MC_LamportMutexTyped` failed at once.
* **`Guess` and `Gen` type polymorphically per use.** They are never
  lowered, so each use reached the fallback that gives one operator one
  monomorphic signature per name: `TestSets.tla`'s `Guess({ i \in … })`
  fixed `Set(Int) => Int` and its `Guess({ T \in … })` – a set of sets –
  mismatched.

## The temporal walk

The tableau (`nixie_tla_check::temporal`) was general over nesting; the
walk that lowers a property to it read four shapes wrong, one cell each in
Apalache's suite, seven cells declined to exit 75 where the oracle gives
`NoError` or `Error`:

| shape | cell | what was wrong |
|---|---|---|
| `LET Plus(a,b) == a + b IN LET var1 == x IN []<>(…)` | `LetIn` | the definitions were out of scope for the leaves; the ordinary path lowered the `LET` and met the `<>` |
| `[](y < 1 \\/ <>(y = 1))`, `~<>[](x > 5)`, `x = 0 /\\ []TRUE` | `NestedTemporalInBool`, `NoTemporalOperatorsInTemporalProp` | the parser delivers `/\\` and `\\/` as infix operators; only a bulleted list was read as a propositional node |
| `<>(<<x' = x + 1>>_x)`, `<>[]([x' = x + 1]_x)` | `TemporalPropsOverActions` | an action operand was refused; it is a leaf the tableau reads on each step, where the box's and the diamond's equations live |
| `flag : Int -> Bool` with `--temporal` | `Bug2107` (three cells) | the lasso's `__saved_flag' = IF … THEN __saved_flag ELSE flag` – an `IF` over functions, which the encoder refused |

The `LET` scope is the ordinary lowering's own (`enter_let`/`exit_let`,
factored out of its stack machine), and a `LET`-bound definition of
temporal level (`LET T == [](x < 2) IN T /\\ …`) expands in the tableau as a
module-level one does – the level report knows module-level names only.
`[A]_v` lowers to `A \\/ UNCHANGED v` and `<<A>>_v` to `A /\\ v' # v`; an
action *beside* a temporal operator under a propositional node still
declines by name, because it would reach an `Init` equation, where a prime
means nothing.

For `Bug2107`: `IF c THEN f ELSE g` over functions has the domain `IF c THEN
DOMAIN f ELSE DOMAIN g` and the graph the same choice of graphs – exact,
since the value is `f` or `g` whole; an `IF` over two candidate-form sets is
the candidates of both, each present only where its side is chosen.

The 26 `--temporal` cells: **Agree-Ok 14, Agree-Violation 10, Inconclusive
2 (the `Range` timeouts #29 records), Declined 0, MISMATCH 0** – from 7, 7,
2, 10, 0.

### What the lengths say

With lasso lengths read (below), five cells have Nixie's counterexample one
step shorter than the oracle's: `LetIn` and `NestedTemporalInBool`
(`FalseLiveness`), and `BoxDiamond`, `LongLoops`, `ManyBoxes`, which had
been counted `Agree-Violation` without their lengths being compared. On
`LetIn`: `<>[](x + y = 2)` on the swap cycle `(0,1) ↔ (1,0)` is false on
every lasso; the shortest violating one is `(0,1) →Step→ (1,0) →Step→
(0,1)`, two steps, its cycle both states, replayed step by step. Its loop
starts one state after `Init`, so the oracle's `unroll@0 = TRUE` (fixed in
`TableauEncoder.auxVarInitEx`) contradicts its own step-0 equation there,
and it reports the violation one step later, rotated. That is the defect
the methodology already records (found while testing #47); these are its
reproducers, and the comparator now has a class for exactly this shape.

## The harness: eight cells it hid, and a length it never read

* **A spec's sibling modules did not come along.** Only a spec in a
  subdirectory received the other `.tla` files of its directory, and the
  corpus is flat. Eight cells ran without theirs – `MC3_TwoPhaseTyped`
  (`INSTANCE TwoPhaseTyped`), `MC3_TwoPhaseUFO`, `MC_LamportMutexTyped`,
  `MC_ERC20`, `y2k_cinit` and `y2k_instance` (both `EXTENDS y2k`),
  `ConstantOperatorImpl` – and the oracle's answer on all eight was its own
  parse error, `Cannot find source file for module …`, which the comparator
  reads as `Refused`: seven sat in `OracleFailed`, one in `Agree-Refused`,
  and **`y2k_instance` was listed as a known oracle defect on that
  evidence**. It is not one. The entries were set aside and the oracle
  re-run with the modules present: `NoError` on six, `Error` on `y2k_cinit`
  and on one `y2k_instance` cell. Against Nixie: 1 `Agree-Violation`, 2
  `Declined`, 5 `Inconclusive` (timeouts on the TwoPhase, ERC20 and `y2k`
  specs at length 3–30), 0 `MISMATCH`.
* **A lasso's length was never read.** The pattern for a counterexample's
  step count was anchored to `counterexample 1: N step(s)` at column 0, and
  a lasso's line is `  counterexample 1: a lasso of N step(s) …`, indented
  under the temporal pass. So `x_len` was empty on every temporal violation
  and no `--temporal` cell's length was compared – while the standing table
  said "lengths equal". It is read now; the one documented disagreement has
  its own class (`Agree-Violation-Shorter`: a `--temporal` cell, both
  `Error`, exactly one step shorter, the trace independently replayed), and
  anything else is a mismatch.

## Corpus A/B

The baseline binary (`main` @ `9b3982d7`) and this branch, each over the
907 modules of `tlaplus-examples` and `apalache`, depth 4, 20 000 conflicts,
`NIXIE_BMC_LIST=1`, four shards. The baseline reproduces the published
numbers exactly – no-violation 81, violation 21, deadlock 7, undecided 58,
blocked 275, skipped 465 – which is what makes the per-file diff worth
reading.

| | no-violation | violation | deadlock | undecided | blocked | skipped |
|---|---:|---:|---:|---:|---:|---:|
| baseline | 81 | 21 | 7 | 58 | 275 | 465 |
| this branch | **82** | 21 | 7 | 58 | **274** | 465 |

* `TestAnnotations.tla` passes the type checker and is checked clean;
  `Test1182.tla` passes it and is honestly `undecided`.
* **Zero verdict regressions:** no module that reached a verdict, a deadlock
  or `undecided` on the baseline is blocked, skipped or decided differently
  on this branch.
* Within `blocked`, seven modules changed their stated reason, all seven
  from "does not type check" to the encoder's own refusal – the annotations
  are read now (`deliver`, `EmptyFunctionSet`, `FoldSetInInit`,
  `LamportMutexTyped`, `MissionariesAndCannibalsTyped`, `TestBags`, and the
  one that now names `Gen`).
* **What the A/B found.** The session's first binary blocked
  `AsyncTerminationDetection.tla` at the type checker, where the baseline
  reaches `undecided`: the over-tight `LET` check of the annotations commit
  ("the shape of `d[2]` is ambiguous"), on a `LET` definition that reads the
  enclosing operator's parameters. With the fix (`8faa6c12`) the module
  passes the type checker again (`nixie-tla typecheck`: no errors), and its
  corpus re-run was still inside the solver when this was written – one
  process, 70 minutes in, on a machine at load 30–60. The six other modules
  the first binary had so blocked were re-run with the final binary: five
  fail the type checker as on the baseline, one (`MC_spanning`, through its
  `.cfg`) is blocked as on the baseline.

## Gates

* Workspace `cargo clippy --all-features --all-targets -- -D warnings`,
  `cargo fmt --all -- --check`, `cargo doc --no-deps`: clean.
* TLA crates, 712 tests: **711 pass**, 1 times out
  (`a_pluscal_bound_the_spec_cannot_exceed_holds`, the depth-8 PlusCal
  check: the same 600 s timeout on untouched `main` under the same load),
  1 skipped by the configuration.
* New tests: `annotations` (+6), `apalache_stdlib` (`:=`), `types`
  (`Guess`/`Gen`), `fairness` (the tuple subscript), `temporal_props` (5),
  `functions` (2), and `frames`' refusal test updated to the action operand
  it now reads.
* The machine carried a load of 20–45 from other work throughout; the one
  suite timeout (`a_pluscal_bound_the_spec_cannot_exceed_holds`, 600 s)
  times out the same on untouched `main` under the same load.

## Remaining, by size

* **#20's heartland** – 9 cells "a set-valued term with no candidate list to
  enumerate" (`SUBSET (1..N)` as a quantifier's domain, `\E x \in v`) and 6
  "a set / a function where a single value is needed" (the candidate
  representation under a place that needs one term).
* **Solver capacity** – the 31 `Inconclusive`: `HandshakeWithTypes`, the
  `y2k`/TwoPhase/ERC20 family at length, `Invariants` (4, `Unknown` at the
  0-step query), `FunExcept`, `PickPerf`; #50's integer witnesses, #29's
  four `Range` cells.
* **Features, one cell or two each:** trace invariants (`Invariants.tla`),
  `INSTANCE` of a built-in module (`TestSequencesExt`), an operator
  substituted through `INSTANCE` (`ConstantOperatorImpl`'s `AreGood`),
  `Int`/`Nat` as a value (4, #22), `^` with a large or symbolic exponent (3),
  a bare `LAMBDA` (2), `[S -> T]` as a value, `BagAdd`, `\o` with a symbolic
  right side.
* **`TestCommunityFunctions`** – a type mismatch (`Str` and `Int`) in the
  community `Functions` module, not yet run down.
* **#48** unbounded liveness, **#50**, **#51** (a decision), **#30**
  (deferred by design): untouched.
