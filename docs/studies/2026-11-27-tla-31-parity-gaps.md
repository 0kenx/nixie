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
decline, an `Unknown` or a mismatch. (The second pass, below, continues
both columns: 129 agreements, OracleFailed 44 – 47 of the 72 above were
not the oracle's crashes but its usage banner, a harness artifact.) The 15 cells that moved are listed in
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
  enclosing operator's parameters. With the fix (`10bf7e56`) the module
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

## Second pass (the same day): the next tier

Seven commits on top of the first pass's, each a class the declined list
names:

* **Dead code, two items** (`theories, sat`): `attach_definition_truths_to`
  is called from `nlsat` alone and that module is behind a feature the TLA
  crates' dependency edge does not enable; `set_last_blocker` is
  `cfg(test)`-only and its one user is a test module behind `bcp-work`.
  Both carry their users' `cfg` now – nothing deleted, and
  `cargo check --workspace --all-targets` under the default features
  reports no dead code.
* **An operator constant substituted by an operator through `INSTANCE`**
  (`ConstantOperatorImpl`, a cell whose real oracle answer the re-run gave
  the first pass: `NoError`). `WITH AreGood <- Equal` made every
  `AreGood(a, b)` inside the module an opaque constant. An instance context
  carries operator substitutions beside value ones now; a defined operator,
  an operator parameter or a `LAMBDA`, at the declared arity.
* **`\E delta \in Nat \ {0}`** (`FoldExcept.tla`, two cells) is
  skolemized as `\E delta \in Nat` is, and – the half the first test
  found, with its invariants accidentally the wrong way round – the
  **replay** reads the witness's membership structurally too: a correct
  counterexample came back `Unknown` while the evaluator tried to
  materialise `Nat \ {0}`. Both cells: declined for `Nat` as a value, now
  encoded and `Unknown` on the 6-step query.
* **`2^100`** (a ground base and exponent) is one literal, the
  evaluator's own; `2^256` (`SafeMath`, two cells) stays declined with a
  truer reason: the replay's integers are 128-bit. Arbitrary-precision
  replay is the piece those two need.
* **`x \in SUBSET Int`** is `TRUE` (`FunInInfiniteSubset`: `NoError`, as
  the oracle).
* **A fold whose step writes the accumulator at the element's own key**
  (`![p, q]` with `p == pair[1]`, `q == pair[2]` over `Proc \X Proc`) is
  order-free, as the single-key form already was (`MC_FoldExcept3`, two
  cells: declined for a "non-commutative" fold, now `Unknown` on the 6-step
  query). A key naming only some components still declines.
* **A record written `[a: Int, b: Str]`** in a type annotation –
  Apalache's second spelling of one, which the reader lacked; found by
  the corpus A/B below, the one module that moved backwards.
* **An `INSTANCE` of a built-in module** (`INSTANCE Apalache`, `LOCAL
  INSTANCE Bags` inside the community `BagsExt`) resolves its members by
  name instead of refusing the specification. The two cells move on to what
  the community modules themselves lack: `SortSeq` has no TLA+ definition
  (TLC implements it in Java, Apalache's `__rewire_sequences_ext_in_apalache`
  defines it). The drop-in needs the oracle's rewire modules.

### Parity after the second pass

The same harness, four shards, on a machine at load 40–85:

| class | first pass | second pass |
|---|---:|---:|
| Agree-Ok | 75 | **88** |
| Agree-Violation | 26 | 27 |
| Agree-Violation-Shorter | 5 | 5 |
| Agree-Refused | 3 | 9 |
| Declined | 43 | 45 |
| Inconclusive | 31 | 37 |
| OracleFailed | 72 | **44** |
| **MISMATCH** | **0** | **0** |

129 verdict agreements against 109. **No cell moved backwards.** And most
of the movement is the oracle's, not Nixie's – the finding of this pass:

#### 47 stored oracle answers were the oracle's usage banner

The worktree for this pass was created without the symlink to the oracle's
store, so the harness – believing the store empty – re-ran the oracle on
every cell, against its own rule. Reading the fresh answers against the
stored ones: on the 204 cells whose stored answer was a real verdict they
were identical, cell for cell. On 47 the stored answer was not a verdict
at all but `apalache-mc [options] command …`, exit 1: the CLI refusing a
malformed argv, printed when those cells were first run under the two
harness bugs fixed on 2026-11-26 (an empty options field collapsing so
that the exit code landed in the spec's place; a multi-option cell
misread). The fix corrected every later invocation, but a stored answer is
never re-run, and the exception the methodology makes for "a cell the
harness kept the oracle from running" had been applied to one cell only.
For a day the tables said "OracleFailed (72): unchanged in nature – the
oracle's crash on its own cells", and nobody had opened the files.

Given a real question, the oracle answers `NoError` on 19 of the 47,
`Error` on 3, refuses 14, and crashes on 11 (the genuine count). Against
those 47: Agree-Ok 11, Agree-Violation 1, Agree-Refused 6, Inconclusive 4,
Declined 6, OracleFailed 19. The 47 old entries sit beside the first pass's
eight in `tla_parity_artifacts_20261127`; the store holds the fixed
harness's answers.

A smaller lesson from the same run: the binary was rebuilt into the
harness's path while four shards were spawning it, and the five cells
whose Nixie lasso is one step shorter than the oracle's lost that lasso
line and were counted plain `Agree-Violation`; re-run clean, they are
`Agree-Violation-Shorter` again.

### Gates (second pass)

* Workspace `cargo clippy --all-features --all-targets -- -D warnings`,
  `cargo fmt --all -- --check`, `cargo doc --no-deps --all-features`: clean;
  `cargo check --workspace --all-targets` under the default features: no
  dead code.
* TLA crates, 721 tests: **720 pass**, 1 times out (the same PlusCal check),
  1 skipped.
* New tests: `instance` (+2), `skolem`, `encode` (`2^100`),
  `functions` (`SUBSET Int`), `folds` (the tuple key, with a control).
### Corpus A/B (second pass)

The same recipe and the same baseline logs as the first pass's (`main` @
`9b3982d7`, reproducing 81 / 21 / 7 / 58 / 275 / 465), both passes over
the 907 modules:

| | no-violation | violation | deadlock | undecided | blocked | skipped |
|---|---:|---:|---:|---:|---:|---:|
| baseline | 81 | 21 | 7 | 58 | 275 | 465 |
| both passes | **84** | 21 | 7 | 58 | **271** | 465 |

* The first pass's two (`TestAnnotations` clean, `Test1182` `undecided`),
  this pass's `ConstantOperatorImpl`, and `tlaplus-examples`'
  `TwoPhase/MCTwoPhase.tla`: `INSTANCE TwoPhase`, with `TwoPhase`'s
  `CONSTANT XInit(_), XAct(_, _, _)` substituted implicitly by the
  same-named operators – "does not lower to the kernel" before, checked
  clean now.
* **Zero verdict regressions – after one was found and fixed.** The first
  binary of this pass failed `ewd998/AsyncTerminationDetection.tla`'s type
  checker: its alias is a record written `[ … ]`, a spelling the
  annotation reader did not have, and the first pass had just made an
  unparseable alias a reported error (as Apalache does). Read now
  (the commit that reads it – "a record in a type annotation may be written
  `[a: Int, b: Str]`"); the module type-checks and lowers again, and its class
  under the harness is `undecided` once more, as on the baseline (re-run
  with the final binary, 200 s). The table above counts it so.
* Eight `blocked` modules state a later refusal than before – an annotation
  read, an operator substituted – all within `blocked`.

### What the "single value is needed" cells are

Six cells – `pr.tla`, `Test1226`, `Paxos`'s `Inv`, `TestBags`, `Bug540`,
`MC_LamportMutexTyped` – refuse with "a set / a function where a single
value is needed", and they are one feature: a function appearing **as a
value inside another structure**. `\E po \in [Nodes -> [Nodes ->
BOOLEAN]]` quantifies over a function set; `SetAsFun({<<SetAsFun(…), "x">>})`
and `BagUnion({A1, A2})` put functions in tuples and sets. A function is a
domain and a graph here, so it has no one term; giving it one (a datatype
pair, read back through selectors, with `eq_values`' extensional equality
kept) is an encoder change of its own, not a reading to add.

### `Gen`: the recipe, not the change

`Gen(n)` is three cells (`Bug2973` ×2, `Bug3158`). The oracle's `GenRule`
generates an arbitrary value of the result type within a size bound: for a
scalar exactly a fresh constant, which would be sound and exact here; for
sets and functions the bound is part of the meaning, and an unconstrained
set or array over-approximates it. A scalar-only rule needs the node's
inferred type, so it belongs after inference (rewrite `Opaque("Gen", [n])`
of scalar type to a fresh free constant there); compound types keep
declining by name.

## Remaining, by size (after both passes)

* **#20's heartland** – 9 cells "a set-valued term with no candidate list to
  enumerate" (`SUBSET (1..N)` as a quantifier's domain, `\E x \in v`,
  `letpoly`) and 6 "a set / a function where a single value is needed":
  functions as values inside other structures (above).
* **Solver capacity** – the 37 `Inconclusive`: `HandshakeWithTypes` ×5,
  `Invariants` ×4 (`Unknown` at the 0-step query), `y2k_instance` ×2,
  `NoLoopsNoProblems` ×2 (the `Range` family #29 records), `MC_FoldExcept3`
  ×2, `FunExcept` ×3, `PickPerf` ×2, and one each on eleven others; #50's
  integer witnesses.
* **The oracle's rewire modules** – the community modules' TLC-overridden
  operators (`SortSeq`, …) have no TLA+ definition; Apalache ships
  `__rewire_*_in_apalache` with them defined and annotated. `TestSequencesExt`,
  `TestBagsExt`, `TestFiniteSetsExt`, `TestSequences` (`\o` with a symbolic
  right side), and `TestCommunityFunctions`' type mismatch all wait on it.
* **Features, one cell or two each:** trace invariants (`Invariants.tla`),
  `Int` as a function domain (`InfDomFun`: `[i \in Int |-> 0]`), `Gen` (3,
  the recipe above), `^` with a result past 128 bits (`SafeMath` ×2:
  arbitrary-precision replay) or a symbolic exponent (`Bug1136`), a bare
  `LAMBDA` in the community folds, `[S -> T]` as a value (`OracleFunSet`,
  `test1`, `EmptyFunctionSet`, `Bug2772`), `$CaseNoMatch`, `BagAdd`.
* **Deliberate:** recursion and self-reference (6 cells), a non-AC fold with
  a non-injective key, `--timeout-smt`.
* **#48** unbounded liveness, **#50**, **#51** (a decision), **#30**
  (deferred by design): untouched.
