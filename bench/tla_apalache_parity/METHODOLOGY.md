# TLA+ verdict parity vs Apalache – methodology

## What this measures

`nixie-tla`'s **verdicts** against the pinned Apalache oracle, on the
`check`/`simulate` cells of Apalache's own CLI integration suite. This is
the harness the tracking issue (#31) named as the measuring instrument for
"drop-in": same argv, same working directory, same exit code class, and –
for agreeing violations – equal counterexample length.

## The oracle

* Binary: apalache-mc **0.63.0**, from the nix store
  (`159k2slmq3qjwxmrawcxg6j4awj0yfq3-apalache-0.63.0`). The `apalache-mc`
  on PATH is 0.52.2 and predates the strict-JSON config – it is the wrong
  oracle and the runner does not use it. `APALACHE_BIN` overrides, for
  re-pinning only; a re-pin is a new store directory, not an edit.
* Source of the corpus: `cli-integration-tests.md` at
  `../temp/apalache/test/tla` (extracted into `corpus.json` by the
  extractor; regenerate only with the pinned version in hand, and record
  where it came from in the corpus header).
* Oracle results are stored once per cell under
  `precompile/apalache-0.63.0/benchmark/tla_parity/<cell-id>/` and never
  re-run. Where the mdx expectation and the pinned binary disagree, that is
  *oracle drift*: recorded as the binary's answer, with the mdx expectation
  kept in `corpus.json` for reference. The one exception: a cell the
  *harness* kept the oracle from running (a spec it could not find) is not
  an oracle result, and its store entry was deleted and re-run.

## Comparator (ported from `bench/z3_parity`)

| class | meaning |
|---|---|
| `Agree-Ok` | both `NoError`, or both `ExecutionsTooShort` |
| `Agree-Violation` | both `Error` (exit 12) with equal counterexample length; a difference is a `MISMATCH`. Both tools search lengths in increasing order, so each one's first counterexample is the shortest. An *action* invariant is counted from the transition Apalache names it at (`State N`) plus one, which is the step Nixie reports |
| `Agree-Deadlock` | both `Deadlock` |
| `Agree-Refused` | both refuse the cell with the same non-verdict exit code |
| `MISMATCH` | same cell, different verdict class |
| `Inconclusive` | `Unknown` or timeout (124) on either side |
| `Declined` | Nixie 75/120/150, or 255 with no outcome line (a refused option, a missing role): it could not evaluate the cell |
| `OracleFailed` | the pinned oracle gave no verdict (exit 1 is its crash on its own cells, 255 its configuration and type errors); never a match, and kept apart from `Inconclusive` because it is the drop-in superset's own count – the rows show where Nixie answers and the oracle does not |

`Inconclusive`, `Declined` and `OracleFailed` **never count as a match**
and are reported as separate counts. The run exits non-zero on any
`MISMATCH` or on zero compared cells.

## Running

```bash
bash bench/tla_apalache_parity/run_parity.sh
```

`MAX_CELLS` takes a deterministic prefix of the corpus (sorted as the mdx
orders it). `CELL_MATCH=<regex>` keeps the cells whose argv matches and
`CELL_IDS=a,b,…` those ids, for re-running a class of cells. The oracle arm
is cached after the first run, so later runs are Nixie-only in cost. Both
arms run under `taskset -c 0-7`. Scratch files are private to the run (two
concurrent runs once shared `/tmp/parity_tla_lines`, and the later one
truncated it under the earlier one's `read` loop, which stopped after 40
cells).

**In a worktree, link the store first**: `precompile/` is not tracked, so
a fresh worktree has none, and the harness would take the oracle's arm as
uncached and re-run it on every cell. It refuses to when the store holds
fewer than half the corpus's cells, unless `APALACHE_FRESH_STORE=1` says a
new store is meant (a re-pin). And never rebuild the Nixie binary into a
path a running harness is spawning it from: a cell launched during the
swap loses its output – on 2026-11-27 five cells lost their lasso line
that way and were classed without their length.

## Standing result (2026-11-27, second pass, all 253 cells)

The parity-gaps session's second pass (seven more commits; the study's
"Second pass"), pinned oracle 0.63.0, the oracle's store corrected (below),
every cell of the corpus, four concurrent runs of the harness on a machine
at load 40–85 from other work.

| class | count |
|---|---:|
| Agree-Ok | 88 |
| Agree-Violation | 27 |
| Agree-Violation-Shorter | 5 |
| Agree-Deadlock | 0 |
| Agree-Refused | 9 |
| Declined | 45 |
| Inconclusive | 37 |
| OracleFailed | 44 |
| **MISMATCH** | **0** |

* **129 verdict agreements, 0 mismatches** (109 in the first pass; 94 the
  morning before it). No cell moved from an agreement to a decline, an
  `Unknown` or a mismatch.
* **Most of the movement is the oracle's, not Nixie's**: 47 stored oracle
  answers were the oracle's usage banner – the malformed argv of a harness
  bug fixed on 2026-11-26 and never refreshed – and were re-run (below).
  Given a real question, the oracle answers `NoError` on 19 of the 47,
  `Error` on 3, refuses 14 (its type and configuration errors), and
  crashes on 11. Against those: Agree-Ok 11, Agree-Violation 1,
  Agree-Refused 6, Inconclusive 4 (`Unknown` or a timeout), Declined 6
  (the classes below), OracleFailed 19 (the crashes and refusals Nixie
  also declines or cannot reach). The same kind of finding as the first
  pass's eight, twice over.
* **Nixie's own movement, this pass:** `ConstantOperatorImpl` and
  `FunInInfiniteSubset` declined → `Agree-Ok`; `MC_FoldExcept3` (two cells)
  declined → `Unknown` (encoded, solver capacity).
* **Agree-Violation-Shorter (5):** unchanged – the oracle's tableau defect
  with its reproducers (below). (A run in which the binary was replaced on
  disk while the harness was spawning it lost Nixie's lasso line on those
  five and counted them plain `Agree-Violation`; re-run clean, they are
  `Shorter` again. Do not rebuild into a running harness's path.)
* **Declined (45):** the first pass's 43 minus `ConstantOperatorImpl`,
  `FunInInfiniteSubset` and `MC_FoldExcept3` ×2, plus six cells that
  became comparable with the corrected store and decline: `CaseNoOther`,
  `CaseNoOtherBool` (`$CaseNoMatch`), `OracleFunSet` and `test1` (a
  function set as a value), `Verifier_functionComparison` and `letpoly` (a
  symbolic set with no candidate list / a function as a value).
* **Inconclusive (37):** the first pass's 31 plus `MC_FoldExcept3` ×2
  (`Unknown`) and three cells newly compared that time out
  (`HandshakeWithTypes` ×2, `RecordExcept987`, `TestReqAckVariants`).
* **OracleFailed (44):** the oracle's own – 11 × exit 1 (its crash on its
  cells), 32 × a refusal (its configuration and type errors), 1 × exit 120.

### The 2026-11-27 standing, first pass

`main` @ `10bf7e56`, the last code commit of the parity-gaps session's
first pass (seven commits on `9b3982d7`'s code), pinned oracle 0.63.0,
every cell of the corpus: four concurrent runs of the harness over disjoint
cell ids (its scratch files are private to a run and the oracle's store was
complete), on a machine carrying a load of 20–45 from other work, so 14
cells timed out at 300 s.

| class | count |
|---|---:|
| Agree-Ok | 75 |
| Agree-Violation | 26 |
| Agree-Violation-Shorter | 5 |
| Agree-Deadlock | 0 |
| Agree-Refused | 3 |
| Declined | 43 |
| Inconclusive | 31 |
| OracleFailed | 72 |
| **MISMATCH** | **0** |

(The rows sum to 255: the corpus carries two cell ids twice.)

* **109 verdict agreements, 0 mismatches**, against 94 on `cc6eb36e` the
  same morning (Agree-Ok 64, Agree-Violation 27, Agree-Refused 3; Declined
  58, Inconclusive 21, OracleFailed 80). No cell moved from an agreement to
  a decline, an `Unknown` or a mismatch.
* **The 15 cells that moved.** Declined → `Agree-Ok`: `Bug1880`,
  `Bug2107` (three cells), `LetIn`'s `Liveness`, `MegaSpec1`,
  `NestedTemporalInBool`'s `Liveness`,
  `NoTemporalOperatorsInTemporalProp`'s `PropertyWithTemporal`,
  `TemporalPropsOverActions`' `Liveness`. Declined → `Agree-Violation`:
  `TemporalPropsOverActions`' `FalseLiveness`. Declined →
  `Agree-Violation-Shorter`: `LetIn`'s and `NestedTemporalInBool`'s
  `FalseLiveness`. Declined → `Inconclusive`: `Invariants` (four cells,
  now `Unknown` where the type checker refused them) and `Test1182` (a
  timeout). `Agree-Violation` → `Agree-Violation-Shorter`, their lengths
  read for the first time: `BoxDiamond`, `LongLoops`, `ManyBoxes`.
* **Agree-Violation-Shorter (5):** the oracle's tableau defect with its
  reproducers (below). Each of the five traces was replayed step by step
  and its loop close re-evaluated by the evaluator.
* **Declined (43), by what the checker named:** 9 a symbolic set with no
  candidate list (#20: `Test951`, `Bug1682`, `FoldSetInInit`, the three
  `Fix365_ExistsSubset`, `mis` ×2, `Test1425`); 6 "a set / a function where
  a single value is needed" (the candidate representation under a place
  that needs one term: `Paxos`, `pr`, `Test1226`, `TestBags`, `Bug540`,
  `MC_LamportMutexTyped`); 4 `Int`/`Nat` as a value (#22); 3 `Gen`
  (`Bug2973` ×2, `Bug3158`); 3 `^` (two exponents over the unfolding
  budget, one symbolic); 2 over the candidate budget of 4096; 2 a
  non-associative `ApaFoldSet` (declined on purpose, #13); 2 trace
  invariants (`Invariants.tla`'s `TraceInv` and `BuggyTraceInv`, a
  feature); 2 a bare `LAMBDA`; and one each: `BagAdd`, `AreGood` substituted
  through `INSTANCE`, a function set `[S -> T]`, `\o` with a non-literal
  right side, `UNION` of a non-set-of-sets, a set compared with a non-set,
  `INSTANCE Apalache` (the module is built in; an instance of it is not),
  a type mismatch (`TestCommunityFunctions`: `Str` and `Int`), an `Init`
  that is an action (`Slicer5`), and `--timeout-smt` (refused on
  principle).
* **Inconclusive (31):** 14 timeouts at 300 s (`HandshakeWithTypes` ×3,
  `y2k_instance` ×2, `NoLoopsNoProblems` ×2 – the `Range` family #29
  records – `MC_ERC20`, `MC3_TwoPhaseTyped`, `Test1182`, `SetSndRcv`,
  `SetAddDel`, `Consensus_epr`, `ast`) and 17 `Unknown` (`Invariants` ×4,
  `Counter` ×2, `FunExcept` ×3, `PickPerf` ×2, and one each on six
  others) – solver capacity (#20's remaining cells, #50), never a wrong
  verdict.
* **OracleFailed (72):** ~~unchanged in nature – the oracle's crash on its
  own cells (exit 1), its type and configuration errors~~ – **corrected the
  same day**: 47 of the exit-1 answers were the oracle's usage banner, a
  harness artifact (see "Fixed 2026-11-27" and the second pass), and the
  eight that were the harness's (above) had already been re-run.

### The 2026-11-26 standing

`main` @ `47b5c438`, pinned oracle 0.63.0, every cell of the corpus with
the harness above (multi-option cells and subdirectory specs included).

| class | count |
|---|---:|
| Agree-Ok | 61 |
| Agree-Violation | 27 |
| Agree-Deadlock | 0 |
| Declined | 101 |
| Inconclusive | 25 |
| OracleFailed | 39 |
| **MISMATCH** | **0** |

* **88 verdict agreements, 0 mismatches.** The standing on 2026-11-25 was
  3 agreements on the first 13 comparable cells.
* **OracleFailed (39):** 27 × exit 1, the oracle's crash on its own cells;
  11 × 255, its configuration and type errors; 1 × 120, its type checker.
  Nixie's answer on them, for the record: 25 NoError, 3 Error, 6 Unknown,
  5 timeouts. Where the corpus documents a verdict (24 cells), Nixie gives
  that verdict on 19 – `NoError` on 18 (`Counter.tla` variants,
  `NonNullaryLet`, `Callback`, `Deadlock712`, `Config.tla`,
  `letpoly_inst`, `Bug1058`, `Test1259`, `Test1623`, `TestRecordsNew`,
  `reorderTest --next=MayFail`) and `Error` on 1 (`Config1.cfg` with
  `--init=Init2 --next=Next2`) – and times out on 5. Where the corpus
  documents the oracle's own refusal (15 cells), Nixie answers on 10:
  `NoError` on 8 (`Bug593`, `Rec3`, `reorderTest --next=MustFail`,
  `ITE_CASE`, `ConfigUnsorted`, `Bug931`, `Test669`, `Test928`) and a
  **replayed counterexample on `Selections` and `ModelValFail`**, where the
  oracle refuses on types. Those 10 are the cells to read before calling
  the checker a superset of the oracle: a spec Apalache will not type,
  answered.
* **Declined (101):** 79 exit 75, 12 exit 120, 10 a refused option or a
  missing role.
* **Inconclusive (25):** 18 Nixie timeouts at 300 s, the rest `Unknown`.

### History

The 2026-11-25 standing (3 Agree-Ok, 7 Declined, 3 Inconclusive, 0
MISMATCH on the first 13 comparable cells of a 40-cell prefix) was computed
before the harness fixes below and is superseded.

## Harness defects, fixed 2026-11-26

* **Multi-option cells were skipped.** The cell line carried one
  tab-separated field per option, and `read` hands the *last* variable the
  remainder, so a cell with two or more options (`--length=5 --config=…`,
  `--config=… --inv=Inv …`) was read as a cell whose spec was its second
  option and skipped ("SKIP …: no --init=Init2"). Every cell the standing
  result was ever computed on had exactly one option. The options are one
  field now.
* **An empty options field collapsed** (`check Spec.tla`): a tab is IFS
  whitespace, so the exit code landed in `spec`. The separator is the ASCII
  unit separator.
* **`Unknown` was a `MISMATCH`**, where the table says `Inconclusive`
  (Fix365_ExistsSubset: `Unknown` on the 2-step successor query in the old
  and the new binary alike, scored against the oracle's NoError); two
  `TooShort` outcomes were a mismatch too; a Nixie 255 with no outcome
  (the refused `--timeout-smt`) was neither declined nor inconclusive.
* **The oracle's own failure was a `MISMATCH`** when Nixie answered.
* **A spec in a subdirectory was not found** by either tool
  (`antipatterns/fold-except/MC_FoldExcept3.tla`: copied to the top of the
  work directory, then missing along with the `FoldExcept.tla` it
  extends). Its two store entries were harness artifacts and were re-run.
* **A non-matching grep ended the script**: under `set -o pipefail` the
  command substitution that reads a counterexample length returned the
  grep's status when there was none to read.
* **The oracle's own refusal was still a `MISMATCH` when Nixie answered**
  (2026-11-27): the `OracleFailed` branch matched `Exit*` classes only, and
  the oracle's 255 with no outcome line – its type errors and documented
  refusals – reads `Refused`. Three cells (`Rec3.tla`, `reorderTest
  --next=MustFail`, `reorderTest --next=MayFail`) were counted mismatches
  on answers (`NoError`) this document lists as the superset's own. A
  `Refused` oracle arm is now `OracleFailed` (or `Agree-Refused` when both
  refuse), as the table says.
* **A cell's `.properties` file did not come along**: `reorderTest
  --next=MayFail` passes `--tuning-options-file=reorderTest.properties`,
  which the work directory never received, so the oracle's stored answer
  was its configuration error – a harness artifact, like `MC_FoldExcept3`'s
  above. The file is copied with the `.cfg`s now, the store entry was
  deleted and re-run: `NoError`, which Nixie agrees with.
* **`Agree-Violation` did not compare lengths** although this document said
  it did. It does now, with the action-invariant rule above.

### Fixed 2026-11-27

* **A spec's sibling modules did not come along.** Only a spec in a
  subdirectory received the other `.tla` files of its directory, and the
  corpus is flat: `MC3_TwoPhaseTyped` (`INSTANCE TwoPhaseTyped`),
  `MC3_TwoPhaseUFO`, `MC_LamportMutexTyped`, `MC_ERC20`, `y2k_cinit` and
  `y2k_instance` (both `EXTENDS y2k`) and `ConstantOperatorImpl` ran without
  theirs. The oracle's answer on all eight was its parse error, read by the
  comparator as `Refused`: seven sat in `OracleFailed`, one in
  `Agree-Refused`, and `y2k_instance` was listed as a known oracle defect on
  that evidence. Every sibling is copied now; the eight store entries were
  set aside under
  `precompile/apalache-0.63.0/benchmark/tla_parity_artifacts_20261127` and
  the oracle re-run. With real oracle answers, the cells are 1
  `Agree-Violation`, 2 `Declined`, 5 `Inconclusive`, 0 `MISMATCH`.
* **47 stored oracle answers were the oracle's usage banner.** The
  comparator counts exit 1 as `OracleFailed` ("the oracle's crash on its
  own cells"), and the first pass's table carried 72 of them. Looking at
  the stored `stdout` of each – which nobody had – 47 are not crashes: they
  are `apalache-mc [options] command …`, the CLI refusing a malformed
  argv, printed when the cells were first run under the two harness bugs
  fixed on 2026-11-26 (an empty options field collapsing, so that the exit
  code landed in the spec's place; multi-option cells misread). The fix
  corrected the argv for every later run but the store was never refreshed
  – the rule that "a cell the harness kept the oracle from running is not
  an oracle result" was applied to one cell then. Found by accident: a
  worktree without the store symlink re-ran the oracle on every cell, and
  28 "crashes" came back verdicts. The 47 entries were set aside
  (`tla_parity_artifacts_20261127`, beside the first pass's eight) and
  replaced by the fixed harness's answers; on the 204 cells whose stored
  answer was real, the fresh answers were identical to the stored ones,
  cell for cell, which is what says the oracle arm is reproducible and the
  store was otherwise sound. **Count a class only after reading what is in
  it**: `exit 1` was read as "the oracle's crash" for a day.
* **A lasso's length was never read.** `counterexample 1: a lasso of N
  step(s) …` did not match the pattern for a plain counterexample, so
  `x_len` was empty on every temporal violation and no `--temporal` cell's
  length was compared – while the standing table said "lengths equal". The
  step count is read now (it is the same count as the plain form), and the
  one documented disagreement has its own class,
  `Agree-Violation-Shorter` (see the known oracle defects).
## Known oracle defects (to grow, each with a reproducer)

* ~~`y2k_instance.tla` – the pinned 0.63.0 binary itself dies on this cell;
  the mdx expectation says OK. Oracle drift, not compared.~~ **Retracted
  2026-11-27.** The stored answer was the harness's own: its work directory
  lacked `y2k.tla`, which `y2k_instance` extends, and the oracle's parse
  error (`Cannot find source file for module y2k`) was recorded as its
  verdict. Given the module, the pinned binary answers `NoError` and
  `Error` on its two cells, as the mdx says. See "Harness defects, fixed
  2026-11-27".
* 28 cells exit 1 in the pinned binary; the mdx documents the outcome as
  if the binary produced it. See `OracleFailed` above.
* **The lasso tableau's `Init` contradicts its step-0 equation for a loop
  that starts in the first state** (`TableauEncoder.auxVarInitEx`: `unroll
  = TRUE` for `[]`, `FALSE` for `<>`, beside `unroll@0 = prev@0 /\
  (~InLoop@1 \/ arg@0)`). A lasso whose cycle starts in state 0 is
  unrepresentable whenever a `[]` argument is false there (or a `<>`
  argument true); the oracle finds the violation one step later, rotated,
  or not within a bound that reaches the shorter form only. Reproducer:
  `Next == x' = 1 - x /\ y' = y` from `x = 0`, `<>[](x = 1)` – violated by
  the two-step lasso `(0,0) -> (1,0) -> (0,0)`, which the oracle (and
  Nixie before 2026-11-27) does not find at length 2. Nixie now leaves
  `unroll@0` to its equation (`temporal.rs`); on this corpus no
  `Agree-Violation` length changed, the shape being absent from the 26
  `--temporal` cells. A cell whose Nixie counterexample is one step
  shorter than the oracle's on a temporal property is this defect, not a
  mismatch. Detail: `docs/studies/2026-11-27-tla-47-fairness.md`.
  **Reproducers (2026-11-27):** `LetIn.tla --temporal=FalseLiveness` and
  `NestedTemporalInBool.tla --temporal=FalseLiveness` – `<>(x + y = 2)` and
  `<>[](x > 5)` on the swap cycle `(0, 1) ↔ (1, 0)`, false on every lasso.
  The shortest violating lasso is `(0,1) →Step→ (1,0) →Step→ (0,1)`, two
  steps with the cycle both states; its loop starts one state after `Init`,
  so the oracle's `unroll@0 = TRUE` contradicts its step-0 equation there
  and it reports the violation one step later, rotated (3 steps). The
  comparator classes exactly this shape – a `--temporal` cell, both
  `Error`, Nixie one step shorter, its trace independently replayed – as
  `Agree-Violation-Shorter`, apart from `MISMATCH`; any other length
  disagreement on a temporal cell is a mismatch.
* **No stuttering in the lasso, on either side.** `LoopEncoder` conjoins
  the loop logic with `Next` as is, so a behaviour that stutters forever –
  which every `Init /\ [][Next]_v` specification has – is not a behaviour
  of the encoded system. That is why `ManyBoxes`/`LongLoops`/
  `NoLoopsNoProblems` "Liveness" pass on a cycle whose first state
  violates the property once stuttering is allowed. Parity is kept (the
  lasso is built the same way); whether to model stuttering is an open
  semantic question for the drop-in contract.
* Candidates to confirm and add: `Deadlock712` ("Apalache may miss a
  deadlock", their issue 712); `InfDomFun` (expected violation but
  `f[0] = 42` appears to hold).
