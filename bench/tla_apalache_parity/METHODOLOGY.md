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

## Standing result (2026-11-26, all 253 cells, harness fixed)

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

## Known oracle defects (to grow, each with a reproducer)

* `y2k_instance.tla` – the pinned 0.63.0 binary itself dies on this cell;
  the mdx expectation says OK. Oracle drift, not compared.
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
