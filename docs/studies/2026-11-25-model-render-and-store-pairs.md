# Model rendering and store-pair enumeration – three cost slices (2026-11-25)

Three slices off the opportunity scan of 2026-11-25, on base `f1200a83`.  Two
sit on the model-printing path – `(get-value …)` rendering the whole model once
per unassigned constant, and the `@uc_S_n` witness allocator rescanning every
declared name for each name it minted – and one on the lazy array-axiom path,
the store-congruence pair loop.  The first two are output-identical and
large-constant-factor wins on the inputs that trigger them; the third is
trajectory-identical and structural (n² → n + eligible pair visits) with no
measurable share of any solve examined – reported as such.

## Method

Cost is paired instruction counts (`perf stat -x, -e cpu_core/instructions/u`,
candidate vs the `f1200a83` release binary cached as
`precompile/f1200a83/nixie`, arms interleaved ABBA), with user CPU (median of
3, bash `time`) for the table.  Instruction counts are load-independent; the
box ran at load 11–47 on 20 cores throughout, so wall is quoted only where the
protocol asks for it (the perf gate) and nowhere else.  Output identity is
`cmp` of the whole stdout of baseline and candidate on the same script.

The printed-text slices are verified three ways: byte-identical output against
the baseline binary on the triggering inputs and on mixed models (witnesses,
a quoted sort name, array chains, UF, Int/Bool/BV defaults, compound query
terms, the legacy Set-sorted path); integration tests that pin the agreement
between a batch's answers and the model's rows; and, for the allocator, the
retired per-weight scan kept in the module as the oracle.

## Landing 1 – `91a635ac`: one model rendering per `(get-value …)` request

A bare constant the model leaves unassigned is answered with the row
`(get-model)` prints for it, and `unassigned_const_value` read that row back by
calling `get_model()` – every row, the class map, every array chain – once per
queried term, then keeping the one at the constant's declaration index: n²
rows for a batch of n.  `model_fmt/get_value.rs`'s `ModelRows` renders the rows
at the first term of the request that needs one and indexes them by term.

| input (release, median user CPU of 3) | base | candidate |
|---|---:|---:|
| `(get-value (…))` over 512 unconstrained `Int` constants | 0.366 s | **0.002 s** |
| `(get-value (…))` over 1,024 unconstrained `Int` constants | 2.849 s | **0.009 s** |
| `(get-model)` of the 1,024-row model | 0.008 s | 0.007 s |

Paired instructions on the 1,024 case: 95,704,705,555 / 207,735,274 /
95,704,706,472 / 207,737,180.

Two properties of the per-term lookup were kept on purpose.  A term that is
not a declared constant never renders the model – the declaration index is
built on its own and answers first, so a `(get-value ((bvult w v)))` over a
large model does not pay a `(get-model)` it cannot use.  And a model
`(get-model)` withholds (decision (54)) is not cached; the check is cheap and
later terms take the same fall-through the first one did.

**A behaviour note the change closes.**  The per-term rendering was
order-dependent inside one request: `printed_reading` and the structural
evaluator intern terms, and the array renderers scan the term arena for reads
over a class and stores over an array, so the rendering a batch's k-th
unassigned constant received could differ from its j-th.  One rendering per
request gives one spelling to every constant in the batch.

## Landing 2 – `bc595804`: reserved witness names collected once

`build_class_values` numbers each uninterpreted-sort class's `@uc_S_n`
witness over the whole declaration list and steps over the numbers the script
itself declared; `format_uninterpreted_witness` made that collision check by
walking every declared constant and function name for *each* name it minted.
8,000 unconstrained constants of one sort: 64 million name visits, none of
which collided.  `model_fmt/witness_names.rs` walks the declarations once, at
the first witness a rendering asks for, splits each `@uc_` name at its last
underscore (the printed-model reader's own split,
`printed_check::parse_typed_printed_term`) and hands each sort its free
numbers through a cursor.  Only declarations are read, never the parse-back
artifacts in the term arena, so repeated `(get-model)` / `(get-value)` keep
one numbering.

| input (8,000 unconstrained constants of one uninterpreted sort) | base | candidate |
|---|---:|---:|
| `(get-model)` user CPU | 1.26 s | **0.069 s** |
| batched `(get-value (…))` user CPU | 1.06 s | **0.072 s** |

Paired instructions on the `(get-model)` case: 34,111,427,696 / 1,178,248,459 /
34,111,406,455 / 1,178,219,844.

The names are the scanned names, digit for digit, including the readings the
scan gave odd spellings: `@uc_U_0` declared moves the first witness to
`@uc_U_1`; `@uc_U_00` is a user symbol and reserves nothing; a function name
reserves like a constant's; `@uc_A_1_2` reserves for sort `A_1` and nothing
for `A`.  `minted_names_are_the_scanned_names` holds the cursor – through
forward passes, rewinds and skips – to the retired scan over declarations
covering those spellings; `the_declarations_are_walked_once` counts the walks;
`model_output_and_options.rs` pins the user-visible half.

## Landing 3 – `a935fc0d`: store-congruence pairs are indexed

`build_store_congruence` visited all C(n, 2) pairs of stores and kept the
pairs the formula relates (a shared base or an explicit equality atom),
cloning both stores' terms per pair visited and again per pair that passed.
`solver/array_axioms/store_pairs.rs` groups the stores by base, attaches the
explicit store equalities to the store at the lower term id, and walks each
store's two lists in term-id order – the order the all-pairs filter produced,
so the lemma sequence and the pair `MAX_STORE_PAIRS` cuts it at are unchanged.
The module's tests keep the old loop as the oracle: the depth-50 `storecomm`
shape (100 stores, the same 2 instances in the same order), 40 writes over one
base (780 pairs, both walks cut at the same 512th pair), mixed bases with
duplicated and reversed equalities (87 instances, premise pairs in the same
order), 12 pseudo-random structures.

`NIXIE_ARRAY_PAIR_LOG` prints the per-round census.  Over the QF_AUFLIA
`storecomm` / `swap` / `storeinv` / `check` families (989 files; the 765 that
reach the refinement loop, 3,150 rounds – the rest are decided before it):

| family | files | rounds | all-pairs visits (before) | indexed-walk visits | instantiated | capped rounds |
|---|---:|---:|---:|---:|---:|---:|
| storecomm | 432 | 1,499 | 3,822,239 | 3,120 | 3,120 | 0 |
| swap | 294 | 1,545 | 511,813 | 8,923 | 8,923 | 0 |
| storeinv | 38 | 103 | 6,312 | 172 | 172 | 0 |
| check | 1 | 3 | 3 | 3 | 3 | 0 |
| total | 765 | 3,150 | 4,340,367 | **12,218** | 12,218 | 0 |

The largest round holds 120 stores (depth-60 `storecomm`, 7,140 pairs before).

**Verdict: structural, cost-neutral where measured.**  Paired instructions vs
`f1200a83`, verdicts and conflicts / decisions / propagations / theory_props
equal on every cell: the standing 17-cell SMT probe geomean 0.9999; the
8-cell array set below geomean 0.9999.  A permutation shape of 151 stores over
one base (11,325 pairs a round, the cap reached) runs 111.794 G vs 111.793 G
instructions – 825,541 decisions dominate it, as the search dominates every
corpus cell.  Rounds are few (3–4) and n is small (≤ 120), so the removed n²
term was microseconds against seconds of search.  What the slice buys is the
asymptote and the removal of four `TermKind` clones per visited pair; it is
not a benchmark win and was not landed as one.

**Harness gap closed.**  The standing probe's storecomm cell
(`storecomm_t1_np_nf_ni_00050_001`) is decided at 0 conflicts and never
reaches the array loop; an array-path change could have regressed freely
under it.  `bench/perf_gate/array_probe_cells.txt` adds eight cells that run
the loop every round (the `*_invalid` depth-60 and `swap` 00008 cells at
`--conflict-limit 3000`), for use with `smt_probe_ab.sh` as its third
argument.

## Bar (run on the final tree)

* `cargo fmt --all -- --check`; `cargo clippy --all-features --all-targets
  -- -D warnings`; `cargo doc --no-deps --all-features` (warnings are
  errors through `rustdocflags`): clean.
* `cargo nextest run --workspace --all-features` (dev profile: `opt-level
  = 1`, debug assertions on): **12,980 run, 12,674 passed, 21 skipped**,
  301 failed, 5 timed out – every non-pass accounted for, none from this
  change:
  * 299 in `nixie-tla-check` (23 binaries): each dies on the tla line's own
    `debug_assert_eq!` at `nixie-tla/src/lower.rs:312:17` (the value stack
    against its mark), which the release bar compiles out; the files are
    byte-identical to `main` (`5c7f1aaf`).
  * 2 in `nixie-solver`: the two documented pre-existing sets failures
    (`choose_of_ite_picks_the_taken_branch`,
    `rejected_set_synthesis_cannot_publish_identical_choices`).
  * 11 `SIGABRT` stack overflows: the 128 KiB-stack canaries
    (`*_small_stack`, `test_format_sort_name_deeply_nested_parametric`)
    over code byte-identical to `main` (`sort_name.rs`, `check_array/*`,
    `format_sort_name`); at `opt-level = 1` the frames exceed the ~10
    B/level the tests pin.  **In the release profile all 11 pass** on this
    tree.
  * 5 slow-timeout terminations at load 24–57.  **In release the two
    array-alias canaries pass** on this tree: `memory_alias_shape_converges`
    135 s (budget 360 s),
    `memory_alias_shape_with_guard_clauses_both_polarities` 98.8 s (budget
    180 s).  The other two are BV differentials
    (`order_network_random_differential`, `odd_width_identity_pairs_hold`)
    over code this branch does not touch (`nixie-theories` and the BV solver
    files are byte-identical to `main`).
  * The documented bar is `--release`.  A full release-profile workspace
    run was not made: cargo links every test target of a selected package
    before nextest's `-E` filter applies (see traps).
* `bench/z3_parity/run_parity.sh`: **171 Correct / 0 Wrong / 6
  Inconclusive** (z3 4.16.0) – the standing result;
  `results.linux-x86_64.json` unchanged.
* `bench/perf_gate/run_gate.sh` vs the pinned baseline: **PASS**, conflicts
  1.000 / decisions 1.000 / wall 0.95 (n = 9).
* `bench/perf_gate/paired_instructions.sh` vs `f1200a83`: geomean **1.0000**
  over 12 cells (the pure-SAT path executes none of this change).
* `bench/perf_gate/smt_probe_ab.sh` vs `f1200a83`: verdicts and counters
  identical on every cell; standing 17 cells geomean **0.9999**,
  `array_probe_cells.txt` geomean **0.9999**.
* Binary cached under the landing tip's commit in `precompile/` (the tree
  the merge onto `main` carries).

## Traps recorded

* **The worktree was not mine alone.**  Mid-session `main` moved to
  `5c7f1aaf` (the tla line's temporal-lasso landing, a merge of `f1200a83`),
  and ~1,600 lines of that work's files appeared uncommitted in this
  directory.  Handled without `stash` / `restore` / `checkout --`: every
  dirty and untracked path was first shown byte-identical to `main`'s content
  (`git diff 5c7f1aaf -- <paths>` empty; `git hash-object` equal to
  `git rev-parse 5c7f1aaf:<path>` for the untracked two), the landing merge
  was made in a throwaway worktree, and only then was this directory brought
  onto `main` – with a check, before and after, that no file's content
  changed.
* **`nixie-cli` does not depend on the tla crates** (`cargo tree -p
  nixie-cli`), so the candidate binary was exactly the three slices although
  the tree carried the foreign files; the gates therefore ran here, on the
  content the landing merge produces.
* **Per-term model rendering was order-dependent** inside one batch (arena
  growth between terms; see landing 1) – any future "render per term" code
  on this path inherits that.
* **Pre-existing, not touched:** on the *legacy* `(get-value)` path (any
  Set-sorted term in the batch switches the whole request to it), an
  uninterpreted-sort constant the model has an entry for echoes itself
  (`(u1 u1)`) where the same constant asked alone answers its `@uc_U_1`
  witness – `f1200a83` and this tree alike.  Two commands describing two
  models, the failure class `model_fmt` exists to prevent; left for its own
  landing – and landed the next day, see the addendum.
* **nextest's `-E` filter runs after the build.** `cargo nextest run
  --release -p nixie-solver -E '...'` first links every test target of the
  package – ~150 fat-LTO binaries here, the better part of an hour – for the
  handful the filter selects.  For a few release-profile tests, build exactly
  their binaries (`cargo test --release -p nixie-solver --no-run --lib
  --test <name>`) and run them from `target/release/deps/`, where libtest's
  own positional filters and `--test-threads` apply.
* `/tmp/nxprobe` held the session's scripts and logs (`/tmp` is age-cleaned
  on this box); the array cell set now lives in `bench/perf_gate/`.

## Addendum (2026-11-26) – the legacy get-value bug, and the array cells by default

**`65b6901c` – the legacy `(get-value)` path answers uninterpreted-sort terms
from the class map.**  The "pre-existing, not touched" bullet above is closed.
A batch holding a Set-sorted term is routed whole to `format_get_value_legacy`,
which had no arm for uninterpreted sorts: a constant the model has an entry
for fell to `model.get(term)`, and the solver's entry for such a constant is a
stand-in term that spells like it.  With `(= u2 u0)` and `(distinct (f u0)
(f u1))` asserted, `(get-value (u0 u1 u2 (f u0) (f u1) k s))` answered
`(u0 u0) (u1 u1) (u2 u0) ((f u0) (f u0)) ((f u1) (f u1))` beside a
`(get-model)` printing `@uc_U_0 @uc_U_1 @uc_U_0 @uc_U_2 @uc_U_3` – and beside
the witnesses the same terms answered without `s`; on `f1200a83` and on
`5cc14910` alike.  The structural path's arm, mirrored: one class → value map
per request, built after the set/bag completions settle the model.  Blast
radius by `cmp` against the eight saved baseline outputs of this record: all
identical; only the Set-sorted probe's uninterpreted answers moved, to the
model's.  `tests/get_value_batch_rows.rs` pins it (the same batch with and
without the set term).  Bar: nextest `nixie-solver` + `nixie-cli` 3,371 of
3,382 (the non-passes the dev-profile itemisation above accounts for, none
new), parity 171 / 0 / 6, clippy clean, SMT probe over the default corpus
(now 25 cells) counters identical vs `5cc14910`, geomean 0.9998.

**The array cells run by default.**  `array_probe_cells.txt` had closed the
harness gap only for a caller who passed it as the third argument.
`smt_probe_ab.sh` with no cells argument now runs the standing set and the
array set – 25 cells, one geomean, a header line between the sets – and
explicit files still override; `smt_probe_cells.txt` marks its storecomm cell
as the verdict canary it is.

**Trap: the shared volume fills.**  `/media/data` ran out of space twice
during these runs (other tenants' builds; 263 GB free → 0 → 177 GB within
the hour).  A link that dies of it reports as `ld.lld … Bus error` /
`collect2: error: ld returned 135`, five test binaries at a time, and cargo
relinks them on the next run once space is back – check `df` before reading
a wave of link failures as code.

