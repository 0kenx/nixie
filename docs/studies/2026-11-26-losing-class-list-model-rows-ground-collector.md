# The losing class's list, the explanation witness, scalar model rows and ground-term collection – four cost slices, and the disequality key that stayed unsorted (2026-11-26)

Four slices off the opportunity list of 2026-11-26, on base `c31d4e2e`, all
trajectory-identical on every cell measured, none of them a benchmark win on
the standing corpus.  Three are walk-and-walk-again costs that no standing
cell shows: the merge that visited the *winning* class's disequalities to
re-write keys that had not changed, the disequality explanation that cloned
a watch list of 8,000 to read one entry out of it, and the model printer
that sent every unassigned scalar constant through the array renderer.  The
fourth, the quantifier tactic's ground-term collector, re-asked a whole
subterm's free variables once per enclosing subterm.

The fifth item is a correctness fix that is **not landed**.  A merge that
moves a disequality's endpoint onto the surviving root stores the key
unsorted, and the O(1) lookup that probes the sorted form answers `false`
for a proven disequality.  The one-line re-sort is correct, tested and
measured; landing it turns an in-tree regression test red and 21 corpus
instances from `sat` to `unknown`, because its trajectory reaches a
final-check gap that the base's trajectory does not – the gap is the base's
too, as 40 shuffles of one file show.  The fix, its tests, its three-arm
attribution and the gap are recorded here for the landing that closes the
gap.

## Method

Cost is paired instruction counts (`perf stat -x, -e cpu_core/instructions/u`
on the P-cores, cores 0–7 of this box), interleaved where both arms exist,
candidate against the base built the same way.  The box ran at load 10–72
on 20 cores throughout (other tenants' builds and test runs, and at times
this session's own); wall is quoted only for the component tables, as the
median of interleaved runs on one pinned P-core, and never as a gate.

The base is `precompile/c31d4e2e/nixie`, and it was verified before use: a
plain `cargo build --release` (the standing recipe) on the `c31d4e2e` tree
reproduces it byte for byte (sha256 `df28beab…`).  The candidate is the same
recipe on the final tree.  Component probes were temporary crates in `/tmp`
depending on the base source tree (`git archive c31d4e2e`) and on the
candidate tree by path, both under the workspace release profile:

* `nxprobe merge n reps`: `n` singleton classes, each holding one
  disequality to its own outside node, merged into one class one at a time
  inside a scope; every disequality is checked through the merged class,
  and again after the `pop`.
* `nxprobe explain n reps`: `n` disequalities on one shared endpoint; every
  pair explained with the shared endpoint first, then with it second.
* `nxprobe collect file reps old|new` and `nxprobe gchain n reps old|new`:
  the collector on a parsed corpus file and on a chain of `n` nested
  applications over a ground base; `old` is the retired per-subterm query
  written over the public API.  Both print a checksum of every sort's
  candidate list in order.

Three arms were built for the theory-path gates, because a fix and inert
changes landed together read as one trajectory shift: the base, the **fix
only** (the `c31d4e2e` tree with the one-line key re-sort), and a **full**
candidate carrying the fix and all the slices.  The landed candidate is the
slices without the fix.

## Slice 1 – the merge: one walk of the losing class's list

The pair-rewrite walked the watch lists of *both* merged classes, with a
per-disequality generation stamp to visit an entry that sat on both lists
once; the comment explained that the winner's list had to be walked for the
`(winner, elsewhere)` pairs "whose key also just changed".  They do not
change: union by rank keeps one of the two roots as the surviving root, so
a key that names the winner reads the same before and after; a key changes
exactly when one of its sides names the *losing* root, which has ceased to
exist.  And every live disequality with an endpoint in the losing class is
on `diseq_watch[loser]` (the copy below keeps that invariant).  So the
losing class's list alone holds every key that changes – and it was already
walked, separately, for the violation test and the copy to the winner.

`propagate` now makes that one walk: re-write the key if a side names the
loser, test the pair for collapse, copy the entry to the winner.  The stamp
and its two fields are gone.  A disequality can sit on the loser's list
twice – only a *violated* one can, its two endpoint classes having merged
into the loser earlier – and the rewrite is idempotent (the second visit
finds no side naming the lost root), so the entry is counted once:
`a_disequality_listed_twice_on_the_losers_list_is_rewritten_once`, through
a scoped version as well.

| `merge`, n classes, one disequality each | base | candidate |
|---|---:|---:|
| n = 4,000 – wall | 11.0 ms | 0.16 ms |
| n = 8,000 – wall | 44.0 ms | 0.36 ms |
| n = 16,000 – wall | 173.3 ms | 0.73 ms |
| n = 8,000 – instructions per repetition (setup included) | 1,496.9 M | 24.4 M |

The base quadruples per doubling (Σ(k+1) over k merges: 32.0 million
winner-list entries visited at n = 8,000, for 7,999 re-writes); the
candidate doubles.  The disequality checks after the merges and after the
`pop` agree with the base (the checksums are equal), and on the 25 probe
cells the counters are bit-identical.

### The key the walk re-writes, and why its re-sort is not landed

`are_proven_disequal` answers from `diseq_pair_counts`, a refcounted map
keyed by `ordered_pair` of the two endpoints' roots.  The rewrite moves an
endpoint onto the surviving root and keeps each side's position.  With
`b ≠ c` asserted and `a = c` merged – three nodes, the union keeping `a` as
the root – the key `(b, c)` becomes `(b, a)`: unsorted, because `b`'s index
is above the new root's, while the lookup probes `(a, b)`.
`are_proven_disequal(a, b)` answers `false` for a proven disequality;
`try_explain_diseq` recovers both premises from the watch lists.  The other
inversion needs a rank-2 class to lose into (the losing root the *smaller*
index, the new root above the other side).  The first trace of two binaries
that differ only in this diverges in the very first batch of forced
equality atoms: the atom-atom trigger in `propagate` probes the pair index
directly, so a key stored unsorted is a propagation never made.  Every
consumer of the lookup is a propagation or a heuristic gate – the equality
atom's forced value, read-over-write-DIFFERENT, the extensionality conflict,
the array pair separation, the arrangement pair skip – so the defect is a
missed propagation, not a wrong verdict; through `eq_news` a missed
propagation is a changed search.

**The fix** takes `ordered_pair` of the moved endpoints.  With it: two
regression tests (`rewritten_diseq_pair_is_resorted_when_the_loser_is_the_
larger_root` – the three-node case – and `…_the_smaller_root`, through a
scoped merge and its `pop`) and a brute-force oracle in the incremental
fuzz pass; the fuzz now checks, every 61 steps and at the end of each seed,
`are_proven_disequal` over every pair of the first 128 live nodes against
its definition – true exactly when the two sit in different classes and
some live disequality has one endpoint in each – and every cached key
against its endpoints' roots.  (A replay cannot be that oracle: it runs the
same code and stored the unsorted key on both sides.  The op stream only
ever merges or separates its first 64 nodes, so the limit covers every node
a merge can move a key off or onto.)  Without the re-sort the oracle fails
at seed 0 step 854 (`are_proven_disequal(0, 7)` answered `false`; the live
disequalities say `true`); with the walk re-broken it fails at seed 0 step
61.  None of this lands: the oracle cannot pass on the unfixed index.

**What the fix does on the corpora**, fix-only against base, verdicts
identical everywhere:

| cell of the 25-cell probe | conflicts | decisions | theory_props | instr, fix / base |
|---|---|---|---|---|
| PEQ020_size5 (unsat) | 3,635 → 3,653 | 5,348 → 5,356 | 98,617 → 118,824 | 1.1347 |
| xs_8_13 (unsat) | 3,357 → 3,802 | 181,972 → 186,453 | 542,134 → 602,299 | 1.0855 |
| xs-10-18-2-2-5-3 (unsat) | 4,337 → 4,133 | 273,577 → 281,315 | 930,902 → 938,025 | 1.0099 |
| xs_10_20 (unsat) | 8,751 → 6,821 | 344,239 → 345,144 | 1,675,703 → 1,393,037 | 0.8498 |
| vlsat3_f30 (limit 3,000) | 3,000 | 128,296 → 4,238 | 233,548 → 44,917 | 1.1196 |
| dlx-pc (limit 2,000) | 2,000 | 3,611,781 → 3,902,939 | 4,591,944 → 5,006,548 | 1.1551 |
| vlsat3_c60 (limit 3,000) | 3,000 | 9,198 → 4,778 | 399,124 → 279,766 | 0.8015 |
| storecomm_invalid_t1_pp_nf_ai_00060_003 (limit) | 3,000 | 5,587,543 → 5,656,248 | 7,225,958 → 7,381,029 | 0.9675 |
| storecomm_invalid_t3_pp_nf_ai_00060_002 (limit) | 3,000 | 6,314,967 → 6,374,933 | 8,228,530 → 8,226,639 | 0.8279 |
| swap_invalid_t1_pp_nf_ai_00004_007 (sat) | 550 → 487 | 24,810 → 22,491 | 46,676 → 42,487 | 0.9584 |
| swap_invalid_t3_pp_nf_ai_00008_002 (limit) | 3,000 | 320,701 → 309,400 | 603,803 → 562,216 | 0.9066 |
| swap_invalid_t3_pp_sf_ai_00008_002 (limit) | 3,000 | 345,755 → 347,056 | 578,817 → 590,854 | 1.0465 |
| storeinv_invalid_t1_pp_nf_ai_00002_001 (sat) | 158 → 174 | 7,501 → 6,703 | 12,208 → 10,852 | 0.9607 |

13 of 25 cells change counters (the other 12 are within 0.9987–1.0013);
instruction geomean of the shifted set 0.9893 – void as a paired cost,
since it compares different searches, and the cells are fixed-budget or
verdict cells, where a budget spent on different conflicts is neither
better nor worse.  Full against fix-only: counters identical on all 25
cells, instruction geomean **0.9958** (0.9448–1.0000) – the walk and the
witness rule are inert, and the three cells below 0.99 are EUF-heavy
(`vlsat3_c60` 0.9448, `PEQ020_size5` 0.9750, `8` 0.9947).

The pinned differential (`bench/differential/bench_diff.py`, 270 instances,
τ = 10 s, z3-validated models), run back to back with nothing else of this
session's on the box:

| arm | solved | agree z3 | disagree | sat (models valid) | unsat | trusted total | PAR-2 |
|---|---:|---:|---:|---:|---:|---:|---:|
| base `c31d4e2e` | 176 | 176 | **0** | 87 (86, one emission failed) | 89 | 175 | 1,990 s |
| fix only | 175 | 175 | **0** | 85 (85) | 90 | 175 | 2,005 s |
| full (fix + slices) | 177 | 177 | **0** | 87 (87) | 90 | 177 | 1,969 s |
| landed (slices, no fix) | 180 | 180 | **0** | 90 (90) | 90 | 180 | 1,925 s |

Per instance, base → full: `QF_UFIDL/pete/cxs-bp.smt2` timeout → **unsat**
in 7.8 s; `QF_UFLIA/mathsat/Hash/hash_sat_08_03` timeout → **sat**;
`QF_IDL/queens_bench/super_queen/super_queen97-1` timeout → **sat** (the two
at 10.2–11.0 s, at the cap, and they read `timeout` in the fix-only arm:
noise at τ); `QF_UFLIA/wisas/xs_25_25` sat with a failed model emission →
timeout; and `QF_AUFLIA/swap/swap_invalid_t3_pp_sf_ai_00003_007`
**sat → unknown** in 0.02 s.  That one is the next section.

The landed arm reads 180 solved against the base's 176, and every one of its
five changes is a cap-borderline instance – `super_queen97-1` 10.8 s,
`RF-00` (QF_LIA) 8.4 s, `c7b_i` 10.2 s, `hash_sat_08_03` 10.4 s, and
`xs_25_25`, whose emission now succeeds at 6.9 s.  A change whose counters
are bit-identical on every probe cell does not solve four more instances;
the box was quieter at midnight than at nine, and τ = 10 s is where that
shows.

### The gap the fix's trajectory reaches

1,376 files of `QF_AUFLIA/{swap,storecomm,storeinv,check}`, `QF_UF/PEQ`,
`QF_UFIDL/{pete,pete2}` and `QF_UFLIA/wisas`, base against full at `-t 5`:
no `sat ↔ unsat` flip in either direction.  33 decisive answers became
`unknown` and 32 `unknown` became decisive.  Re-run at `-t 60`, 12 of the
33 solve (cap effects, 3.3–7.8 s) and 21 are `unknown` in 0.04–3.1 s – all
in the `*_invalid_*_pp_sf_ai` variant.  On that variant alone (192 files,
`-t 20`): the base solves 85, the full candidate solves 85; 22 flip each
way.  A reshuffle, not a loss – and the base's share of that variant is a
coin-flip already: shuffling the order of the 16 assertions of
`swap_invalid_t3_pp_sf_ai_00003_007` (40 seeds) the **base** answers
`unknown` on 32 and `sat` on 8; the candidate 25 and 15.  On the file's own
order the base answers `sat` at 60 seeds of `NIXIE_SAT_SEED` and the
candidate `unknown` at all 60.

In the tree, `nixie-solver`'s `swap_sf_two_skolem_chains_is_sat` – the same
shape, twelve constants – fails with the fix (`Sat` expected, `Unknown`
returned) and passes without it.  That test is what holds the fix back.

**What the `unknown` is.**  The search ends on a full assignment the final
check accepts, and the printed model fails the honesty net (decision (85)):
"assertion 4 is false".  A scratch build with the withholding disabled, and
a scratch accessor dumping the e-graph's classes at the end, show the
candidate for that test: the class `b2 = (store a1 i2 f1) = (store a1 i1 e1)
= a2`.  The two stores are one class because an **internalized store
equality atom** – `(= (store a1 i1 e1) (store a1 i2 f1))`, minted by the
lazy array refinement as a pure branching dimension for its congruence
lemmas – was decided true, and `process_constraint` merges the two sides of
a positive equality atom.  The read-over-write consequences of that
decision at the indices the candidate then chooses were never instantiated
(`select (store a1 i1 e1) i2` sits in no class; the merge trace has no
merge for it), so nothing forces `select(a1, i2) = f1`, and the model
prints `a1 = {1 ↦ 4, −1 ↦ −2, 0 ↦ −1}`, `e1 = −1`, `f1 = 3`: `a2` is
`store(a1, −1, −1)` by its assertion and `store(a1, 1, 3)` by the merge,
and the two differ at `1` and at `−1`.  The renderer prints the merged
class as one chain with both writes, and the net reads the store equation
false.  On the bigger file the same thing shows as `a_66 = a_67` with the
consequences at `i1` missing.  The search's own candidate read through
`Solver::model` in a scratch example is a consistent assignment for the
*unmerged* reading (checked by hand), so what fails is the final check's
acceptance of a decided internal equality whose consequences it does not
derive – a gap of the base's, on every trajectory that decides such an atom
true, which the base's orderings do four times in five.

The fix only moves the original ordering onto the `unknown` side of that
gap.  The landing that closes the gap – deriving the read consequences of a
decided store equality, or instantiating the congruent reads on the decision
– should carry the re-sort, its two tests and the fuzz oracle with it; all
three are prepared and were run green together.

## Slice 2 – `try_explain_diseq`: the shorter list, the same witness

The explanation cloned the watch list of the first argument's class and
walked it to the first disequality joining the two classes.  A disequality
between two classes sits on both classes' lists, so the shorter list finds
every candidate; the witness is now sought there, and only the witness –
`(endpoint here, endpoint there, reason)` – is copied out before its proof
is built.

Which witness matters: when several disequalities join the pair, the one
named decides the reason literal of the propagation built on it and with it
the trajectory.  So the rule is kept exactly – *the first match on the
first argument's list*.  Its list is walked when it is the shorter (or
equal); when the other is strictly shorter, a lone match on it is the
witness (the only one), and several matches send the walk to the first
argument's list, no further than it always went.  A stale index still
abandons the whole explanation, as the inline loop's `?` did.

| `explain`, n disequalities on one endpoint | base | candidate |
|---|---:|---:|
| n = 8,000, shared endpoint first – wall | 97.9 ms | 0.21 ms |
| n = 8,000, shared endpoint second – wall | 0.23 ms | 0.19 ms |
| n = 8,000 – instructions per repetition (both loops, setup included) | 3,671.5 M | 18.1 M |

`diseq_explanation_keeps_the_first_arguments_witness_through_the_shorter_list`
builds two classes whose lists name the same two disequalities in opposite
orders (`[d1, d2, d3]` and `[d2, d1]`) and pins the witness for both
argument orders, plus a lone witness reached through the shorter list from
either side; letting the shorter list choose regardless fails it
(`[111, 102]` for `[101, 112]`).

## Slice 3 – model rows: no array renderer for a scalar constant

`model_rows` renders an array-sorted constant in its own arm (the sort is
matched before anything else).  A later arm called `array_model_value`
again for whatever reached it – arrays having been answered, exactly the
*non-array* constants with no model entry.  For a scalar sort the renderer
can only answer `None`: the constant's class holds no array, so there is no
constant default, no `store` member, no read and no store to inherit.  But
it established that by walking the class (`class_members`, O(nodes)), the
model's assignments, and – in `inherited_parts` – the whole term arena, once
per constant.  The arm is removed; in its place stands `removed_array_arm`,
`None` always, which under `debug_assertions` runs the renderer first and
asserts the `None` – the argument the removal rests on, checked by every
dev-profile model rendering, folded away in release.

| CLI, whole process | base | candidate |
|---|---:|---:|
| `(get-model)`, 4,096 unconstrained `Int` constants and one assertion – instructions | 2,996.5 M | **86.0 M** (0.029) |
| same – user CPU (median of 7, start-up included) | 111 ms | 6 ms |
| batched `(get-value (…))`, 1,024 unconstrained `Int` constants – instructions | 213.0 M | 26.5 M |
| 512 constants of `Int`/`Bool`/`(_ BitVec 8)`/`String`, no assertion – instructions | 3.44 M | 3.32 M |
| a mixed script (arrays, UF, a datatype, a set, a bag, witnesses) – instructions | 45.73 M | 45.41 M |

Output is byte-identical to the base on six scripts (`cmp` of the whole
stdout): the 4,096-constant model, the 1,024-term batch, the mixed script
above, a three-sort script, a 512-constant one, and a compound-query one.
`tests/model_rows_without_array_rendering.rs` pins the rows of the mixed
script, the batch that reads them, 512 defaults in declaration order, and
the completion `(get-value)` builds for a compound over an unassigned
constant.

## Slice 4 – the ground-term collector: groundness once per subterm

`GroundTermCollector::collect` asked `free_vars_including_patterns` of every
subterm on its own: the tree size rather than the DAG size.  The subterms
come in `collect_subterms`' post-order, children before parents, so a
subterm's groundness is now read off its children's where that is its
definition – for every operator that binds nothing, the free variables of a
term are the union of its children's.  The scope- and pattern-aware query
still answers for the four binding forms (`Forall`, `Exists`, `Let`,
`Match`: a body may mention the names it binds, a trigger is walked in its
own scope) and for a variable, which is its own free variable.  The answers
are memoized per `TermId` across the collector's calls and dropped by
`clear`.

| collector | per-subterm query | bottom-up |
|---|---:|---:|
| hamming_stream `…143_1061706` (38 KB, 221 assertions) – wall | 291 µs | 50 µs |
| hamming_stream `…148_1074476` (143 KB, 463 assertions) – wall | 913 µs | 157 µs |
| hamming_stream `…732_1080568` (196 KB, 503 assertions) – wall | 992 µs | 185 µs |
| the last – instructions per collection | 18.90 M | 3.68 M |
| a chain of 2,000 applications over a literal (2,001 candidates) – wall | 59.6 ms | 0.079 ms |
| same – instructions per collection | 1,162.1 M | 1.51 M |

Candidate lists, per sort and in order, checksum equal between the two at
every size (chains of 500, 2,000 and 4,000, and the three corpus files, which
hold no ground terms beyond two).  `ground_term_collector_matches_the_per_
subterm_query` keeps the retired rule as the oracle over terms covering each
binding form closed and open, shared subterms, variables, literals, a
quantifier under an operator, both `collect` entry points and a reused
collector; treating `Let` or a variable as an ordinary operator, or a
quantifier as a candidate, fails it.  The collector is reached only through
`QuantifierSolver`'s own tests and the tactic API; no solve runs it.

## Where the landed slices show

`bench/perf_gate/smt_probe_ab.sh`, landed candidate against the base,
strict: verdicts and counters identical on all 25 cells; instruction
geomean **0.9959** (0.9515–1.0013).  The cells below 0.99 are where the two
EUF slices run: `vlsat3_c60` 0.9515, `PEQ020_size5` 0.9746, `8` (QF_ANIA)
0.9951, `vlsat3_f30` 0.9941; the array cells 0.9990–0.9998.  The model-row
slice is not on the probe (it prints nothing); its cells are the table
above.

## Bar

Run on the final tree (`c31d4e2e` plus the landed slices; `main` did not
move under the session), the candidate built with the standing recipe
(sha256 `5ab24c17…`).

* `cargo fmt --all -- --check`; `cargo clippy --all-features --all-targets
  -- -D warnings`; `cargo doc --no-deps --all-features` (warnings are
  errors through `rustdocflags`): clean.
* `cargo nextest run -p nixie-core -p nixie-theories -p nixie-solver -p
  nixie-cli --all-features --no-fail-fast` (dev profile, `opt-level = 1`,
  debug assertions on, load 10–73): **7,856 run, 7,844 passed (3 slow),
  13 skipped**, 7 failed, 5 timed out – every non-pass accounted for, none
  from this change:
  * 5 `SIGABRT` stack overflows: the documented 128 KiB-stack canaries
    (`*_small_stack` in `context::sort_name` and `context::model_fmt`) over
    files byte-identical to `main`; **all five pass in the release profile**
    (1.1 s).
  * 2: `choose_of_ite_picks_the_taken_branch` and
    `rejected_set_synthesis_cannot_publish_identical_choices`, the
    documented sets pair (a pinned `Unknown` that the solver answers `Sat`
    with `A = {0, 2}`, `B = ∅`).  They fail in the release profile too, on
    this tree and on the base's: the base tree's own release binaries,
    built the same way, answer `Sat` where the tests pin `Unknown`.  The
    day's earlier record has the pair passing in release; built here it
    does not, with or without this change.  (The `Sat` is defensible –
    `choose(∅)` is an unconstrained value, so the two choices can differ –
    but that is the sets line's call, not this landing's.)
  * 5 slow-timeout terminations at 180–360 s.  **In the release profile
    all five pass** on this tree, from binaries built with
    `cargo test --release --no-run --lib --test <name>`:
    `memory_alias_shape_converges` 83 s, `odd_width_identity_pairs_hold`
    107 s, `memory_alias_shape_with_guard_clauses_both_polarities` 27 s,
    `order_network_random_differential` 34 s,
    `pete_5s_family_instance_is_unsat` 16 s.
  * `swap_sf_two_skolem_chains_is_sat` passes in both profiles (it fails
    only with the held-back fix).
* `bench/z3_parity` (in process, `--out` to a scratch file; z3 4.16.0):
  **171 Correct / 0 Wrong / 6 Inconclusive** – the standing result.
* `bench/perf_gate/run_gate.sh` vs the pinned `28e82c65`: **PASS**, conflicts
  1.000 / decisions 1.000 / wall 0.98 (n = 9).
* `bench/perf_gate/paired_instructions.sh` vs `precompile/c31d4e2e/nixie`:
  geomean **1.0000** over 12 cells, conflicts identical – the pure-SAT path
  executes none of this change.
* `bench/perf_gate/smt_probe_ab.sh`: as above, strict.
* The pinned differential above, landed row: **180 solved / 180 agree /
  0 disagree**, every `sat` with a z3-valid model; the five differences from
  the base are the cap-borderline ones listed there.

## Traps recorded

* **A fix and inert changes landed together read as one shift.**  The
  25-cell probe flagged 13 cells against the base and would have let the
  walk and the witness rule share the blame or the credit.  The third arm –
  the base tree with the one-line re-sort – separated them: the inert
  changes are bit-identical against it, and the fix's own deltas are read
  off cleanly.  Build the third arm before reading a shifted probe.
* **A differential arm with a wall cap is not comparable across loads.**
  The first run of the full arm overlapped two LTO builds of this session:
  nine solves of 3.6–8.7 s became timeouts at τ = 10 s and the arm read
  168 solved.  Re-run with nothing else of ours on the box it read 177.
  Read `s` beside every flip before believing it.
* **`sat → unknown` was not the fix's doing, and 60 seeds could not show
  it.**  The seeds re-draw one arm's trajectory; the assertion order
  re-draws the other's.  It took 40 shuffles of the base to show the
  `unknown` is the shape's, not the change's – then a scratch build with the
  withholding disabled and a scratch dump of the e-graph's classes to see
  the decided internal equality that the final check accepts without its
  read consequences.
* **The in-tree test knew before the corpora did.**  `nextest` stopped
  (fail-fast) 3,501 tests in on `swap_sf_two_skolem_chains_is_sat`, an
  array-axiom policy regression of exactly the `swap_invalid_*_sf_*` shape.
  A dev-profile test run is the cheapest differential there is; it should
  have run before the three arms and the family sweep, not after.
* **A dev oracle must sit where the removed arm sat.**  The first form of
  the `model_rows` oracle ran after the whole `if` chain and fired on every
  *array* constant, whose own arm had answered.  It is the chain's arm now,
  reached only by what the removed arm was reached by.
* **A probe that dies reports a cost of zero.**  `inst_delta.sh` appends the
  repetition count as the last argument; a probe mode that takes it earlier
  parsed `old` as a count, aborted, and printed 38 instructions per
  repetition.  The checksum line comes before the instruction line.
* **The oracle's own list is the thing to read.**  The collector test's
  first draft asserted the collector keeps a ground `Forall` as a candidate
  (it never did: quantifiers are skipped by kind) and that an equality was
  an `Int` term.  Two wrong expectations of a rule remembered, against a
  list that was right.
* **`MatchCase` was not nameable.**  It is a public field type of
  `TermKind::Match` behind a private module; building a `match` in a test
  outside `crate::ast` needed it re-exported (`pub use term::{…,
  MatchCase, …}`), which this landing does.
* **The volume filled and `target/` went again.**  The dev-profile test
  build died on `No space left on device` (the shared volume at 100 %), and
  a few minutes later `target/` was gone, the gated `target/release/nixie`
  with it – the trap of the day's earlier record, twice over in one hour.
  The rebuild with the standing recipe reproduced the gated binary's
  sha256 byte for byte, which is what made the earlier gate runs count for
  their tree; a second attempt at the test build was SIGTERMed with every
  other `rustc` on the box.  Cache nothing you cannot rebuild, and check
  the hash.
