# Five walks paid once – the graph model check's closures, the get-value gate, the model render's definition map, the certificate's conclusion and the multi-trigger join (2026-11-27)

Five costs that no standing cell shows, each a walk re-taken per row where
the answer was the same for every row, on base `6efd718d`.  All five are
pure equivalent-work: every verdict, every row, every binding and every
certificate decision is what the base gave, in the base's order, and the
tests that pin that are in the tree.  Four of them change a complexity
class on a shape a user can write in a few lines – an n-edge chain with n
reach atoms, n values per trigger, n one-edge certificates – and the fifth
is a small change with a measured end-to-end payoff.

The opportunity list came from a measurement pass on `0e86c370`; the
prototype numbers quoted there (39.3 ms → 25 µs, 112 → 7.3 ms, 107 →
0.55 ms, 49.2 → 3.03 ms, 10.2 → 0.22 ms) are re-measured here on the
landed code against the landed base.

| # | Target | Where the work grew | Landed form |
|---|---|---|---|
| 1 | Validate graph reachability once per source | `GraphStatement::check_model` recomputed a closure per reach atom, each scanning the whole edge list per vertex reached: Θ(n³) on an n-edge chain with n atoms from one source | The present edges as CSR adjacency, built once per check; one closure per distinct source, shared by every atom naming it; atoms still examined in declaration order |
| 2 | Check for quantifiers once per get-value batch | `format_get_value` evaluated decision (67)'s gate – a walk of every asserted term – before testing whether the queried term was a leaf: Θ(QG) for Q queries on a goal of size G | The leaf test first; the gate computed once per request, on the first compound term |
| 3 | Index Boolean definitions once per model render | `model_rows`' completion arm re-collected the conjunct-level `(= b φ)` definitions for every unassigned Boolean: Θ(UA) for U rows over A conjuncts, before any definition was found | `DefinedBools`: one lazily built definition map per render, and one resolution of every definition under the render's model, so each row is a lookup |
| 4 | Join quantifier triggers on their shared variables | `PatternMatcher::match_against` merged a multi-trigger's partial substitutions by pairwise cross product: n² consistency tests for n bindings | `matching::join`: a level whose matches bind a uniform variable set is bucketed by the values it shares with the merge so far; the merges are streamed in cross-product order and the join stops at the tactic's budget |
| 5 | Index graph certificate conclusions | `GraphCertificate::check` resolved its conclusion by scanning the reach declarations, and the conflict form classified every premise by scanning them too: Θ(R²) for R one-edge certificates | `ReachIndex`, built with the statement: literal → row, first declaration winning; the cold `check_lemma` and the conflict form read it too |

## Method

Cost is paired instruction counts (`perf stat -x, -e cpu_core/instructions/u`
on one P-core, core 5 of this box, under `taskset`), interleaved, candidate
against the base built the same way (`cargo build --release`, the standing
recipe).  The box ran at load 28–72 on 20 cores throughout (other tenants'
builds and test runs, at times this session's own); wall is the probe's own
timing of the operation or the whole script's `task-clock`, as the median
of the interleaved runs, and never as a gate.

The base is `6efd718d` built in a detached worktree; the candidate is the
final tree.  The end-to-end scripts are SMT-LIB through the CLI.  The
component probes are a temporary crate in `/tmp` depending on the base tree
and on the candidate tree by path, both under the workspace release
profile:

* `nxprobe model n reps`: a chain of `n` edges with a reach atom `(0, i+1)`
  per edge – `n` atoms from one source – every edge true; `check_model`
  per repetition.
* `nxprobe certs n reps`: the same chain, one one-edge `Path` certificate
  per edge, each checked against its own conclusion and premise; plus a
  certificate paired with another pair's conclusion and one with no premise.
* `nxprobe join n reps` / `shared n reps k` / `disjoint n reps k`:
  `∀ x. (f x) ∨ (g x)` under `((f x) (g x))` – or `∀ x y. (f x) ∨ (h y)`
  under `((f x) (h y))` – over `n` ground values per trigger; all bindings,
  or the first `k`.  On the base the budget is the tactic's own prefix of
  the full list.

Every probe prints a checksum of its result; the base's and the
candidate's agree on every probe below, and the CLI scripts' outputs are
byte-identical.

## 1 – The model check's closures: one traversal per source

`check_model` is the final check's independent oracle for a graph
statement: every reach atom must equal the closure truth over the model's
`true` edges.  It computed that closure per atom, and the closure scanned
the whole edge list for every vertex it reached.  A chain of n edges with
n atoms from vertex 0 – the shape a transitive closure or a path constraint
writes – visited n × n × n edge entries.

The present edges are now adjacency once (`OutCsr`: one pass to count, a
prefix sum, one pass to scatter), and each distinct source's closure is
computed once and kept for the atoms that name it, as a membership bitmap.
Reach atoms are examined in declaration order and an unknown value still
fails closed, so the first atom to fail is the base's first atom to fail.
The cold `check_lemma` reads the same adjacency (its closure was the same
scan), so the recorded-proof checker is linear in the graph plus the
premise tests.

| `model`, chain of n edges, n atoms from vertex 0 | base | candidate |
|---|---:|---:|
| n = 128 – wall | 505 µs | 1 µs |
| n = 256 – wall | 3,391 µs | 3 µs |
| n = 512 – wall | 23,072 µs | 4 µs |
| n = 1,024 – wall | 178,814 µs | 8 µs |
| n = 512 – instructions per 9 repetitions (setup included) | 7,387.2 M | 6.9 M |

The base multiplies by 6.7–7.7 per doubling (cubic); the candidate by
2–3 (linear in the graph plus the atoms, with the microsecond as the
unit's floor).  `adjacency_model_check_agrees_with_the_scan_on_every_assignment`
keeps the retired per-atom scan as the oracle and judges all 8,192
assignments of a graph with parallel edges, a two-vertex cycle and two
self-loops – verdict and first failing atom alike;
`adjacency_model_check_fails_closed_on_an_unknown_atom` pins the fail-closed
order.

## 2 – The get-value gate: walked once per request

A quantified goal's model is certified as printed (decision (67)), and a
compound query is answered from the printed model first.  The gate "does
the asserted goal contain a quantifier" is a walk of every asserted term,
and the query loop evaluated it before the leaf test, so a batch of Q
queries on a quantifier-free goal of size G walked the goal Q times.  The
leaf test comes first now and the gate is computed at most once per
request, at the first compound term: a batch of leaves never walks the goal.

| whole script, 2,048 asserted Booleans | base | candidate |
|---|---:|---:|
| `(get-value (p0 … p2047))` – instructions | 985.5 M | 110.2 M |
| 512 asserted, batched – instructions | 94.5 M | 33.5 M |

Parsing, `check-sat` and the response are included; the outputs are
byte-identical.  (Wall on these two scripts is not quoted: the box was at
load 99 when the final binary was measured, and the instruction counts are
the stable quantity – an earlier, quieter pass read 78.0 → 10.5 ms of
`task-clock` for the 2,048 script.)  `a_large_quantifier_free_batch_answers_with_the_model_rows`
and `a_quantified_goal_still_reads_its_compound_queries_from_the_printed_model`
(`nixie-solver/tests/model_render_shared_walks.rs`) pin the answers of
both kinds of goal, with the compounds after the leaves in the batch.

## 3 – The definition map: collected once per render

The default-completion arm of `model_rows` asks whether the assertions
DEFINE a Boolean at conjunct level and what its definition evaluates to,
so a defined Boolean is never defaulted to `false` in a model whose own
values make its definition `true` (the QF_NIA/VeryMax invalid-model
class).  It re-collected the definition map from the assertions for every
row that reached it, and most rows have no definition at all: U unassigned
rows over A conjuncts cost Θ(UA) before the first definition was found.

`DefinedBools` is one render-local map: the definitions are collected on
the first row that reaches the arm, and every definition is resolved once
under the render's model – the chain fixpoint is monotone, so its result
does not depend on the order a round visits the definitions in – after
which a row is a lookup.  The map is render-local on purpose: the answer
depends on the model being printed.

| whole script, 2,048 asserted + 2,048 unconstrained Booleans, `(get-model)` | base | candidate |
|---|---:|---:|
| instructions | 4,176.8 M | 148.8 M |

All 4,096 rows are byte-identical, in declaration order.
`definition_bools_complete_from_one_shared_map_in_any_declaration_order`
pins the defined Booleans after a thousand unconstrained ones (the first
row to reach the arm has no definition), chained through one another,
defined twice (first wins), one whose definition does not evaluate
(defaulted) and one whose "definition" sits under an `or` (no definition);
`a_false_definition_and_a_chain_over_model_values_complete_from_the_map`
pins a `false` definition and a chain over model-pinned values.

## 4 – The multi-trigger join: indexed on the shared variables, streamed to the budget

A multi-trigger's partial substitutions were merged by cross product –
every accumulated substitution against every one of the next trigger's, a
consistency test per pair.  Two changes, both invisible in the result:

* **Indexed.**  A trigger whose matches all bind the same variables (the
  ordinary case: the trigger's own free variables) and share some with the
  merge so far is bucketed by the values of exactly those variables, so an
  accumulated substitution meets only the matches that agree with it.  A
  level whose matches bind differing variables is scanned and tested as
  before.  The join is expected linear in input plus output.
* **Streamed.**  The consistent merges are enumerated in the cross
  product's order (first trigger outermost, last innermost) by an
  explicit-stack descent, and the consumer can stop it.  The tactic passes
  its budget in (`match_against_within`), so two triggers over disjoint
  variables – a cross product for an answer – are not materialized for a
  prefix to be instantiated.  The bindings are the first `limit` of the
  unlimited list, in its order.

| `join`, `(f x) (g x)`, n values per trigger, all bindings | base | candidate |
|---|---:|---:|
| n = 1,000 – wall | 4,556 µs | 366 µs |
| n = 2,000 – wall | 12,469 µs | 814 µs |
| n = 4,000 – wall | 43,215 µs | 2,235 µs |
| n = 4,000 – instructions per 9 repetitions (setup included) | 10,517.2 M | 500.0 M |
| `(f x) (h y)`, 256 per trigger, budget 100 – wall | 9,726 µs | 133 µs |
| `(f x) (h y)`, 256 per trigger, budget 100 – instructions per 9 repetitions | 1,026.9 M | 35.0 M |

The base multiplies by 2.7–3.5 per doubling (the n² product and the O(n)
matching); the candidate by 2.2–2.7.  The order is load-bearing: the
tactic instantiates the first `budget` bindings, so a reordered join would
instantiate a different subset.  `join::tests` compare the streamed join
with the retired cross product, binding for binding in order, on shared,
disjoint, varying-variable and empty levels and on the early stop;
`matching::tests::multi_trigger_join_is_the_cross_product_in_order` does
the same through the matcher, and
`quantifier::tests::quantifier_instantiation_budget_is_a_prefix_of_the_unlimited_instances`
through the tactic (16 × 16 = 256 instances unlimited; 100 at the default
budget; the same first `k` at every budget asked).

## 5 – The certificate's conclusion: a literal index

`GraphCertificate::check` runs once per consequence the propagator emits
inside the CDCL loop, and each check began by resolving its conclusion to
the `(from, to)` pair it names – a scan of the reach declarations – and
the conflict form classified every premise by a scan too.  `ReachIndex`
is built with the statement (two maps: atom → row, negation → row; a
literal declared twice resolves to its first row, as the scans' `find`
did) and answers both in expected O(1).  `PartialEq` of a statement is
now written by hand over its declaration, the index and the packed
endpoints being pure functions of it.

| `certs`, n one-edge certificates | base | candidate |
|---|---:|---:|
| n = 2,000 – wall | 529 µs | 37 µs |
| n = 4,000 – wall | 2,106 µs | 74 µs |
| n = 8,000 – wall | 8,949 µs | 160 µs |
| n = 8,000 – instructions per 9 repetitions (setup included) | 2,122.3 M | 104.9 M |

The base multiplies by 4 per doubling (quadratic); the candidate by 2.
`certificate_check_resolves_conclusions_through_the_literal_index` checks a
one-edge certificate per edge of a 64-edge chain against its own
conclusion, rejects the last against another pair's, walks the conflict
form through the index, and pins first-declaration-wins on a literal
declared twice.

## Traps

* **`cargo clean` from a neighbour.**  Another session's `cargo clean` in
  the shared checkout removed `target/debug` under this session's test
  build: 43 `rustc` processes, then `cannot open … libsmallvec…rlib`.  The
  release candidate had been copied out of `target/` first; the test run
  was repeated after the clean finished.
* **Five small-stack tests red on the base.**  `sort_name::tests::test_deep_*`
  and `model_fmt::tests::test_format_sort_name_*` spawn a 128 KiB thread
  and overflow under this dev profile (`opt-level = 1`) on the base as on
  the candidate; they are excluded from the gate below and are not this
  landing's.
* **The nextest filter is a name filter.**  The five are excluded by name
  (`test(/sort_name::tests::test_deep_/) |
  test(/model_fmt::tests::test_format_sort_name_deep_/)`); the other
  small-stack tests (the matcher's own, the substitution ones) stay in the
  run.  A first filter keyed on `small_stack` let
  `test_format_sort_name_deeply_nested_parametric` through – it has no
  `small_stack` in its name – and it failed as on the base.
* **Two more red on the base.**  `finite_sets_cardinality::choose_of_ite_
  picks_the_taken_branch` (reads `Sat` where it pins `Unknown`) and
  `upstream034_model_interfaces::rejected_set_synthesis_cannot_publish_
  identical_choices` fail on `6efd718d` six of six runs each: the set
  synthesis now certifies a `choose` model these tests expected withheld.
  Not this landing's; left in the run and excluded from its count.
* **A 20-second pin under load.**  `qfidl_dl_regressions::qfidl_qlock_11_
  base_is_unsat` solves in 5.4 s alone on the base and read `unknown`
  at its 20 s cap in one pass at load 60; it passes in the final run.
* **Four at the 180 s cap.**  `bv_odd_width_blast_differential::odd_width_
  identity_pairs_hold`, `injective_repair::memory_alias_shape_with_guard_
  clauses_both_polarities`, `bv::solver::order::tests::order_network_random_
  differential` and `check_array::tests::memory_alias_shape_converges`
  (360 s) time out under nextest's `terminate-after` at load 20–100, in
  the dev profile, as they did in the studies of 2026-09-14, 09-16,
  09-22 and 11-09; none of them touches a path this landing changed.

The final gate (`cargo nextest run -p nixie-solver -p nixie-theories
-p nixie-cli -p nixie-core --all-features --no-fail-fast`, dev profile
with debuginfo off to keep the test binaries off the volume, the five
small-stack tests excluded by name): 7,888 run, 7,881 passed, 3 failed
(the two set-`choose` tests and the small-stack one, all red on the base),
4 at the cap.  `cargo clippy --all-features --all-targets -D warnings`,
`cargo fmt --check` and `cargo doc --no-deps --all-features` are clean on
the final tree.
* **The volume, again.**  An isolated test target under `/tmp` to dodge the
  neighbour's `cargo clean` filled the root filesystem: 108 GB of
  dev-profile test binaries with debuginfo and incremental caches for four
  crates, `No space left on device` in `ld.lld` at 100% – and a `Bus error`
  in the linker a minute before that was the same disk.  The run was
  repeated in the checkout's own `target/` on the data volume.
