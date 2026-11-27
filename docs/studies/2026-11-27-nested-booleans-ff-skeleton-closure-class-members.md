# Nested Booleans, the FF skeleton and its function scan, the FF closure and the class members – five cost slices, and three gates that did not denote their connectives (2026-11-27)

The five targets of the 2026-11-27 opportunity list, on base `0e86c370`
(the list was measured on `c31d4e2e`; the four commits between touch none
of the five places). Four change no output and no search trajectory
anywhere they were measured: the finite-field function-hood scan, the
finite-field congruence closure, the class-member lists of a model, and
the finite-field Tseitin encoder (whose variable numbering changes, on
paths no probe cell holds). The fifth, the nested `and`/`or` parse, builds
the term the flat spelling always built and so moves three cells of the
probe. And writing the encoder's oracle found that three of its gates did
not denote their connectives: `(=> p false)` under `(not p)` read `unsat`,
on the base and on every tree since the encoder landed. The fix lands with
the slice; the oracle that found it is kept.

None of the five is a win on the standing probe: 22 of its 25 cells are
bit-identical, and the other three – `QF_UFLIA/wisas` goals spelled with
nested `and` – change trajectory, as the first slice must make them. What
the slices buy is on inputs the probe does not hold, and is measured below
per component.

Two findings are recorded and **not landed**, both in the eager finite-field
procedure: a *consistent* linear system is not answered by the linear
solver but by enumeration (up to seven variables of 𝔽₇) or by the Gröbner
cascade beyond it, so eight variables pinned to constants run for minutes
with no verdict; and through that, `QF_UFFF` with four applications of one
function answers `unknown` after seconds. They dwarf everything below on
their families and are the next targets.

## Method

Cost is paired instruction counts (`perf stat -x, -e cpu_core/instructions/u`
on one pinned P-core), interleaved where both arms exist, candidate against
the base built the same way; the median of three runs. The box ran at load
22–122 on 20 cores throughout (other tenants' builds, and at times this
session's); wall is quoted for the component tables only, never as a gate.

The base of the paired tables is `precompile/0e86c370/nixie` (sha256
`5ab24c17…`), and `target/release/nixie` on the untouched tree was
byte-identical to it. The tables were taken on `0e86c370` plus this
landing, in two steps of the tree (`13341aef…`, then `c8ec816a…` with the
`goal_fields` arm below, which no probe, gate or differential cell
executes).

**Main moved under the session**, to `cc6eb36e` – thirteen commits: the
merge of #20, the TLA line, and `69a909ae`, a solver change in
`set_theory` – none touching the files below. The six code commits land on
it, and the bar at the end was re-run on that tree: the candidate is the
standing recipe on `9b3982d7` (sha256 `5b93b0b3…`), the base the same
recipe on `cc6eb36e` in a worktree **with the checkout's `Cargo.lock`
copied in** (sha256 `782d9725…`, cached as `precompile/cc6eb36e/nixie`).
The slice rows re-measured against it reproduce the tables exactly
(0.7800, 0.4870, 0.0046, 0.0005, 0.0753, 0.0530, 0.9745; the model's
output still byte-identical), and `target/` had been wiped once more in
between, so every binary in this record was built from nothing after the
move.

The component probes were temporary `#[test]`s in the release-profile
library test binaries (`cargo test --release --no-run --lib`), each a
whole-process count over R repetitions with a `-setup` twin subtracted,
driven by `NXPROBE_N` / `NXPROBE_REPS`; the retired rule ran beside the
candidate in the same binary, as a copy:

* the closure: the retired round-based fixpoint over the same fields;
* the encoder: the retired tree walk as a free function beside
  `FfTseitin::encode`;
* the function-hood scan: the retired per-pair `find` loop beside
  `apps_by_function`.

They were removed before the final tree was built; what remains of them
is the counts below and the regression tests each slice carries.

End to end, synthetic scripts through the CLI, base against candidate,
verdicts compared and `(get-model)` output `cmp`ed.

## Slice 1 – the parser: a nested `and`/`or` joins its parent

`mk_and` flattens a nested `and`, so `(and a (and b c))` and `(and a b c)`
build the same term – but the parser closed each nesting level on its own,
and every level copied and interned the whole prefix read so far: n − 1
nodes holding 2 + 3 + … + n operands for n leaves (n(n+1)/2 − 1 stored
operands: 8,390,655 at 4,096), quadratic in time and memory for a term
that is one node.

`Parser::close_or_absorb` (`nixie-core/src/smtlib/parser/terms.rs`) hands
a completed `and` that closes directly under an `and` (an `or` under an
`or`) to its parent as operands, and only the outermost level is interned.
"Directly" is the frame stack: a `let`, an annotation, a `not` or the
other operator between two levels keeps the inner term a term, built as it
always was. The equality of the two spellings is an argument, not a
convention: `mk_and` returns `false` on a `false` operand, drops `true`,
flattens an `and` operand and unwraps a single survivor, so an inner level
contributed exactly its operands and nothing of its own (the four cases are
spelled out in the method's doc comment). The depth budget is unchanged: the absorbed
frame was on the stack, and counted, while it was open.

| CLI, whole process (instructions; verdict `sat` in every cell) | base | candidate |
|---|---:|---:|
| nested `(and p0 (and p1 … ))`, 4,096 leaves | 178.04 M | **138.86 M** (0.780) |
| flat `(and p0 … p4095)`, 4,096 | 133.07 M | 133.04 M (0.9998) |
| alternating `(or p0 (not (or p1 … )))`, 4,096 – nothing to absorb | 276.02 M | 276.00 M (0.9999) |
| nested `and`, 16,384 leaves | 1,134.9 M | **553.0 M** (0.487) |
| flat `and`, 16,384 | 523.7 M | 523.6 M (0.9998) |
| nested `and`, 16,384 – wall, median of 3 (load 22–35) | 2.5–3.4 s | 0.07–0.08 s |

The base quadruples per doubling where the candidate doubles; the
candidate's nested spelling now costs the flat one's plus 1.4 k
instructions per level (the frame, the token, the probe for the parent's
`)`). Stored operands: 8,390,655 → 4,096, and the arena after the parse is
the flat spelling's, node for node.

`nixie-core/tests/nested_boolean_operands.rs` pins it: every spelling of
one conjunction (right-nested, left-nested, flat; `and` and `or`; 2 to
65,535 leaves) builds one term with the ordered operands and exactly one
connective node; 3,000 random trees over `and`, `or`, `true`, `false` and
single-operand levels build the term the retired level-by-level
construction builds (the retired rule is the oracle, run in the parser's
own arena so hash-consing answers it with the parser's id); a `let`, an
annotation, a `not` and the other operator keep the inner term; a
single-operand level, a repeated operand, a `true` and a `false` read as
they closed before; and one level past `MAX_PARSE_DEPTH` still errors in
the nested spelling, 65,535 levels being the most it admits.

**What it does to the probe.** The nested spelling now builds the term the
flat spelling always built, ids included, and the three `wisas` cells of
the 25 are spelled that way:

| cell | conflicts | decisions | theory_props | instructions, cand / base |
|---|---|---|---|
| `xs_8_13` (unsat) | 3,357 → 3,742 | 181,972 → 218,398 | 542,134 → 644,800 | 1.1461 |
| `xs-10-18-2-2-5-3` (unsat) | 4,337 → 3,744 | 273,577 → 254,412 | 930,902 → 865,405 | 0.8249 |
| `xs_10_20` (unsat) | 8,751 → 8,728 | 344,239 → 327,467 | 1,675,703 → 1,618,337 | 1.4254 |

The other 22 cells are bit-identical (0.9994–1.0005 against `0e86c370`,
0.9980–1.0020 against the landed base). The shift is a
reshuffle in both directions (+11.5 %, −13.7 %, −0.3 % conflicts), and the
family says the same: all 108 `wisas` files at `-t 20`, base against
candidate against z3 4.16.0 – 14 `unsat`, 35 `sat`, 59 `unknown` in both
arms, **no disagreement with z3 in either arm**, 10 `sat ↔ unknown` flips
(5 each way); at `-t 60`, 6 of the 10 are cap effects and 4 remain (base
`unknown` → candidate `sat` on `xs_29_39`, `xs_30_50`, `xs_36_36`; base
`sat` → candidate `unknown` on `xs_31_41`, `xs_37_37`). `smt_probe_ab.sh`
needs `EXPECT_TRAJECTORY_SHIFT=1` against a baseline that predates this
landing; the next re-pin should be this landing's binary.

The pinned differential (`bench/differential/bench_diff.py`, 270
instances, τ = 10 s, z3-validated models), the two arms back to back on
the landed tree at load 6–15: base **180 solved / 180 agree / 0
disagree**, candidate **177 / 177 / 0**, every `sat` with a valid model
(88 and 89). Seven flips, all at the cap: four the base solved at
10.04–10.6 s, on the cap's lip, and the candidate did not inside τ
(`bench_134`, `bench_315`, `c7b_i`, `hash_sat_08_03`); `c10_i` (6.4 s →
16.6 s), the one solid shift; and two the candidate solved
(`super_queen97-1` 10.8 s, `xs_30_50` 9.2 s) and the base did not. (A
first run of the candidate at load 28–122 read 176; the four it lacked
were the cap-borderline ones.)

Neither seed nor declaration order re-draws an SMT cell: `NIXIE_SAT_SEED`
over ten seeds gives `xs_8_13` 3,357 conflicts in the base and 3,742 in
the candidate at every one, and reordering `c10_i`'s 19 `declare-fun`
forms leaves both arms' counts where they were. So the null was built
from the spelling itself.

**The matched comparison.** The change is exactly a change of spelling:
the base binary on the textually flattened `c10_i` – every directly
nested `and`/`or` spliced, `let` bindings included – reads 13,110
conflicts, the candidate's count on either spelling, against its own
8,514 on the original. That makes the question the reshuffle leaves – is
the flat spelling dearer than the nested one for this solver? – askable
of the base binary alone, on the two spellings of each file: the
treatment against its own null. Over the pinned sample plus the `wisas`
family, 241 instances spell a directly nested `and`/`or`; at `-t 30`, 120
are decisive on both spellings with conflicts to compare:

| base binary, flat spelling against nested – conflicts | count |
|---|---:|
| bit-identical | 45 |
| worse flat | 37 |
| better flat | 38 |
| geomean flat / nested, all 120 | **1.0048** |
| geomean over the 75 that moved | 1.0077 |
| median of the 75; quartiles 10 / 25 / 75 / 90 % | 0.998; 0.62 / 0.88 / 1.18 / 1.50 |
| wall geomean over the 120 (load 16–20, four in parallel) | 0.981 |
| decisive on one spelling only at `-t 30` | 11 only flat (`xs_40_50`, `xs_30_50`, `elf.rf8`, …); 8 only nested (`c10_i`, `c7b_i`, `xs_17_27`, …) |

Per family: `wisas` 26 worse / 23 better (1.014), `mathsat` 7 / 6
(1.000), `UCLID-pred` 2 / 5 (0.971), `RDS` 0 / 3 (0.957), `pete` and
`pete2` one worse each; no verdict differs between the spellings
anywhere. Inside the neutrality band, in both directions: a reshuffle,
neither a regression nor a win on solving. The 10 s row of the
differential is one draw from it, and the 30 s row reads 11 to 8 the
other way.

## The fix – `=>`, `ite` and `xor` in the FF skeleton

`FfTseitin::encode`'s gates were read against their truth tables while the
memo below was being written, and three did not denote their connectives:

* **`=>`**: the clauses `(¬v ∨ a)`, `(¬v ∨ ¬b)`, `(¬a ∨ b ∨ v)` define
  `v ↔ (a ∧ ¬b)` – the *negation* of the implication. `(and (not (= x
  #f0m7)) (=> (= x #f0m7) false))`, satisfied by `x = 1`, read **`unsat`**.
* **`ite`**: two of the four clauses carried `v` with the other polarity,
  so the gate denoted `ite(c, a, ¬b)`: a true else-branch under a false
  condition read false. `(and (not (= x #f0m7)) (= y #f1m7) (ite (= x #f0m7)
  (= y #f0m7) (= y #f1m7)))`, satisfied by `x = 1, y = 1`, read **`unsat`**.
* **`xor`**: eight clauses, four of them the exclusive or's and four the
  equivalence's, all beside `v` or `¬v` – together unsatisfiable, so any
  `TermKind::Xor` node made the skeleton `unsat` whatever its operands.
  The parser spells `xor` as `(or (and a (not b)) (and (not a) b))`, so
  only an API-built `mk_xor` reached it; the random oracle did, at round
  15.

Two more shapes the base got wrong only up to the honesty net: `(=> (= x
#f0m7) (= y #f0m7))` and `(ite (= x #f0m7) (= y #f0m7) false)` read
`unknown` ("model not certified"), the net refusing the model the wrong
gates proposed. A wrong `unsat` has no net. The candidate answers `sat`
with a model on all five.

The gates are now the textbook forms: `v ↔ (a → b)` as `v → (¬a ∨ b)`,
`(a ∧ ¬b) → v`; `v ↔ ite(c, a, b)` as one clause per row that fixes the
branch; `v ↔ (a ⊕ b)` as the four-clause form. The oracle stays:
`every_gate_of_the_skeleton_denotes_its_connective` reads each of the
seven gates against its table under every assignment of its atoms, and
`the_encoded_skeleton_denotes_the_term_over_the_atoms` does the same over
400 random DAGs (shared subterms, every connective, `distinct`) × the 25
assignments of two variables of 𝔽₅. `ff_solver_regression.rs` carries the
two CLI-level regressions (`an_implication_with_a_false_antecedent_is_satisfied`,
`an_ite_takes_its_else_branch_when_the_condition_is_false`); the `xor` gate
has no CLI spelling and is pinned by the two unit tests.

## Slice 2 – the encoder: a subterm is encoded once

The walk expanded every occurrence of a shared subterm on its own: one
gate and its clauses per occurrence, along every path into it –
exponential in the depth of a diamond whose formula is linear in it.
`FfTseitin::encoded` (a `TermId → Lit` map, kept for the encoder's
lifetime across every assertion of the check) answers the second
occurrence with the first one's literal; a subterm is recorded after its
children are. What each assertion's literal denotes over the atom
variables is unchanged, and so is every model of the skeleton projected
onto them. `Combine` frames carry their term for that; a `distinct`'s
conjuncts `¬(a = b)` are expanded as the ordinary terms they are, so a
pair shared by two `distinct`s is encoded once too.

| one encode of the diamond (three gates per level, the top `ite` the root) – instructions per encode | tree walk | memo |
|---|---:|---:|
| depth 10 | 34.20 M | **0.289 M** (0.0085) |
| depth 12 | 197.2 M | **0.343 M** (0.0017) |
| depth 14 | 1,146.6 M | **0.385 M** (0.00034) |

| CLI, whole process – instructions | base | candidate |
|---|---:|---:|
| depth 10, `unsat` by two unit clauses (encoding only) | 33.14 M | **4.12 M** (0.124) |
| depth 12, same | 173.0 M | **4.35 M** (0.025) |
| depth 14, same | 986.5 M | **4.58 M** (0.0046) |
| depth 16, same | 5,760 M | **4.81 M** (0.0008) |
| depth 14, `sat` through one search | 2,095 M | **5.39 M** (0.0026) |
| depth 16, `sat` through one search | 12,212 M | **5.68 M** (0.0005); wall 5.3 s → 0.024 s |

The diamond is spelled with `let` (14 levels of three bindings; 1.3 KB of
text), so the DAG is shared and the parse is nothing. Verdicts identical
in every cell. `a_shared_subterm_is_encoded_once` pins the count: 40
distinct gates and three atoms mint 43 variables, where the tree spelling
of the same term has more than 40,000 gate occurrences.

## Slice 3 – the function-hood scan: applications by index

For every pair of applications of one function the scan searched the whole
application list twice, once per `find`, to reach the two argument lists:
with equal results and fixed arity, Θ(n³) for n applications.
`apps_by_function` groups the applications as indices into `UfffModel::apps`,
each group ascending by the application's `TermId` and the groups by
symbol, so every pair is visited once, in the order it always was (the
first split on a conflicting case is the same split). The same grouping
serves the repair pass and the final gate of `ufff_complete`.

| one scan, n applications of one function, all results equal – instructions | per-pair `find` | by index |
|---|---:|---:|
| n = 200 | 32.39 M | **4.34 M** (0.134) |
| n = 400 | 241.6 M | **17.35 M** (0.072) |
| n = 800 | 1,862 M | **69.4 M** (0.037) |
| n = 1,600 | 14,617 M | **277.7 M** (0.019) |

The retired scan grew ×7.7 per doubling; the new one ×4 – the n²/2 pairs
themselves, ~216 instructions a pair (two value lookups that clone a
`BigUint`, the argument evaluations). That constant is the next headroom
on this scan; the pair order is what the split depends on, so it is not
touched here.

No end-to-end cell: the `QF_UFFF` path does not reach this scan in
reasonable time on the shape (see the findings below).

## Slice 4 – the congruence closure: the queue

After `x = y` was merged, proving `fⁿ(x) = fⁿ(y)` took one full
signature-table rebuild per level: each round re-signed every application
to find the one pair that had just become congruent, Θ(n²) signature
computations for a chain of depth n. `CongruenceClosure` now keeps

* a use list per node (`use_list`): the applications that take it as an
  argument, extended to the applications registered since the last call;
* the members of each class at its root (`class_members`); a class that
  loses a union hands its list to `pending`, and `propagate` re-signs the
  parents of exactly those members, then appends the list to the root the
  class has by then (it may have merged again before the call);
* the signature table across merges: a re-signed application is looked up
  under its new key and merged with the application already there, and a
  merge of two applications queues its own loser's list.

An entry left under an old key is never read: a signature changes only
when one of its argument classes changes root, and a root that lost a
union is never a root again, so no lookup ever produces that key again.
That is the "no stale entry is read" property the module used to buy with
the rebuild, by an argument instead (the module doc carries it).

| one `propagate`, two chains `fⁿ(x)`, `fⁿ(y)` after `x = y` – instructions | rounds | queue |
|---|---:|---:|
| n = 250 | 46.45 M | **0.796 M** (0.017) |
| n = 500 | 183.1 M | **1.546 M** (0.0084) |
| n = 1,000 | 726.5 M | **3.010 M** (0.0041) |
| n = 2,000 | 2,896 M | **5.906 M** (0.0020) |

The rounds quadruple per doubling; the queue doubles. `a_chain_closes_in_one_resigning_per_level`
pins the work at n re-signings for a chain of depth n (a test-only counter
in `sign`), against n rounds over 2n applications.

| CLI, `(assert (= x y)) (assert (distinct fⁿ(x) fⁿ(y)))` – `unsat` in both arms | base | candidate |
|---|---:|---:|
| n = 250 – instructions | 1,078.8 M | **281.0 M** (0.26) |
| n = 500 | 6,939.8 M | **905.5 M** (0.13) |
| n = 1,000 | 50,702 M | **3,818 M** (0.075) |
| n = 2,000 | 390,209 M | **20,673 M** (0.053); wall 19.1 s → 1.3 s |

The partition is the congruence closure whichever congruent pair merged
first, and every output of the closure (`are_equal`, the classes by
ascending node id, the application list) is a function of the partition, so
the solver's derived literals are the same list in the same order. The
retired rounds are the oracle: `the_queued_fixpoint_is_the_rounds_and_the_definition`
runs 400 random goals (chains, diamonds, multi-ary functions, sums) with
merges and further registrations interleaved over several `propagate`
calls, and compares the queue against the rounds and against the
definition (the fixpoint by brute force over every pair of applications);
`merges_before_a_propagate_queue_their_chunks` covers classes that lose
before their first call.

What remains at n = 2,000 (20.7 G instructions) is outside the closure:
the candidate still grows ×5.4 per doubling on this input, in the
`QF_UFFF` path's own walks (a `fields_of_literal` / `literal_mentions_field`
pass per literal over a chain-shaped DAG is already quadratic) and in the
FF conjunction check of 4,000 derived equalities. Not this landing's.

## Slice 5 – the model: the class members once, by representative

`EufSolver::function_application_entries` gave every entry an owned copy of
every member of each of its argument and result classes, so n applications
whose arguments fall into classes of n members copied n² term ids:
2,048 congruent unary applications copied 8,388,608 (32 MiB) for two
distinct lists. A `FuncAppEntry` now names its classes by representative
only; the members are read from a `ClassMembers` snapshot
(`EufSolver::class_member_snapshot`, one pass, CSR: `offsets[i]..offsets[i+1]`
is class `i`'s range, each class ascending by node index, as
`class_members` lists it) taken once per reading pass and shared by every
function that pass reads: `func_interp_lines`, the honesty net's two table
readers and the numeric projection build one per pass; the single-function
entry points (`get_func_interp_raw`, `(get-value)`'s interpretation arm)
one per call, as each call built the entries before. In
`func_interp_reading` an `AppRow` reads a class's members from the
snapshot, or from lists it owns when the application is not the EUF
solver's (a specialized solver's application, previously served by an
O(nodes) `euf_class_terms` scan per argument); membership "already a row"
is the term's representative among the rows' result classes, a set.

| CLI, n congruent unary applications over an uninterpreted sort, `(get-model)` – instructions | base | candidate |
|---|---|---:|
| n = 512 | 288.46 M | 281.44 M (0.976) |
| n = 1,024 | 928.49 M | 902.18 M (0.972) |
| n = 2,048 | 3,301.6 M | 3,217.4 M (0.975) |
| n = 2,048, no `(get-model)` | 3,244.2 M | 3,188.0 M (0.983) |
| the printing itself, n = 2,048 (the difference of the two rows above) | 57.4 M | **29.4 M** (0.51) |

Output is byte-identical to the base on all three (`cmp` of the whole
stdout; 18–75 KB). The solve with no model printed calls none of this
landing and its counters are identical (0 conflicts, 4,095 propagations),
yet its count reads 1.7 % lower: the rebuild's codegen on that path, not a
change in work. The 3.2 G of the solve is the next cost on this family and
is not the model's.

`class_member_snapshot_lists_every_class_in_node_order` compares the
snapshot with `class_members` for every node of a merged E-graph; the three
`function_application_entries` tests read the members through it.

## Findings not landed

* **A consistent linear system is not answered by the linear solver.** In
  `check_conjunction`, `linear_core` reports `Inconsistent` (with a
  certificate) or rewrites the generators, and a consistent system falls
  through to enumeration (while `pⁿ ≤ 2²²`) or to the Gröbner cascade with
  the field equations. Pure `QF_FF`, 2n variables of 𝔽₇ pinned to
  constants (`x_i = #f1m7`, `v_i = #f0m7`): n = 3 `sat` in 5 ms (6
  variables, enumerated); **n = 4 – eight variables, 24 bits – no verdict
  in 60 s**. A model of a consistent linear core would answer each in one
  pass.
* **`QF_UFFF` with four applications of one function answers `unknown` in
  6 s** (five: 17 s; 200: 22 s), three in 17 ms, on the base and the
  candidate alike. Evidently the same cause – not traced: the per-field
  slice holds the n arguments and the n applications as 2n ring
  variables, eight of them from n = 4, the node budget is 2¹⁷ steps
  against the eager path's 2²⁴, and the honest answer to a budget spent in
  the cascade is `unknown`. It is why slice 3 has no end-to-end cell.
* **Landed with this session, found on the way:** `goal_fields` found a
  field only through a constant or an application, so a goal of
  equalities between field variables alone – `(= x1 x0) (= x2 x0)` over
  𝔽₇ – named no field and was declined (`unknown`), and answered `sat` as
  soon as one constant was mentioned anywhere. A field-sorted variable now
  contributes its sort's field, as `literal_mentions_field` reads it
  (`equalities_between_field_variables_alone_are_decided`).
* **An empty `(and)` / `(or)` is a parse error** (`unexpected token:
  RParen`), in the base and the candidate alike: the driver reads an operand
  the moment a frame opens. SMT-LIB gives `(and)` the value `true` and
  `(or)` `false`. Unrelated to this landing and unchanged by it; noted
  because the first draft of the slice's test assumed it parsed.
* The remaining quadratic terms the new counts expose: the function-hood
  pair scan (n²/2 pairs at ~216 instructions), the `QF_UFFF` path's
  per-literal DAG walks (slice 4's CLI row at n = 2,000), and the solve of
  2,048 congruent applications over an uninterpreted sort (3.2 G
  instructions with no model printed).

## Where the landed slices show

`bench/perf_gate/smt_probe_ab.sh`, the landed candidate against the
`cc6eb36e` base, strict: 22 of 25 cells bit-identical (instruction ratio
0.9980–1.0020); the three `wisas` cells shift trajectory as recorded under
slice 1 (with `EXPECT_TRAJECTORY_SHIFT=1` the geomean reads 1.0119 over 25
cells, which is void as a paired cost). The pure-SAT gates execute none of
this landing: `paired_instructions.sh` geomean **1.0000** over 12 cells,
conflicts identical; `run_gate.sh` vs the pinned `28e82c65` **PASS**,
conflicts 1.000 / decisions 1.000 / wall 0.99 (n = 9).

## Bar

Run on the landed tree – `main` at `cc6eb36e` plus the six commits below
– with the candidate built by the standing recipe (sha256 `5b93b0b3…`)
and the base `cc6eb36e` built the same way with the checkout's lock
(sha256 `782d9725…`). Landed as `91342bb9` (slice 1), `5741ab3c` (the
three gates and `goal_fields`), `efbc2b1a` (slice 2), `b3650095` (slice
3), `b0bc9170` (slice 4), `9b3982d7` (slice 5); this record follows.

* `cargo fmt --all -- --check`; `cargo clippy --all-features --all-targets
  -- -D warnings` (the whole workspace); `cargo doc --no-deps
  --all-features` (warnings are errors through `rustdocflags`): clean.
* `cargo nextest run -p nixie-core -p nixie-theories -p nixie-solver
  --all-features --no-fail-fast` (dev profile, `opt-level = 1`, debug
  assertions on, a target directory on another volume, load 27–39):
  **7,626 run, 7,613 passed (4 slow), 12 skipped**, 8 failed, 5 timed
  out. The non-passes are the documented ones plus one load artifact:
  * 5 `SIGABRT` stack overflows: the 128 KiB-stack canaries
    (`*_small_stack` in `context::sort_name` and `context::model_fmt`),
    which pass in the release profile.
  * 2: `choose_of_ite_picks_the_taken_branch` and
    `rejected_set_synthesis_cannot_publish_identical_choices`, the
    documented sets pair.
  * 5 slow-timeout terminations at 180–360 s (`memory_alias_shape_converges`,
    `odd_width_identity_pairs_hold`, `memory_alias_shape_with_guard_clauses_both_polarities`,
    `order_network_random_differential`, `pete_5s_family_instance_is_unsat`),
    which pass in the release profile.
  * `qfidl_qlock_11_base_is_unsat` ran past its 20 s budget on a loaded
    E-core (5.9 s in the earlier run, on `0e86c370` plus this landing);
    the two release binaries decide it in 3.2 s and 3.5 s with the same
    8,897 conflicts – the parser change does not move this instance.
  * An earlier full run, on `0e86c370` plus this landing, failed three
    tests of the first draft of `nested_boolean_operands` – the tests were
    wrong, not the parser (below) – and nothing else; 5 of 5 pass now.
* `bench/z3_parity` (in process on the landed tree, `--out` to a scratch
  file; z3 4.16.0): **171 Correct / 0 Wrong / 6 Inconclusive** – the
  standing result.
* `bench/perf_gate/run_gate.sh` vs the pinned `28e82c65`: **PASS**,
  conflicts 1.000 / decisions 1.000 / wall 0.99 (n = 9).
* `bench/perf_gate/paired_instructions.sh` vs `precompile/cc6eb36e/nixie`:
  geomean **1.0000** over 12 cells, conflicts identical – the pure-SAT
  path executes none of this landing.
* `bench/perf_gate/smt_probe_ab.sh` vs the same base: as above.
* The pinned differential, both arms back to back: **180 / 180 / 0** for
  the base, **177 / 177 / 0** for the candidate, every `sat` with a
  z3-valid model; the seven cap flips are listed under slice 1.
* The spelling experiment under slice 1: 37 worse / 38 better by
  conflicts, geomean 1.0048, no verdict changed.
* The two hand-split commits `5741ab3c` and `efbc2b1a` were built and
  tested on their own in a worktree before landing (17 and 18 tests
  green), so each is green in isolation.

## Traps recorded

* **A lost gate sample is a load artifact until rerun alone.** The first
  `run_gate.sh` ran beside this session's 6-way family sweep and read
  `base=sat cand=none` on `GP_105_308_40` – the candidate had hit the
  150 s cap, as `paired_instructions.sh` showed the same binary deciding
  it minutes earlier at identical counters. Rerun with nothing of this
  session's on the box: PASS. (The script's `VERDICT MISMATCH … seed=1`
  line names the *previous* iteration's `$name`; the table row is the one
  to read.)
* **An oracle written for a perf change is a soundness test.** The memo
  needed a truth table; the truth table failed on `=>` at round 7, on
  `xor` at round 15, and the gate-by-gate table then failed `ite` on its
  own. None of the FF suites reached a `=>` with a false antecedent, an
  `ite` with a true else-branch, or an API-built `xor`.
* **A `-setup` twin must stop where the component starts.** The encoder's
  twin counted the diamond's *tree* occurrences to assert the shape –
  110 M of the 115 M it reported at depth 14 – and the subtraction went
  negative. The twin builds the term and stops.
* **A CLI probe can be unreachable for reasons of its own.** The
  function-hood scan's family never got there: four applications of one
  function exhaust the `QF_UFFF` node budget in the FF cascade. The
  component was measured in-process, and the family's `unknown` is the
  finding above.
* **The volume filled, again.** `cargo clippy --all-targets` for the whole
  workspace died on `No space left on device` at 100 % of `/media/data`;
  `target/debug/incremental` was 5.2 GB of this session's dev-profile
  cache and is what was removed. The gated binary was already cached
  outside `target/`, and its sha256 was re-read after.
* **A worktree has no `Cargo.lock`.** It is gitignored, so a baseline
  built in a throwaway worktree resolves the day's dependency versions
  (`ahash` 0.8.12 → 0.8.14, `const-random` 0.1.18 → 0.1.20, `cc` 1.11.3 →
  1.12.0, …) and is another binary. The first `cc6eb36e` base here was
  built that way (`93bb63dd…`); its differential arm (181) and its probe
  runs were discarded and redone against the locked build. Copy the
  checkout's lock into the worktree first, and read a base's trajectory
  on a known cell before trusting it.
* **A textual flattener must descend into a `let`'s binding list.** The
  first form took a form's first element for its operator and never
  entered `((x v) …)`; `c10_i`'s nesting lives in chained `let` bindings,
  so the "flattened" file kept 326 of its nested `and`s and the base read
  9,141 on it – neither spelling's count, and 3 s of misattribution. The
  candidate's 13,110 on both files is what exposed it.
* **`pkill -f <pattern>` kills the shell that runs it** when the pattern
  occurs in that shell's own command line – twice here, mid-command.
  A script file with the patterns inside is the way.
* **A nextest filter on the test name does not reach an integration test's
  file.** `test(/nested_boolean|…/)` matched nothing of
  `nixie-core/tests/nested_boolean_operands.rs` – its tests are named for
  what they pin, not for the file – and the targeted run reported the
  package green with the new file never built. The full run built it, and
  failed three of its tests. Filter by `binary(name)` too, or run the file.
* **An oracle compares what both sides built, or nothing.** The degenerate
  cases were scripts with no `declare-const`, and both spellings parsed to
  no assertion at all: `"true" == "true"`, nine times, green. Every
  `shape_of_assert` declares its variables now and the loop asserts
  neither side is the empty reading.
* **The solver's `; stats:` line is stderr.** A probe that captures
  stdout alone reads verdicts and no counters.
* **`perf record` is not available on this box** (`perf_event_paranoid = 2`
  and no sample events open): attribution comes from instruction counts
  of twins and variants, not from a profile.
