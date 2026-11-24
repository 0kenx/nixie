# Optimization opportunity audit against Kissat 4.0.4 and Z3 (2026-11-24, HEAD `61fbec68`)

**Method:** code reading of nixie's SAT core, CDCL(T) integration and arithmetic
solver side by side with the local reference trees (`../temp/kissat`, commit
`8af8e56`, VERSION 4.0.4; `../temp/z3` at `b1168b4`, `smt.arith.solver=6` =
`theory_lra` + `math/lp`), cross-checked against every closed study in
`docs/studies/` so nothing already measured dead is re-proposed. A handful of
short counter runs back the arithmetic findings (below). **Nothing below is
implemented or A/B-measured as a change**; the wall numbers are directional
only (box load was 27–61 on 20 cores), the deterministic counters are exact.

The existing `NEXT_TARGETS.md` (2026-09-05) and scans #1–#5 (2026-11-10…14)
remain accurate for what they close. This audit only lists what is **still
open and not yet tried in the reference's shape**.

## Already at reference parity — do not redo

Watch layout / BIG-authoritative binaries (scan #4 item 4), sweep (kitten port,
default on), factor pre-search, congruence/gate subsumption (opt-in, powered
refusals recorded), OTFS, shrinking, stable/focused machinery (the kissat
tiered arm `NIXIE_TIERED` measured 1.267× worse), reduce tiers / used-shield /
adaptive retention (negative on counters), CSR watches (reverted), root sweep,
lucky phases, DIMACS parser (SIMD landed), `iter_views`, arena compaction,
parser/hashcons (batches J+K), EUF pop trail, simplex column slots.

## Evidence gathered for this audit

Binary `target/release/nixie` (built 19:17 from the current code; the two
later commits are docs-only), single core, `STATS=1`, 25 s cap, interleaved
A‑B‑B‑A. Z3 4.16.0 `-st`.

| instance | nixie default | nixie `NIXIE_NO_RESTART_RESYNC=1` | z3 |
|---|---|---|---|
| QF_UFLIA/mathsat/Wisa/xs-10-18-2-2-5-3 | `unsat` 2.44 / 1.98 s — conflicts 4337, decisions **273 577**, theory_props 930 902 | `unsat` 12.06 / 12.99 s — conflicts 4025, decisions 210 913 | 0.136 s — conflicts **296**, decisions **547**, `arith-bound-propagations-lp` **2090**, `arith-fixed-eqs` **2370**, `arith-conflicts` 56, restarts 2 |
| QF_UFLIA/wisas/xs_8_13 | `unsat` 1.16 / 1.11 s — conflicts 3357, decisions 181 972 | **unknown at 25 s (both runs)** | 0.025 s |

Pure QF_LIA gap cells (nixie counters unavailable on timeout — neither
`--stats` nor `STATS=1` prints on the timeout path):

| instance | nixie | z3 | z3 counters |
|---|---|---|---|
| QF_LIA/rings/ring_2exp4_6vars_2ite_unsat | unknown @20 s | `unsat` 0.03 s | conflicts 141, decisions 858, lp-bound-props **254**, fixed-eqs **156**, arith-conflicts 90 |
| QF_LIA/bofill-scheduling/SMT_random_LIA/ex24800_2600_100 | unknown @20 s | `sat` 0.52 s | conflicts 350, decisions 9121, lp-bound-props **15 963**, fixed-eqs **1843**, arith-conflicts 225 |
| QF_LIA/nec-smt/med/checkpass_pwd/prp-2-26 | unknown @20 s | `unsat` 0.61 s | conflicts 6059, decisions 226 592, lp-bound-props **22 657**, fixed-eqs **17 586**, arith-conflicts 58 |

Two signatures stand out in every gap cell: nixie's search is **starved of
conflicts** (63 decisions per conflict on wisa where z3 runs 1.8), and z3's
runs are dominated by the two arithmetic propagation channels nixie does not
run outside the difference-logic family: LP-derived bound propagation and
"cheap" (fixed/offset) equalities.

## Ranked opportunities

### A. CDCL(T) arithmetic — the Z3 reference (largest measured gap: 156 QF_LIA cells in scan #4)

#### A1. Z3-shaped LP bound propagation + cheap equalities on every LIA/UFLIA fragment (structural, biggest payoff)

**Nixie today.** An arithmetic atom is only *asserted* (`process_constraint` →
`arith_assert_parsed`, `theory_manager.rs:3145`) and checked for crossed
bounds on its own variable (`check_bound_conflicts`, `theory_manager.rs:3836`/
`4218`). The LP runs at `final_check` only (`theory_manager.rs:4460`). The two
propagation channels that exist — `Simplex::propagate_bounds_in`
(`simplex/mod.rs:5961`, internal bound tightening) and
`derive_arith_bound_propagations` (`theory_manager.rs:2358`, atom forcing) —
are armed on `is_dl_family` only.

**Z3.** `theory_lra::propagate()` (`src/smt/theory_lra.cpp:2261`) runs after
*every* BCP fixpoint of the core (`smt_context.cpp:1754 propagate_theories`):
assert the queued bound atoms → `make_feasible()` (line 2312) →
`propagate_bounds_with_lp_solver()` (2401):

* `lar_solver::propagate_bounds_for_touched_rows` (`src/math/lp/lar_solver.h:284`):
  only rows touching a column whose bound changed are examined
  (`detect_rows_with_changed_bounds_for_column`); rows longer than
  `max_row_length_for_bound_propagation` or containing a big number are skipped
  (`calculate_implied_bounds_for_row`, line 113).
* `lp_bound_propagator::add_bound` (`src/math/lp/lp_bound_propagator.h`):
  an implied bound is kept only if it is **interesting** —
  `bound_is_interesting` (`theory_lra.cpp:2423`) requires an *unassigned
  existing atom* on that variable to be implied; `m_unassigned_bounds[v]`
  is an O(1) gate (`propagate_lp_solver_bound`, 2478). No new atoms, no
  speculative bound store.
* The explanation is Farkas (`consume`, 2396 + `explain_implied_bound`) and
  the propagation is a core assignment (`assign(lit, m_core, m_eqs, …)`).
* `propagate_eqs` (`arith.propagate_eqs=true`, default): for each touched
  row with ≤ 2 non-fixed columns, `cheap_eq_on_nbase` derives
  `v1 = v2` from the fixed tables (`try_add_equation_with_lp_fixed_tables`)
  or from two rows of equal value — explains by the bounds of the fixed
  columns only, no probing. These are the `arith-fixed-eqs` /
  `arith-offset-eqs` counters that are 1.5k–23k per solve in the table above.
* Cost control: `arith.propagation_mode=1` (existing literals only);
  `setup_QF_UFLIA` disables both channels after 1000 conflicts
  (`src/params/smt_params.cpp:313`).

**Why this and not the closed threads.** The three negative attempts
(scan #4: per-assignment expression-level channel, the gated widening, the
`NIXIE_ROWPROP` row-driven probe) all pushed *derived expression bounds* and
measured on bofill/convert/pb2010 solve-rate. None of them is the z3 shape:
touched-row interval arithmetic filtered to **existing unassigned atoms**,
plus the cheap-equality channel that feeds EUF/equality atoms. The counter
evidence above says this is where z3's conflict supply comes from on wisa,
rings, bofill and nec-smt.

**First slice (equivalent-work, gateable on counters):** instrument — for the
four cells, count how many *existing* atoms would be implied by a touched-row
pass at each `final_check`, and how many `cheap_eq_on_nbase` equalities exist
among fixed columns. If either number is material, port
`calculate_implied_bounds_for_row` over `columns[v]` for the vars whose
bounds changed since the last pass (`bound_ver` already exists), emit
`theory_props` with Farkas reasons, and arm it per fragment starting with
QF_LIA/QF_UFLIA. Keep `is_dl_family` for the legacy channel.

**Reference files:** `src/smt/theory_lra.cpp` {2261, 2312, 2396–2560},
`src/math/lp/lar_solver.h:113,284`, `src/math/lp/lp_bound_propagator.h`,
`src/smt/smt_context.cpp:1754`, `src/params/smt_params.cpp:313`.

#### A2. Remove the per-restart theory rebuild by fixing what it compensates for (structural, prerequisite for A1/A4)

`TheoryManager::on_backtrack` (`theory_manager.rs:5100–5120`) resets EUF,
arithmetic, BV and DL **on every backtrack to level 0** for function-bearing
inputs with arithmetic — i.e. on every restart — and replays the root atoms.
The A/B above shows the rebuild is **load-bearing**: without it wisa runs 5×
slower with *fewer* conflicts and xs_8_13 times out. The code comment names
the reason: `Simplex::pop` keeps rows permanent (Dutertre–de Moura,
`simplex/mod.rs:6951`), but the internal branch-and-bound interns a fresh
row per Gomory cut (`lia_cuts_then_bnb` → `gomory_cut` → `add_le_with_reasons`,
`arithmetic/solver.rs:3094/3330`; branch bounds themselves are bounds
only, `bnb_search:3614`), so the tableau grows
"430 → 9300+ rows" over a search and only the restart reset compacts it.

Z3 never rebuilds: rows come from *internalized constraints* (finite, one per
atom/cut lemma), integer branches are bounds only (A5), and the basis is kept
across restarts (`theory_lra.cpp:1112 restart_eh` only resets the equality
adapter; the `int_solver::simplify` it calls is a `return;` stub,
`int_solver.cpp:814`).

**First slice:** the scoped-row contract is written down but not
implemented: `Simplex::row_scope_trail` (`simplex/mod.rs:1621–1637`, doc:
"rows interned inside a decision scope are REMOVED by that scope's `pop`")
is never pushed to and never read by `pop` — it is only cleared in `reset`
(`:6905`). So every cut row `lia_cuts_then_bnb`
interns is permanent, for the whole search. Count them per search on the two
A/B cells, make cut/branch rows scope-local (fill the trail in
`intern_row_reported`, consume it in `pop`, fix the stale doc), then re-run
the `NIXIE_NO_RESTART_RESYNC=1` A/B: it should turn from 5× slower to ≥
neutral. Only then does removing the resync become a pure win (it also
restores the warm-started basis that A4 needs).

#### A3. O(1) arithmetic atom assertion (equivalent-work; profiled as scan #2/#3 item 7, still open)

Every re-assertion of an atom (`ArithSolver::assert_le/ge/lt/gt/eq`,
`arithmetic/solver.rs:1464–1947`) rebuilds the canonical form before hitting
the cache: `row_key` (607: Vec + `binary_search_by_key` inserts + gcd),
`cached_row_slack` (698: a fresh `LinExpr` through `add_term`'s linear scans,
`canonicalize_lin_form`, sort, `is_integral_form`, then **a second
`row_key`**), one `(RowKey, TermId)` hash, `add_reason`, plus
`std::env::var_os("NIXIE_TRACE_TWRITES")` for single-term atoms. The result
(`slack: VarId`, bound kind) is a pure function of the atom.

Z3 precomputes it at internalization: `mk_bound`/`internalize` register the
term's columns and push an `api_bound` into `m_bounds[v]`; at search time
`assert_bound` is one `set_bound` plus the column walk.

**First slice:** memoize `slack` (and the reason id) on the
`ParsedArithConstraint` the theory manager already keys by `Var`; make
`arith_assert_parsed` a `set_lower/upper(slack, 0, reason)`. Trajectory must
stay bit-identical (same rows, same bounds). This is the "intern key churn"
leaf of scans #2/#3 (`is_full` 33.7 %, `find_or_find_insert` 20.8 % on
storecomm).

#### A4. Run the simplex during propagation, not only at `final_check` (structural)

With A2/A3 in place, `make_feasible` can run after each assertion batch as in
z3 (`theory_lra.cpp:2312`), so bound violations surface at *partial*
assignments — short explanations, early backjumps — instead of at complete
candidates. The current comment at `theory_manager.rs:4212` records why this
was switched off (a full re-solve per literal was 50 % of `dlx`/`pp-*`); the
precondition is an incrementally maintained assignment (`assignment_current`)
and basis across restarts, i.e. A2.

#### A5. CDCL-first integer branching (structural; mixed prior evidence)

`lia_branch_and_bound` (`arithmetic/solver.rs:3047`) runs an internal
tree (`bnb_search`, 3585; node/depth budgets) first and asks the core for a
split only at budget decline (the branch channel, default armed since the
rung-3 flip). Z3 has no internal tree: `int_solver::check`
(`src/math/lp/int_solver.cpp:272`) runs gcd test → patch → cube → HNF →
Diophantine → Gomory (2 cuts) → `int_branch` (`src/math/lp/int_branch.cpp`:
`select_int_infeasible_var` prefers small boxed columns, small values, then
usage) which mints a fresh bound atom `t ≤ k` / `t ≥ k+1` with gcd-reduced
coefficients (`theory_lra.cpp:1849 mk_bound`, case `branch` at 2033) and lets
the core decide it. Every branch is a CDCL decision with learned clauses; no
rows are added.

The earlier budget-cut arm regressed `v20_problem__019`; that arm kept the
internal search as the primary and only shortened it. The z3 shape inverts
the order and removes the row growth that forces A2's rebuild. Treat as a
pre-registered heuristic experiment with the existing channel infrastructure
(the rung-3 machinery: `NIXIE_LIA_BRANCH_NULL` matched null, ≥10 seeds).

#### A6. In-place sparse tableau (NEXT_TARGETS #3, still open)

`LinExpr` is an unsorted `SmallVec<[(VarId, Rational64); 4]>`
(`simplex/mod.rs:709`); `try_add_term_mul` (766) linearly searches the
destination row per term, so a pivot costs O(|pivot row| × |row|) per dependent
row plus a replacement `Arc` row per row. Z3's `static_matrix` edits rows in
place with a work-vector index (`src/math/lp/static_matrix_def.h:51
pivot_row_to_row_given_cell`, `:45 scan_row_strip_to_work_vector`). The
column-slot back-pointers (`f5fb11ef`) did the removal half; the substitution
half remains.

### B. SAT core — the Kissat reference (smaller, heuristic class; each needs the ≥10-seed matched-null protocol)

#### B1. `reorder` — never ported (deferred "Slice B" of the tiered-schedule study)

`src/reorder.c`: every `reorderint` (10 000) conflicts, weight each variable
by `max(pos,neg) + 2·min(pos,neg)` over occurrence weights `2^(2−size)` in
irredundant clauses (size capped at `reordermaxsize` 100) plus binaries; in
focused mode re-order the VMTF queue by weight, in stable mode rescale scores
and add the weight. Default `reorder=2` (both modes). Nixie has no equivalent
(`decide.rs:38 pick_branch_var` has no structural re-weighting). Cost O(clause
literals) per 10k conflicts.

#### B2. Random decision sequences in focused mode (`randec`)

`src/decide.c:86 next_random_decision` + `:57 kissat_start_random_sequence`: every
`randecint` (500) conflicts at level ≤ 1, pick uniformly random unassigned
variables for `randeclength` (10) × log₂(sequences so far) conflicts; on by
default in focused mode
(`randec=1`, `randecfocused=1`), off in stable. Nixie has random *polarity*
only (`random_polarity_prob`, 0.01 in the cadical preset).

#### B3. Bump reason-side literals (`bumpreasons`)

`src/analyze.c:169 analyze_reason_side_literals` (default on): after the
1-UIP clause, also bump the literals of each conflict-side literal's reason
clause, capped at `bumpreasonslimit` (10×) extra literals and gated on a
decision-rate EMA < `bumpreasonsrate` (10) with exponential back-off. Nixie's
`conflict.rs` has no reason-side bumping (the throughput campaign only
considered cadical's capped variant as a cost).

#### B4. Glue recomputation and promotion on use (`promote`)

`src/deduce.c:14 mark_clause_as_used` → `kissat_recompute_glue` +
`kissat_promote_clause` (`src/promote.c`): a reason clause whose current LBD is
below its learned glue is promoted (tier limits follow usage in `tiers.c`).
Nixie freezes `lbd` at learn time; `ClauseDatabase::record_usage`
(`clause.rs:507`) promotes on counts only, and `dynamic_lbd.rs`
(`DynamicLbdManager`) is exported but unwired into `Solver`.

#### B5. Binary-clause double storage (NEXT_TARGETS #5, still open; memory)

`BinaryImplicationGraph::edges: Vec<(Lit, ClauseId)>` (`solver/mod.rs:136`)
plus a full arena slot per binary. Kissat keeps binaries in the watch lists
only (`clause.c new_binary_clause` → `INVALID_REF`). Memory item, large scope.

### C. Hot-path hygiene (equivalent-work, mechanical)

Per-call `std::env::var` in theory hot paths — each takes the environment
lock and scans `environ`:

* `arithmetic/solver.rs:1255,1275,1326,1502,1543,1874,1936`
  (`NIXIE_TRACE_TWRITES`) — on every single-term assertion and every
  propagation-bound write;
* `arithmetic/simplex/mod.rs:5974,5998` (`NIXIE_S6_NDIR2`, `NIXIE_S6_PINNED`)
  — per `propagate_bounds_in` call;
* `solver/theory_manager.rs:5113` (`NIXIE_NO_RESTART_RESYNC`) — per
  backtrack to root; `:2629` (`NIXIE_APROP_VERIFY`) — inside the derive loop.

The SAT kernel already snapshots such gates once per solver (`63bed214`,
`ScanProbes`); the theory side should do the same (`OnceLock`).

## Suggested order

1. **A3 + C** — equivalent-work, bit-identical counters, no new invariants;
   removes the per-assertion churn that A1/A4 will multiply.
2. **A1 instrumentation slice** — counters only: how many existing atoms and
   cheap equalities a touched-row pass would yield on the four cells. That
   number decides whether to port the z3 propagator.
3. **A2** — make B&B rows scope-local, re-measure the resync A/B; then drop
   the rebuild.
4. **A4 / A5** — once the state survives restarts.
5. **B1–B4** — independent of the above; one pre-registered arm each
   (`docs/BENCHMARKING.md`), B1 first (it is the only structural one and has
   no prior negative).

## Traps recorded during this audit

* `nixie --stats` prints nothing on the timeout path; use `STATS=1` and a
  solving instance, or accept counter-less timeouts.
* The in-repo `smt-lib/non-incremental` layout nests families one level
  deeper than `docs/studies/data/scan4/smt.tsv` names them
  (`CAV_2009_benchmarks/smt/<n>-vars/…`); resolve with `find`.
* `NIXIE_NO_RESTART_RESYNC=1` changes the trajectory (conflicts 4337 → 4025),
  so its A/B is not a pure cost comparison — the 5× wall with fewer
  conflicts/decisions is the signal, not the ratio.
