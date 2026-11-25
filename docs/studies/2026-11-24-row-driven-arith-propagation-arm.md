# Row-driven arithmetic propagation – the A1 study arm, its census, and the false-`unsat` the clause dump caught (2026-11-24)

Execution of item **A1** of
[`2026-11-24-kissat-z3-opportunity-audit.md`](2026-11-24-kissat-z3-opportunity-audit.md)
(z3 `propagate_bounds_with_lp_solver`'s bound half): a default-off study arm
`NIXIE_APROP_ROW=1`, the yield census that sized it, the soundness record, and
the measurement that says how far the first three slices get. **Nothing here
changes the default search**: unarmed, the tree is counter-identical to
`3f6f83b9` on the 17-cell probe corpus (instructions 1.0014 geomean – the
unarmed hook is one `OnceLock` load per arithmetic assertion and one `bool`
test per bound write).

## 1. The census (`NIXIE_APROP_CENSUS=1`) – why the arm exists

One stderr line per FEASIBLE arithmetic final check
(`[aprop-census]`), plus event counters every 2 000th event (`[aprop-tick]`):
where the search's conflicts come from and whether it reaches a feasible LP
check at all.

| cell | final checks | feasible checks | arith conflicts | atoms | forced / feasible check (assigned that way) | fixed pairs |
|---|---:|---:|---:|---:|---:|---:|
| QF_UFLIA Wisa xs-10-18-2-2-5-3 (`unsat`, 4 337 conflicts) | ≥ 2 012 | 48 | ≥ 2 000 | 520 | **187.8** (9 015 same / 0 opposite / 0 unassigned) | 12.6 |
| QF_UFLIA wisas xs_8_13 (`unsat`, 3 357) | ≥ 2 043 | 172 | ≥ 2 000 | 430 | **173.9** (29 911 / 0 / 0) | 14.7 |
| QF_LIA bofill ex24800_2600_100 (base `unknown`) | ≥ 6 000 | **0** | ≥ 6 000 | – | – | – |
| QF_LIA nec-smt prp-2-26 (base `unknown`) | ≥ 6 000 | **0** | ≥ 6 000 | – | – | – |
| QF_AUFLIA cvc/dlx-pc (base `unknown`) | ≥ 6 000 | **0** | ≥ 6 000 | – | – | – |

Two facts. (1) On the wisa cells the search is *guess a complete assignment,
let the LP refute it* – over 2 000 leaf refutations against 48 feasible
checks – and at every feasible leaf **36–40 % of the atoms are already forced
by the arithmetic bounds of the other atoms** (z3 on the same cell: 296
conflicts, 547 decisions, 2 090 `arith-bound-propagations-lp`). (2) On the
three pure/arithmetic-heavy gap cells nixie **never reaches a feasible LP
check**: every one of ≥ 6 000 complete assignments is LP-infeasible. z3 solves
bofill in 350 conflicts / 15 963 bound propagations, prp-2-26 in 6 059 /
22 657, the ring in 141 / 254 – its conflicts come from propagation at
*partial* assignments, nixie's from refuting *complete* ones.

## 2. The arm – what it does

`TheoryManager::on_assignment`, after a successful arithmetic atom assertion:

* `ArithSolver::drain_implied_atom_polarities` – z3's `touched_rows`: the
  simplex marks the rows a bound write can change (`aprop_mark_rows_of`: the
  variable's own row when basic, the rows of the basics in its column); the
  drain pops them.
* Per row (an inequality atom's slack, basic, live narrow row): the Dutertre–de
  Moura interval of the row from the **effective** bounds of its variables –
  the simplex bound, the single-term tracker bound (`record_prop_bound`: the
  z3 internalization analogue for `coef·x ∘ rhs` atoms, which the
  slack-per-atom tableau never shows as a bound on `x`), or the tighter – with
  every consumed bound's complete antecedent set (`all_reasons`, the tracker's
  atom). A form's own polarity is forced when the interval entails its
  `slack ∘ 0`, its negation when it entails the strict opposite (δ-ordering).
* **Equality pins** (the fixed-table half of z3's `cheap_eq_on_nbase`): a
  pinned `s = coef·x − rhs` pins `x`, and every other single-term inequality
  atom row on `x` gets a value.
* SAT half (`arith_row_propagations`): only atoms the core has not assigned
  (z3 `bound_is_interesting`), polarity translated through the atom's parsed
  constraint type (the parser may flip the comparison), antecedents all live,
  never the atom itself among its own antecedents, explanation built by the
  conflict machinery (`terms_to_conflict_clause`: derived-equality tags
  expanded, tautologies dropped).

Tooling, all env-gated and kept:

* `NIXIE_APROP_ROW_VERIFY=1` – LP oracle: push a scratch scope, assert the
  form's opposite bound on its own slack, require `Simplex::check` to report
  infeasibility; an unjustified propagation is dropped and reported.
* `NIXIE_APROP_ROW_VERIFY=2` – SMT-LIB dump of the propagation clauses
  (`/tmp/aprop_row_clauses/NNN.smt2`, `NIXIE_APROP_ROW_DUMP_N` cap):
  antecedents with their assigned polarity, the forced literal negated –
  `sat` from z3 is an invalid clause. (`3` = both.)
* `NIXIE_THEORY_CONFLICT_DUMP=<cap>` – the same for every theory conflict
  through `conflict_from_terms` (`/tmp/theory_conflicts/`).

## 3. The false `unsat`, and how it was found

First armed run: wisa dropped to **104 conflicts** (from 4 337) and the ring
solved in 10 – and bofill `ex24800_2600_100` answered `unsat` where z3 answers
`sat` (z3's model re-checks: the instance instantiated under it is `sat`,
`unsat` under `false`).

The LP oracle reported nothing and the first 500 dumped clauses were valid;
widening the dump to every clause (2 199) and checking them all with z3 gave
**2 199 / 2 199 valid** – and still `unsat`. The clauses were right; their
*polarity at the SAT interface* was not: `TheoryCheckResult::Propagated`
takes the antecedents' **true** literals (`add_theory_reason_clause` builds
`lit ∨ ¬r₀ ∨ …`), the conflict machinery returns each antecedent's **false**
literal. The arm passed false literals, so the core materialized
`lit ∨ r₀ ∨ …` – a clause satisfied by its own antecedents, meaningless once
resolution resolved through it. One `negate()` fixed it; the dramatic counts
went with it.

That is the trap worth keeping: **a theory-propagation channel needs the z3
clause check before any conflict count is believed** – the LP oracle proves
the propagation, not the clause the core learns from it.

## 4. What the sound arm measures (armed vs `3f6f83b9`, single deterministic counters)

First cut of the touched-row drain (big-rational arithmetic per derived
bound, a full `slack_forms` scan per equality pin): wisa conflicts 0.72–0.76×,
decisions 0.38–0.45×, **instructions 1.69–1.83×** (wall 2.0 → 4.4 s on
xs-10-18), UFIDL 4.1×. The cost slice that followed (`3b6c8e92` → this
commit): `i64`-checked narrow arithmetic (`checked_scale_add`; overflow
declines the row) instead of `BigRational`, and a `variable → single-term
atom rows` index rebuilt only when `slack_forms` grows, instead of the
per-pin rescan. Counters are unchanged on every cell (the index keeps the
scan's visit order); the cost moved:

| cell | base | armed | conflicts | decisions | instructions (before → after) |
|---|---|---|---:|---:|---:|
| QF_UFLIA Wisa xs-10-18-2-2-5-3 | `unsat` 4 337 / 273 577 | `unsat` 3 273 / 105 076 | **0.755** | 0.384 | 1.76 → **1.15** |
| QF_UFLIA wisas xs_8_13 | `unsat` 3 357 / 181 972 | `unsat` 2 417 / 68 127 | **0.720** | 0.374 | 1.69 → **1.15** |
| QF_UFLIA wisas xs_10_20 | `unsat` 8 751 / 344 239 | `unsat` 6 261 / 155 910 | **0.715** | 0.453 | 1.83 → **1.42** |
| QF_ANIA avg20_true-unreach-call.i_0 | `unknown` (283 / 21 096) | **`sat`** 463 / 79 744 – z3 `sat` | – | – | 1.05 |
| QF_UFIDL vlsat3_f30 (budget 3 000) | 3 000 / 128 296 | 3 000 / 117 243 | 1.000 | 0.914 | 4.11 → **3.87** |
| QF_AUFLIA dlx-pc (budget 2 000) | 2 000 / 3 611 781 | 2 000 / 2 252 764 | 1.000 | 0.624 | 2.94 |
| QF_LIA ring_2exp4_6vars_2ite (`unsat`) | `unknown` @60 s | `unknown` (664 conflicts at the 3 000 budget, 0.24× the work) | – | – | – |
| QF_LIA nec-smt prp-2-26, bofill ex24800 | `unknown` | `unknown` | – | – | 0.83 / 0.51 of the base work in 60 s |
| QF_LIA CAV 25/40-vars, slacks ×2, dillig (sat, 0 conflicts); QF_UF PEQ020; QF_IDL vlsat3_c60; QF_ANIA `8` | identical counters | | 1.000 | 1.000 | ≤ 1.005 |

Verdicts agree with z3 on every cell either solver decides. The search
benefit is real but modest (25–28 % of the wisa conflicts; one ANIA
`unknown → sat`), and the cost is still positive everywhere the arm has
work to do: +15 % on the wisa class, 3–4× on UFIDL and the AUFLIA budget
cell (many two-term rows go stale per assertion there; the equality-pin pass
iterates every single-term row on the pinned variable). Wall on a quiet core
would be roughly break-even on wisa and a regression elsewhere – not a
landing candidate as is.

## 5. Verdict on this slice, and what the z3 gap actually is

Three sound slices (touched rows, tracker bounds, equality pins) recover
**25–28 % of the wisa conflicts** and one ANIA `unknown → sat`; z3's count on
the same cells is another 10× lower. The census says why the bound half alone
cannot close it:

* **Atoms are slack rows, not bounds on columns.** In z3 `x ≤ c` and `x = c`
  are bounds on `x`; a touched row's interval arithmetic sees them directly.
  In nixie an atom is `s = lhs − rhs` with a bound on `s`; `x` itself is
  bounded only through the tracker (single-term inequalities) and the new
  equality-pin pass. A two-term atom (`arg1 ≥ fmt0`) bounds nothing a later
  row can use until the LP pivots it into a basic's row – which the arm, by
  design, never runs.
* **No LP in propagation.** z3 calls `make_feasible` after every BCP fixpoint
  (`theory_lra.cpp:2312`), so a violated bound is a conflict at a *partial*
  assignment, and at a feasible vertex every non-basic sits at a bound (rows
  derive). nixie's LP runs at `final_check` only; the three gap cells never
  get there feasibly.
* **No closure.** A derived bound is used once, never stored, so it cannot
  feed the next row (z3 gets the closure through the core: a propagated atom
  is an asserted bound on the next pass).

### Next slices (pre-registration sketch, in order)

1. **Cost, second round.** The first round landed (`Rational64` checked
   arithmetic; the `variable → single-term atom rows` index): wisa +15 %.
   Still open: UFIDL / AUFLIA 3–4× – every two-term assertion stales every
   row through both of its variables, each stale row pays `defining_row`
   (an `Int`-form row materializes on read: one gcd per term) and two
   `effective_bound` pair lookups per term; and the equality-pin pass walks
   every single-term row on the pinned variable. Candidates: skip rows whose
   variables are all unbounded in the needed direction before materializing
   (a `has_any_bound` pre-filter per column), memoize the materialized narrow
   row per dirty round, and bound the pin pass per assertion. The arm must
   cost < 1.05× on the non-gap probe cells before any search claim is
   readable.
2. **A4** – `make_feasible` + the propagation drain at each BCP fixpoint on
   the arith atoms (z3 `propagate()`), behind `NIXIE_APROP_ROW=lp`: the leaf
   refutations become partial-assignment conflicts. Prerequisite: the
   incremental assignment survives restarts (audit item A2).
3. **Closure** – store derived *variable* bounds with antecedents (un-scope
   the slice-6 `propagate_bounds_in` direction-2 from wide-row states), so
   multi-term rows derive; or the 2-hop form (derived bound on `x` applied to
   the rows through `x`) without storing.
4. Gate per family (the 4× UFIDL cost) and re-run the matched-null protocol of
   `docs/BENCHMARKING.md` §2 before any default flip; the census (`opposite`
   must stay 0) and the clause dump stay in every run.

## 6. Bar for the landing (default-off arm, unarmed path)

`cargo fmt --check`; `cargo clippy --release --all-features --all-targets
-p nixie-theories -p nixie-solver -- -D warnings` clean (after the
`needless_borrow` follow-up `fec10404` to `3f6f83b9` – that landing's clippy
run predated its last edit); `cargo nextest run --release` for the two crates
**5 291 passed** (the two documented pre-existing HEAD failures excluded);
`bench/z3_parity/run_parity.sh` **171 Correct / 0 Wrong / 6 Inconclusive**
(z3 4.16.0); `bench/perf_gate/smt_probe_ab.sh` unarmed vs `3f6f83b9`:
counters identical on all 17 cells, instructions 1.0014. The cost slice
(on top of `3b6c8e92`): same suite, clippy clean, `smt_probe_ab.sh` unarmed
vs `3b6c8e92` identical counters, 1.0002; armed counters identical to the
first cut on every cell above.

## 7. Traps recorded

* **Explanation polarity is the core's contract, not the conflict
  machinery's.** `Propagated((lit, reason_lits))` wants TRUE antecedent
  literals; `terms_to_conflict_clause` yields FALSE ones. Negate at the
  boundary, and z3-check the learned clause before believing a conflict
  count – the wrong polarity made the search look 40× better.
* The SMT-LIB reconstruction prints operators glued to the first operand
  (`(=xH211 …)`, `(-xH210 xH471)`); z3 reports parse errors and still prints
  `sat`. Normalize (`(<=|>=|[<>=*+-])` + non-space → insert a space) and treat
  any `error` line as a failed check.
* `assigned_pol_of` is not a liveness test (it returns the polarity a var was
  ever assigned); use `is_level_assigned` for "currently assigned".
* **Never `cargo fmt --all` in the shared tree**: it reformats other agents'
  unformatted in-progress files (two `nixie-tla-check` files were rewritten
  and restored to HEAD here). `cargo fmt --all -- --check` to look, per-file
  `rustfmt` on owned files to fix.
* `cargo nextest` fails fast: one pre-existing failure cancels the remaining
  3 233 tests; pass the documented exclusion filter.
* `&`-terminated `&&` chains in a tool call may not survive the call's exit;
  `setsid nohup script.sh &` for long verification chains.
