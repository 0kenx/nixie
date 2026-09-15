# The `smt_model_finder` project, first landing: the constructor tables close the chase, the certification endgame stays open

**Date:** 2026-09-14 (eighth pass of the UFLRA/set arc).
**Input:** `docs/studies/2026-09-14-uflra-handoff-executed.md` — "the
remaining project is Z3 `smt_model_finder`'s entry-table search … a
bounded finite-model-finder project of its own".  Landed as `d49c8936`
(base `5f495e55`); binaries at `precompile/d49c8936/`.
**Comparator:** z3 4.16.0.
**Landing state:** the unit is on branch `mfinder` (code `d49c8936`,
this study `47888de7`, then `--no-ff`-ready merges of the concurrently
moving `main`, tip `1a828838`); binaries cached at
`precompile/d49c8936/` (the exact-SHA build) and
`precompile/1a828838/`.  The primary checkout stayed continuously
dirty with other agents' in-flight work, so the ref move was left to
the next clean window: from any clean checkout,
`git merge --ff-only mfinder` (or `git push . mfinder:main` from this
worktree).  Do NOT `update-ref` over a dirty primary checkout: the new
files would be missing on disk and a careless `git add -A` would commit
their deletion.
**Verdict:** the prescribed entry-table search is built, sound, and it
kills the compound-closure chase outright — the set-family rounds decay
from 300+ instantiations per round to single digits and freeze at the
2-point semantic structure Z3 itself converges on (its model for set16
has `Set!val!0..1`).  **set9/16/19 still answer `unknown`**: the
remaining blocker is the late certification wave against stale frozen
rows, isolated below with the exact instrumented shapes.  Along the way
the hint-macro completion found (and was contained against) a false
`sat` in interaction with the `sat_certify` saturator — that exposure
is the arc's next root-cause project.

## What landed (one unit)

1. **Quasi-macro extraction + semantic constructor tables**
   (`mbqi/constructor_tables.rs`, completion step 10).  For every
   constructor `f : S^n -> S` (uninterpreted range) defined through a
   Bool-valued observer `g` by `g(v..., f(w...)) = psi(v..., w...)`:
   the *row* of a range element is the observer's truth vector over the
   row points (the ground universes of the observer's other arguments);
   at every *unpinned* tuple the computed entry is `f(t) := z` for the
   first — constant-preferring — element whose row matches `psi`'s
   truth at `(row point, t)`.  The completed interpretation is closed
   under its own definitional axioms by construction; `union(b,b)`
   reads `b` because their rows coincide.  Entries live in a separate
   `computed_entries` table consulted after ground pins and before the
   `else` (`eval_apply`, `CompletionEval` concrete and ite-chain), so
   "never override a pin" is structural.
2. **Frozen table domains** (`ModelCompleter::frozen_table_domains`).
   The round a tabled sort (constructor ranges, observer axes) first
   has a non-empty ground universe fixes that universe — canonically
   ordered — as the completed structure's own domain.  This is Z3's
   cardinality choice done at the completion layer: Z3's proto-model
   universes are *model values with fixed cardinality* (its set16 model
   has exactly 2 `Set!val`s and 8 `Elem!val`s), while nixie's harvest
   grows with every term the ground solver mints.  The freeze makes the
   structure immune to that growth: witnesses and late compounds stay
   outside it, the tables recompute over the frozen domain every round,
   and the nested check's Skolem restriction (`table_domain`) confines
   falsifiers to exactly the points the interpretation is defined over.
3. **Semantic value normalization** (`semantic_value_of`, explicit
   stack) and per-quantifier **semantic domains**, installed only for
   constructor argument axes and gated by a **row-determined fixpoint**:
   the collapse `union(b,b) -> b` is only sound to *enumerate over*
   when every use of the tuple variables in the axiom body reads them
   through the observer (row-determined by definition) or a tabled
   constructor (row-closed by construction).  Consumers: the
   enumerative seeder (`build_small_domains`), the counterexample
   generator's candidate lists, the falsifier-mining odometer, and the
   defining pins — each keeps the *raw* universe for non-defining
   axioms (the `seteq` merge-forcing pairs must keep seeing every
   ground pair).
4. **E-matching suspension for table-owned quantifiers**
   (`EmatchEngine::suspend_quantifier`).  The E-match phase after every
   MBQI round matches triggers against the ground term pool — a match
   at a compound term mints the next compound level, and it was the
   last engine still feeding the chase after the domain filters (the
   universe dumps showed second-level compounds
   `(difference b (difference a b))` arriving exactly while the tables
   were declined).  While a constructor table owns a quantifier's
   defining role, its matches are skipped; the pins come from
   `SatisfiedWithPins` at semantic tuples instead.
5. **Evaluation-only certification**: a completed body that folds to
   the literal `true` certifies with no nested solve and no budget
   charge (the ite chains already covered every point of every bound
   variable's domain).  Per-quantifier budget refunds (productive
   checks, certifications, and a once-per-barren-round convergence
   dividend) — **gated on table mode** so goals without tables keep the
   old cap behaviour (see the cost section).

## Measured trajectory (set16, this machine, single seed — indicative)

| build | round-0 insts | steady-state insts/round | universe | verdict |
|---|---|---|---|---|
| base (`5f495e55`) | 142 | 80–400, no decay | 14 → 4000+ entries (`member`) | unknown |
| + tables/domains/freeze | 142 | 3–20 by round 15 | frozen 2-point `Set` | unknown |
| z3 4.16.0 | — | — | `Set!val!0..1`, 8 `Elem!val`s | sat (0.5 s) |

The chase is dead: instantiation flow decays to single digits, the
frozen structure matches Z3's cardinality, and the minting engines
(enum/mining/E-match/cex) are all filtered or suspended for the
defining axioms.

## The remaining blocker (exactly instrumented)

After the flow dies (~round 8), rounds run out with
`per-quantifier check budget exhausted` and late falsifiers for the
defining axioms themselves (`aux Ok(Sat)` at `?s1 := (union a b)`,
`?x := (skf!0 (union b b) (union b b))`).  The instrumented shapes:

- the frozen `Elem` domain can catch **stale compound-arg witness
  Skolems and synthetic seeds** (`u!4`, `skf!0 (union a a) (intersection a b)`)
  in its row points, and ground member pins at those points move after
  the freeze — the rows the tables were computed from drift from the
  rows the pins now assert, and the table's entry at a tuple is then
  *stale* against the pins (the aux falsifier is real; the instance
  lands; the pin cannot move — it is pinned);
- the **merge pump** (axiom-5 at unmerged equal-row pairs forcing
  `w = b` through the interlocking subset/seteq instances) needs the
  nested-∀ antecedents to be *evaluated*, and at the ground layer those
  antecedents are free wrapper Booleans (the committed-Boolean dodge):
  the ground solver satisfies the instances without merging, the
  completed structure ignores the unmerged elements (frozen), and the
  two views never meet.  Z3 never has this gap because its model *is*
  the object being searched — it repairs a table entry and re-checks;
  nixie's completed model is a read-out of the ground solver, so a
  repair must flow back through a lemma the ground solver can accept.

Next step (pre-scoped): the repair path for a *stale pinned row* —
either (a) the falsifier's commitments for the table-owned axioms are
exactly ground pins (`pinned=true` shapes in the mining output), so a
Z3-style `add_blocking_clause` in the **aux** context (never the main
solver — the removed-emission lesson stands) can diversify the falsifier
until it names the pin that must move; or (b) re-freeze: when a frozen
structure's certification wave fails N barren rounds in a row, thaw the
sort and re-freeze at the current universe (a bounded cardinality
escalation, Z3's actual search shape).  Instrumentation that worked:
`NIXIE_DEBUG_CT` (extraction/table/domain lines, depth-tagged),
`NIXIE_DEBUG_QROUNDS` + `NIXIE_DEBUG_MC`, the universe dump at the OOB
decline, and the per-step `function_interps` probes in `complete()`.

## Negative results (do not retry blind)

- **The hint completion is held back (implemented, compiled out).**
  `psi => h(args)` completing a Bool predicate as psi's truth closes
  the *predicate* half (subset as row-containment: axioms 1–3 hold by
  construction, the axiom-2 witness churn dies, axiom-5 becomes the
  merge pump) — but it produced a **false `sat`** on the
  contradictory-definitional-twins shape (`P(x) = not(P(x) => P(x))`
  with tautological-antecedent forcing; z3: unsat; quant_fuzz seed 46).
  The self-reference check on psi does **not** contain it: the
  triggering hint came from a P-*free* psi (`(forall z. false =>
  false) => P x`).  The interaction: the hint's certification + its
  defining pins change the recorded-instance set enough to reach
  `sat_certify` saturation ("every relevant instance is a duplicate ⇒
  Sat") over a goal whose every model is refuted.  The saturation
  logic's complete-set construction is the actual defect surface — that
  is its own root-cause project.  With hints off the reproducer answers
  `unsat` (z3 agrees; base answered `unknown`).
- **Unconditional budget refunds regress the convergence pins**: the
  scope-rebase heaviest pin (`re_running_the_search_on_an_unchanged_
  goal_converges`) ran 636 s release single-threaded with unconditional
  refunds vs ~560 s on clean base — the refunds only stretched
  re-checked goals.  Gated on table mode the pin passes at 219 s
  (within its `terminate-after = 5` budget); note current main-tip
  (`e987b4b6`) *fails 4 of the 9* scope-rebase tests outright from
  another agent's in-flight arc — always diff against the branch base.
- **Freezing after the tables compute is too late**: the freeze must
  run *before* the compute passes in the round a sort first becomes
  non-empty — the row-point product over the grown raw universe
  (`> 64`) silently declines the tables, the freeze then skips the
  sort (it only freezes table-owned sorts), and the growth continues.
  The silent `MAX_ROW_POINTS` decline (no debug line) cost a full
  debug cycle: every cap decline should print under `NIXIE_DEBUG_CT`.
- **The E-match phase is a minting engine**: no amount of
  completion-layer filtering stops the chase while trigger matches at
  compounds keep minting the next level — the suspension is load-bearing.

## Verification

- `quant_fuzz` (strengthened) seeds {41..46} x 150 — **900 cases,
  CLEAN** (≈560 decisive verdicts matched; it *found* the hint
  false-sat at seed 46 before the containment).
- `mixed_fuzz` 250 cases: one `VERDICT` false-`unsat` on a QF_LIRA
  case — **pre-existing at the branch base** (`5f495e55` answers
  `unsat` too; z3: `sat`; current main-tip moved it to `unknown`) —
  another agent's arithmetic arc, not this diff.
- Parity (`run_parity.sh`, z3 4.16.0): **176 Correct / 1 Inconclusive /
  0 wrong** (the pre-existing z3-side `array_unique`).
- nixie-solver + nixie-core: 4656/4657 (the heaviest convergence pin
  times out only under full-suite parallel load; standalone 219 s).
- fmt clean; clippy clean on every touched file (three needless-`mut`
  fixes in another agent's concurrent simplex landing ride along, the
  `15fbf617` precedent; `encode.rs` clippy noise is from a *newer*
  commit than this base and is not touched here).
- **Corpus item closed**: `smt-lib/` verified complete — all 270
  `bench/differential/sample/selected.json` instance paths resolve;
  `set9`/`set16`/`set19` present verbatim (`UF/misc/`).

## The set family's own pins

`set16_family_is_never_wrong` (never `unsat`) and
`set16_diagonal_diseq_disjunct_is_never_falsely_satisfied` (never
`sat`) still pass — the family honestly answers `unknown`.  The
reproducer that the hint containment produced (`twins` shape answering
`unsat` like z3 where base said `unknown`) is pinned inline in the
held-back note; promote it to a named regression when the hint
re-lands.
