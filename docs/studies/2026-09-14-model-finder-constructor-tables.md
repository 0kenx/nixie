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


## The saturation root cause and fix (2026-09-15, follow-up)

The held-back hint's false-`sat` is root-caused, fixed, and the hint is
**un-held**.  The defect was never the hint — it was (and is now closed
in) `sat_certify`'s fragment eligibility:

**The mechanism, instrumented end to end.**  The twins goal
(`P(x) = not(P(x) => P(x))` plus tautological-antecedent forcing) has
its forcing axiom registered with a *simplified* body
`(=> (forall ((z S)) true) (P x))`.  The EU walk's catch-all admits a
subterm that "mentions no bound variable" — and the collapsed premise
`(forall z. true)` mentions none, so the nested quantifier passed as
"ground".  The round-0 enumerative instances were then asserted with
their **raw** bodies: the encoder wraps `(forall z. true)` in a free
Boolean, the SAT core commits it FALSE (the committed-Boolean dodge),
and the implication clauses are satisfied *vacuously* — the ground
model never sees the forcing.  Round 1 asserts the twin's clean units
(`P(u!k) = false`); round 2's `sat_certify` observes "every relevant
instance already recorded + a ground solver model" and concludes
`Satisfied` — over an instance set the model satisfies only in its
Tseitin encoding, not in its semantics.  The audit that pinned it: at
saturation, the model's values for the recorded twin instances read
`false`/unassigned (violated), and the SAT model showed
`P(u!k) = false` for every `k` while the forcing instances' wrapper
premises read FALSE.

**The fix** (`sat_certify::universal_instances`): a body containing
*any* quantifier is outside the certifiable fragment, however EU its
variable occurrences — the instance lemmas would carry the nested
binder, and the ground solver's model of their encoding is not a model
of their semantics.  One guard:
`contains_quantifier(body) => NotEligible`.  Conservative (a nested
binder that other engines eliminate first could, in principle, be
certified later); soundness first.

**Pre-existing, not hint-caused.**  Nothing in the mechanism depends on
the hint — it only created the trajectory.  The exposure needed: an
axiom whose tracked body has a bound-var-free nested quantifier (any
`forall z. <no-x>` premise — the tautological-antecedent family
`contradictory_definitional_twins_*` generates them), a stabilised
relevant set, and round-0 emissions that dodge.  The bug has been on
`main` since the fragment certifier landed.

**Verification.**  With the hint re-enabled *and* the fix in:
the twins reproducer answers `unsat` (z3 agrees; pinned as
`nested_quantifier_premise_never_saturates_a_false_sat`); quant_fuzz
seeds {41..46} x 150 CLEAN; parity 176 Correct / 1 Inconclusive /
0 wrong (z3 4.16.0); nixie-solver + nixie-core 4719/4720 (the one
timeout is the heaviest convergence pin under full-suite parallel
load — passes standalone); fmt/clippy clean.

**The hint is live**: subset-class predicates complete as their
defining implication's truth (the set family's `subset` as
row-containment).  The two remaining legs of that arc — the merge pump
and the frozen-row repair — are unchanged from the study above.


## Bounded-quantifier expansion in the completed body (2026-09-15, second follow-up)

With the hint live, the set family's stall moved to the *nested
quantifiers in the completed body*: the aux check of an axiom whose
body' carries a nested `forall`/`exists` (axiom-2's witness, axiom-3's
containment antecedent) spawned the nested solver's *own* full MBQI
loop per check — thirteen budgeted iterations per round — and timed
out to `Unknown` exactly on the quantifiers the hint should have
certified.

**The fix** (`CompletionEval`, the binder arm): a binder whose every
bound variable ranges over a *finitely restrictable* domain — read
from `CompletedModel::table_domain`, the same source the nested
check's Skolem restriction uses — is expanded at completion time into
its pointwise fold (`forall x. phi` -> `and(phi[d])`, with
short-circuit), under a 64-point product cap.  This is not an
approximation: the restricted nested solve decides exactly the
expanded reading, and doing it deterministically at completion makes
the completed body quantifier-free, so the nested solve becomes a
plain ite-chain solve and the aux's own quantifier loop disappears.
Binders over sampled/infinite sorts (Int, Real, ...) stay symbolic,
as before.  This is Z3's model evaluator's own behaviour (it evaluates
ground quantifiers over its finite model universes).

**Measured**: set16 62 s -> 18 s to its (unchanged) `unknown`; the
round flow now dies within ~13 rounds.  The residual stall is the
*stale pin* shape isolated above: a dodged ground pin (e.g.
`subset(w, a) = true` from an era whose rows differed) permanently
contradicts the current rows; the falsifier at that pair is permanent,
its instance a duplicate, and nothing moves the pin.  Notably, the
expansion also kills the dodge *for future instances* — an axiom-3
instance asserted now has its antecedent pointwise-concrete, so the
ground solver can no longer satisfy it vacuously.  Old pins from
pre-expansion rounds remain; the repair for those is the next
mechanism: blocking the demonstrated-incompatible pin arrangement
(Z3's `add_blocking_clause` semantics on *ground-model pin*
commitments only — never on asserted-constraint atoms; the
false-`unsat` lesson of the removed emission stands, so the
atom-classification needs its own careful design).

Verification: quant_fuzz {41..46} x 150 CLEAN; parity 176 Correct /
1 Inconclusive / 0 wrong (z3 4.16.0); nixie-solver + nixie-core
4725/4728 (the 3 timeouts are the convergence pins under full-suite
parallel load); fmt/clippy clean.


## The stale-pin repair: sound at last, via the raw-body walk (2026-09-15, third follow-up)

The blocking-clause repair is re-landed, sound.  Two findings on the way:

1. **The completed-body walk is the documented trap, re-derived the hard
   way.**  Emitting the clause from falsifiers recorded over the
   *substituted completed body* produced six false-`unsat`s in one
   quant_fuzz sweep (seeds 41-46): the completed body's syntax bakes
   the completion's choices (macro unfoldings, ite-chain shapes, else
   leaves) in positions the recording walk never visits — a macro that
   unfolded `seteq(a,b)` to `(= a b)` during the *construction* of
   body' leaves no macro application for the walk to flag, so
   "fully pinned" counted the choice as a pin.  The original removal
   note said exactly this; the transfer argument (every model of the
   assertions agreeing with all recorded commitments falsifies the
   asserted quantifier, so the blocking disjunction is valid) is only
   as good as the recording, and the recording can only see what the
   *walk* consults.  **The walk now runs on the raw substituted body**
   (`q.body` under the falsifier's substitution): every completion
   choice passes through `fold_apply`'s macro/computed/else arms, which
   flag it; the recording is then complete and the transfer argument
   closes.  The entry-normalization consults the chain construction
   bakes in (`entry_arg` read through its model value) are recorded too
   — the one consult class the old audit missed.

2. **The cost gate is load-bearing.**  Ungated, the clauses churn
   re-checked searches: the scope-rebase convergence pin regressed past
   400 s (219-279 s in band).  Emission is gated on the quantifier
   being table-owned — the repair exists for the table arc's stale-pin
   stall, and the falsifier that matters (axiom-3's at the unmerged
   pair, whose walk is pure ground pins: the member rows plus the
   dodged `subset(w,a)` pin) is table-owned by construction (it is the
   hint's defining axiom).

**State of the family**: the repair fires (one clause on set16) and the
whole family got faster (set16 18 s -> 5 s; set9/set19 ~25 s) — but all
three still answer `unknown`.  The next blocker, precisely: rounds
6-11 each mint ~6 fresh defining pins against the caps ("per-quantifier
check budget exhausted") — the pin tuples stay *fresh* because the
mining domains churn slightly per round.  That churn is the next
instrumentation target (NIXIE_DEBUG_MC's pin lines plus the domain
dump).

Verification: quant_fuzz seeds {41..46} x 150 CLEAN (it killed the
completed-body variant first); parity 176 Correct / 1 Inconclusive /
0 wrong (z3 4.16.0); nixie-solver + nixie-core 4724/4728 (timeouts =
the parallel-load pins; the heaviest passes standalone at 279 s, inside
its terminate-after budget); fmt/clippy clean.


## Table mode owns the whole problem (2026-09-15, fourth follow-up)

The fresh-pin churn was two engines certifying one problem against two
different semantics:

- `sat_certify` (the Ge & de Moura fragment certifier) runs against the
  *raw ground model* — and its relevant-set harvest grows with the
  model's own entries.  Each emitted instance mints the next compound
  level; the tuples never stop being fresh.  After the table-owned
  quantifiers were declined, the churn simply moved to the *other*
  axioms' relevant sets (~6 "fresh" instances per round, minter of the
  permanent `member` bloat that later priced every nested check past
  the global budget).
- The table machinery certifies against the *completed structure*
  (frozen domains, tables, aux restrictions).

**The fix is a semantics separation**: when `constructor_sources` is
non-empty (table mode), `sat_certify` declines the whole problem, and
every engine domain — the enumerative seeder, the counterexample
generator's candidate lists, the falsifier-mining odometer — reads the
frozen `table_domain` for *every* axis of *every* quantifier, not only
the table-owned ones.  One problem, one interpretation, one
certification path.

**Measured**: set16 62 s (session start) -> **0 s**; set9 22 s -> 0 s;
set19 timeout -> 8 s — all still `unknown`, but the rounds now run
barren within ~5 iterations and the whole search is instant.  The
final blocker, for the next cycle: the main-level checks are
cap-starved by round 5 ("per-quantifier check budget exhausted") — the
dividend refunds fire but the caps re-exhaust; the cap accounting in
table mode (which quantifier burns what) is the remaining
instrumentation target.  The aux's own bodies fold to literal `false`
for the residual quantifiers (`q57`, `q20` under the aux's completed
model), so the certification content is there — the loop just cannot
pay for it.

Verification: quant_fuzz seeds {41..46} x 150 CLEAN; parity 176
Correct / 1 Inconclusive / 0 wrong (z3 4.16.0); nixie-solver +
nixie-core 4736/4740; the heaviest convergence pin passes standalone
at 271 s (in band; one flaked FAIL under concurrent load, clean on
rerun); fmt/clippy clean.


## The aux solver's own MBQI was the budget fire (2026-09-15, fifth follow-up)

The cap starvation's root: the aux solver's *internal* MBQI loop.  A
main-level check's `aux_refute` charges the aux's whole solve —
including the nested quantifier search the aux runs on its own goal —
to the main checker's global conflict budget.  A handful of checks
whose aux went digging (43 nested empty-mine rounds in one trace)
burned the 50 k budget from the inside; every later main-level check
then declined silently at the global gate.

**Fix (table mode only)**: `aux.mbqi.set_max_rounds(0)` when
`constructor_sources` is non-empty — the aux exists to decide one
expanded body', its own MBQI adds nothing there but churn.
Unconditional it was *not* free: `wisas/xs_8_13` (QF_UFLIA, no tables)
lost its `unsat` — the nested search inside an aux check contributed
the refutation the outer loop could not reach alone.  Gated on table
mode, both worlds keep their behaviour.

**Effect on the family**: the certifications that were always
semantically there now actually land — q28 (seteq-as-subsets), q10
(axiom 1), q33/q38 (union/intersection) certify; q57 (the witness
axiom), q20, q42 remain falsified.  q57's falsifier is the
*cardinality* gap: the frozen `Elem` domain lacks the distinguishing
element the axiom demands — z3's model uses 8 `Elem` values, the
freeze caught ~2-4.

**The cardinality escalation was wired and measured — and held
back.**  `ModelCompleter::thaw_table_domains` (bounded by
`MAX_TABLE_THAWS = 4`) thaws after two barren uncertified rounds; the
completion re-freezes at the grown universe.  It *fires* — and does
not close: each thaw re-freezes over the stale pins too, the bigger
structure re-stalls at a higher cardinality, and set16 went 0 s ->
35 s without a verdict.  The escalation needs its own design (thaw
only the sorts whose witness axioms falsify; re-derive rows rather
than re-freezing stale pins).  The hook and the cap are landed for
that follow-up; the trigger is documented in place.

Verification: quant_fuzz seeds {41..46} x 150 CLEAN; parity 176
Correct / 1 Inconclusive / 0 wrong (z3 4.16.0); nixie-solver +
nixie-core 4738/4742 — the two failures (`wisas_xs_8_13_*`) are
pre-existing on the base (`6eec76dd` verified in a throwaway
worktree), another agent's in-flight arc; the heaviest convergence pin
passes standalone in band; fmt/clippy clean.


## The targeted cardinality escalation, landed (2026-09-15, sixth follow-up)

`ModelCompleter::thaw_axes_only` — the targeted escalation — is landed
and wired: after two barren uncertified rounds, the *axis* sorts (the
observer's row-point domains — `Elem`) thaw and re-freeze at the grown
universe; the constructor *range* sorts stay frozen, so the tuple
space, the tables and every already-landed certification stay stable.
`frozen_range_sorts` records which frozen sorts are ranges during the
freeze.  It fires on set16 (four escalations, the cap).

**The diagnosis it confirmed**: the ground solver has already minted
the witnesses the axiom demands — `skf!0(b,a)` with its forcing pins
(`member(skf!0(b,a), b) = true`, `member(skf!0(b,a), a) = false`,
visible in the completion's entry tables) — and the post-thaw
expansion domain admits them (the body' carries 24 skf mentions).
The pre-thaw falsifier's evidence told the whole story: the walk
consulted `member(u!i, ·)` for the eight synthetic seeds only — rows
(a) = rows(b) = {u!0} under that reading — with `subset(b,a) = false`
asserted, so axiom 3's containment antecedent held while its pin said
false and axiom 2's witness ∃ was unsatisfiable *at the points the
domain offered*.  After the thaw, the witnesses are in.

**What still blocks `sat`** (the next cycle's target, precisely): the
late-round q57 aux verdicts remain `Sat` while the walk over the same
body' at every odometer tuple does not fold to false — an aux-vs-walk
disagreement over the expanded body (the aux exploits freedom in the
ite-chain conditions that the walk resolves through pins; the aux's
falsifying assignment is the thing to dump next).  Rounds oscillate
between "model unchanged" (the signature gate) and "no relevant
falsifier" — the escalation cap then ends the search honestly.

Verification: quant_fuzz seeds {41..46} x 150 CLEAN; parity 176
Correct / 1 Inconclusive / 0 wrong (z3 4.16.0); nixie-solver +
nixie-core 4763/4767 (the two wisas failures pre-existing on base;
qlock_11 flaked once under full-suite load, passes standalone); the
heaviest convergence pin passes standalone at 180 s — the fastest it
has been all arc; fmt/clippy clean.


## The merge exploit closed; the ite-abstraction route remains (2026-09-15, seventh follow-up)

Dumping the aux's falsifying assignment found the *merge exploit*: the
aux satisfied its Skolem restriction `(or (= sk a) (= sk b))` by merging
`a` and `b` (both disjuncts true under the merge — nothing in the aux
goal forbade it), then the `(b, a)` ite-branch fired at the merged
point with `member(x, s1)` and `member(x, s2)` collapsed to the same
term — `p ∧ ¬p` — and every witness axiom falsified at a point that is
not an element of the structure.

**Fix**: `aux_refute` now asserts pairwise `distinct` over the
restriction universe.  The domain elements are pairwise distinct *by
construction* (the universe is the set of the model's distinguished
values); Z3's model values carry exactly this semantics — this is
that, told to the aux.  The stale-pin repair's cost gate also relaxed
from table-*ownership* to table-*mode*: the witness axioms (axiom 2)
are not table-owned, but their `(b, a)` falsifier — the
asserted-antecedent point with the stale subset diagonal — is exactly
the fully-pinned shape the repair exists for.  Goals without tables
keep the old behaviour entirely (the convergence pin passes at 212 s
standalone).

**Remaining blocker** (the next cycle, precisely): with the merge
closed, the aux still falsifies q57/q42/q20 through a different route
— the dumped assignment reasons over equalities between compound terms
and *ite abstraction variables* (`(= (intersection a a) __nixie_ite_N)
= false`): the aux exploits the chain construction's abstraction
boundaries rather than value merges.  The caps still starve the loop
before the repair compounds ("per-quantifier check budget exhausted"
at round 5; the signature gate then alternates with empty mining).

Verification: quant_fuzz seeds {41..46} x 150 CLEAN; parity 176
Correct / 1 Inconclusive / 0 wrong (z3 4.16.0); 4761/4767 (the two
wisas failures pre-existing); the heaviest convergence pin 212 s
standalone (in band); fmt/clippy clean.


## The `p => p` collapse (2026-09-16, eighth follow-up)

The walk-vs-aux divergence's simplest instance, closed: when the
member atoms of an antecedent fall through to the else, the walk
produces hash-consed *identical* symbolic terms — `(=> (member u!0 a)
(member u!0 a))` — and the fold machine rebuilt them unchanged, so a
diagonal antecedent stayed a non-constant and-chain the walk read as
"not false" while every solver reads `true`.  `CompletionEval`'s
`Implies` arm now collapses `p => p` (and short-circuits decided
sides: `true => b` is `b`, `false => _` and `_ => true` are `true`).
The first cut of this fix was itself wrong (`true => b` folded to a
constant — the twins canary caught it within seconds: a false `sat`).

The family's verdicts are unchanged by this alone (the persistent
q57/q20/q42 falsifiers sit elsewhere), but the mining can now reach
else-heavy diagonals it could not before, and the rule is generally
sound.

Verification: quant_fuzz seeds {41..46} x 150 CLEAN (the canary fired
*within* the battery's development loop); parity 176 Correct / 1
Inconclusive / 0 wrong (z3 4.16.0); 4767/4771 (wisas pre-existing);
fmt/clippy clean.


## The witness pins exist; the antecedent still folds (2026-09-16, ninth follow-up — handoff)

Landed this session: `ceca2d31` (the `p => p` collapse) is on `main`
(via `d2a83f3f`).  The remaining blocker chain, resolved to one
concrete puzzle:

1. **The forcing works end to end.**  The skolemized axiom 2 is a
   tracked quantifier; its `(b, a)` instance landed; the ground solver
   pinned the witness — `member(skf!0(b,a), b) = true ∧
   member(skf!0(b,a), a) = false` — visible in **94 rounds'** worth of
   completions.  The escalation admits the skf terms (12-element
   domain confirmed by the `[quant]` probe).

2. **The puzzle**: with those pins, axiom 3's antecedent
   (`∀x. member(x,s1) => member(x,s2)`, expanded over the 12-element
   domain, each disjunct a chain-implication over symbolic `?s1/?s2`)
   must read FALSE at `(b, a)` — the skf disjunct is `true => false`.
   Instead, q20's completed body' collapses to the tiny
   `(ite (and (= ?s1 a) (= ?s2 a)) true (and (= ?s1 b) (= ?s2 b)))`
   — the antecedent is gone, the body' is falsifiable at `(b, a)`
   through its else-reading, and the aux verdict stays `Sat`.

   The next cycle ties that tiny term to its construction path: it
   looks like the antecedent's 12 chain-implications folded into a
   two-point equality table (or the subset-hint's own symbolic psi
   became the chain's else-leaf).  Instrumentation that is proven to
   work, all print-only:
   - `[quant]` (the Quant frame's first-tuple dump: tuples count +
     first disjunct) — the expansion runs 12-tuple post-thaw;
   - `[skf-pin]` (member/subset entries with skf args) — the witness
     pins, every round;
   - `[late-body']` (short/quantifier-carrying completed bodies) —
     where the tiny term appears;
   - the aux falsifying-assignment dump (merge exploit era) — for the
     aux-side view of the same check.

Disk note (2026-09-16): `/media/data` hit 99% during this session —
the concurrent arcs' worktrees (`/tmp/sets-arc` 132 G, shared `target`
106 G, `outputs/` 70 G) plus this arc's builds.  This arc's artifacts
are cleaned (only its precompile entries remain, ~100 M); the next
agent should budget builds carefully and re-run `git worktree prune`.


## Entry-table semantic normalization (2026-09-16, tenth follow-up)

The aux's falsifying assignment, fully decoded, showed the exploit's
exact shape: the Skolems sit at `(a, b)`, and the aux **merges `a`
with `union(a,a)`** — legitimate in the completed structure (same
row, the table identifies them) — then routes the ite-chains through
the **compound-keyed entries** (`subset(union(a,a), ·)`,
`member(u!0, union(a,a))` — stale pins from the search era) whose
values disagree with the domain-keyed ones.  Two normalizations close
the identity gap:

1. **Chain conditions**: `fold_apply`'s symbolic path normalizes each
   entry argument through `semantic_value_of` before building the
   `(= sk entry_arg)` condition — the chain compares the Skolem
   against the *representative*, not the compound.
2. **The entry tables themselves** (`compute_constructor_tables`,
   after the compute passes): every ground entry's arguments are
   rewritten through `semantic_value_of` and duplicates at the same
   normalized point collapse (first wins).  The completed structure
   identifies those points; the tables must agree with their own
   quotient — a table holding two values for one point was never a
   coherent interpretation.

The family's verdicts are unchanged by these alone (the residual
q20/q57/q42 `Sat` route survives through another leg — the next dump
target is the *post-normalization* aux assignment), but both changes
are semantically required, not optional: the completed model's own
quotient semantics demands them.

Verification: quant_fuzz seeds {41..46} x 150 CLEAN; parity 176
Correct / 1 Inconclusive / 0 wrong (z3 4.16.0); nixie-solver +
nixie-core 4779/4780 (the one timeout is the convergence pin under
full-suite parallel load — it passes standalone at 139 s, the fastest
of the whole arc); fmt/clippy clean on the touched files.


## The expansion is a completion choice — the repair's last hole, closed (2026-09-16, eleventh follow-up)

The residual falsifier, decoded end to end, exposed a genuine
soundness hole in the stale-pin repair: the `(b, a)` falsifier (17
commitments: the eight pre-escalation member pins plus the *asserted*
`subset(b,a) = false`) was `fully_pinned` — yet its falsity rested on
the **bounded-quantifier expansion's domain choice** (`not subset =>
exists x. ...` with no witness *among the chosen elements*).  The
expansion never set `free_choice`, so the transfer argument silently
included the domain as a ground fact.  The blocking clause built from
that falsifier blocks an arrangement containing an asserted fact —
the false-`unsat` vector, resurfaced through the very mechanism built
to be sound.  A model agreeing on every pin but carrying the missing
element (the skf witness, minted one escalation later) satisfies the
quantifier.

**Fix**: the `Quant` frame sets `free_choice` in recording mode — the
expansion's domain is the interpretation's own decision, so any
falsifier whose falsity needed it is not a function of its
commitments.  (The aux certification is unaffected: there the
expansion is the legitimate restriction semantics; this flag governs
only the mining/repair bookkeeping.)

Verification: quant_fuzz seeds {41..46} x 150 CLEAN; parity 176
Correct / 1 Inconclusive / 0 wrong (z3 4.16.0); 4782/4783 (the one
timeout is the convergence pin under parallel load — 145 s standalone,
fastest of the arc); fmt/clippy clean.

**Family state**: the pre-thaw `(b,a)` repair clause no longer fires;
the loop's remaining `Sat` verdicts are the post-normalization legs
(the stale *constructor-table* ground pins — e.g. the ground solver's
own `union(b,a) ↦ a` assignment harvested as a never-override pin
whose row no longer matches post-escalation).  The revision loop for
*those* — the falsifier path emitting the defining-axiom instance so
the ground solver re-solves the pin — is the design the study has
carried since the first landing; the probe recipes for it are all
proven.
