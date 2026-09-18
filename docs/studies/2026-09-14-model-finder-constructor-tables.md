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


## The ite-abstraction holes, confined (2026-09-16, twelfth follow-up)

With the choice-flagging landed, the walk-vs-aux picture sharpened to
this: the walk evaluates the constructor axioms **true at every
odometer tuple** (the `[nontrue]` probe shows falsifiers only for the
observer axioms), yet the aux still returns `Sat` on them.  The aux's
freedom is the encoder's **ite abstraction**: the chains become
Tseitin variables (`__nixie_ite_*`), and a *nested* chain's condition
`(= sk __nixie_ite_N)` mentions one — a Boolean the Skolem restriction
does not decide, so the abstraction variable floats and the aux routes
the outer chain through whatever branch its free choice prefers.

**Fix (sound, principled)**: the aux now confines every
uninterpreted-sorted ite-abstraction variable to the same frozen
domain as the Skolems — every chain value IS a domain element (an
entry result or the else, both drawn from the structure), so this is
the chain's own semantics, told to the aux's encoding.  It does not by
itself close the family (the aux retains legitimate freedom over
*which* domain element an undecided abstraction takes), but it removes
a whole class of off-structure falsifications.

**The next probe, precisely**: minimize the aux goal at a q33 `Sat` —
extract `not body'[sk]` with its restriction clauses and solve it
standalone — the surviving falsifying assignment shows which chain
branch the aux legitimately prefers that the completed model's tables
do not justify (the stale constructor-table ground pins are the prime
suspect: the ground solver's own `union(b,a) ↦ a` assignments,
harvested as never-override pins whose rows no longer match
post-escalation).

Verification: quant_fuzz seeds {41..46} x 150 CLEAN (plus spot
re-checks); parity 176 Correct / 1 Inconclusive / 0 wrong (z3 4.16.0);
4796/4797 (the convergence pin 159 s standalone, in band); fmt/clippy
clean.


## The minimized goal, decoded: three defects, the family half-closed (2026-09-16, thirteenth follow-up)

The handover's prescribed probe — dump every aux-`Sat` goal as
standalone SMT-LIB and minimize — ran on set16 and decoded the
walk-vs-aux divergence into **three independent defects**, each fixed
at its layer with the layers above it guarded:

1. **Ill-typed defining pins (the diagonal bug).**  The well-typedness
   audit on the dumped goals showed `union(u!3, u!3)` and
   `member(u!4, u!4)` — Elem-sorted seeds in Set positions.  A
   `TermManager::intern` tripwire (same function symbol applied at two
   argument-sort sequences → backtrace) pinned the minting site:
   `emit_macro_defining_pins`' "diagonals first" pre-pass repeated one
   element of `sets[0]` across **all** axes — for
   `forall ?x:Elem ?s1:Set ?s2:Set` that substitutes an Elem constant
   into the Set positions, asserting instances with ill-typed
   applications.  The ground solver accepts them (EUF does not
   sort-check), the harvest reads them back as garbage table entries
   (`member(u!4, u!4) = false`), the instantiation-set harvest
   re-buckets an Elem *value* under the Set position's sort, and the
   compounds surface in the aux goals as free function applications
   the walk can never reproduce — exactly the documented divergence.
   **Fix**: a diagonal is per **sort class** (axes of one sort take
   one value; the odometer skip checks value-equality within classes,
   not index equality — same-sort behaviour is bit-identical), plus a
   defense-in-depth guard that skips any tuple whose value sorts do
   not match their axes, plus own-sort bucketing in
   `build_instantiation_set` and the counterexample candidate lists
   (an assignments value joins the sets of *its own* sort, never the
   substituted term's).

2. **The artifact default (the symbolic else).**  With the ill-typed
   mint dead, `difference`'s completed else still read as the **free
   variable `?s2`**: `collect_universes_from_model`'s harvest carried
   the encoder's binder constants (the internalized axiom bodies'
   `?s1`/`?s2` free constants) into the raw universe, and
   `set_default_values` picked `universes[Set].first()` — the artifact
   — as the sort default, which `complete_function_interpretations`
   then installed as every entry-less function's `else_value`.  A
   symbolic else means the completed body folds to a *term* mentioning
   the Skolem, never to a constant: the aux legitimately falsifies
   (its reading of the else is a free choice), the mining walk never
   folds false ("no relevant falsifier"), and the loop stalls — the
   exact residual q42/q20/q57 shape with no falsifier to mine.
   **Fix**: every universe element must be a ground term of its own
   sort (own-sort check + free-variable/artifact filter, the same
   name-set test `freeze_ground_universes` uses), applied at the
   harvest; the default and both candidate-list sites inherit it.

3. **The missing row (the fresh-element mint).**  With (1)+(2) fixed,
   q33/q38/q10/q28 certified but `difference`'s table computed **zero**
   entries every round: its target rows — the empty row for the
   diagonals, `rows(b)∖rows(a)` for `(b,a)` — exist in *no* element of
   the frozen 2-point domain (z3's set16 model closes because its
   search reaches `a = ∅`; nixie's ground solver had pinned
   `u!0 ∈ a` and nothing ever retracts a free choice).  Leaving
   missing-row tuples to the else strands the defining axiom at them
   permanently.  **Fix** (`mint_fresh_row_element`): on a row miss,
   GROW the completed structure with a fresh element that *has* the
   target row — z3's own model-finder semantics
   (`proto_model::get_fresh_value` / `mk_extra_fresh_value`: the model
   is the object being searched; a user sort's universe grows when the
   interpretation needs a new distinguishable value).  The fresh
   element is **row-canonical** (named by its target row's bits, so
   the same row mints the same element across rounds and from any
   constructor), its observer entries are installed at every row
   point, and the frozen/table domains grow with it (capped at the
   aux-restriction universe bound; 16 mints per table per round).  A
   mint round is model *movement*: it does not count as barren for the
   axis-thaw escalation (thawing while the structure grows explodes
   the row space — measured below).

**Result**: set16 answers **`sat` in 0.1 s** (z3: `sat`, 0.5 s; its
model has 2 `Set!val`s — nixie's completed structure is the 4-element
row closure, equally a model, certified end to end).  set9/set19 still
answer `unknown` honestly; the residual blocker is diagnosed precisely
below.

**set9's residual (the next cycle's target)**: the goal needs the
*powerset closure* of the used rows (`not seteq(difference a b,
(difference b a))` forces disjoint non-empty base rows; union/intersection
then demand the full and empty rows — no 2-element structure carries
them, so the mint fires, which is correct).  What does not converge is
the **base rows**: the ground model's `member` rows for the base
elements are free choices no asserted instance pins (defining
instances are satisfied at the free compound terms — the ground solver
never has to commit `difference(a,b)` to a domain element), so they
churn between rounds and the mint chases them: 17-wide row points,
the 32-element cap, and every nested check past its conflict budget
("nested check undetermined").  The mechanism the study has carried —
the revision loop that forces the ground solver to re-solve a pin —
must therefore bind the *compounds* to the structure: the domain
restriction `f(t...) ∈ {d1..dn}` told to the main solver.  That clause
is **not** a logical consequence (a real model may use a third
element), so it cannot be asserted unguarded (false-`unsat` vector);
it needs either the guarded-lemma pattern (a fresh guard literal the
`sat` path sets and the `unsat` path never depends on) or z3-fm
semantics (cardinality assumption with escalation on the conditional
refutation).  set9's freeze also caught a round whose Set universe was
the *compounds* `difference(a,b)`/`difference(b,a)` (the ground model
had merged `a ≈ difference(a,b)` — a legitimate model whose defining
instances then force the base rows disjoint); a re-freeze design that
recognises semantically-equal domains belongs to the same cycle.
set19 (z3: timeout) needs the same machinery — its honest `unknown`
at 10 s is parity-correct today.

Verification: quant_fuzz seeds {41..46} x 150 **CLEAN**; parity
**176 Correct / 1 Inconclusive / 0 wrong** (z3 4.16.0); workspace
suite **11880/11880** (the one `nixie-sat` failure was environmental —
a worktree without the `satcomp2024` corpus symlink; passes with the
corpus present); clippy/fmt/doc clean; the perf gate **PASS**
(conflicts geomean 1.000, no verdict changes — the three fixes are
off the SAT hot path and the mint is completion-layer only); the
twins canary and both set16 honesty pins pass;
`set16_family_answers_sat` added as the convergence pin (it fails if
any of the three mechanisms regresses).


## The out-of-structure keys dropped; the family closes (2026-09-16, fourteenth follow-up)

The thirteenth follow-up left set9/set19 with the "base-row churn"
diagnosis.  Per-round row dumps (`[rows]`) sharpened it: the base rows
were *mostly* right — `rows(a) = ∅`, `rows(b) ≠ ∅`, disjoint, exactly
the shape z3's model has — and the residual aux-`Sat` verdicts were
**not** row churn at all.  The failing bodies' chains were keyed at a
zoo of *out-of-structure compounds*: `(= ?s1 (union b a))`,
`(= ?x (skf!0 (difference a b) (difference b a)))`, `(= ?s2
(intersection a a))` — stale `member` pins harvested from instances
asserted at terms the frozen two-element structure
`[difference(a,b), difference(b,a)]` does not contain.  In the aux goal
those compounds are free function applications: the aux can merge its
Skolem with `union(b,a)` (both free) and route the chain through the
stale branch — a falsification route the completed structure never
justified.  The walk (odometer over the *frozen domain*) can never
visit those keys, so the mining found nothing ("no relevant
falsifier") — the divergence, fully decoded this time.

**Fix (the arc's own rule, enforced)**: "the completed structure's
tables must agree with their own quotient" — an entry keyed at a point
the structure does not contain constrains nothing inside it.  The
entry-table normalization (`5a6bc16c`'s block) now rewrites every
entry argument through the *ground assignment chain* first (this is
also what keeps asserted ground equalities true in the completed
structure), then the constructor-table quotient, and then **drops the
entry** when the argument is still outside the sort's frozen domain.
Dropped keys cannot match the walk's tuples, cannot build chain
conditions, and cannot feed the instantiation-set harvest — the aux's
exploit routes disappear; the structure's own tables are all that
remains, and they were already consistent.

**Result: the whole family answers `sat`** — set16 0.1 s, set9 ~20 s,
set19 ~2 min.  **z3 4.16.0 times out on set19**: nixie now decides a
goal the reference solver cannot.  `set9_family_answers_sat` and
`set19_family_answers_sat` join `set16_family_answers_sat` as the
family's convergence pins (set19 gets a nextest slow-timeout override
following the `pete_cxs_bp` precedent — it is the one goal in the
family that needs the full row-closure growth).

**Why the drop is sound**: the completed structure is the `sat`
witness.  Asserted ground atoms survive — their terms normalize
through the ground assignment chain before any drop decision, and the
problem's own constants were in the frozen domain from the freeze
round (their compounds minted by later instances were not, which is
precisely why their pins were garbage).  Quantifier certification runs
against the cleaned structure by construction.  An entry that survives
normalization onto a structure point keeps its value (first-wins
dedup, unchanged).

Verification (recorded under a machine at load ~140 from concurrent
arcs — the two full-suite timeouts below are the documented
load-sensitive pins, both passing standalone at load 144 immediately
after): quant_fuzz {41..46}x150 **CLEAN**; parity **176 Correct / 1
Inconclusive / 0 wrong** (z3 4.16.0); nixie-solver + nixie-core debug
**4833/4833**; workspace 11893 passed + the `arith_incremental`
replay-fuzz and `re_running_the_search` pins terminated at their
budgets only under 149-load parallel oversubscription (143 s / 152 s
standalone); clippy/fmt/doc clean; perf gate **PASS** (conflicts
geomean 1.000, no verdict changes); twins canary and all three family
honesty pins pass.


## The mint budgeted: one stably-needed row per round (2026-09-17, fifteenth follow-up — perf)

The family answers `sat` everywhere but set9/set19 pay for structure
bloat: a cost-split (env-gated cumulative aux wall vs total) showed the
aux checks are only ~14% of set19's 76 s — 86% is the completion layer
and ground churn over a structure the eager mint had grown to the
32-element restriction cap (194 of 245 compute passes at the cap, the
member table peaking at 841 entries) for a goal that needs a handful of
elements.

**The experiment** (aux conflicts — a deterministic counter — as the
primary metric; wall secondary): sticky-miss gating (mint only tuples
that missed two consecutive rounds) was built first with a matched null
(NIXIE_MINT_NULL=<seed>: the same mint count chosen by a seeded pick of
the miss set).  Result: the null *beat* the treatment — set19
4963 vs ~586 median conflicts (treatment/null ≈ 8.5), set9 720 vs ~300
(≈ 2.4) — the churn-tracking semantic content is *negative*; the entire
effect is the **mint count** (fewer rows per round ⇒ slower, cleaner
structure growth).  A prefix-budget sweep deconfounded the rest: budget
1 lands inside the null band on both goals; budget 4 and the in-walk
mint both blow past 5k conflicts on set19 — extending the odometer to
fresh tuples mid-walk covers `(fresh, fresh)`-shaped tuples against
rows still in flux and mints garbage the nested checks then fight
through.

**What landed**: `MINT_BUDGET_PER_ROUND = 1` — at most one fresh row
per constructor per round, the first miss in odometer order, installed
*post-walk* (never extending the live odometer); the row-canonical mint
name now sorts the row points by TermId and namespaces the bits by an
FNV fingerprint of that sequence (a re-freeze can reorder the frozen
axis domain, and the old positional bit string would re-mint the same
row under a new name — a duplicate the structure's own quotient says
is one point).  `NIXIE_MINT_NULL` ships as the matched-null knob, and
`NIXIE_DEBUG_QROUNDS` gains a cumulative-aux-conflicts line
(`[qround-stats]`) so the deterministic metric is readable without a
probe build.

**Measured** (treatment/null conflicts, 8 null seeds): set9
255/~279 (0.91), set19 485/~586 (0.83) — the prefix selection carries
no penalty; the count reduction is the mechanism.  Wall: set16 0.1 s
(unchanged), set9 16.3 → **8.0 s**, set19 76.5 → **13.8 s**.  Verdicts
unchanged (all three `sat`; z3 4.16.0 still times out on set19).

Verification: quant_fuzz {41..46}x150 CLEAN; parity 176/1/0 (z3
4.16.0); nixie-solver + nixie-core debug 4854/4854; workspace
**release** 11921/11922 — the one failure is
`solver::model_eval::tests::assertion_past_the_depth_budget_stays_inconclusive`,
a **pre-existing release-profile-only stack overflow on main**
(SIGABRT, `DEEP_WORKER_STACK` overflowed at depth 6250): verified
failing at `bd05775b`, `067e89a3` (this arc's own earlier landing),
`91f73fac` and current main — it predates every arc compared this
week and is invisible to the default gate because the gate runs the
debug profile (larger frames, no overflow).  It is *not* introduced by
this diff (the mint-budget change does not touch `model_eval` or any
eval-path frame); flagging it here for the owning arc — a release-run
of the workspace suite belongs in the verification rotation, or the
test's stack budget needs release-profile headroom.
clippy/fmt/doc clean; perf gate PASS (conflicts geomean 1.000).


## The unsat-forcing fuzz family (2026-09-17, sixteenth follow-up)

The carried continuation ("the generator skews sat-heavy — the
unsat-forcing family") is landed: `quant_fuzz.py FAMILY=unsat` generates
goals that are **unsat by construction**, so the oracle needs no
comparator — a nixie `sat` is a soundness bug outright, an `unknown` is a
counted completeness gap, and z3 runs only as a cross-check of the
generator itself (it must answer unsat; 36/36 on validation).  Six
families, each targeting different refutation machinery:

| family | shape | stresses |
|---|---|---|
| `chain` | `P(c)`, `∀x. P(x)⇒P(f(x))`, `¬P(f^k c)` | instantiation depth |
| `skolem` | `∀x∃y. Q(x,y)` + `∀xy. ¬Q(x,y)` | two-quantifier logic |
| `pigeonhole` | finite enumeration + distinct + injective-but-missing `f` | finite-model reasoning |
| `card` | `|S|≤n` + `n+1` distinct | cardinality |
| `cycle` | transitivity + irreflexivity + ground cycle | order axioms |
| `extensional` | set semantics + membership collision | the model finder |

**Standing on current main** (seeds 51–54 × 150, z3 4.16.0 cross-check
all-unsat): **zero false-sats**; chain/skolem/cycle/card solved
outright; the completeness gaps are **pigeonhole ~20/30 unknown** and
**extensional ~6/24 unknown** — the next targets, with by-construction
reproducers one generator invocation away.

**The negative results (do not retry blind)** — two attempts to close
the pigeonhole gap by exporting the ground model's committed equality
values for S-valued applications (`f(c0)=c1`-style facts the model
readback never records, which is why unowned S-valued functions harvest
empty entry tables and complete to a constant `else`):

1. **Global export (model-builder)**: introduced **false `sat`s** on the
   extensional family.  Mechanism, decoded end to end: exported pins on
   *table-owned* compounds → the entry normalization re-keys them onto
   completion-minted elements → the minted rows mutate after minting →
   the row-canonical mint names lie → the (real, pre-existing) duplicate
   domain-push bug in `mint_fresh_row_element`'s frozen side (no
   contains-check) bloated the domain (24+ copies, 578 duplicate table
   entries, 85 KB chains) → the ground-pin branch the certification
   needed was buried → the aux certified a corrupted body'.  The frozen
   push's missing contains-check is a real defect (the dedup fix was
   validated) but landing it alone regresses the set family to
   `unknown` — the pre-dedup convergence rides on accidental else-reads
   of vanished mint rows.
2. **Ownership-gated export (completion, unowned funcs only)**: sound
   (no false-sats) but inert for the family convergence — and it exposed
   the deeper design gap: **minted rows vanish at round boundaries**
   (the harvest rebuilds the observer table from the ground solver
   alone), and a *static* row memory conflicts with ground-row churn
   (re-keyed stale pins pollute remembered rows).

Also built and validated but **held back with the revert** (they belong
to the row-memory session): the completed-model-vs-ground-assertion
honesty gate on the `Satisfied` path (it correctly downgraded the
mint-vs-asserted-equality divergence class), and the per-round mint
check-budget refund.  The next session's map: give minted elements a
*churn-proof* row source (derive from the frozen structure, not a
snapshot), then land the dedup + the assertion gate + the export (theory
layer, EUF representatives) in that order, re-running the unsat family
and the set pins at each step.

Verification (final landed state — generator only, solver reverted to
main): random family seeds {41..46}×150 **CLEAN**; unsat family seeds
{51..54}×150 **CLEAN** (0 false-sats, gaps as measured); family pins
set16/set9/set19 all `sat`; clippy/fmt clean.


## The minted-row memory decoded to the last layer (2026-09-17, seventeenth follow-up — negative result, precise map)

The sixteenth follow-up left the minted-row design gap open ("a
churn-proof row source").  This session built the row memory
(`ModelCompleter::fresh_rows` — the mint records its installed row,
re-injected each round before the harvest) and drove the pollution hunt
to the last two layers, both real and now precisely understood:

1. **The polarity override**: the loop's own falsifier lemmas mint ground
   atoms AT minted elements (the encoder internalizes the minted term;
   the SAT core commits `member(u!4, e0) = true` to satisfy the
   instance).  The harvest feeds those polarities back, and the
   completion evaluator's *whole-term assignment lookup* answers
   `member(u!4, e0)` from them — before any entry is consulted,
   overriding the remembered row.
2. **The same-key twin**: even with the assignment keys purged, the
   harvest (`extract_function_interpretations`, which runs before the
   purge) had already converted them into observer *entries* whose args
   coincide exactly with the mint's own — and a key-based retain filter
   keeps both.  The purge must drop every entry touching a minted
   element and re-inject the remembered rows after.

With both fixed, the mint's names become honest (the `!bits` suffix
matches the element's actual row — verified in the row dumps) and the
minted elements keep their rows across rounds.  The **new** blocker is
honest convergence pacing: the semantically-correct structures are
bigger, the nested checks now spend their per-check conflict limits
(`Err(MaxConflicts)` on the union/intersection/difference checks), and
the loop dies at the global budget (~26 rounds, 53 k aux conflicts on
set16) before the witness-axiom instances drive the ground rows apart.
The old (landed) build converged by riding *dishonest* else-readings of
vanished rows — smaller structures, cheaper checks.

**The next session's entry point**: with honest rows in place, retune
the pacing — the aux per-check conflict limit against table size, and
the refund cadence (the mint-round refund was re-added and helps the
round count but not the per-check caps).  Do NOT ship the row memory
without the family pins green; the held-back state is
`fresh_rows` + the two purges + the refund, all in this worktree's
history (branch `row-memory`, reverted before landing).

Verification of the reverted state: set family all `sat`; quant_fuzz
seed 41 × 60 CLEAN.
