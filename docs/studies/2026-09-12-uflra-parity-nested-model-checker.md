# UFLRA parity: closing the FFT gap, porting Z3's nested model checker

**Date:** 2026-09-12
**Logic:** UFLRA (randomly picked via `shuf` from the in-repo SMT-LIB corpora)
**Comparator:** z3 4.16.0 (`z3 --version`), the installed parity gate
**Verdict:** **Landed.** The two z3-decidable-but-`unknown` corpus files
(`FFT/smtlib.620487`, `FFT/smtlib.620535`) now answer `unsat`, matching z3;
parity goes 174→176 Correct (of 177; the one Inconclusive is z3-side
`Unknown`, pre-existing). The `misc/set*` sat family remains `unknown` —
diagnosis and the concrete blocker are recorded below.

## The gap

`find smt-lib/non-incremental/UFLRA -name '*.smt2'` (15 files) against z3:

| family | nixie before | z3 | after |
|---|---|---|---|
| FFT (10) | 8 unsat, **2 unknown** | 10 unsat | **10 unsat** |
| misc/set (5) | 5 unknown | set9/16/19 sat, list2/set14 timeout | set9/16/19 still unknown |
| misc/list2, set14 | unknown | timeout | unknown (not a gap) |

## Root-cause layers found (each independently pinned by a regression)

Working the FFT shape (`forall v. f3(f4, f6+v) = -f3(f4, v)` refuted by the
single instance `v := f5-f6` against a ground disequality) peeled **five**
layers. Fixing any proper subset leaves the file `unknown`.

1. **E-matching was already correct.** The engine produced the money lemma
   `(= (f3 f4 (+ f6 (- f5 f6))) (- (f3 f4 (- f5 f6))))` in round 0. The gap
   was downstream. (It also produces junk unsubstituted-body lemmas by
   matching patterns against the pattern term itself — pre-existing,
   harmless-but-noisy; not fixed here.)

2. **Compound linear UF arguments never reached the arithmetic interface**
   (the true root cause, ground-layer). Congruence `f(..x..) = f(..y..)`
   needs the e-graph to learn `x = y`; for arithmetic arguments only
   arithmetic can prove that; the Nelson-Oppen model-equal/entailed-equality
   probe only considers UF arguments that are arith *interface terms*. The
   assert-time purifier creates those, but `purify_numeric_uf_args`
   deliberately skips functions under quantifiers (a `model_certify`
   completeness concern), and the quantifier engines mint fresh compound
   arguments anyway. Isolated reproducer (both through `assert` and through
   mid-search lemma encoding): ground disequality + the spelled-out positive
   instance is `unsat` in z3, `unknown` here.
   **Fix:** `Solver::intern_compound_uf_args_into_arith` — internalize every
   compound *linear* arith-sorted UF argument reachable from the encoded
   vocabulary with its **definitional row** (`x − Σ cᵢ·tᵢ = k`, a tautology
   that only names the fresh variable, same class as the const-arg pins).
   Runs before each `TheoryManager` construction (initial search + MBQI round
   boundary), memoized on vocabulary size, invalidated on push/pop.

3. **Z3's MBQI core was missing** (the sat side). Nixie's counterexample
   engine *samples* candidate values and evaluates with a hand-rolled
   evaluator; over an infinite domain no sample certifies `∀`. Ported Z3's
   `smt_model_checker` architecture as `mbqi::model_checker`: complete the
   model (entries + **else**, Z3's `func_interp` else), evaluate the body
   keeping bound variables symbolic (symbolic-argument applications become
   the entries-as-ite-chain, Z3's macro expansion), Skolemize the negation,
   and **refute it with a nested full CDCL(T) solve**. `unsat` ⇒ the
   completed model satisfies the quantifier over the whole domain (a total
   interpretation extending the ground model — genuine `sat` evidence);
   `sat` ⇒ mine falsifiers from the instantiation set (entry args/results +
   assigned values, Z3's `restrict_sks_to_inst_set` + `value2expr`), each
   mined binding a sound instantiation lemma. Budgets: 4096 conflicts /
   65536 decisions per check, ≤50k conflicts and ≤1 check-per-quantifier per
   solve lifetime (see layer 5 for why the caps are tight), depth-2 nesting
   guard (atomic, no_std-safe), entry tables ≤256, body evaluation ≤20k nodes.

4. **A false `sat` in my own first cut** (caught by the corpus, fixed before
   landing): the model's assignment table contains Tseitin artifacts keyed by
   terms that *mention the bound variable* (`(f3 f4 (+ f6 ?v0)) = 0`); the
   evaluator's "pinned ground term" lookup fired on them, freezing the
   variable at one value and fabricating satisfaction. Second defect of the
   same class: the completed model's "universe" for an *interpreted* sort is
   merely a **sample** of its values; restricting the Int Skolem to it made
   `2v+1 = y` "unsat" exactly when the true falsifier `(y−1)/2` fell outside
   the sample — false `Satisfied` on a goal the
   `mbqi_unverified_quantifier_is_not_sat` audit family guards. Both fixed:
   assignment lookups and entry tables only apply to terms **free of bound
   variables**, and the universe restriction applies **only to uninterpreted
   sorts** (Z3 restricts under `is_finite` — finite-model semantics).

5. **Cost control under forced re-runs.** The nested checker is the most
   expensive tool in the box; `scope_rebase_tests`' 600-rerun convergence
   pins (verdict-cache bypass) re-pay everything per rerun, and in the debug
   profile a handful of nested solves per rerun tips the 180 s bar. Final
   shape: the checker **escalates only when the sampling search found no
   counterexample at all** (a round that sampled any cex, even duplicates,
   does not escalate), plus the same-model signature gate and the hard
   per-quantifier lifetime cap. With those, the heaviest pin runs at
   baseline cost (68 s vs 66 s baseline) and the whole workspace suite is
   11199/11199 with zero timeouts.

## What did *not* work (negative results — do not retry blind)

- **Restricted nested solving as the falsifier miner**: re-solving with the
  Skolems confined to the instantiation set (the literal Z3 recipe) produced
  the *same* binding every iteration, because the nested `Solver`'s `Model`
  does not report values for theory-irrelevant Skolem constants (Set-sorted
  consts with no arith/EUF pin), so every read fell back to the sort default
  and the blocking clauses chased values the model never showed. Replaced by
  **term-level combo mining**: enumerate instantiation-set combinations and
  evaluate the completed body with the module's own evaluator (which needed
  exact constant folding of `+`/`-`/`*`/neg — added, `mk_numeric` refuses
  non-representable results rather than truncating).

- **Unsat-side convergence via arbitrary falsifiers**: the unrestricted
  nested model's falsifier points (−2/3, −7/6, … orbit) generate lemmas that
  never interlock; the loop diverges. The refutation is carried by e-matching
  (layer 1) + the interface repair (layer 2); the checker's mining is only a
  bootstrapper.

## Remaining gap: the `set9`/`set16`/`set19` sat family

**Update (2026-09-13, second pass — root cause found, pinned, not fixed).**
Five more layers were peeled; each fix below is landed and pinned, and the
family's *engine* is now understood end to end:

1. **Universe seeding blew up two-element sorts.**  The completed model
   never assigns constants of an uninterpreted sort (they live only as
   *entry arguments* of `Bool`-valued functions), so the empty-sort seeding
   gate (`complete_universes`'s `has_values`) read "no values" for a sort
   whose domain elements stared at it through every entry, and minted 8
   synthetic `u!i` elements.  Fixed: entry arguments/results of the sort
   count as domain evidence.  After the fix the mined counterexamples land
   on real terms and the subset table converges to the target model.

2. **Junk bindings through encoding artifacts.**  The instantiation set
   mapped values back to terms whose free variables are *named like bound
   variables* (Tseitin-era constants), producing `?s1 := ?s2` lemmas.
   Fixed: `mentions_bound` filter on both the values and the map.

3. **`forall x. c` did not collapse.**  With the bound variable kept
   symbolic, a body that folds to a constant is *pointwise* constant, and
   the binder is that constant; leaving it symbolic made A3's falsifier
   (`(forall x. true) => false`) unminable.  Fixed for both binders
   (`forall x. false` refutes A2's witness under the completion).

4. **Nested binders of instantiation lemmas had no owner.**  An instance of
   `forall s1 s2. (forall x. ...) => subset(s1,s2)` carries the inner
   `forall` as a free Boolean — the SAT core picks a truth value its real
   meaning need not have.  Fixed: unit-asserted lemmas register their
   binders, **polarity-aware** — positive universals and negative
   existentials as universals *guarded by the binder's own literal*
   (`add_guarded_quantifier`; instances are consequences exactly when the
   binder is true), positive existentials as witness obligations.  **A
   first cut registered the guarded universals with the e-matching engine
   too — whose emission path is unit clauses only, dropping the guard —
   and the A2/A3 pair went false-`unsat`** (the e-matched instance
   collided with A2's witness).  Caught by the corpus diff, fixed by
   excluding e-matching for lemma binders, pinned by
   `witness_extensionality_alternation_is_never_wrong`.

5. **The blocker (pre-existing, assert path).**  An asserted `forall` whose
   `exists` sits in a **non-head position** (`(=> (not (subset s1 s2))
   (exists x. ...))` — an `Implies`, not an `Exists` body) is registered
   *unskolemized* (`register_asserted_forall`'s `body_is_exists` test only
   recognizes a bare `Exists` head).  Its instances therefore carry the
   `exists` node as an opaque Boolean: the model commits
   `(exists x. member(x,b) /\ ~member(x,a)) = true` while no
   `member(...)` entry ever lands in the model, and the witness the
   satisfying completion needs is never forced.  Convergence proceeds to
   the exact target `subset` table and then freezes on this.  **Fix
   direction:** NNF-skolemize at assert for any positive-polarity `exists`
   under the `forall` (`SkolemizationContext::skolemize` already does the
   NNF walk; today it is only invoked for the head-`Exists` shape).  That
   is a broad trajectory change across UFLIA/AUFLIA and needs its own
   study with the full parity gate — not attempted in this session.

Cost-control note: removing the per-quantifier lifetime cap (experimenting
with streak-based budgets) regressed the 600-rerun convergence pins from
~70 s to timeout; the cap is what bounds a forced rerun whose model *moves*
on every rerun.  The landed shape is: strict escalation trigger (a round
that sampled any counterexample does not escalate) + same-model signature
(hash of the whole completed model, not sizes) + hard per-quantifier
lifetime cap + global conflict budget.  Main-tree suite: 11230/11230.

The earlier text (kept for the record): the completion's universe seeding,
mined counterexample lemmas, and round budget interacted so the rounds
exhausted before all quantifiers were simultaneously satisfied; what is
missing relative to Z3's `smt_model_finder` is candidate else/default
searches per function (search, verify, revise) — still true for the *else*
choices, but the primary blocker is layer 5 above.

## Third pass (2026-09-13): nested-∃ skolemization landed; a false-`sat` found, contained, and root-caused

**Landed:**

1. **NNF-Skolemization of the witness-in-implication shape**
   (`exists_skolem::head_is_rewritable_quantifier` +
   `contains_positive_exists`): an asserted `forall` whose body carries
   an `exists` at *definite positive polarity* — the A2 set-theory axiom
   `(=> (not (subset s1 s2)) (exists x ...))` — is now Skolemized at
   assert (`forall s. (not P) => phi s (sk s)`), so its instances carry a
   *ground* witness term and the ground solver searches for the witness
   instead of committing a free Boolean.  Both-polarity positions (`ite`
   conditions, `xor`, Boolean `=`) do not trigger (their NNF negative
   copies make the `exists` a universal; Skolemizing would weaken).  The
   minimized A2+A3 pair now answers `sat` (z3 agrees) — the first
   set-family verdict — though the full `set16` still needs per-function
   else-search to converge.

2. **A pre-existing false-`sat`, found by the 200-file differential and
   root-caused through three wrong containment hypotheses.**
   `AUFLIA/20170829-Rodin/smt4688353851435564037` (`:status unsat`, z3
   `unsat`) answered `sat` — and dozens of archived `precompile/`
   binaries answer `sat` too, so the defect is old; the second commit's
   universe-seeding fix merely made it *reachable* again.  The chain:

   - *Not* the instantiation-budget hole (that veto — budget-exhausted
     quantifiers no longer ride along as "satisfied" — is a real
     hardening, but not this instance's mechanism).
   - *Not* the empty-mining mask (the aux-`sat`-with-no-relevant-falsifier
     case now reports an empty counterexample so the caller can veto).
   - The mechanism: the **legacy finite-exhaustion `Satisfied`** certified
     a model the completed interpretation demonstrably refutes — the
     nested checker finds falsifiers *inside the finite universe* at the
     very tuples the sampling evaluation claims are true (a stale-entry
     TermId lookup in `evaluate_under_model`'s path).  Fix:
     `ModelChecker::check_veto` — a second opinion at the moment the
     legacy verdict is about to be accepted, memoized per (quantifier,
     model signature), with else-search parity (the closed-world
     completion can clear it), conservative on undetermined checks
     (`unknown` costs completeness; an unvetted liar costs soundness), and
     a 32-check lifetime budget.  The gate is evaluated **last** in the
     conjunction — evaluating it eagerly cost the 600-rerun convergence
     pins 20x (a nested solve per round per quantifier on goals the cheap
     gates disqualify anyway; found by a per-file A/B bisect in a clean
     worktree: 55s HEAD vs 1718s mine, then 66s with the lazy ordering).

3. **The closed-world else-search** (bounded, one candidate): when the
   primary completion admits a falsifier, retry with every Bool-valued
   function's `else` forced `false` — the completion under which
   membership-style axioms are vacuously satisfied off their entry tables.
   Both are total extensions of the same entries, so an `unsat` under
   either is a sound satisfaction proof.  Gated on the body actually
   applying a Bool-valued function at a symbolic-argument position, so
   arithmetic goals pay nothing.

**Still open:** `set9`/`set16`/`set19` converge their `subset` tables to
the target model but the final `Satisfied` needs per-function else
search (the `union`/`intersection` Set-valued functions' defaults),
which is the real `smt_model_finder` project.  The Rodin-class hole is
closed at the verdict gate; the legacy evaluator's stale-entry lookup
itself remains (every certification now passes the second opinion, so it
can only cost `unknown`, never a wrong `sat`).

## Fourth pass (2026-09-13): the set-family divergence mechanism, isolated

Three sound refinements landed, and the `set16` divergence is now isolated
to a single precisely-scoped mechanism:

1. **Bool-valued else is closed-world by default** (`choose_else`): the
   entry-mode heuristic flipped a Bool function's else to `true` once a
   lemma round pushed its true entries past its false ones — every fresh
   domain point then read `member(x, s) = true`, the union/intersection
   axioms failed at *every* new candidate, and the loop diverged over the
   infinite `Real` index domain.  `false`-unless-pinned is the standard
   finite-model reading (Z3's `get_some_value(Bool)`).

2. **Redundant entries collapse** (`fold_apply` + the entry-cap gate): the
   enumerative seeder pins the function at every fresh candidate point,
   and pins that agree with the else are pure noise — thousands of
   `member(x, s) = false` entries burying the structural pins and blowing
   the ite chain past every cap.  Entries whose result equals the else
   leaf are skipped; the cap counts only chain-relevant entries.

3. **The residual mechanism (next session, precisely scoped)**: the SAT
   core commits a nested-`forall` binder's guard **false** to dodge its
   consequence — `A3[a,b] = (forall x. member(x,a) => member(x,b)) =>
   subset(a,b)` with the antecedent vacuously true under the closed-world
   completion, so committing the binder's Boolean false is the only way
   to keep `subset(a,b)` unconstrained.  The completed model inherits the
   lying commitment (its assignment table reads the quantifier Boolean
   straight from the SAT core), the falsifier mining finds (a,b) every
   round, the instance is a duplicate, and the loop exhausts its rounds.
   The binder's committed-false is an existential claim (∃x.¬φ) that
   needs a *witness*; no finite instantiation set refutes a committed
   existential.  The fix is Z3's `add_blocking_clause` model repair:
   when the completed model proves the binder's body constantly true
   (constant-collapse) while the SAT core commits it false, exclude that
   model arrangement (block the conjunction of the commitments the lie
   rests on) — the next model must either produce a witness or flip the
   Boolean.  Also: `sync_guard_commitments` marking such a guard
   `guard_inactive` (vacuously satisfied) is the loophole that lets the
   dodge stand; lemma-registered binders should not get that treatment.

## Fifth pass (2026-09-13): macro completion wired end to end

The fourth pass's diagnosis ("per-function else search") was one layer
short.  The actual missing piece: **`macro_to_interpretation` built an
*empty* interpretation** — the macro solver correctly extracts
`seteq(s1,s2) = (s1 = s2)` from its defining axiom, but the defining body
was dropped on the floor, so the completion fell back to entries+else and
every reflexive pin had to be seeded individually (an unbounded chase for
definitional axioms).  Landed:

1. **`CompletedModel::macros`** carries each solved macro's defining body;
   `CompletionEval::fold_apply` beta-reduces it at the (evaluated)
   arguments and evaluates the result under the same completion (depth
   capped at 16, arity mismatch declines).  When several axioms define the
   same function (`seteq` as equality *and* as double-subset), the
   *simplest* body wins — the conjunction macro inherits other functions'
   else at symbolic points and breaks the equality axiom's own check.

2. **Universe-distinctness folding for uninterpreted-sort equality** in
   the evaluator: two *ground* universe representatives are unequal by
   construction — without the fold, a mined substitution's ite-chain
   conditions `(= z a)` stayed symbolic and the falsifier the aux check
   found was never mined.  The first cut folded symbolic operands too
   (the universe contains bound-variable artifact terms from entry
   arguments!), fabricating `(= ?s1 ?s2) = false` and with it a fake
   falsifier — the groundness guard is load-bearing.

3. **`p -> p` collapses in `deep_simplify`**: the reflexive-implication
   shape the set axioms instantiate into (`A3[z,z]`'s tautological
   antecedent) now collapses, turning the instance into the unit
   `subset(z,z)` and forcing the diagonal pin the SAT core otherwise
   dodges via the wrapper Boolean.

4. **Falsifier mining iterates the finite universe** for uninterpreted
   sorts (not just the instantiation set), and the MBQI bail counts a
   *streak* of unproductive rounds (10) instead of a flat total — a flat
   25 taxed every re-check 2.3x on the rerun convergence pins (63s ->
   150s single-threaded); the streak restores 88s while letting
   converging goals run past round 10.

The set family still answers `unknown`: after all of the above, the
residual falsifiers sit at the *universe's compound elements*
(`union(b,a)`, ...) whose subset diagonal pins the mining emits as
duplicates of already-instantiated pairs — the ground solver satisfies
the forcing equivalence by committing the *inner* nested binder's Boolean
false (the committed-existential dodge from pass four, now the only
remaining mechanism).  Model repair (Z3's `add_blocking_clause`) remains
the fix.

## Sixth pass (2026-09-13): the dodge's emission-side root cause found; repairs built, measured, reverted

**Root cause (emission side), precise:** `deep_simplify_cached` had no
`Forall`/`Exists` arms — quantifier nodes were *opaque* to the
instantiation post-simplifier.  A tautological-antecedent instance
(`(forall x. P(x) => P(x)) => subset(z,z)`) therefore kept its wrapper,
and the SAT core dodged the consequence by committing the wrapper's free
Boolean FALSE.  Descending under the binder (letting the existing
`p -> p` collapse fire) plus collapsing constant bodies (`forall x. true
-> true`, sound under SMT-LIB's non-empty domains) turns such instances
into forcing units at emission — structurally removing the dodge for the
tautological class.

**Built and measured, then reverted:** the binder descent + constant
collapse, macro ground-pinning on satisfaction (`SatisfiedWithPins`:
certifying a macro's defining axiom also emits its defining instances at
the universe tuples, so *other* axioms over the same function instantiate
forcing-ly), simplest-macro preference inside `solve_macros`, and a
productive-check refund of the per-quantifier cap.  All sound (each
verified against the FFT/Rodin/differential screens), and each moved the
set-family convergence one step further — q14 certifies, q18's residual
falsifier isolates to *compound* universe elements
(`union(b,a), union(b,a)`) whose diagonal pins the enumerative seeder can
no longer emit (its per-quantifier budget is spent by the time the
compound term enters the universe).

**Why reverted:** the collapses change every MBQI instance's clause
shape, which shifts the SAT trajectory — the 600-rerun convergence pins
(`scope_rebase_tests`) went 88s -> 132-167s single-threaded user time
(a 1.5-1.9x trajectory cost, not a code-path cost; bisected against
clean HEAD in a worktree).  Per the benchmarking discipline
(`docs/BENCHMARKING.md`), a trajectory-shifting change needs the
matched-null protocol before landing, and the verdict upside was not
realized (the set family still answers `unknown`).  The designs are
recorded here for a re-land *together with* the blocking-clause model
repair, measured as one unit.

**Remaining mechanism (final form):** the universe admits compound
constructor terms (`union(b,a)`) as elements; definitional closure over
them needs pins the seeder's exhausted budget cannot emit.  The repair
is Z3's `add_blocking_clause` model repair at the escalation's
duplicate-falsifier point: block the arrangement (the falsifier's
supporting commitments), forcing the next model to either produce the
witness or flip — plus re-landing the binder-descent collapses with the
matched-null measurement.

## Verification

- `cargo build --all-features` clean; `cargo nextest run` over the six
  core crates **9083/9083**, 0 timeouts (whole-workspace runs blocked by
  concurrent agents' in-flight `nixie-tla-check`); `cargo clippy -p
  nixie-solver --all-features --all-targets -- -D warnings` clean, `cargo
  doc -D warnings` clean, `cargo fmt --all -- --check` clean on every file
  I touch; the heaviest rerun pin measured single-threaded at 74 s vs 55 s
  clean HEAD (A/B worktree bisect).
- 200-file random differential (AUFLIA/UFLRA/UFLIA, 10 s budget): **zero
  wrong answers** — this is the screen that caught the Rodin false-`sat`.
- Fourth pass: 150-file differential zero wrong; the heaviest rerun pin
  63 s single-threaded (55 s clean HEAD); the set-family rounds now run
  their full budget productively (the flat `subset` table is reached)
  instead of diverging.
- `./bench/z3_parity/run_parity.sh` (z3 4.16.0): **176 Correct / 1
  Inconclusive** (the pre-existing `array_unique`, z3-side `Unknown`); the
  two FFT corpus files were added to the suite
  (`benchmarks/UFLRA/fft_62048{7,5}.smt2`) so the gap stays closed.
- Regressions: `nixie-solver/tests/uflra_quantifier_regressions.rs` (7
  tests) — the FFT shape, the spelled-out instance (assert path), the ground
  congruence pair (unsat + its satisfiable twin), the false-`Satisfied`
  shape over Int, the A2/A3 alternation never-wrong pin, the vacuous-
  membership never-wrong pin, and the Rodin goal never-falsely-satisfied
  pin (exact transcription of the false-`sat` file).

## File map

- `nixie-solver/src/mbqi/model_checker.rs` — new: the Z3-style nested model
  checker (completion evaluator, else/ite-chain interpretation, Skolemized
  refutation, term-level falsifier mining, budgets).
- `nixie-solver/src/mbqi/integration/mod.rs` — escalation wiring (only on a
  cex-empty round), satisfaction accounting (`satisfied_by_checker` exempt
  from the finite-exhaustion gate), logic hint.
- `nixie-solver/src/mbqi/model_completion.rs` — the universe-seeding gate
  counts function-entry arguments/results as domain evidence.
- `nixie-solver/src/solver/mod.rs` — `intern_compound_uf_args_into_arith`
  (layer 2 repair; initial site + MBQI round boundary; memoized,
  push/pop-invalidated), `register_unit_lemma_quantifiers` +
  `register_lemma_binder` (polarity-aware, guarded, e-matching-excluded
  nested-binder registration), `collect_apply_args` helper.
- `nixie-solver/src/solver/config.rs` — `set_logic` forwards the logic hint.
- `nixie-solver/src/solver/trail.rs` — the new fields' scope invariants.
