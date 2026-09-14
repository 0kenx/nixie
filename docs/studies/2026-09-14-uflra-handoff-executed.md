# UFLRA handoff executed: the blocking-clause unit, the collapses re-landed, and where the set family stands now

**Date:** 2026-09-14
**Input:** `docs/studies/2026-09-13-uflra-handoff.md` (executed in the
worktree `/tmp/wt-uflra` at `main` = `96bee940`).
**Comparator:** z3 4.16.0.
**Verdict:** the two prescribed items landed as one unit (plus five
independently-pinned defects found on the way). The set family
(`set9/16/19`) still answers `unknown`; its *remaining* mechanism is now
isolated to a single precisely-scoped project — the **entry-table search**
of Z3's `smt_model_finder` — which this unit's else-revision search
bounds but does not replace. No regression anywhere: parity stays
176/1, the Rodin canary holds, FFT holds, the full solver suite passes.

## What landed (one unit)

1. **The emission-side collapses (handoff item 2), re-landed.**
   `deep_simplify_cached` gained `Forall`/`Exists` arms (`QuantBody`
   frame): the simplifier descends under binders (letting the existing
   `p -> p` collapse fire there) and folds constant bodies
   (`forall x. true -> true`, `exists x. false -> false` — sound because
   every SMT-LIB sort is non-empty). The set axioms' tautological
   instances `(forall x. P(x) => P(x)) => subset(z,z)` now reach the
   ground solver as the forcing unit `subset(z,z)`; the
   committed-Boolean dodge is structurally removed for this class.
   `CompletionEval` gained the matching `Forall` constant-collapse (the
   `Exists` arm existed; the `Forall` arm did not — the aux goal
   `(forall x. true) => false` stayed opaque to its own solver).

2. **`SatisfiedWithPins`** (`emit_macro_defining_pins`): certifying a
   macro's defining axiom emits its defining instances at ground-universe
   tuples (diagonals first, capped 64/round) — the forcing pins at
   compound elements the exhausted seeder budget can no longer reach.

3. **Simplest-body macro preference inside `solve_macros`**: a plain
   `insert` collapsed competing definitions to the last-seen before any
   downstream tie-break could see them; the size preference now lives
   where all candidates are visible (the completion-side preference
   stays as defense). `seteq` now completes as its equality body.

4. **The blocking-clause model repair (handoff item 1), sound-core
   form.** The escalation trigger broadened to *duplicate-only* rounds
   and to *budget-exhausted* universals (a certification is a proof,
   bounded by the checker's own budgets, not by the search budget that
   starves the pins — this is the literal "seeder budget exhausted"
   mechanism of the handoff's diagnosis). The falsifier miner records
   its supporting commitments (assignment hits, entry hits as
   `f(args)=result` atoms) and its free choices (else fallthroughs,
   macro reads, universe folds, sort defaults). A duplicate falsifier
   whose evaluation is **fully pinned** (no free choice) carries a
   blocking clause `or_i (atom_i != value_i)` into the main solver —
   Z3's `add_blocking_clause` adapted: the falsification is a function
   of the recorded commitments alone, so the excluded arrangement
   provably fails the quantifier and the clause loses no solution; an
   atom the ground solver never internalized drops the *whole* clause
   (skipping it would strengthen the clause into a claim it never made).

5. **Wasted-solve streak + certification memory** (replaces the
   per-quantifier lifetime cap of 2): the cap now counts only solves
   that produced neither a fresh instantiation nor a satisfaction
   verdict; `certified_at` remembers certifications per model signature
   (the dual of `falsified_at`) so a stable model never re-pays.
   Without this, the broadened trigger exhausted the old cap on
   signature-declines and silenced exactly the certification the loop
   needs (pinned: rounds 2+ answered "per-quantifier check budget
   exhausted" for every quantifier).

6. **Actual-conflict accounting** in `aux_refute`: the global 50k budget
   was charged the 4096 per-check *cap* per solve; 12 small solves
   exhausted it. Now charged `aux.stats().conflicts` deltas.

7. **Bounded per-function else-revision** (the handoff's
   `smt_model_finder` direction): when a body is falsified and its
   evaluation consulted non-Bool functions' defaults, each consulted
   function's default is revised over its entry results and the range
   sort's ground universe (≤4 functions, ≤8 candidates, ≤6 solves per
   check), each revision verified by the nested refutation. This is the
   "search, verify, revise" loop, single-revision-bounded.

8. **Value-normalized, ground enumerative domains and mining sets**
   (Z3's inst-set semantics): `build_small_domains` and the falsifier
   odometer enumerate the model's *distinguished values* (one
   representative per assignment value) over the *ground* universe.
   Before: raw universe terms, compounds and bound-variable artifacts
   included — `union(a,b)` and `b` counted as two domain points,
   `?s1 := ?s2` bindings were mined, and semantically-redundant lemmas
   kept the rounds "productive" while the model never moved.

9. **The universe-distinctness fold's groundness guard** (handoff trap
   #2, fixed at the consumer): the completed model's universes contain
   bound-variable artifact terms (entry args harvested by
   `collect_universes_from_model`); folding `(= ?s1 ?s2)` to `false`
   for *symbolic* operands fabricated a pointwise-constant body the
   completion does not justify (observed live: the seteq-equality axiom
   body' read `(= false ...)` with symbolic `?s1/?s2`). The fold now
   requires both operands ground; `ground_universe(sort)` filters
   artifacts for the Skolem restriction, the mining sets, the defining
   pins and the sort defaults. Pinned by
   `set16_diagonal_diseq_disjunct_is_never_falsely_satisfied` (a
   `(or (not (= s1 s2)) psi)`-shaped goal the fold could certify
   pointwise-true; z3 refutes it).

## Why the set family still answers `unknown` (the isolated mechanism)

With everything above, the rounds no longer spin on duplicates — they
*converge* the subset/seteq tables and then diverge on an unbounded
**compound-closure chase**: mining the `union`/`intersection`/
`difference` axioms at universe tuples pins `member` at ever-deeper
compounds (`union(union(b,b),a)`, ...), each pin a fresh instance, each
instance minting the next compound; the entry tables pass the checker's
1024 cap and everything declines. The root cause is that the ground
model is free to give every compound a *fresh* value — nothing forces
`union(b,b) = b` — while the axioms only constrain *member* at the
compounds, so the value-partition never stabilizes. A uniform `else`
revision cannot fix it (union needs `union(b,b)=b`-shaped *entries*),
which is why the else-revision search bounds but does not close the
family.

**The remaining project** is Z3 `smt_model_finder`'s *entry-table*
search: for each Set-valued constructor, search its table over the
small universe (combinatorially, with verification) so the completed
interpretation is closed under its own definitional axioms. That is a
bounded finite-model-finder project of its own — correctly out of
scope for this unit, and possibly subsumed by the native set theory
another agent is building (`solver/set_theory.rs`).

## Cost decomposition (the heaviest convergence pin, single-threaded, one seed each — indicative, not the formal 10-seed protocol)

`scope_rebase_tests::re_running_the_search_on_an_unchanged_goal_converges`,
this machine, 2026-09-14 (chaotic — treat ±30% as noise; the *arms* are
the signal):

| arm | time | vs baseline |
|---|---|---|
| clean HEAD (`96bee940`) | 2m08s | 1.00x |
| + always-on unit (collapses, groundness, normalizations, pins), all new escalation arms off | 2m49s | 1.33x |
| + exhausted/duplicate escalation (old hard cap) | 2m18s | 1.05x (noise) |
| + else-revision, per-check budget (6/check) | 5m10s | 2.5x |
| + wasted-solve streak with productive resets (landed first) | 10m54s | 5.2x |
| streak bounded by hard total 4, else-revision lifetime-bounded 16 | 3m01s | 1.45x |
| **landed shape** (+ frozen ground-universe views: the ground filter now computed once per completion, not per `choose_else` call) | **2m42s** | **1.29x** |

The landed 1.29x is consistent with the sixth pass's own measurement of
the collapses' trajectory cost (1.5–1.9x) — the treatment's inherent
clause-shape change, which the handoff prescribed re-landing together
with the blocking clause and measuring as one unit.

## Negative results (do not retry blind)

- **A pure wasted-solve streak (productive resets, no hard total) is the
  fifth-pass cap-removal regression in new clothes**: a quantifier that
  keeps mining semantically-fresh-but-unproductive lemmas on a moving
  model (the set family's compound-closure chase) resets its own streak
  forever — 5.2x on the heaviest pin.  The streak is only sound *with*
  a non-resetting total underneath.
- **Uniform else-revision closes nothing on set16**: a single default
  cannot satisfy `union(a,a) ∈ {a}` and `union(b,x) ∋ sk(b,a)`
  simultaneously; the violating points are entry-shaped.  (The search is
  still sound, cheap after the lifetime bound, and may close other
  families; it just is not the set family's closer.)
- **Value normalization alone does not stop the compound chase**: it
  collapses only compounds the *assignments* table already equates, and
  nothing equates unpinned compounds.  The chase is driven by fresh
  *values*, not fresh terms.
- **Signature-gate declines consumed the old lifetime cap**: the cap
  increment happened before the signature gate, so every duplicate-model
  round burned a "check".  Any future per-quantifier budget must count
  only executed solves (the streak+total redesign does).

## Verification

- Six core crates `nextest`: nixie-core 2208, nixie-math 753,
  nixie-sat 1084 (one `si2_b03m` failure under parallel load + corrupted
  incremental cache — passes in isolation and in the clean rerun),
  nixie-proof 731, nixie-theories and nixie-solver full suites green
  after the cache fix (see the landed commit's CI record).
- `./bench/z3_parity/run_parity.sh` (z3 4.16.0): **176 Correct /
  1 Inconclusive** (pre-existing z3-side `Unknown` on `array_unique`).
- New regressions: `set16_family_is_never_wrong` (bounded 8s; never
  `unsat`), `set16_diagonal_diseq_disjunct_is_never_falsely_satisfied`
  (never `sat`),
  `tautological_antecedent_instance_becomes_a_forcing_unit` (the
  collapse forces `g(0)` against `(not (g 0))`).
- FFT corpus canaries (`fft_62048{7,5}`): still `unsat`. Rodin canary:
  pinned by the exact transcription test, passing.

## Corpus loss (blocking for future differential screens)

During this session the **`smt-lib/` corpus was deleted from the shared
tree** (external, `.gitignore`d, ~100k files; `smt-lib/non-incremental/`
incl. the UFLRA `misc/set*` and the AUFLIA Rodin tree). The
`bench/z3_parity` suite (in-repo) is intact and was the verification
gate. `set16` was reconstructed verbatim from this study's record and
pinned as a test. The 150-file differential screen of the handoff could
not be run as specified; **substitute screen (run post-landing with the
`precompile/15fbf617` release binary, z3 4.16.0, 12 s budget)**: every
in-repo `bench/{z3_parity/benchmarks,extended_theories,regression}`
file — **224 files: 213 definitive agreements, 11 inconclusive
(unknown/err on either side, in both directions), 0 wrong answers**.
Re-fetch SMT-LIB (StarExec space 239) before the next prescribed screen;
`set9`/`set19` could not be reconstructed (content not recorded
anywhere — only `set16` was).

## Post-landing audit: the else-revision removed (divergence vector)

A follow-up audit of the landed unit found a theoretical soundness shape
in the else-revision search: its certifications could rest on *different*
one-shot interpretations for different quantifiers (q1 certified with
`union`'s else revised to `b`, q2 with `a` — the round's `Satisfied` then
exhibits no single model of the conjunction).  A live false-`sat` could
not be constructed (probes collide the instances at ground level first —
finite-universe mining meets `forall s. phi(f s))` and
`forall s. not phi(f s))` at the same ground `s` before either
certifies), but the vector was real.  Closing it the consistent way (one
globally accepted revision merged into every later check) **quadrupled
the convergence pins** (4/9 timeouts: the merged table reshapes every
subsequent aux goal — trajectory cost, not code cost).  Decision:
**remove the revision search entirely** — it demonstrated no win
anywhere (set16's violating points are entry-shaped, not default-shaped),
it is completeness-only, and it carried the vector.  The entry-table
search that would actually close the set family must be built
*globally-consistent from the start* (one interpretation, revised
monotonically, every certification against the current one) — recorded
as a design requirement for that project.

Landed as the follow-up commit (`ea461630`); pins 9/9 (194s group, 3m00s
heaviest single-threaded — within the unit's band, trajectory chaos),
parity 176/1/0, all 51 quantifier regressions pass, and the 224-file
substitute differential re-run with the new release binary: **0 wrong
answers** (213 agree / 11 inconclusive).

## Post-landing record

- Landed as `533ae756` (the unit) + `15fbf617` (clippy/fmt hygiene on
  another agent's concurrent simplex landing: two needless `mut`,
  formatting) after two rebases onto concurrently-moving `main`.
- Release binaries cached: `precompile/533ae756/` and
  `precompile/15fbf617/` (same build, exact-SHA entries).
- The heaviest convergence pin carries a `terminate-after = 5` nextest
  override (`.config/nextest.toml`), following the `pete_cxs_bp`
  precedent: debug single-threaded 2m42s, but the full suite's parallel
  load inflates wall time past the 3x60s default.


## The entry-table attempt (2026-09-14, third pass): tables fire, convergence needs the full finder

A bounded attempt at the entry-table search landed in a worktree and was
**reverted** — the table machinery works, but the family's convergence
needs the whole `smt_model_finder` loop, not the tables alone.  What was
built and measured:

1. **Quasi-macro extraction** (`extract_quasi_macros`): axioms
   `g(v..., f(w...)) = psi` with `f` an uninterpreted-range constructor
   over distinct bound vars, observed through the Bool-valued `g` — the
   `member(x, union(s1,s2)) = (member(x,s1) or member(x,s2))` shape.
   Extracts union/intersection/difference reliably (3/3 on set16).
2. **Semantic table computation** (`compute_constructor_tables`,
   completion step 10): at each unpinned tuple of `f`'s argument
   universes, the target row is `psi`'s truth over the observer's
   distinguished row-points; `f(t) := z` for the universe element whose
   row matches.  Verified firing: 4 computed entries per constructor over
   the two-element universe.  Computed entries marked
   (`computed_functions`) so blocking-clause commitments treat them as
   free choices; ground pins never overridden.
3. **Semantic value normalization** (`semantic_value`, explicit-stack):
   domain/mining normalization through the tables, so `union(b,b)` and
   `b` collapse to one domain point.

**Why it still answers `unknown`**: the rounds churn on the *other*
engine — the enumerative insts over the growing Real-domain sample
(each round's witness Skolems join it) keep the model moving, and the
checker's per-quantifier caps (the ones that bound the measured 5.2x
streak cost) silence certification while the model moves.  Closing that
needs the full search-verify-revise loop over the *whole* interpretation
per round (Z3's `smt_model_finder` project proper), not the entry tables
in isolation.  The essential design requirements are now proven by
experiment: one globally-consistent interpretation per round (the tables
are computed at completion — every consumer sees them), semantic (not
syntactic) value normalization, and ground pins never overridden.

**Bugs found and FIXED on the way (landed)**:

- **The ground-universe artifact filter rejected free constants.**  A
  `(declare-fun a () S)` constant is represented as a `Var` node, and
  the landed filter rejected *any* `Var` — so a universe whose elements
  were free constants froze EMPTY (starving the mining sets, the
  enumerative domains and the Skolem restrictions built on it).  The
  filter is now by bound-variable NAME (a `Var` is an artifact exactly
  when its name is a tracked quantifier's bound variable), with the
  names frozen alongside the universes.  The convergence pins got
  *faster* with the fix (151s vs 194s group time).
- A constructor the ground model never applied has no interpretation
  entry; the table computation must create one over the axiom's domain
  (recorded in the reverted design; relevant again if the finder project
  picks the tables up).

**The reverted diff's shapes** are recoverable from this session record;
re-derive rather than resurrect — the `semantic_value` first cut
overflowed the native stack (native recursion over argument depth — the
AGENTS.md explicit-stack rule exists for exactly this) and the frame
machine rewrite is the version to keep.


## The quant_fuzz catch (2026-09-14, fourth pass): the blocking clause was unsound — removed

A new differential fuzzer over the *quantifier surface*
(`bench/differential/quant_fuzz.py`, modeled on `mixed_fuzz`: random
uninterpreted sorts + Bool-valued observers + definitional/witness/
tautological-antecedent axioms, every decisive verdict diffed against
z3) found a **false `unsat` within 120 generated cases** — and the
bisect pinned it on the blocking-clause path, exposed once the
artifact-filter fix made the universes non-empty:

The mining pass evaluates the *substituted completed body*, whose
ite-chains already bake in completion choices (else leaves, entry
conditions).  Those choices are not flagged in that pass — only live
`fold_apply` calls are — while chain-condition atoms that are
**asserted constraints** (`(not (= c1 c0))`) get recorded as
"commitments".  Blocking that arrangement emits a clause asserting
`= c1 c0` against the assertion: an instant refutation of a goal whose
every model keeps the constants distinct (z3: `sat`).  Pinned by
`tautological_axiom_over_disequal_constants_is_never_unsat`.

**The emission is removed** (the commitment recording stays as
diagnostics): Z3's `add_blocking_clause` blocks on the AUX context's
*Skolem values* — a context where blocking only diversifies the
falsifier search — never on main-solver commitments.  Any future port
must live in the aux context; the handoff's item (1) is thereby
*honestly closed as removed*, not adapted.  Verification: the 300-case
quant_fuzz screen runs **CLEAN** (133 sat + 114 unsat decisive, 0
disagreements), parity 176/1/0, pins 9/9, 52 quantifier regressions
pass.

Post-fix multi-seed evidence: seeds {41..46} x 300 cases against the
landed `precompile/ae6cea17` release binary — **1800 generated goals,
0 disagreements** (~1300 decisive verdicts matched; ~23% honest
`unknown`).  The generator skews sat-heavy (z3: ~195 sat / ~103 unsat
per 300) — a future unsat-forcing shape family would balance it.

Lesson recorded: the two soundness shapes this arc (the else-revision
divergence, this commitment blocking) were both in *my own* additions,
both found by differential screens, and both resolved by removal rather
than repair — when an adaptation of a reference mechanism cannot carry
the reference's context guarantees, the adaptation is the bug.


## Screening the concurrent landings (2026-09-14, fifth pass)

`main` absorbed two large concurrent landings after the unit (the CSR
primary-watch FLIP `c77ddf76`, and the set-equality wrong-`sat` fix
`200b3eab`) with no quantifier-surface screen.  Re-ran the screens on
`ed401429` (current `main` at the time): quant_fuzz seeds {41,42,43} x
300 — **0 disagreements**; mixed_fuzz 400 cases — **no verdict
disagreements, no refuted models**; parity — **176/1/0**.  Binary
cached at `precompile/ed401429/`.


## Sixth pass (2026-09-14): the filter admission reverted — a false-`sat` it exposed

The strengthened generator (contradictory-definitional twins + a spoil
step) found a **false `sat`** on seed 42 (`contradictory_definitional_
twins_are_never_sat` pins it): `P = not (phi => phi)` forces `P` false
everywhere, a tautological-antecedent axiom forces `P` everywhere — z3
refutes; the solver certified `sat`.  Bisected to `2700e3d7` (the
ground-universe filter admitting free constants); **reverted** — its
standalone value was the (also reverted) entry-table experiment, and the
starvation it fixed is completeness-only.

**Root-cause trail for the next session** (the exposure, not yet the
defect): with nonempty universes the falsifier miner's *substituted
completed body* can mention an artifact variable outside the check's
bound set (it arrives through the completion's entry chains — an entry
keyed on an encoder binder constant normalizes into a chain condition).
The substitution does not cover it, and the mining eval runs with an
*empty* bound set, so (a) `is_symbolic` is vacuous — the
universe-distinctness fold treats the residual Var as a ground element
and fabricates `(= y c_i) -> false`; (b) a `body'` was observed folding
to literal `true` against an all-false 101-entry table — the same leak
class reaching the certification path.  The *class* predates the filter
change (latent with empty universes): fixing it properly means (1)
threading the check's bound names into the mining eval as the artifact
set, (2) filtering bound-named keys out of the harvested entry tables
(the same name rule the universes use), and (3) re-deriving why a
macro-completed application evaluated to `true`.  Instrumentation
shapes that worked: `NIXIE_DEBUG_ENTRIES` (entry dumps),
`NIXIE_DEBUG_FOLD` (fold/wildcard/macro-fire traces).

Post-revert verification: quant_fuzz seeds {41,42,43} x 150 with the
strengthened generator — CLEAN (101+96+93 unsat and 15+16+15 sat, all
matching z3); pins 9/9; parity 176/1/0; 58 quantifier regressions.


## Seventh pass (2026-09-14): the root cause — binder nodes read from the SAT core's wrapper commitments

The sixth pass's containment (the filter revert) is superseded by the
root-cause fix, found by instrumenting the exact fold that never fired:

**`CompletionEval`'s assignment-table shortcut applied to binder
nodes.**  The encoder internalizes a quantified subformula with a
Tseitin wrapper Boolean, and the ground model's assignment table carries
that wrapper's *commitment* — a value the SAT core chose freely (the
wrapper dodge), not the subformula's truth.  The evaluator's `Enter`
arm looked the term up whenever it was "not symbolic" — and
`(forall z. true)`'s traversal sees no free variable, so the shortcut
fired: the *valid* subformula read as `false`, and
`(=> (forall z. true) (P x y))` certified vacuously.  That is the whole
false-`sat`; the entry-chain and mining-bound leaks were secondary
exposures of the same admission.

**The fix bundle** (one unit, re-landing the reverted admission with
the class closed):
1. `Enter` never consults the assignment table for `Forall`/`Exists`
   nodes (a binder is never a ground-model fact).
2. The ground-universe filter re-admitted, keyed on tracked
   bound-variable *names* (free constants are elements; encoder binder
   constants are not), with the name set frozen on the model.
3. Entry tables drop artifact-keyed entries at harvest (the wildcard
   `[x, y] -> v` rows the encoder's internalization leaves behind).
4. The falsifier-mining evaluation runs with the tracked names as its
   symbolic set — a surviving artifact variable stays symbolic instead
   of being fabricated into `(= artifact c) -> false` by the
   universe-distinctness fold.

Verification: the twins reproducer answers `unsat` (z3 agrees);
quant_fuzz (strengthened) seeds {41,42,43,44} x 150 — **CLEAN**; 58
quantifier regressions (both new pins in); pins 9/9 (173s); parity
176/1/0; fmt/clippy clean on the touched files.
