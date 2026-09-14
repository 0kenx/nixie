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
