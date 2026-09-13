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

Diagnosis: the axioms are vacuously satisfiable under a completed model with
`else = false` (member nowhere true), and the nested checker *does* certify
individual quantifiers (`Satisfied` verdicts observed). Convergence fails at
the **model-search** level: the completion's universe seeding mints synthetic
`u!i` elements (8+ for a two-element sort), the mined counterexample lemmas
pin the Bool tables over that blown-up domain, and the rounds exhaust their
budget before all quantifiers are simultaneously satisfied. What is missing
is Z3's `smt_model_finder` behaviour: candidate *else/default searches* per
function (search over plausible defaults, verify, revise) and a conservative
universe (the e-graph's known roots, not synthetic seeds). That is a
finite-model-finder work item, not a bug in what landed.

## Verification

- `cargo build --all-features` clean; `cargo nextest run --workspace
  --all-features` **11199/11199**, 0 timeouts; `cargo clippy --all-features
  --all-targets --workspace -- -D warnings` clean; `cargo fmt --all --
  --check` clean; `cargo doc -D warnings` clean.
- `./bench/z3_parity/run_parity.sh` (z3 4.16.0): **176 Correct / 1
  Inconclusive** (the pre-existing `array_unique`, z3-side `Unknown`); the
  two FFT corpus files were added to the suite
  (`benchmarks/UFLRA/fft_62048{7,5}.smt2`) so the gap stays closed.
- Regressions: `nixie-solver/tests/uflra_quantifier_regressions.rs` (5
  tests) — the FFT shape, the spelled-out instance (assert path), the ground
  congruence pair (unsat + its satisfiable twin, the repair's soundness
  guard), the false-`Satisfied` shape over Int, and a never-wrong pin for
  the set family.

## File map

- `nixie-solver/src/mbqi/model_checker.rs` — new: the Z3-style nested model
  checker (completion evaluator, else/ite-chain interpretation, Skolemized
  refutation, term-level falsifier mining, budgets).
- `nixie-solver/src/mbqi/integration/mod.rs` — escalation wiring (only on a
  cex-empty round), satisfaction accounting (`satisfied_by_checker` exempt
  from the finite-exhaustion gate), logic hint.
- `nixie-solver/src/solver/mod.rs` — `intern_compound_uf_args_into_arith`
  (layer 2 repair; initial site + MBQI round boundary; memoized,
  push/pop-invalidated), `collect_apply_args` helper.
- `nixie-solver/src/solver/config.rs` — `set_logic` forwards the logic hint.
- `nixie-solver/src/solver/trail.rs` — the new memo field's scope invariant.
