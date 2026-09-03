# EUF theory-lemma certificates for certified `unsat` — grounded design (2026-09-03)

Status: **designed, not implemented**. Every code surface below was verified
against the tree at `be0587e`; file:line references are live. This document
is the implementation plan for the next session, with the hazards already
found so they are not rediscovered.

## Motivation (measured)

The certified-path re-measure (`2026-09-02-lrat-default-path.md`, addenda
6–7) bounds the remaining gap: certified `unsat` still fails closed to
`unknown` whenever the refutation needs theory semantics — **39/46 unsat
QF_UF cells and 23/29 unsat QF_LIA cells** in the stratified sample. The
UF `sat` side is closed (addendum 7); this is the certified-`unsat`
frontier named there.

## Architecture (proof-carrying, not re-solving)

The gate must stay a *checker*, not a second solver. The main run already
materializes every theory fact it uses as a Boolean clause over equality
atoms; the design exports those clauses to the gate, where each is
independently verified by congruence closure, and LRAT refutes
skeleton ∪ verified-lemmas:

1. **Lemma recording** (main run). Theory facts surface at exactly two
   shapes in the CDCL(T) loop:
   * conflicts: `TheoryCheckResult::Conflict(lits)` — the conflict clause
     is a valid EUF lemma (oxiz-sat `solver/mod.rs:168-175`, consumed at
     `search_ext.rs:201` and `:413`);
   * propagations: `TheoryCheckResult::Propagated((lit, reason_lits))` —
     the explanation clause `lit ∨ ¬r₁ ∨ … ∨ ¬rₖ` is materialized by
     `add_theory_reason_clause` (`learn.rs:489`); the lazy-reason path
     (`assign_theory_propagation`) keeps the same clause immaterialized —
     record it anyway (it participates in conflict analysis and hence in
     the final refutation).
   Add `fn record_lemma(&mut self, _clause: &[Lit]) {}` (default no-op) to
   `TheoryCallback` (`oxiz-sat solver/mod.rs:181`) and call it from those
   consumption points with the full clause literals.

2. **Solver-owned log.** The `TheoryManager` is a per-search local
   (`check_core`, `solver/mod.rs:1646`, recreated at rebase sites
   1836/1880/1966), so the log cannot live on it. It already holds
   `&mut DerivedReasons` (Solver-owned, `theory_manager.rs:583`
   constructor) — extend `DerivedReasons` (`theory_manager/derived_reasons.rs:68`)
   with `theory_lemmas: Vec<Vec<(TermId, bool)>>` + a poisoned flag.
   `record_lemma` maps each SAT lit through `var_to_term`
   (`Vec<TermId>` indexed by var) to its atom term; a literal whose term is
   not `TermKind::Eq` over non-Bool operands sets **poisoned** (the gate
   then declines — QF_UF scope only). Dedup by sorted (term, polarity) key.
   The log is *never* cleared on theory reset (lemmas stay valid clauses);
   clear it at `check_core` entry (per-goal hygiene).

3. **Independent CC verification** (gate). `certify_unsat`
   (`certification.rs`) extends `BooleanLratChecker::assert_all` with the
   lemma pass: for each recorded lemma, run a small congruence closure over
   the lemma's own literals — union the positive `Eq`s, collect the
   negative `Eq`s as pending disequalities, close under congruence
   (signature table over `Apply` terms, fixpoint), then check a pending
   pair merged. Merged ⇒ the lemma's conjunction is EUF-unsatisfiable ⇒ the
   clause is valid ⇒ encode it (`encode` already abstracts non-Bool `Eq`
   as atoms, `certification.rs` encode arm
   `True | False | Var | Eq => {}`) and buffer it. Any lemma that FAILS CC
   rejects the whole certification (a wrong lemma means the theory lied —
   fail closed, never skip-and-continue). Poisoned log ⇒ skeleton-only
   behavior (today's).

4. **Distinct.** The gate's skeleton encode abstracts `Distinct(args)` as
   one opaque atom, but the theory's disequality facts surface as `¬Eq`
   literals — the link `distinct ⇒ pairwise ¬Eq` is missing and the
   refutation will not close. Encode `Distinct` structurally in the gate:
   fresh var `D` plus `(¬D ∨ ¬Eq(aᵢ,aⱼ))` for each pair (forward direction
   only — sound, and sufficient for UNSAT). The `Eq(aᵢ,aⱼ)` atoms are
   hash-consed, so they are the *same* TermIds the lemma literals use.

## Soundness argument

* The gate trusts only: the skeleton clauses (its own Tseitin encoding of
  the original assertions) and lemmas that pass the independent CC check.
  A broken EUF, a lying propagation reason, or an unsound recording hook
  can only make a lemma FAIL CC (⇒ `unknown`), never certify a false
  `unsat`.
* Completeness (coverage) rests on CDCL(T)'s invariant that the final
  refutation resolves only skeleton clauses, materialized theory reason
  clauses, and lemmas derived from them by Boolean resolution (which LRAT
  checks). Over-recording is harmless (extra valid clauses).

## Hazards already found (do not rediscover)

* **ite-over-uninterpreted-sort applications are not EUF-interned** (the
  addendum-7 candidate bug): lemma literals may reference `Eq` atoms whose
  operands contain such terms. The CC verifier must walk subterms via
  `get_children` generically (no assumption that operands are leaves).
* **Lazy theory reasons** (`assign_theory_propagation`,
  `theory_lazy_reasons_enabled`): no clause is materialized in the SAT DB,
  but the reason clause still feeds conflict analysis — it must be
  recorded at the consumption point, before the branch.
* **Rebase recreations** of `TheoryManager` mid-`check_core` drop nothing
  that matters only if the log is Solver-owned (hence `DerivedReasons`).
* **Boolean `Eq` (iff)**: a lemma literal whose atom is `Eq` over Bool
  operands is *skeleton* structure, not a theory atom — treat as poison
  (conservative; the skeleton-only path already handles pure-Boolean
  contradictions).
* The `Conflict(lits)` clause is valid as given (theory lemma); the
  1-UIP clause `analyze_theory_conflict` derives from it is Boolean
  resolution over it + reason clauses — RUP covers it, no need to record.

## Gates

* Unit: CC verifier accepts congruence-axiom instances and transitivity
  chains; REJECTS a non-valid lemma (e.g. `a≠b ∨ f(a)=f(b)` with no `a=b`);
  handles distinct-derived disequality and nested applications.
* E2E (`certified_uf_sat.rs`): congruence-dependent unsat (the
  `congruence_unsat_stays_unknown` test flips to `unsat` — update it), a
  quasigroup-shaped file, sat-side unchanged, poisoned log (add an arith
  atom to force it) ⇒ `unknown`.
* Full battery, clippy/fmt/doc, Z3 parity; then the QF_UF sample
  re-measure (39 unsat-unknown cells are the target) recorded in the
  result store as a new config (`euflemma-cert`).

## Estimated scope

~250 lines of new code (CC verifier ~120, recording ~60, gate wiring ~50,
Distinct encode ~20) plus tests. No change to any verdict path outside
certified mode.
