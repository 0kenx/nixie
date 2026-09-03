# LIA theory-lemma certificates — grounded design for the next certified-unsat frontier (2026-09-03)

Status: **designed, not implemented.** Surfaces verified against the tree
at `9a117ea`. Companion to `2026-09-03-euf-lemma-certificates-design.md`
(whose EUF half is landed and measured at 92% QF_UF coverage).

## Motivation (measured)

After the EUF-lemma work and both residual hunts, certified QF_UF coverage
is 70/76 (92%) while certified QF_LIA sits at 52/174 (30%): every one of
the 23 theory-dependent unsat cells (and any unsat beyond the 6
skeleton-refutable ones) fails closed to `unknown`, because pure-QF_LIA
theory lemmas are arithmetic comparisons — the EUF recorder correctly
poisons them, and congruence closure cannot verify arithmetic.

## Architecture (same proof-carrying shape, a new verifier)

Recording, Solver-owned log, gate-side verification, LRAT over
skeleton ∪ verified lemmas — all identical to the EUF half. What changes
is the recordable-atom predicate and the verifier:

* **Atoms**: `Lt/Le/Gt/Ge` and `Eq` over Int/Real-sorted linear terms,
  decoded in the gate from the assertion DAG (each atom's linear
  constraint: Σ aᵢxᵢ ⋈ b with exact `Rational64`; `Eq` in the negated
  conjunction is an equality, `¬Eq` a pair of strict bounds — no, the
  negated conjunction *asserts* `Eq`; a positive `¬Eq` clause literal
  asserts a disequality, which for the LP check splits as a disjunction —
  see the completeness note below).
* **Verifier, phase 1 (LP / rational Farkas)**: the lemma's negated
  conjunction is a set of linear constraints over the lemma's own
  variables. Two implementation options, both verified against the tree:
  1. *Witness-carrying*: the simplex conflict already sits on the Farkas
     combination — `explain_conflict` (simplex/mod.rs:2466) walks
     reason IDs, but the violated tableau row
     (`tableau.get(&basic_var)` at that site) IS the dual combination.
     Plumb the row coefficients + each contributing bound's constraint
     out alongside the reason clause; the recorder attaches them; the
     gate does an exact rational Farkas check (Σ λᵢ·(aᵢ·x ⋈ bᵢ) with
     λᵢ ≥ 0 deriving `0 ⋈ c` with c contradictory). Cheapest per check,
     most plumbing (ArithSolver → TheoryManager → callback recorder
     needs a second channel or a wider `record_lemma` payload).
  2. *Gate-side re-derivation*: a small exact-rational simplex in the
     gate over the lemma's conjunction only (the CC-analogue: a
     self-contained decision procedure for the fragment, trusted by
     smallness and review, not by the solver). No solver plumbing at
     all; the recorder accepts arith atoms unconditionally and the gate
     decides. Slightly more gate code (a ~150-line bounded-variable
     simplex), zero theory-layer changes.
  Option 2 is the recommended first slice: it is exactly how the CC
  verifier relates to EUF — independent, complete for the rational
  fragment, fail-closed beyond it.
* **Completeness boundary (documented, fail-closed)**: rational
  infeasibility only. Integer-only infeasibility (parity/divisibility
  conflicts, e.g. `x = 2y+1 ∧ x = 2z`) is LP-feasible; such lemmas fail
  the verifier and the certification declines to `unknown` — never a
  wrong verdict. Covering them later means integer certificates
  (Chvátal–Gomory cuts with rational multipliers + integer rounding, each
  step exactly checkable; or branch trees) — a follow-up with the same
  gate shape.

## Soundness argument

Identical structure to the EUF gate: the gate trusts only its own
Tseitin skeleton and lemmas that pass the independent verifier. A
mis-explained arith conflict can only produce a lemma that fails the LP
check. Disequality handling: a clause literal `¬Eq(t,k)` makes the
negated conjunction assert `t ≠ k` — NOT an LP constraint; treat such
lemmas as unverifiable (skip → fail closed) in the first slice, which
keeps the verifier purely conjunctive-LP.

## Hazards pre-found

* `ParsedArithConstraint` decoding: the gate cannot use the solver's
  `var_to_parsed_arith` (that is solver state, not certificate state) —
  decode atoms from the assertion DAG terms directly; non-linear or
  non-decodable atoms poison (same discipline as EUF).
* Mixed EUF+LIA files: lemmas may mix Eq-over-uninterpreted atoms and
  arith atoms. The first slice records a lemma only when ALL its atoms
  are arith (EUF lemmas keep their own path); mixed lemmas poison →
  skeleton-only. A combined CC+LP verifier (Nelson–Oppen-style interface
  reasoning) is the eventual complete answer.
* QF_LIA's `distinct` over integers: the gate's structural Distinct
  encoding emits `¬Eq(aᵢ,aⱼ)` clauses whose Eq atoms are integer-sorted —
  consistent with arith-atom lemmas once those are recordable.

## Gates

* Unit: LP verifier accepts a genuinely infeasible conjunction (bound
  collision through an equality), rejects a feasible one, rejects
  parity-only infeasibility (documented boundary), handles strict
  bounds exactly.
* E2E: a bound-conflict QF_LIA unsat file (e.g. the `p20.smt2` shape)
  certifies; `certified_arith_eq_unsat_stays_unknown` — the `x=1 ∧ x=2`
  case — flips to `unsat` once LP verification lands (it is
  LP-infeasible!); a parity-only unsat stays `unknown`.
* Full battery, clippy/fmt/doc, parity; sample re-measure recorded as
  `lialemma-cert` cells.

## Estimated scope

Option 2: ~300 lines (gate LP ~150, atom decoding ~80, recorder
predicate ~30, tests). No changes to any search path.

## Addendum (2026-09-03): implemented and measured

Landed as `ba14fe7`, per the design (option 2 — gate-side re-derivation,
zero solver plumbing beyond the atom predicate). Two Fourier–Motzkin sign
bugs were caught by the units mid-landing — the upper residual needs
negation (`v ≤ U` from `E = c·v + R` with matching signs), and the
violated check is `E ≤ 0` iff `E > 0` — both pinned by regressions.

Measured: `x=1 ∧ x=2` and linear bound conflicts certify `unsat`
(previously `unknown`); the QF_LIA sample gains 2 unsat cells (6 → 8,
coverage 52 → 54/174). The modest sample gain reflects the real
bottleneck: search completeness (99 of 174 cells are unknown-at-cap in
*plain* mode). The unknown breakdown: 17 cells decline on
congruence-closure verification (Eq atoms routed to CC on QF_LIA files —
worth a look at why non-LP atoms appear), 4 on insufficient lemmas, the
rest are search-incomplete.

Next movers on this frontier, in order: (a) the 17 CC-decline cells'
atom shapes, (b) disequality literals (currently declined), (c) integer
certificates (CG cuts) for the parity boundary, (d) mixed EUF+LIA
lemmas (Nelson–Oppen interface verification).
