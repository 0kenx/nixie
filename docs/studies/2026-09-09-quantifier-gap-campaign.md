# Quantifier-completeness campaign vs Z3 (2026-09, consolidated)

Nine sessions, one goal: close the decisive-answer gap to z3 4.16.0 on
quantified corpora without a single wrong answer.  All landed on `main`;
every step carried the full verification battery (workspace tests, z3
parity 174/175, QF differential 0 disagreements) and a regression test
next to the code it protects.

## Headline numbers

| corpus (stratified, 20 s, z3 4.16.0) | before | after |
|---|---|---|
| 717-file submission screen — WRONG | **19** | **0** |
| 717-file submission screen — agree | 33 | 78 |
| 717-file submission screen — fabricated `sat` (gap_nixie) | 80 | 14 (all honest) |
| 567-file classic LIA/UFLIA/AUFLIA — agree | ~131 | 169 |
| classic — WRONG / declared mismatches | 1 / 10 | 0 / 0 |
| parity suite | 174/175, 0 wrong | unchanged throughout |

## The fixes, in causal order

1. **Negated-quantifier ownership** — `¬∀`/`¬∃` spine conjuncts were free
   Booleans with no engine; `Satisfied`/`NoQuantifiers` certified only
   registered quantifiers (funcprobs/U48 false `sat` class).  NNF + spine
   Skolemization/registration, plus `unowned_quantifier_seen` gating sat
   exits on full-assertion certification.
2. **Big-`IntConst` abstraction** — `2^64` literals nuked whole goals
   (every Verus encoding pins `uHi 64`).  Shared opaque tableau columns,
   exact for refutation, certified-or-unknown for models; signed
   distinctness rows at the constraint level.  UFBVDTNIA 0→39/40.
3. **Finite-exhaustion coverage** (CLEARSY) — `Satisfied` trusted a
   truncated universe over a 2270-value model; coverage now recorded where
   the candidate lists are built, from the untruncated model harvest.
4. **Guarded boundary instantiation** — for `q = ∀x⃗.φ` the clause
   `(!q ∨ φ[t⃗])` is valid in every model; boundary universals (and the
   derived universal of boundary existentials) instantiate under their own
   propositional guard (Ultimate +22).
5. **Linear witness solving** — isolate the bound variable of a
   single-Int-variable universal from its body's linear atoms; emit the
   exact concrete quotient and the symbolic `div` form.
6. **Comparison reflexivity folds** — `t ≤ t`/`t ≥ t` constructors;
   tautological quantifiers no longer burn the round budget.
7. **Integral dive** — free nonbasic integers rest at crash-basis
   defaults, making half-integral vertices where cuts are inapplicable and
   B&B diverges; the dive pins fractional vars to floor/ceil equalities.
8. **Nullary `sk!N` candidates + spine-rewrite collection** — the witness
   of an asserted `∃` is the refuting instance for its sibling `¬∃`.
9. **k7 parity closure** — free-variable sign splits (Z3
   `constrain_free_vars`) with split-scoped Gomory cuts.

## What remains (ranked, with repros)

1. **k9 class** (`docs/studies/2026-09-09-lia-parity-infeasibility.md`):
   four-plus free vars in a defining sum; the split leaves churn.  The
   fourth-session probe (remainder case enumeration) is
   necessary-but-insufficient — combine with the conditional
   divisibility lemma at the div-axiom site.  Blocks jain_2 + the
   compound Ultimate shapes.
2. **E-matching depth at scale** — Rodin/tptp/AUFLIRA (~100 z3-only on
   the classic sample): instantiation selection and throughput on
   2000+-axiom theories.  Profile first (where do the rounds go?).
3. **psyco sat-class** — boundary `∃` witness exhibition for `sat`.
4. **NL zero-factor fold** — `sk·f(x)` with `f` pinned 0 (funcprobs).
5. **Duplicate-instantiation audit** — dedup persists within a check
   (cleared only at `pop`/blind, by design); cross-check re-emission via
   search-state restore costs clause re-adds, not soundness.  No live
   starvation repro found; revisit if round exhaustion shows up in
   profiles.
