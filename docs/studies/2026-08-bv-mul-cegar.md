# bvmul CEGAR in the pure-BV dispatch (Priority 1 first slice) (2026-08-24)

## Basis

Niemetz, Preiner, Zohar — *Scalable Bit-Blasting with Abstractions*
(Bitwuzla).  Expensive operators are over-approximated, spurious models
are eliminated by sound lemma tiers, and full bit-blasting is the
terminal refinement.  First slice per the established-candidates doc:
quantifier-free `bvmul`, width ≥ 32, non-constant operands only.

## Baseline (the gap the slice targets)

168-file mul-heavy sample (Sydr/uclid/calypto/wienand/brummayerbiere2/
Goel/log-slicing/float; seed 42, 20 s, 8-way): **nixie 53 solved vs z3
101**; all 40 one-sided nixie TOs were width-32+ `bvmul` shapes (Sydr
width-64 predicates, `smulov*`).

## Implementation

- **Tier 1 — abstraction** (`BvSolver::abstract_mul`): the exact
  multiplier circuit is replaced by fresh result wires + the published
  identity lemmas (`a=0→m=0`, `b=0→m=0`, `a=1→m=b`, `b=1→m=a`), each a
  consequence of the exact definition.  Gate-folded (`Sig` layer), so a
  provably-zero operand emits the strong `m=0` units and a provably-
  nonzero one emits nothing.
- **Tier 2 — value lemma** (`refine_mul_value`): under a spurious
  candidate, `(a≠va ∨ b≠vb ∨ m = va·vb mod 2^w)`, one clause per result
  bit, BigUint-exact.
- **Tier 3 — terminal**: `bv_mul` wired into the already-abstracted
  result bits (`wire()` constrains existing wires, verified in source).
- **Loop** (`dispatch_pure_bv_solve`): check → exact BigUint product
  consistency per abstraction → refine spurious (2 value rounds, then
  terminal) → re-check; 50-round budget ends in terminal-blast-everything,
  so the loop always terminates with a fully exact instance.  Every
  clause ever added is a logical consequence of the exact formula ⇒
  `Unsat` transfers at every round (relaxation); `Sat` requires the
  consistency check AND the existing whole-assertion model validation.
- Scope: dispatch-only (`set_mul_abstraction_width` toggled around the
  blast); general CDCL(T) default is 0 = always exact, clause stream
  unchanged.  Preprocessing folds constant operands before the switch,
  so only genuinely symbolic wide muls abstract.  `NIXIE_BV_CEGAR=0`
  disables for A/B.

## A/B (release, sequential, 15 s cap, 168 mul-heavy files)

| | CEGAR | exact |
|---|---|---|
| solved | 54 | 55 |
| geomean (solved) | 0.263 s | 0.313 s |
| verdict disagreements | — | **0** |

- Time wins 14 / losses 9 (>10% delta); big deltas all wins:
  `calypto/problem_24` sat **13.4 s → 0.0 s** (value lemmas converge with
  no circuit), `predicate_2118` unsat 14.5 → 11.0, `query-1355` 1.6 s.
- One TO-cap flip loss (`predicate_2110`, exact unsat under 15 s, CEGAR
  TO): value rounds delayed the inevitable terminal blast.
- Inertness: files without wide non-constant muls are clause-stream
  identical (differential solved-set byte-identical at 160, 0
  disagreements; parity 167/0/1 identical).

## Known limitations (recorded, not hidden)

1. **~~Re-checks drop learned clauses~~ — ERRATUM (same day, measured)**:
   this diagnosis was wrong.  `check_body` already RETAINS both the trail
   and the learned clauses across checks (the incremental-resume lever;
   `forget_learned_since` runs only inside the defensive re-solve on a
   first-verdict `Unsat`).  Re-profiling the cited evidence:
   `smulov2bw032` abstracts 2 muls, takes 3 spurious rounds, then TOs on
   the *exact terminal solve itself* — the instance is bounded by the
   underlying exact solve, not by CEGAR overhead.  `predicate_2110`
   (2 muls, ZERO refinement rounds — the first check refutes the
   relaxation outright, soundly) measures 16.4 s vs 11.9 s in release:
   the relaxed refutation is simply a harder CDCL trajectory there, and
   the A/B "flip" was that 4.5 s delta crossing the 15 s cap.  No
   retention follow-up is warranted.
2. Escalation is per-term round-count; a global signal (many spurious at
   once ⇒ skip value tier) would cut the round tax on UNSAT instances —
   but the measured round counts are small (≤ 3), so this is low-value.
3. ~~`bvudiv`/`bvurem` abstraction is the next published slice~~ —
   **DONE, same session; shipped default-OFF (a measured negative)**:
   `abstract_udiv_urem` generalizes the skeleton with the SMT-LIB-exact
   zero-divisor lemmas (`bvudiv a 0 = 1…1`, `bvurem a 0 = a` — wired as
   tier-1, so the abstraction is already complete on that case), `b = 1`,
   `a = 0 ∧ b ≠ 0`, and `a = b ∧ b ≠ 0` identities, plus kind-dispatched
   value/terminal refinement (`BvAbstraction::exact_value`, separate
   `set_div_abstraction_width`).  Sound: 3 division regressions
   (zero-divisor exactness, satisfiable model exactness, the bounded
   Euclidean-identity refutation — the last one's shape is load-bearing:
   without bounding `q`, `q·b + r` wraps mod 2^64 and the identity has
   spurious solutions; verified against z3), 52-file wide-division A/B
   (`spear` + Goel + challenge, 20 s cap) with **0 verdict changes** at
   both the 32 and 64 thresholds.  Performance: geomean 1.079× (width 32)
   and 1.057× (width 64) vs exact — solved identical both times.  The
   value lemmas rarely converge on this corpus and the round tax is real,
   so the division half ships behind `NIXIE_BV_CEGAR_DIV=<width>`
   (default 0 = exact); the mul half keeps its measured win.  A
   division-dominated corpus that flips this verdict would justify
   revisiting the default.

## Soundness evidence

- 3 new regressions (`bv_cegar_regressions.rs`): bounded zero-divisor
  unsat (refinement transfers refutation), low-word-identity unsat
  (exactness enforced across two shared-operand muls), satisfiable model
  exactness (`get-value` returns the true products).
- Differential (z3, 270-file corpus): 0 disagreements, solved 160
  unchanged, on the final tree.
- Z3 parity: 168 files, 167 solved / 0 wrong / 1 unknown — identical.
- Full bar: 10 097 tests, clippy/fmt/doc.

## Verdict

LANDED, default on (32-bit threshold).  Go/no-go satisfied: terminal
blasting reduced on mul-heavy QF_BV (value-lemma convergence path exists
and fires), adjacent families byte-identical, aggregate geomean above
the ±5% band (0.263 vs 0.313) with zero verdict changes.  The honest
limitation is #1 above — the slice's real win awaits learned-clause
retention across refinement rounds.
