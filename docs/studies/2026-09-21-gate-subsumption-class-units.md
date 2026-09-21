# Gate-based subsumption, the mutual-retirement bug, and the base-solver class-crossing false-sat it exposed (2026-09-21, item 3)

Item 3 of the handover chain (`2026-09-21-sat-next-three.md` →
`2026-09-21-sat-parser-landed-fold-refused.md`).  The session landed the
kissat port AND, on the way, found and fixed a **pre-existing default-
config false `sat`** in the equivalence fold — the gravest find of the
arc, caught only because the new differential generator was shaped like
the target family.

## What landed

1. **`gate_subsume.rs`** — the `forward_subsume_matching_clauses` port
   (kissat `congruence.c`): inside the closure, after the SCC map, before
   the fold's rewrite.  Canonical sets per live original (mapped through
   `sub`, level-0 value-filtered, sorted+deduped by code); candidates =
   matchable-containing originals, probed smallest-set-first through
   shortest occurrence lists; whole-clause retirement only.  Deliberately
   incomplete exactly like kissat (one list per victim).  Env-gated
   `NIXIE_GATE_SUBSUME=1`, default off; retirements ride `retire_clause`
   and count toward the fold-collapse ratio that arms
   `NIXIE_FOLD_BVE_SKIP`.
2. **The class-crossing-unit derivation in
   `substitute_equivalent_literals_round`** (the base-solver fix — see
   below).

## Bug 1 (the port itself): mutual retirement of equal-set clauses

The first draft kept retired victims in the subsumer pool: two clauses
with equal canonical sets retired **each other** (5 by 9, then 9 by the
now-deleted 5) — the constraint vanished entirely and the formula became
over-satisfiable.  Found by the 20K-instance differential fuzzer at
iter 1186 (invalid model), minimized to 26 clauses, root-caused by
direct instrumentation (victim/subsumer trace).  Fix: `sets.remove(&cid)`
on retirement — a deleted clause can never subsume (kissat's dense-mode
`assert (!d->garbage)` is the same guarantee).

**Layer checks done around the fix** (one fix can mask another):
scan-phase retirees (satisfied/tautology) never enter the pool; unit
constraints survive through the surviving subsumer copy; the probe's
work-budget break is incompleteness only; learned clauses are excluded
from both roles (misses opportunities, never unsound).

## Bug 2 (pre-existing, DEFAULT CONFIG): the class-crossing-unit false `sat`

After bug 1's fix the bv_ILA arms STILL answered `sat` on an UNSAT
instance.  The toy generator (extended with AND-gate twins — the bv_ILA
anatomy: equivalences that exist only through
`augment_big_with_gate_congruence`, no binary path) reproduced it at
iter 2986; minimized to **16 clauses** (`fold_class_unit_regression.rs`
`CE2_MIN`); kissat: UNSATISFIABLE; **plain default-config CLI: `sat`** —
not gated by any study knob.

Anatomy (all 1-indexed vars): unit `¬2`; `1 ≡ 18` (binaries); `2 ↔ 18∧13`
(complete AND-gate: `(¬18∨¬13∨2)`, `(¬2∨18)`, `(¬2∨13)`).  The three are
one entailed class `{1 ≡ 2 ≡ 18}` — itself SOUND (1≡18 + the gate give
1→2 and 2→1).  The bug: **the class contains the level-0-assigned member
2 (false) and the unassigned representative 1 — and the round never
derived `¬1`.**  Instead every connecting clause retired through the very
same class + trail values (`(¬2∨18)`/`(¬2∨13)` satisfied; `(1∨¬18)`/
`(¬1∨18)` tautologies; `(¬18∨¬13∨2)` a mapped tautology `(¬1∨¬13∨1)`),
so the search saw NO clause linking 1 and 2, branched `1 = true`
freely, answered `sat`, and the model reconstruction assigned `2 := 1 =
true` — violating the live unit `¬2` (the reported violated clause).

The fix (kissat's closure `propagate_units_and_equivalences` shape): after
the round's early-out, one pass over the non-identity `sub` map derives
level-0 class-crossing units — assigned member forces unassigned rep and
vice versa, opposite assigned values across one class is Unsat — riding
the round's existing `new_units` pipeline (assigned + propagated after
the watch/BIG rebuild).  `ce2_min` now: `unsat` on the default CLI;
the bv_ILA arms all honest.

## Post-fix measurements (bv_ILA, conflicts)

| arm | before the fix | after |
|---|---|---|
| default | 16,023 (unsat) | 16,023 (bit-identical) |
| `NIXIE_GATE_SUBSUME=1` | **sat (false!)** 4,312 | unsat 18,765 |
| fold stack | unsat 8,098 | unsat 8,098 |
| fold + gate subsume | **sat (false!)** 2,189 | unsat 8,821 |

The gate-subsumption port adds no conflict win on the motivating
instance (8,821 vs 8,098 — kissat's 44 % figure was against ITS closure
baseline; ours already collapses the same structure through the SSR +
fold pipeline).  The pass stays default-off machinery pending the
corpus-wide verdict (`env_ab.sh`, recorded in the landing).

## Traps

- **Differential fuzzer generators must mimic the target's inferred-
  equivalence structure** (AND-gate twins), not just explicit
  equivalence pairs — the base bug is unreachable through plain pairs
  (propagation covers them via live binaries; only augmented classes
  strand the unit).
- **A "no-op" pass can still expose base bugs by trajectory**: the
  16-clause false-sat needed none of the port's retirements — the env
  knob merely perturbed the search into the broken fold state.
- `rg -rn` replaces matches with the letter n (it is NOT grep -rn);
  three mangled greps this session before it stuck.
- The `--dimacs` flag must not reach kissat in shrink harnesses; and
  kissat verdicts print as `s UNSATISFIABLE` (case, prefix).

## Verification

nixie-sat 1095/1095 (incl. the new `gate_subsume_soundness` 20K
differential, the `fold_class_unit_regression` pair, and the 4 unit
tests); workspace suite, gate (trajectory shift expected and justified —
deliberate soundness fix), env_ab full-stack table, Z3 parity — in the
landing message.
