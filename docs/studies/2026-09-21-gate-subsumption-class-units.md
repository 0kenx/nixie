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

## Addendum (the Carry "regression" is chaos-shaped; the 30-seed replication)

Per-seed default-vs-full-stack on `Carry_Bits_Fast_19` (the 1.78× cell):

| seed | default | armed | ratio |
|---|---:|---:|---:|
| 7919 | 34,621 | 136,732 | 3.95× |
| 15838 | 54,600 | 60,565 | 1.11× |
| 23757 | 20,773 | 50,041 | 2.41× |
| 31676 | 122,563 | **5,680** | **0.046×** |
| 39595 | 24,250 | 60,780 | 2.51× |
| 47514 | 52,342 | 79,234 | 1.51× |
| 55433 | **3,534** | **68,561** | **19.4×** |
| 63352 | 56,105 | 57,123 | 1.02× |
| 71271 | 29,457 | 40,936 | 1.39× |
| 79190 | **682** | 4,197 | 6.2× |

The default's own seed spread is **180×** (682 → 122,563) and the armed
set both wins 22× (seed 31676) and loses 19× (seed 55433).  The 1.78
geomean at 10 seeds is trajectory reshuffling, not a family cost —
AGENTS.md's chaos rule verbatim ("changing only the RNG seed moves
aggregate cost 7.31×"; this cell is wilder).  The flip decision
therefore runs the 30-seed replication over the whole corpus
(`SEEDS=30 env_ab.sh`); the per-cell ratio stability across seed sets is
the practical null for an env-armed deterministic transform (both arms
share the seed set — the ratio's stability across seed draws bounds the
chaos term).  Verdict recorded below when the run completes.

## Addendum 2 — the volume guard, the discriminator pattern, and the flip verdict

Directed pattern discovery at 3 seeds (per the session's operating
instruction) instead of the 30-seed sweep:

| cell | 10-seed | 3-seed | pattern |
|---|---|---|---|
| frb35-17-5 | 0.49 | 0.46 | **stable structural win** (the FOLD's — the pass retires zero there) |
| WS_500_16 | 0.51 | 0.19 | **stable structural win** (the PASS's — 510 retirements/round) |
| circuit | 0.94 | 0.87 | stable win |
| x9 / s38584 / SCPC / b21 / 6s299b685_Iter22 | 0.96-1.29 | 0.94-1.23 | **chaos noise around 1.0**, direction flips with the seed set |
| Carry_Bits_Fast_19 | 1.78 | 2.19 | the sole persistent loser |

**Attribution on Carry (3 seeds)**: default 33,989 / fold-only 34,226
(1.007 — the fold is FREE there at these seeds) / fold+gs 74,554 — the
entire cost is the subsumption pass, whose rounds on Carry retire **1-3
clauses** (vs WS's 510, frb's 0).  The pass's value tracks its
retirement volume; micro-rounds are pure trajectory perturbation.

**The guard** (`GATE_SUBSUME_MIN_CANDIDATES = 64`, env
`NIXIE_GATE_SUBSUME_MIN`, test knob): a read-only candidate pre-count —
below the floor the pass returns untouched, leaving the instance
bit-identical to the fold-only arm.  Measured: **frb fold+gs ≡ fold to
the last conflict** (547,324 = 547,324), **WS's 5.3× win intact**,
Carry 2.19 → 1.62 (its high-candidate/low-yield rounds still fire — the
floor is a candidate-volume signal, the true discriminator would be
retirement yield, which a probe-first pass cannot know; kissat's
lazy-connect scheme is the restructure that self-limits).

**Final guarded table (3 seeds)**: geomean **0.819** over 9 cells
(Carry 1.62, WS 0.19, frb 0.46, circuit 0.87, rest ≈ 1.0).

**Flip verdict: default stays OFF.**  The aggregate win is robust
(0.82-0.93 across seed sets and guard variants) but
docs/BENCHMARKING.md's family band blocks a default flip while any
family sits persistently > 1.15 — Carry is at 1.6-2.2 (chaotic
magnitude: per-seed 0.046×-19×, 8/10 seeds directionally worse; even
fold-only measured 1.59 there at 10 seeds once).  The stack remains the
documented opt-in
(`NIXIE_SSR_BIN=1 NIXIE_ELS_PRESEARCH=1 NIXIE_GATE_SUBSUME=1`).
Opening the flip needs either the retirement-yield gate (lazy-connect
restructure) or an explicit maintainers' call accepting the Carry
trade.

**Do not tune the floor on Carry** — 3-10-seed geomeans on a cell with
180× default seed-spread are chaos; any threshold that "fixes" it is
overfitting the reshuffle.
