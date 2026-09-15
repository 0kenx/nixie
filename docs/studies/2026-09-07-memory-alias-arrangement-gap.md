# Study: memory-alias large timeouts — the integer-arrangement search (negative result, root cause isolated)

**Date:** 2026-09-07
**Found by:** the obligation-grammar fuzzer (`bench/obligation`, finding 5, `memory` half)
**Status:** two eager-reduction attempts measured negative, root cause isolated and
pinned here with do-not-retry notes; the scoped-but-unattempted fix is
arithmetic-side distinct-value assignment at candidate-build time.

## The finding

`memory-alias-sat-*-large` (two 50-deep store chains over all-distinct
symbolic `Int` indices with one planted alias `idx9 = idx16` and distinct
values, obligation `(distinct (select a1 idx9) (select a2 idx9))`):

| solver | time |
|---|---|
| z3 | `sat`, 25 ms |
| nixie | `sat`, 20.2 s (s0) / timeout (s1) |
| nixie, same instance with concrete index constants | `sat`, 0.03 s |

`memory-incremental-*-large` (same chains under push/pop histories)
timeouts likewise.  The `reorder-*` (unsat) variants are fast (<1 s).

## Root cause decomposition (each step measured)

1. **It is not array reasoning.**  Replacing the symbolic indices with
   concrete constants — identical chains, identical alias, identical
   obligation — nixie answers `sat` in **0.03 s** (z3 unchanged, 25 ms).
   With concrete indices the read-over-write `ite` conditions fold at
   rewrite time and the selects collapse to plain values; the entire 20 s
   is the search discovering the index *arrangement*.

2. **The search signature is enumerative arrangement search.**  Decision
   trace (`NIXIE_TRACE_DECISIONS`): **1.98 M decisions, 5.9 k conflicts**
   (0.003 per decision), flat decision histogram (~330 decisions per var
   across ~6 000 vars), conflict split `825 bool / 24 theory-prop /
   5004 theory-assign / 35 final-check`, theory-assign conflicts at
   average level 1369, decision levels reaching 8678.  The LP relaxation
   co-locates all 50 indices (nothing in the tableau knows they are
   distinct — `distinct` went to the injective-map EUF encoding); each
   candidate model is refuted by EUF congruence against the distinct
   marks (`theory-assign`, deep), the colocated-split trichotomy clauses
   commit one pair-arrangement at a time, and the loop enumerates ~2^k
   arrangements.

## Attempt 1 — eager select-over-store chain reduction (measured negative: no effect)

Level-0 `IndexKnowledge` oracle (union-find over asserted equalities,
distinct-group membership, exact constant pins) feeding a
`reduce_selects_over_store_chains` pre-pass: for each `select(chain, j)`
walk stores outermost→innermost, resolve `i_w = j` through the oracle,
emit the ground lemma `select = v_last_hit`.  Mechanically correct —
both selects reduced to their last-write values — but **the trajectory
did not move** (20.2 s → 20.0 s): the value units constrain nothing the
search was bottlenecked on; the read-over-write `ite` atoms remain free
Booleans that CDCL still enumerates.

## Attempt 2 — plus level-0 index-fact units (measured negative: 4.5x WORSE)

Extended the pass to assert each oracle-resolved `(= i_w j)` /
`¬(= i_w j)` as a level-0 unit (the lazily minted axiom atoms are
hash-consed to the same TermIds, so they would be "born decided").
Result: **20 s → 92 s** (decisions 1.98 M → 4.68 M, conflicts
unchanged).  Why: a unit-false numeric equality atom's trichotomy
encoding leaves `i < j ∨ j < i` — an open two-way disjunction — so each
fact ADDS a free ordering atom; the arrangement search space grew, not
shrank.  (The colocated-split mechanism reaches the same clauses lazily
but only for pairs the final check actually finds co-located.)

**Do not retry** eager index-fact units, and do not assert value lemmas
alone, on this class.  Both directions are measured above.

## What would actually close it (scoped, not attempted)

The burden is giving 50 pairwise-distinct unbounded Ints an injective
value assignment.  Options, in increasing ambition:

1. **Injective candidate repair (model construction).**  Teach the
   arithmetic side of candidate building to respect e-graph distinct
   classes: when the final assignment co-locates two terms the e-graph
   holds distinct, greedily re-assign a fresh value to one and re-verify
   (the existing whole-assertion model certification gates every `Sat`,
   so a bad repair is rejected, never trusted).  This is z3-adjacent
   (its arith model finder assigns distinct values on demand) and stays
   inside the candidate loop.
2. **Arith-internal distinct handling** (z3 `theory_arith`'s disequality
   bookkeeping + bound propagation for distinct groups) — a larger
   port; see `../temp/z3/src/smt/theory_arith*`.
3. Accept as scaling boundary (current state; honest timeouts).

Any such change is a **heuristic** change (steers the candidate search)
and falls under the matched-null discipline of `docs/BENCHMARKING.md`
(≥10 seeds, treatment/matched-null, replay at fresh seed).

## Reproducers

- `bench/obligation`: `obligation-gen --seeds 2 --size large --family
  memory --out …` — `memory-alias-sat-s0-large.smt2` (20 s sat, the
  sharpest measurable repro), `memory-alias-sat-s1-large`,
  `memory-incremental-*` (timeouts).
- Concrete-index control (this study's step 1): the same file with
  `idx_i := 10+i` (and `idx16 := 19`, alias assertion dropped) —
  0.03 s.  Generator-side knob idea: a `--concrete-indices` variant
  would keep this control reproducible.

## Attempt 3 — injective-candidate repair (implemented, measured, NOT landed)

The scoped design above was built exactly as specified:
`ArithSolver::probe_term_pins` (a scoped LP probe at term granularity, the
`try_eq_incumbent` shape: push, pin, one lean feasibility pass + integrality
scan, `lia_model` snapshot on accept, pop — nothing survives the pop except
the snapshot, so no pin ever constrains a later search) plus
`Solver::repair_injective_distinct_collisions` (cluster the colliding
members of an asserted-true `distinct` by model value, re-seat every
cluster at fresh pairwise-distinct integers disjoint from the spec's
values, probe, and only on full acceptance rebuild the model).  Sound by
construction: a rejected probe leaves the candidate untouched; an accepted
one still faces the whole-assertion evaluation and the dishonesty
downstream gate.  A matched null (`NIXIE_REPAIR_NULL`) did the identical
work with collision-preserving values.

### Measurement 1 — ungated, seeds 0–9 (60 instances: alias-sat + incremental, small/medium/large)

| arm | wall (both-decided 47) | per-instance ratio |
|---|---|---|
| treatment | 438 s | median 1.01, min 0.49, max 1.43 |
| null | 454 s | |

Aggregate T/N = **0.97** — the large-instance wins (0.49–0.66 on the four
previously-stuck larges) were paid back as probe overhead on small/medium,
where candidates collide on tiny clusters the chain-shaped splits already
separate in one round.

### Measurement 2 — gated to clusters ≥ 8, FRESH seeds 10–19 (added `--seed-offset` to `obligation-gen` for exactly this)

| size | n | T/N | median ratio | max ratio |
|---|---|---|---|---|
| small | 20 | 1.00 | 1.05 | 1.28 |
| medium | 20 | 0.96 | 0.99 | 1.29 |
| large | 20 | 0.91 | 0.90 | 1.42 |
| all | 60 | **0.93** | 1.00 | 1.42 |

Zero verdict mismatches in both protocols.  Directionally right on the
large tail, but a 7–10 % aggregate effect needs an order of magnitude more
runs to certify against the null (`docs/BENCHMARKING.md` power table) —
**the gated repair cannot be certified at this sample size and was not
landed.**  Code reverted; this section is the artifact, and
`probe_term_pins`'s pattern (scoped term-granularity probe) is worth
resurrecting if a certified consumer appears.

### Interaction with b9c750d (chain-shaped separation)

Landed concurrently, `b9c750d` ("chain-shaped separation — O(n)
convergence for free-variable distinct") fixes the ARRANGEMENT side from
within the split machinery: k−1 chained trichotomy clauses instead of
clique pairs.  It converted the memory family's timeouts on its own
(null-arm ≈ chain-only ≈ 20 s on the larges) but does not touch the
remaining cost (below), which is why the larges still sit at 14–22 s.

## The actual remaining cost: the array-axiom saturation cascade

Instrumented rounds on `memory-alias-sat-s0-large` (with the repair):
**67 array refinement rounds**, the first asserting 103 read-over-write
instances, subsequent rounds ~200 new instances each, decreasing by ~4
per round — each round is a full `rebase_theory_state` + re-solve over a
formula that keeps growing.  The driver is the saturation design itself:
`instantiate_array_axioms` re-walks the assertions *plus every axiom
instance asserted so far*, so each round's fresh lemmas (base-reads the
else-clauses mint, congruence pairs over the growing array-term
population) seed the next round.  ~13 of the ~15 s is this loop; the
arrangement search it was mistaken for is gone.  Closing it means bounding
the cascade — eager flat whole-chain read-over-write for observed reads
behind *define-fun* aliases (the `aliased_store_map` path exists but these
instances reach the drip-fed family), or de-duplicating the
congruence-pair enumeration — a scoped next rung, in
`nixie-solver/src/solver/array_axioms.rs`.

## Verdict table (memory-alias-sat-s0-large, end to end)

| configuration | time |
|---|---|
| baseline (b63a9c0) | 20.4 s sat (s1: timeout) |
| + chain-shaped separation (b9c750d) | ≈ 20–22 s sat, all seeds decided |
| + ungated repair | 15.7 s (T/N 0.63 vs null on the larges) |
| + gated repair (fresh seeds) | 0.93 aggregate T/N — not certifiable, not landed |
| z3 | 25 ms |
