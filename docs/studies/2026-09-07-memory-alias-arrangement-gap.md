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
