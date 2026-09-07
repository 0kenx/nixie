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

## Attempt 4 — witness-read routing into the model-filtered path (measured nil vs main, reverted)

Deeper instrumentation of the cascade (`NIXIE_DBG_ARRCAS`, per-family
candidate counts per refinement round on `memory-alias-sat-s0-large`):

* the select population grows +8 per round (2 extensionality witnesses
  × 2 reads + base reads minted by else-clauses);
* each witness read over a store chain re-flattens the whole chain the
  next round: ~+100 `row` candidates per witness pair, ~200 asserted
  instances per round, 60+ rounds, ~5 500 instances total;
* `ext` candidates reach ~120/round (mostly deduped no-ops: the two
  INPUT select-congruence pairs × the grown read-index population).

**The fix tried**: a read whose index is an extensionality witness (a
fresh variable no input constraint mentions) is a *synthetic* read — its
flat-chain implications `(w = k_i) ⇒ select = v_i` are vacuously model-true
until the model puts `w` on a store index.  Such reads were routed into
the model-filtered candidate list (the `upward` family's contract: assert
an instance the round the candidate model actually violates it).  Sound
by the same saturation argument as upward; rounds got cheaper
(to_add → 0 earlier per round) but the population still grew:

* the else-clause `select(chain,k) = select(base,k) ∨ ⋁(k = k_i)` is
  asserted anyway — its atoms are *unassigned* in the model, the filter
  ("skip iff the model proves the instance true") does not skip it, and
  each one mints another base read (+1 select per witness per round);
* net wall vs the same-commit main: 15.8→15.8 / 17.7→17.4 / 15.0→13.6 /
  timeout→timeout — **nil overall**, reverted.

## The actual structural fix (scoped, needs design against Z3)

The cascade is the flat-encoding artifact meeting lazy instantiation:
per synthetic read, our encoding must either assert a 51-wide else clause
that the model cannot yet satisfy or leave the read's theory content
absent (which the saturation gate correctly refuses).  Z3's
`theory_array_full` has neither problem because it instantiates
`select(store(a,i,v), j)` **per store level, model-based**: the axiom for
level `i` is asserted only when the model's `j` reaches that level's
neighbourhood, and there is no else clause — the base read is just the
next level's axiom.  The nixie-native equivalent, for witness-borne reads
only:

1. per-level lazy RoW: assert level `i`'s `(k = i_w ⇒ …)` / `(k ≠ i_w ⇒ …)`
   pair only when the model's `k` value makes that level relevant (the
   model filter above, extended to the negative side);
2. a refutation-based filter contract for synthetic reads: assert only
   what the model *refutes*, and let saturation be decided by the
   honesty gates rather than by open atoms — this is the
   correctness-sensitive half (an accepted model must still interpret
   the witness reads through the array semantics, which the
   whole-assertion evaluation checks);
3. or, cheapest of all: cap the witness population per pair per check
   (one witness index per pair is semantically sufficient — re-minting
   per round is pure waste; the deterministic `extensionality_witness`
   already keys by pair, so the growth comes from the *pair* population,
   which is the separation universe — see below).

The separation universe was also probed: restricting the model-false
cause of `array_pair_separation` to atoms assigned above the root level
(one-line experiment) measured MIXED (one instance 40 s → 24 s, the other
three unchanged-to-slightly-worse) — and on reflection the gate is
inverted from its rationale: a level-0 false atom is *unit-propagated*
(entailed — a genuinely demanded separation), while a level>0 false can
be a mere decision.  Reverted with the rest; the pair population is not
the cascade's main engine — the ~5 500-instance closure itself is.

## The structural fix (IMPLEMENTED 2026-09-07, later still: all three points)

`nixie-solver/src/solver/array_axioms.rs` now instantiates synthetic reads
model-based, z3-`theory_array_full`-shaped.  The composition:

1. **Synthetic-read routing (points 1+2).**  A read whose select term no
   USER assertion mentions (`ArrayStructure::input_selects`, recorded by
   the collection walk's `from_input` flag) or whose index is an
   extensionality witness (structural: the `!nixie!ext!` name prefix —
   attempt 4's registry was rebuilt per round and only saw FRESH mints,
   the bug that made it measure nil) routes its whole read-over-write
   batch into the model-filtered assertion path (the `upward` family's
   contract: skip iff the candidate model PROVES the instance true;
   undetermined asserts).  Input reads keep the eager flat batch — the
   drip-feed negative lives on exactly those.
2. **Miss-guarded else for synthetic reads.**  The disjunctive else
   (`sel = select(base, i) ∨ ⋁(i = k_w)`) is undetermined until the read
   settles, asserts every round, and the base read it mints re-seeds the
   next chain level — one level per refinement round, the O(depth) peel.
   Synthetic reads instead get `(∧_w i ≠ k_w) ⇒ sel =
   select(ultimate_base, i)`: determined by the model's index values
   (skipped as true the moment `i` lands on or off any write), asserted
   at most once ever (dedup), and the single base read it can mint is
   over the ULTIMATE base — it terminates instead of peeling.
3. **Witness budget (point 3).**  At most `MAX_ARRAY_WITNESS_PAIRS = 256`
   witness pairs per `check` (one index per pair was already guaranteed
   by the deterministic mint).  A refused mint sets
   `array_witness_budget_exhausted`, which forces
   `array_axioms_saturated = false` — the Context honesty gate answers
   `Unknown`, never a dishonest `Sat` whose array disequality lost its
   witness.
4. **Entailed-only `AtomFalse` separation.**  A pair whose equality atom
   the model falsifies counts as a demanded separation only when the
   falsity is assigned at the ROOT level (unit propagation — durable);
   a branch-committed falsity can be retracted by the next backtrack
   while this module's clauses persist at the root, so reading every
   commit as demand minted witnesses the search kept flipping.

**Falsified in passing (do not retry):** a broad skip of e-graph-PROVEN
disequal pairs — reading Z3's `assert_extensionality` → `already_diseq`
as "skip proven-apart pairs" — measured spectacular (all four larges to
1.3–2.7 s) but broke `array_incompleteness1_needs_interface_witness`:
Z3's `already_diseq` checks whether a pair of SELECT terms over the two
classes is ALREADY disequal (a concrete differing read exists), NOT
blanket e-graph apartness; congruence-derived array disequalities (a UF
application `g(a) ≠ g(b)`) still need their witness.  The correct port
needs e-graph parent scans and was not taken; levers 1–4 above close the
family without it.

### Measured (release, `memory` family)

| instance (large) | before | after |
|---|---|---|
| `memory-alias-sat-s0` | 15.8 s sat | ~1.3–2.9 s sat |
| `memory-alias-sat-s1` | 17.7 s sat | ~1.9–2.1 s sat |
| `memory-incremental-s0` | 15.0 s sat | ~1.5–3.1 s sat |
| `memory-incremental-s1` | timeout (40 s) | ~2.7–4.8 s sat |
| fuzzer `--seeds 2 --size medium` (all families) | 56/58 | **58/58** |
| fuzzer `--seeds 2 --size large`, memory family | 2/8 | **8/8** |

(Wall clock under this session's parallel-agent load varied ×5; the
conflict counts — ~4.5–5.5 k on the larges, unchanged by the else-form
A/B — confirm the residual cost is the integer-arrangement search, which
`b9c750d`'s chain-shaped separation bounds and the fuzzer's 10 s cap now
accommodates.)  Gates: nextest 10 603/10 603 (including the
storecomm/swap/storeinv/read8-shaped regressions and the interface-
witness test), clippy/fmt/doc `-D warnings` clean, z3 parity 170 entries
/ 0 mismatches with no verdict changes, 40/40 QF_AUFLIA and 24/24
storecomm/swap industrial spot checks identical, fuzzer sweeps zero
FAIL/CRASH/GENFAIL.  New tests: the 12-deep alias shape both polarities,
and the witness-read-lands-on-a-write decision (sat + unsat sides, z3
agreement).

Remaining honest timeouts: `parity`-large CNF/BV/incremental graphs (the
SAT-side in-search xor rung), and the arrangement residue above.

## Attempt 3, third measurement — on the clean tree, with a deterministic metric (closed)

After the saturation cascade was fixed (`0d51a30`), the repair was
rebuilt from this record and re-measured with **conflicts as the primary
metric** (deterministic, load-independent — the session's wall-clock was
unusable at machine load ~60): 60 instances (alias-sat + incremental,
seeds 0–9, all sizes), treatment vs matched null, same protocol.

| size | n | conflicts T/N |
|---|---|---|
| small | 20 | 0.998 |
| medium | 20 | 1.048 |
| large | 19 | 1.018 |
| **all** | 60 | **1.022** |

Zero verdict mismatches.  **Neutral-to-slightly-negative — the attempt is
closed with a mechanistic account:** the ~4.5–5.5 k conflicts on this
family are spent *on the path to the first candidate* (the arrangement
search), before any model exists to repair; a post-hoc repair can only
shorten the collision-rejection tail after a candidate arrives, and the
chain-shaped separation plus the synthetic-read fixes already minimized
exactly that tail.  The earlier 0.91–0.93 wall readings were the repair
interacting with the (then-dominant) array-round cost, which no longer
exists.  No further measurement of post-hoc model repair on this family
is warranted; the remaining gap to z3's 25 ms is closable only by
separation that happens *during* the search — the in-search rung below.

## The remaining gap to z3's 25 ms (decomposed)

1. **Arrangement conflicts (~4.5–5.5 k)**: CDCL learns the pairwise
   arrangement one trichotomy clause at a time; z3's `theory_arith`
   final check separates e-graph-apart variables *inside the simplex
   model*, paying ~zero conflicts.  In-search separation (propagation-
   time or final-check tableau repair) is the only lever that touches
   this term.
2. **Round-based theory work**: each array refinement round backtracks
   the SAT core to root, rebases every theory solver, and re-solves from
   zero; z3 asserts its axioms on the live trail.  A handful of rounds ×
   a full re-solve is most of the residual wall time.  Lemma assertion
   without root-backtrack is the architectural rung.
