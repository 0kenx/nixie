# BV constant-flow results & the gate-layer AIG screen — what z3's `aig` tactic actually does on this corpus

**Date:** 2026-09-11. **Task:** handover option 1
(`docs/handovers/2026-09-10-qf-bv-tier-a-landed.md`) — "AIG/pre-blast
simplification in the unified path": check whether an AIG simplification
pass exists but is unwired between blasting and CNF emission in the unified
path, and wire it if so.

**Verdict (three findings, two landed):**

1. **There is no AIG pass to wire.** `nixie-theories/src/bv/aig.rs`,
   `aig_builder.rs`, and `bitblast_advanced.rs` are standalone, test-only
   modules; nothing in the unified or lazy path constructs them.  Wiring
   them in is not "cheap" — the real work is building the layer they
   presuppose.
2. **Gate-level structural hashing has nothing to hash on this corpus**
   (measured, then reverted): term-level hash-consing already dedups every
   gate the memo would have caught — 0 memo hits in ~20–60k gate requests
   per file across `maxandminor016`, `bitrev1024`, and the mul/shift
   families.
3. **The real gap is constants re-opacifying at operation boundaries.**
   Landed: (a) the op encoders (`bv_sub`, `bv_neg`, the barrel shifters)
   rewritten to compose over signals with no temp variables — measured
   neutral-to-positive, strictly fewer vars/clauses on constant operands;
   (b) a constant-flow canonicalization layer that installs reserved
   constant *variables* as operation-result bits — sound (zero verdict
   flips over the 509-file A/B) and a deterministic 1.3–2× win on the
   `bitrev` family, but −1 cell on the campaign aggregate, so it ships
   **default-off** behind `NIXIE_BV_CONST_FLOW=1`.

## What z3 actually does on maxandminor016 — corrected 2026-09-11 (evening)

> **Correction.**  This section first claimed `bit-blast` *alone* closes
> the goal, based on `(apply (then bit-blast …))` printing nothing.  That
> inference was an artifact: the corpus file ends with `(check-sat)
`(exit)`,
> and the `sed` surgery used for the probes removed only `(check-sat)`, so
> z3 executed `(exit)` *before* the appended probe — every "0 bytes =
> closed" row was z3 terminating, not the tactic deciding.  A closed goal
> prints `(goal false)` (verified on trivial probes).  The corrected
> stage-by-stage table:
>
> | pipeline (`check-sat-using`, 60 s cap) | outcome |
> |---|---|
> | `then bit-blast sat` | **timeout** |
> | `then bit-blast simplify solve-eqs sat` | timeout |
> | `then bit-blast simplify solve-eqs aig sat` | timeout |
> | `then simplify bit-blast sat` | **unsat, 206 ms** |
> | full default stage order + `sat` | unsat, 32 ms |
>
> So the blaster alone does **not** close the file — the **term-level
> `simplify` before blasting** is the entire lever (z3: 5561 → 3191 ASTs),
> and everything downstream is decided on the simplified goal.  The
> "constants stay constants through the DAG" account of the blaster layer
> below remains true and is what the landed emitter rewrite ports; it is
> just not the whole story for `maxandminor`.

The handover's premise ("z3's trace shows its aig tactic deciding the file
after blasting") is true but the attribution is wrong.  `z3 -v:10` shows
`simplifier → propagate-values → solve-eqs → elim-uncnstr → reduce-bv-size
→ simplifier → max-bv-sharing → ackermannize_bv → bit-blast → simplifier →
solve-eqs → aig → unsat` at 0.05 s total; the `(aig :num-exprs 1)` line is
the closed goal, and bisecting the stage prefixes pins the win on the
**first `simplify`** (see the corrected table above).

Nixie's `Sig` gate layer folds constants — but each *operation result*
was written into pre-allocated fresh variables, and `wire` re-opacified
each folded constant into a pinned variable the next gate could not see
through.  The chain died at every operation boundary.

## What was measured

### Gate structural hashing (reverted)

Implemented a `(kind, canonical operands) → var` memo over the six gate
constructors (`Not`/`And`/`Or`/`Xor`/`Mux`/`AndNotA`), journaled per
embedded scope for pop-retraction, cleared on unified-generation
boundaries — Z3 `aig.cpp`'s `aig_table` in miniature.  Measured hit rate:
**0.0 %** on every family tried (trace counters, `NIXIE_BV_GATE_TRACE`).
Term-level hash-consing (plus `canonical_pair` commutative normalization
in the term builder) already shares everything structural.  Reverted
without landing; do not retry as a standalone win.

### Constant-flow results (landed, default-off)

`finish_result` + `const_pinned`: when an operation's encoding wires a
result bit to a constant, the stored bit becomes the reserved
`const_true`/`const_false` variable instead of a fresh pinned one, so
downstream gates fold.  Active only in unified generations (base-scope,
never-popped clauses make "permanently constant" true); the lazy path is
byte-identical to before.

Matched-null A/B over the 509-file stratified sample (same binary
`md5 16964ebd…` lineage, `NIXIE_BV_CONST_FLOW` 0 vs 1, 25 s cap, 4 pinned
cores, load 5–13):

| arm | solved of 509 |
|---|---|
| null (off) | 285 |
| treat (on) | 284 |

Zero verdict flips (the soundness bar); 3 differing cells, all
sat/unsat↔unknown boundary moves.  Serial per-file re-verification
(pinned core, repeated):

| file | null | treat | class |
|---|---|---|---|
| `brummayerbiere/bitrev1024` | 15–21 s | 7–10 s | deterministic 2× win |
| `bitrev0256/0512/2048/4096` | — | 1.3–2× faster each | deterministic family win |
| `brummayerbiere3/maxandminor016` | 28 s | 43 s | deterministic 1.5× loss |
| `uclid/std_bv_formula` | 19–22 s | 32–33 s | deterministic 1.6× loss (crosses the 25 s cap) |
| `bruttomesso/lfsr_004_015_112` | 20.5 s | 20.5 s | load artifact |

The shape split is clean: const-mask-dominated encodings (the `bitrev`
`x ^ (x << const)` chains) shrink structurally and speed up 1.3–2×;
symbolic-bound-propagation files (`maxandminor`, `std_bv_formula`) only
get their variable allocation order reshuffled, and CDCL trajectory luck
goes the other way.  Aggregate −1 cell ⇒ ships off; the family win and
the z3-parity design (constants stay constants) are why the layer stays
in the tree behind the flag.

### The emitter rewrite (landed, default-on, no flag)

`bv_sub` and `bv_neg` now compute one ripple-carry pass over signals
(`a + ~b + 1` with carry-in true) — the old versions built temp variable
vectors (`~b` bits, `-b = ~b+1` bits) whose pinned constants died at the
temp boundary.  The barrel shifters (`shifts.rs`) build their mux stages
over signals, so a constant shift-amount bit selects the branch at build
time and constant value bits stay constants through every stage (the old
per-stage fresh variables re-opacified each folded mux).  `bv_shl_const`
pins through `wire` so its constants are recordable.

Measured: byte-identical solve time on `maxandminor016` vs the previous
binary under matched serial conditions (28.1–28.5 s both); corpus null
arm 285 ≥ the banked 283; zero verdict flips in the A/B (both arms carry
the rewrite).  Regression tests pin the wide-`bvsub` semantics
(`bvsub_wide_matches_exact_semantics`), over-shift forcing
(`lshr_const64_forces_zero_high_bits`), and the new const-chain behavior
(`unified_const_results_flow_as_reserved_constants`,
`unified_const_chain_preserves_semantics`,
`unified_const_shift_collapses_to_constants`,
`embedded_const_results_stay_pinned_variables`).

## Side finding: the rewrite unlocked RWS/Example_7 — and validated it

The emitter rewrite makes `RWS/Example_7.txt.smt2` solvable (~43 s; the
previous binary needs > 390 s; z3 4.16.0 times out at 60 s).  Its `sat`
verdict and full model were validated externally: nixie's model (24
`define-fun`s) pinned back into the original formula is accepted `sat` by
z3.  This is the differential-validation recipe for any future `sat` on
files z3 cannot decide: dump the model through a `Context::execute_script`
driver, pin it, cross-check.

The debug model-validity net fires spuriously on this file, in both arms.
Root-cause narrowed but not closed: the adopted main-core snapshot is
complete-with-reconstruction (41 k of 154 k vars are ELS/BVE-eliminated
and reconstructed by `save_model`), every bit the net reads is *defined*,
yet raw gate-variable reads contradict definitional clauses that a true
model of the final clause set cannot violate — pointing at clauses
missing from, or redirected away from, the core the snapshot came from
for late-minted round-boundary circuits.  Two net hardenings landed:
undetermined bits (vars past the snapshot) now suppress the comparison
instead of reading as `false`, and the residual false-positive mode is
recorded here.  The net is debug-only; user-facing models ride frozen
(theory-mapped) variables, which ELS/BVE never fold.

## What NOT to retry

- Gate-level structural hashing as a standalone win — 0 % hit rate on
  this corpus; the sharing already exists one level up.
- "Wiring `aig.rs` into the unified path" — it is a self-contained toy
  (u64-only constants, default width 32, no BV-op encoders); the unified
  path's own `Sig` layer is strictly closer to Z3's design.
- Treating z3's `simplifier → solve-eqs → aig` trace lines as the win —
  on this corpus the file is already closed at `bit-blast`; post-blast
  tactic work is a red herring for `maxandminor`.

## Where the next lever is (if this family is picked up again)

The `maxandminor` collapse needs constants to flow through the **`ite`
selector layer**: the recurring shape `(= #b1 (bvnot (ite (= (bvand …) 0)
#b1 #b0)))` makes selector-equalities that z3 substitutes symbolically
(its blaster's muxes fold when the *condition* folds).  Our selectors are
atom variables pinned by units — the SAT search must *propagate* what z3
*rewrites*.  Closing that gap means boolean-level value-substitution at
the Tseitin layer (a real AIG IR between term blast and clause emission),
which is the principled version of this whole exercise and a bigger build
than a wiring job.  The measured ELS data point: the main core's
equivalence substitution already folds 45 k literals on `maxandminor016`
(first round) without collapsing the file — clause-level equivalence
reasoning is not the bottleneck; substitution *into selector positions*
is.

## Follow-up screen (same evening): De Morgan canonicalization — rejected

With the corrected attribution (the term `simplify` is the lever), the most
plausible portable rule was identified in Z3's source:
`bv_rewriter::mk_bv_and` **unconditionally eliminates AND** —
`bv_and(args) → bv_not(bv_or(bv_not(args)))` — putting every bitwise chain
in one OR+NOT normal form so De Morgan-equivalent shapes hash-cons to the
same term (verified on probes: `bvand x y` and `bvor (bvnot x) (bvnot y)`
both normalize to `~(~x | ~y)` under z3 `simplify`).

Implemented behind `NIXIE_BV_DEMORGAN=1` in `bv_preprocess`
(AND-elimination at the `BvAnd` arm, `mk_not_norm` with Z3's
concat/ite-const-branch NOT-pushdowns, `X | ~X = all-ones` complement
folding in the OR flattener, all flag-gated so the off-arm is the
historical term stream) and measured per family (same binary, flag on/off,
pinned core, load ~25 — the box was busy, so absolute times are inflated
but the arm delta is decisive):

| file | off | on | verdict |
|---|---|---|---|
| `maxandminor016` (the target) | 43.4 s | 43.4 s | **no effect** |
| `maxandminor008` | 0.52 s | 0.57 s | no effect |
| `brummayerbiere/bitrev0256` | 0.39 s | 3.14 s | **8× slower** |
| `RWS/Example_1` | 2.09 s | 0.69 s | 3× faster (already solved) |
| `RWS/Example_7` | 56.6 s (sat) | timeout | regression |
| `2018-Mann` arbiter ×2 | 2.8 s | 3.0 s | ~8% slower |
| `calypto/problem_14` | timeout | timeout | no effect |

Reverted without landing.  The pattern is the structural-rewriting study's
pattern again: the bitwise convergence the normal form buys does not
decide the flagship file (whose difficulty sits in `ite`/`bvult`/`bvadd`
loops, not in De Morgan mirrors), while committing to the normal form
everywhere costs blast size (not-or-not chains are 3 gate vars per bit
where `bvand` is 1) — hence the bitrev/Mann regressions.  A
convergence-*probe* variant (rewrite on trial inside equality checks,
keep the original term stream unless the sides collapse) was considered
and skipped: it cannot help `maxandminor` either, because the top-level
sides contain non-bitwise structure that bitwise-only normalization does
not converge.

**Do not retry** rule-by-rule ports of z3's simplifier for this file
family.  If the `maxandminor` class is picked up again, the lever is a
bound-propagation / value-substitution analysis over the `bvult`/`ite`
loop structure (what z3's simplify+propagate-values cascade computes in
concert), not bitwise normalization.

## Follow-up (late evening): the odd-width fuzzer found a real false `sat`

The identity-pair differential harness described above
(`nixie-solver/tests/bv_odd_width_blast_differential.rs`, built to probe
the dormant width-126 concat/extract class) found and reduced, on case
51, a live soundness bug — not in the blaster but in the term layer:

```smt2
(set-logic QF_BV)
(assert (not (= (_ bv4 1) (_ bv0 1))))   ; nixie: sat (z3: unsat)
```

`(_ bv4 1)` is out of range (reads as `4 mod 2 = 0`).  The live parser
path for `(_ bvN W)` (`smtlib/parser/terms.rs`) interned the raw value
with no range handling; the two spellings of the same constant hash-consed
as distinct terms, and the equality folder answered `(= 4 0)` **false** —
so the negated equality was satisfiable (false `sat`) and the positive
one unsatisfiable (false `unsat`).  The second parser arm
(`indexed.rs`) *rejected* out-of-range literals, so the codebase held
both semantics at once.

Fix (landed as `37551372`): `mk_bitvec` reduces every constant into
`[0, 2^width)` at construction — the canonical representative — with a
fast path for in-range values; both parser arms delegate to it, matching
z3's accept-and-wrap reading.  Negative values reduce to their
two's-complement residue, so no `BitVecConst` ever carries a negative
value.  Parity after: 175 files, 0 disagreements.

The fuzzer itself stays in the tree as a standing net: it builds random
terms over free variables at limb-boundary widths and asserts
construction-valid identities in unsat/sat pairs (double negation,
concat/extract split, extract-of-concat, De Morgan, xor-const twice,
add/sub cancel, udiv/urem reconstruction) — a wrong verdict in either
direction fails the pair.  Extending its template set is the cheapest
way to harden the blaster layers against the next width-edge bug.

## Appendix: the debug-net false positive — evidence trail (unresolved)

The debug model-validity net's residual false-positive mode on
multi-round unified solves (`RWS/Example_7`, both const-flow arms) is
narrowed to the following facts; a future session can finish it:

1. **Not snapshot staleness.**  Re-adopting `self.sat.model()` immediately
   before the net changes nothing — the mismatching bits read the same.
2. **Not undefined reads.**  Every bit the net reads is *defined* in the
   model (the undetermined-bit filter is in place), and the model vector
   spans the full var space (`len == num_vars`).
3. **The contradiction is against clauses absent from the live core.**
   For the mismatching `bvand` gate: the live core's own
   `model_value` reports `p = True, q = True, out = False`.  A CDCL solver
   returning `Sat` cannot hold a model violating a clause it contains, so
   the gate's defining clauses (`out ⇔ p ∧ q`) are not in the core the
   model came from — or the vars' indices no longer mean what the stored
   `term_to_bv` entry says.
4. **Ruled out**: mid-run `Solver::reset` (never called on a single-file
   QF_BV run), double-encoding of the term (traced once, `pre_entry=None`),
   and ELS/BVE reconstruction gaps for these particular reads (the values
   are the live core's, post-reconstruction).

Verdict correctness is not in question on the evidence: the file's `sat`
and full model are z3-validated by pinning, the parity suite is
175/175, and the 509-file A/B shows zero verdict flips.  The open
question is *which era's clause set* the stored `term_to_bv` entries
reference when a unified generation spans pending-atom link rounds.

**RESOLVED (57e9fb7e).**  The prescribed debug API landed
(`Solver::debug_clauses_containing`, full arena scan + binary-graph
edges) and the dump ran: the mismatching `bvand` bit had **zero live
clauses** — not "never emitted", but *eliminated*: BVE/ELS preprocessing
(2.98M substitutions, 44.9k eliminations on that file) had resolved its
defining clauses away, and `save_model`'s reconstructed values satisfy
the **rewritten** formula, which need not satisfy the original (deleted)
circuit clauses.  The net was comparing raw post-elimination reads
against original-circuit semantics — a category error, not a solver bug
(verdict correctness was never in question).  The net now stands down
loudly whenever eliminations ran (`bv_unified`'s stand-down gate), and
`NIXIE_NET_DUMP_CLAUSES` remains wired for the next incident.

## Session close (late 2026-09-11 → 2026-09-12): the simplify cascade, landed (4292c427)

The maxandminor mechanism question is now fully answered end-to-end:

1. **Ground truth** (with the probe-order mistakes corrected — `(apply …)`
   must run *after* the asserts, and worktrees need the corpus symlink):
   z3's `simplify` **alone** collapses maxandminor016's 16-round
   bound-propagation chain to `(not (= (bvor (¬a!244) (¬a!263)) (bvor a!501 a!514)))`
   — one near-mirror equality — and z3 decides the result in 0.068 s.
   Nixie on z3's simplified form: **unsat in 8.3 s** (vs 28–43 s raw).
   The term-simplifier cascade is the entire gap.
2. The cascade's visible transformations: De Morgan pushdown of
   `~(a & b)`, constant masks folded as `bvor` operands, NOT through
   concat, on top of sorted operand flattening (which nixie already had —
   it is the convergence substrate).
3. **Landed** (`NIXIE_BV_SIMCASCADE=0` disables; default on): the
   NOT-descent rules in `bv_preprocess` + `X | ~X` complement folding.
   Standalone AND elimination was screened and **excluded** (bitrev0256
   10× regression — not-or-not chains cost 3–4 gate vars per bit).
   A/B: 286 vs 284, zero flips; maxxor016 2.2× and under the cap;
   maxandminor016 −24% (≈21 s at settled load — crossing the cap);
   bitrev untouched by construction.

Remaining gap on this family (8.3 s vs 0.068 s on the simplified form)
is blast+SAT on the converged shape; the missing cascade pieces
(ite-through-concat lifting, `= #x0000` selector normalizations) are the
next increments if more is needed.

## Addendum (2026-09-12, small hours): shift wiring landed default-off (797a6bf0)

The last visible piece of z3's cascade for the shift-heavy families —
const-distance shifts rewired to concat/extract at term construction
(`x << k = concat(x[w-1-k:0], 0^k)`, `x >>u k = concat(0^k, x[w-1:k])`;
Z3 `mk_bv_shl`/`mk_bv_lshr` numeral cases) — is in, behind
`NIXIE_BV_SHIFT_WIRING=1` (default off).

- Deterministic serial: bitrev0256 1.5×, bitrev0512/1024 2.0× faster;
  composes with `NIXIE_BV_CONST_FLOW` (same family, different layer).
- RWS family re-verified file-by-file against z3 in both arms (the
  width-126 `bvlshr` shapes the reverted structural study tripped on):
  zero disagreements.
- 4476/4477 solver+core tests green with the flag forced on; the single
  failure is the printer structural-contract test that pins "bvshl x 3
  stays BvShl" — the exact contract this flag changes when enabled.
- The 509-file screen ran settled: **287 vs 286, zero verdict flips**
  (all three differing cells are z3-unknown boundary files; two measure
  identical serially, the third — `mcm/54` — is the real win:
  **43.5 → 7.1 s, 6.1×**, the shift-add multiplier chains collapsing
  under the wiring).  **Default flipped on** in `53246010`; cells +
  binary in `precompile/53246010/`; parity 175/175 (0 disagreements).

## Appendix (final): gate-level structural sharing is dead for this family — measured twice, now with complements

The question "would an AIG-style gate layer (structural hashing with
complement edges) collapse maxandminor?" is answered **no**, definitively:

- The first probe (var-keyed SH memo, pre-cascade): **0 hits** across
  every family tried.
- The second probe (2026-09-12, post-cascade): De Morgan-normal literal
  keys — `OR(x,y)` keyed identically to `AND(¬x,¬y)`, operands sorted —
  on `maxandminor016` with the full cascade landed: **0.0 % collisions**
  (≈6 k gate requests, zero repeats).

The two sides' boolean circuits share no structurally-identical gates
because their *leaves* differ (operand bits of distinct, non-convergent
TermIds) — the trees cannot collide at any level.  Z3's collapse on this
family is therefore **semantic** (its post-blast goal passes do
value-propagation and definition substitution, not structural sharing).
Any future "AIG layer" for this family must propagate values through the
DAG — hash-consing alone, however canonical, cannot close it.  Do not
re-try structural gate sharing for the bound-propagation family.

## Appendix (2026-09-12): the AIG gate layer — implemented, debugged, measured, rejected

"Implement z3's post-blast semantic passes" was taken literally: a full
complement-edge AIG layer in the `Sig` gate constructors (`Sig::Var`
became a SAT *literal* — `not` free, `or = ¬and(¬x,¬y)` De Morgan
collision, literal-keyed hash-consing for and/xor/mux nodes, z3
`aig.cpp`'s two-level substitution/subsumption/contradiction rules,
scope-journaled memo retraction for embedded pops, era clears at unified
boundaries).  Full patch preserved at
`docs/studies/assets/2026-09-12-aig-gate-layer-experiment.patch`.

**Two bugs found by the safety nets before any commit** (both exactly the
collision class the implementation comments warn about):
1. `gate_mux`'s branch-swap key normalization without the sel inversion
   — `mux(s,a,b)` and `mux(s,b,a)` collided on one memo entry while the
   emit built only one of the two functions (under-constrained order
   network; caught by `order_dispatch_free_vars_sat`).
2. `materialize_not` inverted polarity (returned `l` for positive `l`
   instead of the materialized complement) — a **false `unsat`** on
   `RWS/Example_1/5` caught by the RWS spot-check.

After both fixes: correct everywhere (1939 theory tests, 4213
solver tests, RWS 19/19 vs z3, all verdicts clean) — and **win-less**:

| file | landed binary | AIG layer |
|---|---|---|
| maxandminor016 (original) | 28.1 s | 31.6 s |
| maxandminor016 (z3-simplified) | **6.1 s** | 8.2 s |
| Mann arbiter | 2.80 s | 2.78 s |
| bitrev0256/0512/1024 | — | neutral |

The structural collisions this family would need do not exist (the probe:
0.0 % De Morgan-normal gate repeats, pre- and post-cascade), so the layer
pays bookkeeping without sharing.  z3's `aig` tactic closes the
simplified form through sharing that its *expression-level* blast DAG
provides — sharing our *term-level* hash-consing already supplies — plus
goal-level value propagation that has no local counterpart.  **Third and
final structural kill**; the do-not-retry now covers: var-keyed SH,
De Morgan-keyed SH, and a correct complement-edge implementation with
two-level rules.  If the maxandminor/cjpeg class is ever closed, it is
by goal-level semantic propagation over a boolean expression IR —
a different architecture, not a better gate memo.

## Session close (2026-09-12, afternoon): the expression IR built and landed default-off (8f8f5683)

The "remaining architecture" is in: `nixie-theories/src/bv/bool_ir.rs`
(hash-consed boolean-expression DAG: and/or/xor/mux nodes over
complement-encoded literals, construction-time folding, constant
re-fold fixpoint, deferred Tseitin with dead-structure elimination) +
the gate-layer integration (`Sig::Ir`, definition recording,
`materialize_ir` at check entry and window close).  `NIXIE_BV_IR=1`.

**It closes the blast-vs-z3 gap on the maxandminor family**: the
z3-simplified form drops 6.1 s → **0.18 s** (34×; z3 itself 0.028 s),
the original 29.2 → 12.5 s, `ex7_prime` timeout → 3.4 s, bitrev1024/2048
3×.  The mechanism is exactly what z3's post-blast passes exploit:
definitions inline (result bits enter the CNF only at materialization),
nodes hash-cons across terms, constants refold through shared structure
— measured over three structural kills, this *semantic* layer is the
one that pays.

Two soundness bugs caught by the nets pre-commit (raw-equality in the
mixed `encode_eq_node` arm — false `unsat`, minimized by delta-debugging
RWS to a 2-bit probe; `debug_assert`-guarded node-0 reservation —
release-only false `sat` on all of bitrev, found by model-pinning
against z3).  Both are the collision class the study keeps warning
about; both are now regression-covered by the probes that found them.

Corpus A/B: 289 vs 288, **zero verdict flips**, 17 cells split evenly —
real deterministic wins (maxandminor/ex7/bitrev/mcm-87/lfsr) AND real
cap-crossing losses (VS3-A7, mcm/54, catchconv-1568).  Default OFF; the
follow-up that would justify default-on is a per-class gate (the losses
are mul-chain/catchconv shapes whose trajectories the deferred encoding
hurts) and seeding `refold_consts` from level-0 units (the machinery is
in, unwired).  Binary + both A/B arms: `precompile/8f8f5683/`.

**Update (beb6cadc)**: the level-0 seeding is wired — `materialize_ir`
pins every IR leaf var the SAT core has permanently assigned at
decision level 0 and re-folds before Tseitin (snapshots cleared per
materialization, so pops can't read stale folds).  Every measured win
holds or improves (ex7_prime → 6.6 s, bitrev1024 → 4.4 s).  The losses
persist, and the pattern sharpened: **gains concentrate on UNSAT-verdict
files, losses on SAT-verdict files** — plausibly the deferred emission
removes branchable Tseitin variables that refutation never needed but
model-finding exploited.  A gate on that observation needs a blast-time
predictor (no verdict exists yet at blast time), so it stays a study
hypothesis; the corpus decision remains default-off.
