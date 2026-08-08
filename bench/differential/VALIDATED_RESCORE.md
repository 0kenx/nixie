# Validated re-score of v0.3.2 (oz) under model validation

Run with the upgraded `bench_diff.py --validate-models` (z3-based model
consistency check + family-neighbour flag), τ=10 s, release builds, sample
seed 20260807 (270 instances). z3 4.16.0 is the oracle. The validator is
**z3-based, not oziz's own** `eval_in_model` — measured to false-alarm on
genuinely-satisfiable UF instances (e.g. `iso_brn1083`: oziz "FAILED 5/19"
where z3 confirms sat), so it cannot be the oracle. See `README.md` §Trust model.

Raw per-instance results: `results/oz-v032/`, `results/main-validated/`
(gitignored run artefacts; reproducible by re-running the harness).

## Headline (validated, declaration-accurate quoting)

| build | solved | agree_z3 | disagree | sat_mod_valid | sat_mod_invalid | sat_trusted | unsat_trusted | **trusted_total** |
|-------|-------:|---------:|---------:|--------------:|----------------:|------------:|--------------:|------------------:|
| **main** (`965285b`)    | 125 | 121 |  4 | 58 |  6 | 45 | 61 | **106** |
| **oz** (`v0.3.2`=`7fb36aab`) | 156 | 140 | 16 | 53 | **50** | 46 | 53 | **99** |

oz solves more (156 vs 125) and agrees more (140 vs 121), but is **less
trusted** (99 vs 106). Two reasons, both concentrated:

1. **oz's model construction is severely broken.** 50 of its 103 `sat`
   answers emit a model that *contradicts* the assertions (z3:
   `asserts ∧ model` = unsat). main has 6 such cases (see defect inventory
   below). This is the single biggest deflator.
2. **oz is 4× unsounder** (16 vs 4), all in the same direction (z3 unsat,
   oz sat) — the over-eager-sat mechanism. Per family:

   | family | disagree | (also sat_invalid in family) |
   |--------|---------:|------:|
   | QF_AUFLIA/storecomm | 5 | 5 |
   | QF_LIA/rings | 3 | 3 |
   | QF_UFLIA/mathsat (xs_*) | 2 | 13 |
   | QF_ANIA/GrandProduct-Ozdemir | 1 | 6 |
   | QF_AUFLIA/Rodin, QF_BV/bruttomesso, QF_IDL/job_shop, QF_UFIDL/mathsat, QF_UFLIA/wisas | 1 each | — |

   The GrandProduct and `xs_*`/storecomm/rings clusters are exactly the
   one-mechanism-scores-and-errs pattern the family check exists to catch.

oz's briefed "159" → **99 trusted**. The brief's claim that "the true ceiling
from porting v0.3.2 is well below it" is confirmed — and the ceiling is below
main's own trusted count.

### main's model layer — the bigger catch (2 real defects, pinned)

Re-scoring oz surfaced that **main's own model layer is unsound**: 6 of its 64
`sat` answers emit a model z3 rejects. Two are the known-unsound verdict bugs
(`bench_679`, `ext_con_064`, `storecomm_t3`, `xs_8_13` — wrong verdict, so any
model is bad); the other **2 are correct-verdict sats with a genuinely
unsatisfying witness** — a `build_model` construction defect:

| instance | logic | z3 | main | symptom |
|----------|-------|----|------|---------|
| `UCLID-pred/DLX/DLX1C0.smt2` | QF_UFIDL | sat | sat | emits negative Int (`impl.fdType=-4`) where z3's model is non-negative |
| `VeryMax/SAT14/1659.smt2` | QF_NIA | sat | sat | emits a model z3 rejects (482/482 symbols pinned, declaration-accurate) |

A separate **evaluator defect** (`Model::eval`, behind `Context::eval_in_model`)
false-alarms on a *correct* model: `iso_brn1083` (z3 accepts the model) but
`eval_in_model` reports assertions unsatisfied — so `(get-value)`/`(get-model)`
and the CLI's `--validate-model` are unreliable for UF. Both defects are pinned
as `#[ignore]`d guards in `oxiz-solver/tests/model_soundness_regressions.rs`,
distinct from each other (different components: `build_model` vs `Model::eval`).

### Correction log: validator quoting bug

An earlier version of these numbers (main 8 / oz 52 `sat_invalid`; main 104 /
oz 97 trusted) counted **4** main construction defects. Re-checking with
nondeterminism and declaration-accurate symbol quoting showed `21.lp` and
`3.lp` were a **harness validator quoting bug**: the validator pinned symbol
names bare (`(assert (= hc(18,17) false))`) while the file declares them
quoted (`|hc(18,17)|`), so the pin referenced a disconnected token and z3
returned a spurious `unsat`. Fixed in `bench_diff.py` (pins now use the file's
exact declared token); both builds re-validated offline (`revalidate.py`). The
real-defect count dropped 4 → 2; trusted totals rose to 106 / 99. The lesson —
recorded in the test module doc — is the one the review flagged: a validator
artifact looks exactly like a construction defect until re-checked.

## What is actually portable (oz trusted, main does not solve)

Per-instance diff of the two validated runs:

**Genuinely-new solves — oz trust-solves, main does not solve at all (3):**

| instance | logic | oz | main | z3 | oz time |
|----------|-------|----|------|----|--------:|
| `qlock/qlock-4-10-7.base.cvc.smt2` | QF_IDL | unsat | timeout | unsat | 1.38 s |
| `20220307-SMPT/Diffusion2D-PT-D50N010/RC-10.smt2` | QF_LIA | sat | timeout | sat | 1.41 s |
| `20190429-UltimateAutomizerSvcomp2019/sum10_..i_12.smt2` | QF_ANIA | sat | unknown | sat | 0.02 s |

All three re-verified by direct invocation (qlock unsat 1.38 s, RC-10 sat
1.41 s, sum10_i_12 sat 0.02 s; main times out / returns unknown on each).
These are the confirmed-genuine targets. qlock is the unsat-direction one
(can't be faked); the other two are sat-direction but isolated (no family
disagreement, valid model) so they survive every filter.

**Soundness fix opportunity — oz sound where main is not (1):**

| instance | logic | oz | main | z3 |
|----------|-------|----|------|----|
| `QF_BV/sage/app9/bench_679.smt2` | QF_BV | **unsat** | sat (unsound) | unsat |

v0.3.2 answers correctly; main's bvule/bvshl path is unsound. Porting v0.3.2's
BV comparison/shift handling here fixes a main soundness bug (already pinned as
`#[ignore]`d guard `bench_679_is_not_sat`). This is a *soundness* win, not
completeness.

(The other 5 "oz-trusted / main-solves-but-untrusted" rows are `QF_BV/sage`
sats that main solves *correctly with valid models* — they are flagged only
because the family check collateralises the whole `sage/` family for
`bench_679`'s unsoundness. They are not real converts; see caveat below.)

## Reverse — main trusted, oz not (16)

main trust-solves **16** that oz does not. Breakdown:

- **main is sounder where oz is wrong:** storecomm (4), rings (1), xs-06-15
  (1), jobshop (1), smt8591 (1) — oz says `sat` with an invalid model (or
  unsound) where main correctly says `unsat`.
- **main solves instances oz can't:** `DTP_k2_n35_c210_s1/s14` (QF_IDL),
  `gensys_icl785` (QF_UF), `hash_uns_03_16` (QF_UFLIA) — oz returns no
  verdict (timeout/unknown); main solves them.
- **main emits valid models where oz's are bogus:** `hash_sat_05_06/05_12/
  08_03`, `sorted_list_insert_noalloc0`, `smt5695` — same verdict, but oz's
  model is invalid where main's is valid (and the family is clean for these).

So main is a net **+16** on trusted solves vs oz, and oz's apparent +31
solved-edge is almost entirely unsoundness + bogus models.

## Validator limits (read the sat_model_invalid column as a lower bound)

The z3-based check builds `(asserts ∧ pinned-constants)` and asks z3.
- **Sound in the unsat⇒bad direction:** if z3 says `unsat`, no function
  extension rescues the formula under those constants, so oziz's claimed model
  (which uses those constants) cannot satisfy the asserts ⇒ the model is
  genuinely bogus. So every `sat_model_invalid` row is a *real* defect — there
  are no false accusations from this path.
- **Lenient on partial / function models:** function models are skipped during
  pinning (only top-level constants are pinned), and a partial model can let
  z3 find *some* consistent extension even when oziz's specific model is wrong.
  So a `sat_model_valid` row means "consistent," not "provably correct."

Consequence: **`sat_model_invalid` is a lower bound on the true count of
unjustified sats.** main's 6 (2 on agreeing sats + the 4 known-unsound) could
be more — a model whose only error is in a skipped function value would pass
as `valid`. The 4 known-unsound rows are flagged for certain (their instance
is unsat, so no model exists); the 2 agreeing-sat rows (DLX1C0, 1659) are the
construction defect's confirmed floor. Treat none of these numbers as exact
ceilings.

### Second oracle limit: the internal gate shares `arith.value` with `build_model`

A *clean* `model_refutes_assertions` gate is **not** evidence the model is
correct in the theory-combination case. The gate's evaluator
(`Solver::eval_in_model_outcome`) reads numeric `Var` values from
`self.arith.value(term)` — the **same source `build_model` uses** — so when the
arithmetic solver's model is itself the bug (see defect B below), the gate
evaluates the assertions with the same wrong values and, where the violation
surfaces as a numeric-equality collision, returns `Undetermined` by
construction (collisions are the gate's deliberate blind spot, because LP
collisions are legitimate). Acting on collisions would mass-downgrade correct
`sat`s, so the gate cannot be cheaply strengthened here. **Two oracle limits
now sit next to the numbers: (1) leniency on partial/function models, (2) the
gate shares `arith.value` with what it validates.** Neither lets a reader
infer `sat_model_valid` is a correctness proof.

## Defect B re-scoping (diagnostic, not the false-sat root cause)

Defect B was briefly suspected to be the root cause of main's remaining
unsound sats (a Nelson-Oppen failure: EUF entails an equality between two
arithmetic terms; the arith solver never receives it; simplex picks values
violating the implied bound → false `sat`). A cheap instrumentation diagnostic
(dump EUF congruence classes + the arith assignment at the final sat) **refutes
that for the named false-sat guards**:

- **`storecomm_t3`** (QF_AUFLIA, false sat): **zero arith terms** at the sat —
  its wrong verdict is UF/array-mediated, not arith. Different bug.
- **`xs_8_13`** (QF_UFLIA, false sat): arith present, but all 20 EUF classes are
  value-consistent (0 with divergent arith values) — the direct missing-
  propagation signature is absent. Format/LIA structure; unattributed to B.
- **`DLX1C0`** (QF_UFIDL, *correct* sat, wrong model): the only instance with
  B's flavor — arith returns values violating a transitively-**entailed**
  bound; EUF classes are themselves consistent.

So B does **not** unify the false sats and does **not** retire the pinned
guards. B stays a bounded **arithmetic model-layer** follow-up (the arith
solver returns infeasible values for a congruence-class the formula
transitively constrains); `storecomm_t3` and `xs_8_13` are **separate**
soundness investigations (array/UF and format/LIA respectively). B was
*not* staffed as a high-priority root cause on the strength of this diagnostic.

## Caveat on the family-neighbour flag

The family flag is conservative by design (it exists to catch the ANIA shared-
mechanism pattern, where over-flagging is cheap and missing it is costly). It
over-flags in families where the disagreement is an *isolated* bug rather than
a shared mechanism — e.g. `QF_BV/sage` is flagged wholesale because of the
single `bench_679` unsoundness, collateralising 5 otherwise-clean sats. This
affects the `sat_family_suspect` column and the exact `sat_trusted` counts,
but **not** the headline (main 104 vs oz 97) and **not** the portable set of
3 (those are defined by "main does not solve," which is family-independent).

## Calibration answer

**Mining v0.3.2 is barely worth it.** The validated, portable ceiling is:

- **+3 genuinely-new solves** (qlock, RC-10, sum10_i_12) — small, concrete,
  each verifiable in isolation.
- **+1 soundness fix** (bench_679: port v0.3.2's BV handling to retire a main
  `#[ignore]`d guard).

…and nothing else. Every other oz-over-main "win" is unsound (16), a bogus
model (36 agreeing sats), or family-suspect. Meanwhile main is +16 trusted
over oz. v0.3.2 is a **net regression on trusted solves** (97 < 104).

**Recommendation:** take the 3 confirmed solves + the bench_679 soundness fix
(step 3 of the plan, now precisely bounded — one mechanism at a time, gate
after each), then **stop mining v0.3.2**. The real completeness gap is
elsewhere and v0.3.2 does not address it:

- **Timeout clusters:** 145 main timeouts / 114 oz timeouts — oz barely dents
  these (it trades 31 timeouts for solves, but 28 of those are unsound/bogus).
- **QF_NIA:** 1/30 for *every* build including oz. Nothing in v0.3.2 fixes
  nonlinear integer arithmetic; that is separate, larger work.

So: bounded v0.3.2 ports first (cheap, confirmed), then the effort belongs on
the timeout/NIA clusters directly.
