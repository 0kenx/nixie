# FP constant semantics: value marks, EUF-pinned folding, and two engine soundness fixes

**Date:** 2026-09-08 · **Follow-up of:** `docs/studies/2026-09-08-fp-format-aliases.md`
(scoped rungs 1–2) · **Found by:** directed probe + a purpose-built z3 differential
battery · **Status:** FIXED, landed.

## What this closes

The format-alias study left three scoped rungs.  This lands the big one and
finds two more soundness bugs on the way:

1. **`=` on floats had no semantics** (false-`sat` class): `(assert (= c1 c2))`
   over two distinct fp literals — including `(_ +zero e s)` vs `(_ -zero e s)`
   — was a free Boolean; nixie answered `sat`, z3 `unsat` (verified on four
   shapes: direct literals, spelled bits, and variable-mediated).
2. **The unsat direction through variables** (the rung as scoped):
   `x = c ∧ y = (fp.add RNE x x) ∧ y = c2` with `fold(c,c) ≠ c2` answered
   `unknown` where z3 says `unsat`.
3. **Two `Ieee754Engine` soundness bugs** found by the differential battery
   built for this rung: directed-mode gradual underflow, and SMT-LIB
   `fp.min`/`fp.max` semantics.

## Design (three layers, all landing)

### Layer 1 — bit-pattern value marks on FP literals

`EufSolver` gains a persistent `fp_value_ids` map from
`(eb, sb, sign, biased exp, significand)` to a shared distinguished-value id
(symbol-level like `value_consts`; collision-safe because ids issue from the
monotone counter that never rewinds).  The constant-interning leaf path
declares every FP literal before its first intern, so two *different* bit
patterns can never share an e-graph class — the merge raises a value conflict
with a complete proof-forest core (the same machinery the BV constants use).

Datum semantics (every pin z3-verified on *exact-width* literals — the probes
must pad the exponent to its exact bit width or z3 silently errors):

| shapes | `=` |
|---|---|
| `(_ +zero e s)` vs `(_ -zero e s)` (any spelling) | **distinct** |
| two distinct finite bit patterns | **distinct** |
| `(_ +oo)` vs `(_ -oo)` | **distinct** |
| any two NaNs of one format (either sign, any payload, incl. `(_ NaN e s)`) | **one datum** |

The NaN collapse is implemented as a canonicalization in the literal decode
(`fp_const_value`); everything else keys on raw bits.

### Layer 2 — constant folding through EUF pins (`solver/fp_fold.rs`)

One `check_core`-entry pass per check.  It harvests the ground `fp.*`
operations of the assertions (quantifier bodies opaque), pins operands from
three sources — **definitional assertions** (`(= t lit)` conjuncts at positive
polarity — the crucial one, because the early instantiation phase runs before
any propagation, so the e-graph holds no level-0 merges yet), pins recorded
in this pass (chains, including EUF-equal aliases), and the e-graph class
constant on re-checks — evaluates exactly via `Ieee754Engine`, and asserts
each fold as a **guarded valid clause**:

```text
(a = lit1) ∧ (b = lit2) → (fp.op(rm, a, b) = fold(lit1, lit2))     (value ops)
(a = lit1) → fp.pred(a)                                            (predicates)
```

Every clause is valid *standalone* — the guard set is the union of the
operand pins' justification atoms (pins carry `{value, witness literal term,
guards}` through define links and fold chains), never a reference to another
fold clause being present.  Literal operands contribute no guard.  Value ops
pin their result for downstream folds (fixpoint loop, capped at 512
ops/check); predicates emit only the clause.  Dedup + `pop` retraction
mirror the parity lemmas (`TrailOp::FpFoldLemmaAdded`).

The headline shape then refutes by unit propagation + one value conflict:
the fold clause forces `fp.add = fold(c1,c1)`, the asserted equalities merge
`y` with both the folded literal and `c2`, and the two distinct bit patterns
collide in one class.

**Gate restructure:** with fp atoms present and no fold output, the early
honesty gate still answers `Unknown` before the search (unchanged).  With
fold clauses asserted, the gate now falls through to the CDCL(T) search (the
refutation needs EUF transitivity, which is not SAT-level UP), and any
`Sat` the search returns must first survive `try_fp_model_sat` — the same
bit-exact witness the early path uses (`fp_fold_verify`).

### Layer 3 — engine semantics (found by the differential battery)

* **Directed-mode gradual underflow** (`Ieee754Engine::pack`): rounding for a
  result at/below the smallest normal now happens on the **subnormal grid**
  (guard/round/sticky re-extracted at the coarse position, `should_round_up`
  reused, carry into the smallest normal handled).  The old path truncated
  with the dropped bits never consulted and returned ±0 unconditionally:
  `fp.mul RTN (-min_subnormal) (+min_subnormal)` produced `-0` where IEEE
  requires `-min_subnormal` — a false-`sat` on its `= -0` refutation.
* **SMT-LIB `fp.min`/`fp.max`** (not IEEE `minNum`): a NaN operand yields
  the *other* operand, and a tie prefers the negative zero for `min` / the
  positive zero for `max` (`fp.min(+0,-0) = -0`).  The engine returned the
  NaN itself and the first operand on ties.

## Measurement (z3 differential, the real gate for this change)

Purpose-built generator: random Float64 literals (subnormals, ±0, ±inf,
ulp-adjacent normals), 1–3 variables, pin/define chains over
`add/sub/mul/div/rem/min/max` under all five rounding modes, closing
equalities/disequalities/predicates in both polarities; plus targeted
batteries (specials identity, directed-underflow corners, halfway ties per
mode, fma, rem) — **every expectation z3-verified**:

| battery | result |
|---|---|
| random, seeds 42/7/123 × 150–200 | **600/600 agree**, 0 unknown |
| fma + rem | **180/180 agree** |
| specials (30 shapes) | **30/30 agree** |
| targeted probes (e-series, m/z-series, mediated forms) | all agree |

Two probe-construction traps are now pinned in the study record: bare hex
literals take their width from the digits (`#x7ff` is **12** bits — a
Float64 exponent must be `#b11111111111`), and a z3 parse error leaves the
instance *vacuously sat* — the mismatch direction to distrust.  The z3 NaN
semantics were derived three times before the exact-width probes settled
them; the well-formed answer is the one in the table above.

## Gates

Full verification on the landing tree: build `--all-features`; nextest
workspace `--all-features` **10701/10701**; clippy `-D warnings`; fmt; doc
`-D warnings`; z3 parity **170 entries / 0 wrong** (per-environment record
unchanged); obligation fuzzer medium **58/58** and small+stress-heavy
**58/58**, zero FAIL/CRASH/GENFAIL.  Tests landed: engine pins for the
underflow corners and min/max semantics (`ieee754_full/tests.rs`, plus the
pre-existing IEEE-minNum NaN expectation in `fp_comprehensive.rs` updated to
the SMT-LIB definition), and `nixie-solver/tests/fp_const_folding.rs` — the
false-`sat` shapes, fold refutations (variable-pinned, literal-operands,
chains, predicates), the NaN datum collapse, `fp.min` ties, and scope
retraction (`push`/`check`/`pop`/`check`).

## Remaining scoped rungs (not this landing)

1. **`((_ to_fp e s) x)` application-form parsing**: the *correct* SMT-LIB
   syntax for the real→fp conversion is rejected by the parser today
   ("unknown function/constant"); the nonstandard `(_ to_fp e s x)` spelling
   this session's early probes used does not parse either.  A parser feature
   (indexed function application), not a fold gap.
2. **fp congruence**: `fp.op(x,…) = fp.op(y,…)` when `x ≡ y` but the terms
   differ syntactically needs fp ops interned as congruence applications
   (`intern_operands` currently handles only `Apply`/`Select`).  The value
   marks and folds are independent of this.
3. **`fp.roundToIntegral`** is outside both the engine and the fold shapes
   (no exact engine implementation); still owned by the pattern checks and
   the model builder.
4. **The `fpboundary` obligation family** (the roadmap productions that
   motivated the whole arc): the differential generator in this study is its
   prototype — promoting it into `bench/obligation` with manifest + fuzzer
   wiring is mechanical from here.

## Reproducers

* The false-`sat` battery and every targeted probe: `nixie-solver/tests/fp_const_folding.rs`
  (assertions verbatim) and the engine unit tests.
* The differential generator (seeded, deterministic): reconstructed from the
  study text; the essential shapes are all pinned in the landed tests.
