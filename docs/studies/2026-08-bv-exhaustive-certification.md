# BV exhaustive sat-certification: finite domains instantiate completely (2026-08-24)

## The residual, closed

The MBQI pool study recorded: satisfiable quantified-array goals cannot
be *certified* `sat` — `(∀i:BV4. select a i = #x0) ∧ select(a,#xb) ≠ #x1`
answered `unknown` (z3: `sat`), on both sides of the pool change.

## Root cause

`sat_certify::universal_instances` had two domain sources:
`int_box_domains` (Int-only: any non-Int bound var ⇒ decline) and
`eu_domains` (relevant terms harvested from the completed model).  For
the array-over-BV goal the body is EU-eligible, but the completed model
carries **no select keys and no function-interp entries** — the relevant
set was *empty* (measured: `relevant_sorts=0`), `eu_domains` declined,
and certification never fired.

## Fix — the sound one needed no relevant terms at all

A **BitVec-sorted bound variable ranges over exactly `2^width` values**.
Enumerating them instantiates the universal over its entire domain:
complete in both directions (`unsat` when an instance falsifies, `sat`
when the ground solver models them all), *unconditionally* sound, no
model-extension argument, no body-shape restriction.  `int_box_domains`
is generalized to `bounded_domains`: per bound variable, BV sort ⇒ full
finite domain (width-capped at 20 before the shift; the product-vs-`cap`
check — 4096 — does the real limiting), Int sort ⇒ the body's guard box
(unchanged), anything else ⇒ decline to the EU path.

## Results (z3 parity)

| probe | oxiz | z3 |
|---|---|---|
| array-over-BV sat control (the residual) | **sat** (was `unknown`) | sat |
| array-over-BV unsat probe (regression guard) | unsat | unsat |
| `∀i:BV2. bvult i 2` (pure BV body, refuted) | **unsat** | unsat |
| `∀i:BV2. bvule i 3` (pure BV body, holds) | **sat** | sat |

The last two matter: the EU path requires essentially-uninterpreted
bodies; exhaustive enumeration does not — plain BV comparisons certify
too.

10 094 tests (3 new), clippy/fmt/doc; differential 0 wrong / solved 160
unchanged; parity **167/0/1 byte-identical**; canaries unchanged.

## Residual

`mk_bitvec` exhaustive domains stop at the certification cap (width 12
for a single variable, smaller for tuples) — wider BV quantifiers keep
the MBQI counterexample path, unchanged from before.
