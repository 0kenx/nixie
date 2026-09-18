# The XOR-congruence repair: 2534 invisible parity gates, two closure bugs, and bv_ILA at kissat parity (2026-09-18, third landing)

Continuation of `2026-09-18-ite-gate-congruence.md` and
`2026-09-18-ssr-binaries.md`. The SSR study corrected its own "pure search
gap" claim along the way (see below), which redirected the arc to the one
remaining extraction blindness: **XOR/XNOR parity gates**.

## The correction first

The SSR study's headline — "the remaining 16–36× is pure search quality" —
was wrong. The missing control: kissat on our residual with
`--congruence=0` needs 766K conflicts (≈ us), with `--preprocess=0` still
only 10.5K — kissat's IN-SEARCH congruence re-collapses our residual
(20,742 more merges + 65,145 gate-subsumed clauses there). The gap was
still structural, and the residual's 60,602 exact duplicate clauses (our
fold rewrites clauses onto representatives but never deduplicates across
clauses; the elim-phase subsume round cleans 46K of them at conflicts=
2000 — transient, not the difference) were a red herring.

## The blindness

The raw bv_ILA file contains **2,534 complete parity 4-clause sets** — but
the XOR arm found **zero** gates (the trace's `xor=0` against kissat's
7,530). Two compounding causes, both found the hard way:

1. **Extraction polarity**: the scan checked the input signs *as they
   appear in the base clause* — one of four sign presentations. A
   definition whose o-form clauses negate an input (every XNOR shape) is
   invisible. Fix: iterate all four input-sign combinations per base
   (clause-literal polarity is a red herring I tripped on three separate
   times this arc — first in the ITE canonicalization, then in a python
   checker that "proved" zero XOR sets existed, then in my own regression
   tests' break clauses).

2. **Closure algebra**: XOR needs the same presentation discipline as ITE.
   `f = a⊕b` has presentations `(a,b)` and `(¬a,¬b)`; `¬f` has `(¬a,b)`
   and `(a,¬b)`; canonical = min per family; the cross rules (3+4) apply.
   Two broken designs were caught (each by fuzz + minimization + a
   56-clause pinned regression):
   - keying the affine relation over **all three gate vars**: one parity
     definition reads three ways (any var as output), all sharing the
     signature — merging inputs with outputs (`37 ≡ 41 ≡ 122 ≡ 123` from
     a single definition; false UNSAT on Iter22 at 0 conflicts);
   - **parity-folding** the input signs into one key: a definition's `o`
     and `¬o` readings then share the key — merging `o ≡ ¬o`, an instant
     contradiction class.
   The sound shape keys the **signed inputs** only; duplicate polarity
   readings then land pos-of-one on neg-of-the-other and self-cancel.
   Kissat's rhs-keyed hash table has this shape from the start (it hashes
   the gate rhs as-is; the negate_lhs flag handles output polarity).

## Measured effect (default config, deterministic counters)

| instance | before | after | |
|---|---|---|---|
| bv_ILA_Piccolo | 302,978 conflicts / ~100 s | **15,144 / 6.0 s** | 0.05×; kissat is 9,465 — parity reached |
| b21 | 157,666 | 172,092 | 1.09× (noise band) |
| s38584 | 15,159 | 16,241 | 1.07× |
| Iter22 / Carry / x9 / frb35 / SCPC / circuit | — | — | bit-identical (inert band) |

## Soundness

- 5 regression tests (twins, XNOR presentation folding, single-definition
  non-merge, self-cancel of polarity readings, the minimized false-unsat).
- 1,500 parity-heavy differential fuzz instances vs the landed base +
  kissat tiebreak: 0 disagreements.
- **78,164 claimed equivalence pairs on bv_ILA, every one kissat-verified
  (0 bogus)** via the class-dump + `F ∧ ¬(a↔b)` check.
- Crate suite 1080/1080, clippy/fmt clean, Z3 parity 177/0/1 (baseline).
- Perf gate GATE_SEEDS=10: PASS (0.983; worst cell 1.07 = trajectory
  noise on a sat instance).

## Standing after three landings

Session start → now on bv_ILA: **405,848 → 15,144 conflicts (27×), wall
51.65 s → 5.97 s**; vs kissat 1.24 s / 9,465 conflicts. The remaining
per-family gaps from the handover: oddball (25×) untouched, hwmcc-6s299
(12×) is parse-dominated, the `normalised`/GP_190 families untested
against the new congruence. Named next slices, in measured order:

1. **Gate-based subsumption** (kissat's `forward_subsume_matching_clauses`
   over repr-canonicalized literals — 65K clauses on our residual, 108K
   on the raw file) plus the post-fold dedup (60K duplicates today).
2. **The armed composition** (SSR + pre-search arm) re-measured on top of
   the XOR closure — the BVE interaction may have changed now that the
   fold collapses 5× more.
3. The n-ary gates (arity ≤4 XOR, n-ary AND) — still lower priority.
