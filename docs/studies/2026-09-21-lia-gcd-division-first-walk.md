# The joint-reduction chain: division-first walk (Route B of the LIA floor)

**Date:** 2026-09-21 (evening).  **Tree:** `faaf5471` + the change below.
**Predecessor:** `docs/handovers/2026-09-21-lia-floor-handoff.md`
(Route B); the arc's measurement-log discipline per
`docs/handovers/2026-09-21-bareiss-landed-table-par2.md`.

## Pre-registered question

The handoff sized four experiments on the `gcd_i128` ~30 % share of the
churn probe (`CAV/30-vars/problem__011`, `sat` at 0 SAT conflicts, all
cost in theory checks).  This session measured all four cheaply with a
throwaway histogram build (`gcdhist`, committed only to the measurement
worktree), then built the one the data selects.

## The measurement (problem__011, one solve, instrumented `faaf5471`)

5 245 352 chain calls; widths 30/29/28 = 3.16 M/1.0 M/447 k;
131 545 802 walk steps (27.1 per chain).

| counter | value | reading |
|---|---|---|
| `noexit` chains | 4 509 252 (93 % of walked) | the early exit almost never fires — the walk is effectively always full-width |
| `A_EXIT` mass | at index 29–30 | exits that do fire are at the END |
| MINFIRST shadow | cost 870.5 M vs 882.3 M (−1.3 %) | **experiment 1 (chain order) is DEAD** |
| SORTED shadow | 871.0 M | same |
| `gcd_i128` calls | 166.8 M; 99.3 % via the u64 kernel | volume, not width, is the cost |
| `G_MINBITS` | 42 % ≤ 3 b, 71 % ≤ 7 b, 80 % ≤ 11 b | the accumulated `g` is small almost always |
| `gcd_u64` pow2 fast path | 171 M / 605 M calls | pow-2 operands everywhere |
| `A_FINAL_G_BITS` (noexit) | 79 % ≤ 15 bits | the final g is small |
| `BAREISS_CLS` | `==d_r` 35.6 %, `==g0` 30.6 %, `==d_e` 11.1 %, `==|n_e|` 1.4 %, `==gcd(d_r,d_e)` 1.2 %, none 20.1 % | **experiment 2 (Bareiss structure) CONFIRMED**: the final g is a structural quantity 80 % of the time |

`problem__026` reproduces the same shape (93 % noexit, `==d_r` 33 %,
`==g0` 34 %, none 28 %).  `prp-3-18` never reaches the ff path (0 chain
calls — the fold solves it at 0 conflicts).  `022-45`'s cooperative
timeout path skips process-exit Drops (no histogram; same family by
011/026).

**The decisive shape:** the `==g0` class (30.6 % of full walks) means NO
numerator ever reduces `g` — every step is "g already divides n" — and
the other no-exit classes stabilize `g` early and then divide every
remaining numerator.  The dominant per-step operation is therefore NOT a
gcd discovery; it is a *divisibility confirmation* paid at full
binary-gcd price.

## What was built

`substitute_row_ff`'s joint-reduction walk, per step (operands inside
u64, the 99.3 % case):

```
r = |n| % g;  if r == 0 { continue; }  else { g = gcd_u64(g, r) }
```

Euclid's identity — `gcd(g, n) = n % g == 0 ? g : gcd(g, n % g)` for
`g > 0` — makes the walk's `g` EQUAL the naive chain's at every step:
**bit-identical output by construction** (the reduced row, term order,
admission decision and all downstream state are unchanged).  Wide
operands (> u64::MAX, 0.7 %) keep the `gcd_i128` fallback.

This subsumes the handoff's experiment 4 (2-adic skip): when `g` is a
power of two the modulo compiles to an AND mask, and the pow-2 fast
paths inside `gcd_u64` handle the residue side — no separate hoist
needed.  Experiment 3 (partial reduction) stays un-built: it changes
row content (widths), not just cost, and the division-first walk
removes the pressure that motivated it at zero identity risk.

## Measured result (back-to-back A/B under load 35–50)

| probe | baseline `faaf5471` | candidate | counters |
|---|---|---|---|
| `30-vars/problem__026` | sat, 77 ms | sat, 70 ms | identical |
| `30-vars/problem__011` | sat, 17 348 ms | sat, **15 673 ms (−9.7 %)** | identical (Decisions/Propagations/Conflicts) |
| `prp-3-18` | unsat, 14 ms | unsat, 13 ms | identical |
| `45-vars/problem__022` | timeout-cap | timeout-cap | identical |

## Verification bar

(see the landing commit message for the executed values)

* `cargo build --all-features` — clean.
* `cargo nextest run --workspace --all-features` — green (the
  `scope_rebase`/`bv_odd_width` cells are the documented load-flake
  class; isolated re-runs before believing a failure).
* clippy `-D warnings` / fmt / rustdoc — clean.
* `./bench/z3_parity/run_parity.sh` (z3 4.16.0) — 176/177, 0
  disagreements (the standing result).
* `./bench/perf_gate/run_gate.sh` — conflicts/decisions 1.000/1.000
  (bit-identity canary).
* fixed-seed survey `gap_survey.py` seeds 20261000–02 × 600 — exactly
  `i129` (the documented simplex-tail cell), no silent drops.
* new pin: `substitute_row_ff_division_first_walk_matches_naive_chain`
  (four shapes: stabilized-g, mid-walk residue, early exit, wide
  operands) alongside the standing seeded grid and the born-row pin.

## Negatives recorded (do not retry blind)

* **Chain order (smallest-magnitude-first or full sort): −1.3 % cost
  proxy, firstkill 4.8 %** — the exit fires at the walk's end; ordering
  cannot move it.  Measured dead on both shadows.
* **The Bareiss carried divisor as a SHORTCUT** (skip the chain when a
  structural candidate divides everything) is unsound as a skip: a
  verified divisor is only a LOWER bound on the true g; concluding
  equality needs the same walk.  The structure is real (80 %) but its
  only sound use is exactly the division-first walk built here — the
  candidate is discovered as `g0`/stabilized `g` and the remaining
  steps confirm it at one division each.

## Verification on the LANDING tree (main moved mid-session)

Main advanced `faaf5471` → `1255312e` while this session ran (the
simplex-family retirement `2a7dc324`, the deep-split deletion
`867d9b68`, the parse arc).  The walk's region (`simplex/mod.rs`) was
untouched by all of it — the net patch applies cleanly.  Rebuilt pair
(main tip vs main tip + this change), full re-verification:

* four probes: identical verdicts and IDENTICAL counters (011/022 at
  the 45 s cooperative cap — see the note below; 026/prp-3-18 normal);
* perf gate: conflicts/decisions **1.000/1.000**, PASS;
* fixed-seed survey (`gap_survey.py` 20261000–02 × 600 on the
  faaf5471-pair candidate): **exactly `i129`**, no silent drops;
* parity on the landing tree: see the landing message.

**Observed in passing, NOT caused by this change** (counters identical
between base and candidate on every probe): `problem__011` moved from
`sat`/~17 s (at `faaf5471`) to `unknown` >100 s (at `1255312e`) under
the intervening landings — the churn cell's trajectory changed
somewhere in `2a7dc324`/`867d9b68`/parse arc.  This belongs to the
simplex-family retirement's post-landing audit (their handoff's own
discipline); flagged here with binaries: `precompile/19391786/nixie`
(this tree) vs any `faaf5471`-era binary.
