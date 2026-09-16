# Handover update: the `wisas_xs_8_13` unknown's SECOND layer is the simplex wide-row propagation (`24cb0567`) — 2026-09-15, third session

Supersedes the "current main has evolved / surface unknown" reading of
[`2026-09-15-wisas-xs-8-13-unknown-regression.md`](2026-09-15-wisas-xs-8-13-unknown-regression.md).
That handover's layer 1 (the merge-era `add`-loses-its-Vec-write) was real
but was already fixed by `0aa996f2` ("revert: restore nixie-sat to b05d949e
— e987b4b6 accidentally landed the B′3 bisection arms"). What keeps
`wisas_xs_8_13` at `unknown` on today's `main` is a **second, independent
regression in the simplex**, isolated below with clean worktree rebuilds.

## The main-line story, clean-rebuild verified

| commit | verdict (3× each, deterministic) | role |
|---|---|---|
| `d4b72e2c` | `unsat` | good parent (sets model synthesis) |
| `d832b82e` | `unsat` | sets intersection-sharing fix — **exonerated** |
| **`24cb0567`** | **`unknown`** | **feat(simplex): wide-row bound propagation (slice 6, round three) — FIRST BAD** |
| `83b985a6` … `main` | `unknown` | carries it to the present |

`24cb0567`'s diff: +538 lines in `nixie-theories/src/arithmetic/simplex/mod.rs`,
+29 in `arithmetic/solver.rs` (`propagate_bounds` → `propagate_bounds_in(&int_vars)`).

## Why the commit landed with failing guards

Its own message says: "suites green **except the pre-existing wisas pair
(fixture-level Unknown, verified on the parent)**". The parent is `unsat`
(clean rebuild above) — the "verified on the parent" check must have run a
stale binary or a dirty tree. The same trap bit this investigation:

**`precompile/d832b82e/nixie` answered `unknown` but a clean rebuild of
`d832b82e` answers `unsat`** — a cached binary disagreed with its own commit.
The cached copy has been replaced with the clean rebuild. Treat any cached
precompile binary that disagrees with its neighbors as unverified until
rebuilt.

## Probes on current `main` (`cd544511`)

| probe | result |
|---|---|
| plain | `unknown` (canary silent — layer 1 is gone) |
| `NIXIE_S6_NDIR2=1` | no verdict within 180 s (worse, not rescued — so wisas is NOT the commit-message's "chain-sat twin trades to unknown" NDIR2 trade) |
| `NIXIE_S6_AUDIT=1` (corner-enumeration auditor) | `unknown`, auditor silent — no fabricated-corner complaint on this instance |

Search signatures (fixture, release):

| | conflicts | restarts | decisions | time |
|---|---|---|---|---|
| `d4b72e2c` (`unsat`) | 2 866 | 455 | 157 173 | 0.9 s |
| `24cb0567` (`unknown`) | 1 899 | 31 | 158 601 | 2.8 s |

Same decision volume, ⅓ fewer conflicts, 1/15 the restarts, 3× slower: the
propagation's per-final-check cadence interacts with the search loop, and the
`refine_int_case_split` path no longer closes. **Open question for the
simplex owner (marked "recorded for the next round" in the commit):** does
direction-1 propagation change what `ArithSolver::lp_int_bounds` /
`compute_int_bounds` feed `refine_int_case_split` (lemma starvation →
completeness loss), and is the `[ceil(min), floor(max)]` superset guarantee
(`"the case-split never excludes a reachable value"`) still intact under the
new wide-store derivations? A narrowed range would be a **false-UNSAT**
risk, not just incompleteness — the auditor staying silent on this instance
is weak evidence only.

## Reproducer & artifacts

```bash
nixie nixie-solver/tests/fixtures/wisas_xs_8_13.smt2     # unsat (z3-certified); main says unknown
cargo nextest run -p nixie-solver --test int_case_split_determinism_regressions
```

Clean-rebuild binaries now cached: `precompile/{d4b72e2c,d832b82e,24cb0567}/nixie`
(`d832b82e`'s replaced). 181-binary sweep (pre-fix era, some entries stale —
see the trap above): `precompile/cd544511/benchmark/wisas_verdict_sweep.txt`.

## Unrelated note from the same session

`bv_odd_width_blast_differential::odd_width_identity_pairs_hold` passes in
**445 s (release)** — it and `recfun_e2e::symbolic_argument_solves_for_the_variable`
are slow-but-correct tests exceeding nextest's 180 s cap (verified at load ~9,
not a hang). They need a slow-profile annotation or cap bump, not a fix.

## Second casualty found (2026-09-16, same commit): the recfun refinement loop diverges

`24cb0567` has a **second, still-live victim** that never recovered
(unlike `wisas_xs_8_13`, which the CSR-mirror fix incidentally restored):

```scheme
(define-fun-rec sum ((n Int)) Int (ite (<= n 0) 0 (+ n (sum (- n 1)))))
(declare-const k Int)
(assert (and (>= k 0) (= (sum k) 6)))
(check-sat)(get-value (k))
```

Expected: `sat` with `k = 3` (the recfun_e2e test
`symbolic_argument_solves_for_the_variable` — its doc: "the certifier
computes `sum` at the rejected model's `k`, and those concrete instances
rule that `k` out").  Measured via cached binaries, 30 s cap:

| commit | verdict |
|---|---|
| `82c3c926` (09-14 09:49) | `sat` in **0.94 s** |
| `d49c8936`, `0d3d2378`, `5bf4d1a1` | `sat` |
| **`24cb0567` → current `main`** (including `80a0cee8` pinned-D2 default-ON and the wide-driven repair) | **timeout** |

The in-suite test hangs **30+ minutes standalone** (killed at the 180 s
nextest cap) — this corrects the earlier note in this file that grouped
it with `odd_width_identity_pairs_hold` as "slow-but-correct": only
odd_width is; recfun is this regression.  Same handoff question as
wisas: what does the wide-row propagation feed the refinement/certifier
path — here likely the model-rejection loop (concrete `sum` evaluations
that should rule out each rejected `k`) never converges.

Reproducer: `/tmp/recfun.smt2` body above; any cached binary pair
(`82c3c926` vs current) demonstrates it in under 30 s.

## Answer to the recfun question (2026-09-17, the simplex owner)

Decoded end to end (study continuation 27, item 62): the propagation
feeds the refinement path NOTHING wrong — the certifier, the learning,
and the blocking all behave; its only role was trajectory reshuffling
onto a pre-existing treadmill.  The treadmill: the unfolding's boundary
app is SYMBOLIC (`sum (k - d)` follows `k`), so learning CONCRETE
applications never constrains the chain — every round's model escapes to
the truncation edge (measured `k = 7, 11, 8, 16, 32`, always the fuel
boundary), the certifier refutes, learning lags forever.  The
pre-24cb0567 solve certified at round 3 by proposing an interior `k=3` —
luck.  Fixed driver-side (sound assumption-scoped probe inside the
pinned range; a certified model there is a genuine `sat`): the
reproducer answers `sat (k=3)`, and the suite timeout is gone.  The
`24cb0567` casualty list is now empty.
