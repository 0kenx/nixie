# The per-final-check theory resync: never fires, 2/3 of UF+arith theory cost — and why removing it does not (yet) land

Date: 2026-09-10
Scope: UF+arithmetic combination throughput (the #1 ranked target of the
QF timeout profile: 39/101 differential timeouts in QF_UFLIA/QF_UFIDL/QF_ANIA).
Baseline: `7fe833c1` (main, includes the GMI cut sign fix landed the same day).

## The finding (measurement)

`TheoryManager::final_check` runs `resync_theory_state` — a full
reset+replay of EUF + arithmetic + DL (+ embedded BV state) from the
deduplicated shadow trail — on **every final check of every UF-bearing
problem** ("the incremental EUF state can lose a congruence or
disequality").  Instrumented counters over the 270-file differential
sample (z3-solvable, 10 s cap):

| family instance | final_checks | resyncs | resync atom-replays | backstop conflicts |
|---|---|---|---|---|
| QF_UFLIA hash_sat_05_06 | 6 302 | 6 301 | 4.59 M | **0** |
| QF_UFLIA xs_25_25 | 2 353 | 2 352 | 2.81 M | **0** |
| QF_UFIDL vhard7 | 1 346 | 1 345 | 1.78 M | **0** |
| …all 270 files | ~50 k | ≈final_checks | ~40 M | **0** |

The backstop's *conflict* channel never fired once: across the whole
corpus, the incremental checks (DL `check`, `euf.check_conflicts`, array
axioms, `propagate_euf_equalities_to_arith`, `arith.check`) found every
conflict first.  The replay volume dominates `process_constraint` calls
(~2/3) and drives the simplex rebuild cost (`intern_row`, `crash_basis`,
`make_feasible`) — the top of every UF+arith profile.

## The premise audit (per-layer differential fuzzers)

Three incremental-vs-replay differential fuzzers were built (all landed):

* `euf_incremental_matches_replay_fuzz` — partitions + conflict verdicts,
  40 seeds × 3 000 ops.  **No divergence**: the e-graph's push/pop undo
  trails are faithful.
* `arith_incremental_matches_replay_fuzz` — verdicts, 30 seeds × 2 000
  steps.  **Found a real bug instead**: the GMI cut continuous-branch
  sign error (`-bar_a / f0` where `bar_a / f0` is required) — a false
  `unsat` on a satisfiable four-constraint system (landed fix
  `7fe833c1`, with a boxed-witness brute-force oracle test
  `arith_verdicts_match_bruteforce_oracle` that now also verifies the
  solver's own `value()`s satisfy every live constraint on `Sat`).
* `dl_incremental_matches_replay_fuzz` — DL verdicts, 30 × 2 000.  **No
  divergence**.

So the resync's stated premise (incremental divergence) has no supporting
evidence at any theory layer; what it actually does is rebuild a FRESH
tableau basis per final check — pure trajectory shaping.

## The removal experiments (all reverted)

Four variants were measured on the 270-file differential (10 s cap;
baseline 169 solved, all with **0 soundness disagreements**):

| variant | solved | xs_8_13 (pinned regression) | notes |
|---|---|---|---|
| baseline (resync kept) | 169 | unsat 2.5 s | |
| + GMI fix only | 167 | unsat 2.7 s | rings lose the invalid cuts |
| resync removed, snapshot-pop kept | 161 | unsat 4.8 s | column bookkeeping (15 %) emerges |
| resync removed, DdM bounds-only pop | **171** | unsat 16 s → **regression test times out** (180 s budget, test profile) | xs_15_15 3.6× faster; QF_NIA +5 |
| … + row GC (sweep boundless rows > 1 024/check) | worse | > 120 s | per-check cut re-intern churn |
| … + row GC + live-cut cap 512 | worse | > 150 s | B&B starves without fresh cuts |
| … + rare GC (> 4 096) | mixed | > 45 s | |
| … + scope-bound row lifecycle (drop rows interned in the popped scope) | worse | 15.5 s | xs_15_15 regresses to timeout |

Root cause of the fragility, mapped precisely:

1. **Rows are permanent** (`intern_row_cached`; "a row without bounds
   constrains nothing").  Without the per-final-check reset, Gomory-cut
   rows and retracted-branch atom rows accumulate for the whole search —
   measured 430 → 9 300+ live rows over 8 s on xs_8_13 — and every
   `check`/pivot pays for the history (`pivot` 28 %, `make_feasible` 7 %
   of cycles; `find_violating` is O(rows)).
2. The old **basis snapshot-restore in `Simplex::pop`** accidentally
   bounded this (in-scope rows died with the restore) — but its cost is
   an O(tableau) clone per mutated scope that shares every column `Arc`,
   turning each in-scope column edit into a full column clone
   (`column_drop_known` 12 % + `Arc::make_mut` 5.5 % once the resync no
   longer keeps tableaus small).
3. Cut rows want to **persist** (content-addressed re-derivation hits the
   cached, already-substituted row) while dead atom rows want to **die**;
   every uniform policy (sweep-all, cap, scope-drop) helped one family
   and hurt another — the search trajectory is coupled to the basis
   history far more strongly than to any of these policies.

The DdM-pop variant (171 solved, PAR-2 2 057 vs 2 117) is the best corpus
result measured in this session — but it breaks
`int_case_split_determinism_regressions::wisas_xs_8_13_*` (the in-process
solve exceeds the test budget), so per the verification bar it does not
land.  A candidate that recovers xs_8_13's speed without the resync needs
to reproduce not just the *bounded tableau* but the *basis-reset
trajectory* of the old rebuild — e.g. periodic basis re-canonicalization
at restart points, or exporting effective cuts as CDCL lemmas so the
tableau never carries them.  Both are real designs, not knobs; neither
was attempted here.

## What did land

* `7fe833c1` — GMI cut sign fix + EUF/arith fuzzers + oracle
  (a genuine false-`unsat` soundness fix, found by the premise audit).
* This commit — the DL fuzzer + the `value()`-consistency half of the
  arith oracle (test-only).

## Verdict

The resync backstop is **2/3 overhead with a 0-firing conflict channel**,
but it is load-bearing as trajectory shaping: removing it nets +2 solved
at the corpus level while breaking a pinned soundness-shape regression
beyond its budget.  Reverted; the map above (row lifecycle, basis
restore, cut-as-lemma export) is the follow-up surface.
