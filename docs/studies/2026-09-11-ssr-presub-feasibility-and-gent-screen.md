# Pre-search SSR feasibility gate + Gent saved-position screen (2026-09-11)

Follow-up to [Z3 LUT-cube SSR](2026-09-10-z3-lut-ssr-presearch.md). The 3-arm
mini bench (`51f8f19e` vs `6435c0fe`, DIMACS arm) flagged two regressions:
`si2-b03m-m800-03` wall 2.7 s → 9.6 s ("conflicts dropped but wall exploded"),
and `noL_11_14` sat-in-43 s → timeout. Fresh-build bisect over the 35-commit
window found **two independent culprits**:

1. **`cc6d3e1e` (Gent saved-position watch replacement)** — the entire noL and
   summle regression. Reverting only the scan start (`saved_pos_tail_start` →
   always 0, HEAD kernel otherwise) restores both **bit-exactly**
   (noL 1,727,396 conflicts sat in 47 s; summle 42,511 vs 87,248). This is CDCL
   trajectory chaos of a net-winning change, not a port defect (the port was
   re-checked against CaDiCaL `propagate.cpp` / `clause.cpp` `pos` semantics:
   always-save-on-hit at the hit index, park on a true replacement, `pos = 2`
   on re-allocation).
2. **The pre-search SSR+probe cluster (`6b05e22b`+`fb371731`+`079c9456`)** —
   the si2 wall explosion. The pass legitimately fires there (97 % of si2's
   long clauses have min-literal occurrence > 100, the exact premise that
   CaDiCaL one-watch subsumption never connects them), but round 0 hits the
   flat 1e8 check cap after 7.2 s — a **truncated partial round** — then the
   probe adds ~0.9 s, to save 19 % conflicts (~1 s of search).

## Bisect gotcha: stale precompile binaries

`precompile/bfa6570b…/stats_solve` was **stale** (built from a different tree):
it showed si2 26,938 conflicts / 1.9 s, while a fresh build of the same commit
gives 18,928 / 31.8 s with 2.1 M self-subsumed. Every bisect step in this
study re-built from source; cached `stats_solve` binaries were used only after
cross-checking one cell against a fresh build.

## Gent keep/revert screen (4 arms × 54-file standing corpus, 60 s cap)

| arm | solved / 54 | conflicts geo vs HEAD | verdict mismatches |
|---|---|---|---|
| HEAD | 40 | 1.00 | — |
| HEAD + Gent scan off | **35** | 1.21× worse (sat 1.33×) | 0 |
| HEAD + SSR feasibility | 40 | 1.008 (neutral band) | 0 |
| both | 37 | 1.21× | 0 |

Gent-off loses `circuit_48in64out` (44.9k → 140.6k), `qwh.50` (32k → 134k),
`af-synthesis`, `g2-slp`, `mp1-klieber` (timeouts) while recovering summle /
Break_08_24 / shuffling / pb_300. **Verdict: keep Gent.** noL/summle are
recorded chaos losses of a change that is +5 solved on the corpus; if a later
multi-seed A/B reverses this, the revert is a one-line flip
(`saved_pos_tail_start → 0`).

(One screen cell was a flake: `worker_550` timed out in the feasibility arm
under 20-way load, but is bit-identical solo in both arms — 10,011 conflicts,
6.6 s. SSR never fires on it.)

## The fix: run-to-completion or skip

`backward_subsume_round` now has an exact feasibility projection: for every
sched-eligible original clause, the two polarity occurrence-list sizes of its
minimum-occurrence literal (the two lists the round scans) — O(total
literals), one flat counter array, mirroring the round's construction so the
round can only stay under it. When the projection exceeds the existing
`PRESEARCH_SSR_CHECK_CAP` (1e8 pair checks — the same constant that previously
truncated), the **whole pass** (rounds and the follow-up probe) is skipped.
`NIXIE_PRESUB=1` (explicit force) bypasses the projection.

Why skip rather than truncate: a partial round is the measured-worst regime —
[the LUT SSR study](2026-09-10-z3-lut-ssr-presearch.md) showed extra rounds and
partial flattening are trajectory-negative, and si2 paid 8 s for a partial
flatten that never amortized. Cells where the round completes are untouched.

| file | projection | behavior |
|---|---|---|
| `circuit_48in64out_700gates` | 4.5e7 (completes in 3.4e7) | runs — 44,894 conflicts, unchanged |
| `si2-b03m-m800-03` | 3.4e9 | skips — 26,938 conflicts, wall 9.6 s → **1.65 s** (beats kissat 2.2 s) |
| `circuit_64in64out_8in5out` | 3.5e9 | skips — timeout both arms at HEAD |

Corpus-wide, the fix changes exactly one cell (si2); all other 53 files are
conflicts-bit-identical to HEAD. The candidate-list `Vec` clone per clause
pair was also removed (the occurrence lists are frozen during the scan) —
trajectory-identical, multi-GB less memcpy on forced runs.

## Verification

- `nixie-sat` full suite + workspace `nextest --all-features`: 10,928/10,928.
- Clippy `-D warnings`, fmt, rustdoc `-D warnings`: clean.
- Z3 parity 4.16.0: 175 files, **0 wrong** (1 inconclusive where Z3 itself
  returns Unknown), parity 100 %.
- New unit tests: `presearch_ssr_projection_hand_count`,
  `presearch_ssr_projection_bounds_round_checks`.

## Residual (not addressed here)

noL and summle remain worse than `51f8f19e` (Gent chaos, corpus-justified);
j3037/break/crn retain their pre-existing 1.3–2× conflict gap to kissat —
separate search work, not regressions of this window.
