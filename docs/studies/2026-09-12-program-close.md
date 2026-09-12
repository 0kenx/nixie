# The 2026-09-12 amplitude + restart program: session close (round 9)

The round-8 handoff listed four priorities.  All four ran to a measured
conclusion, and the follow-on questions they opened were chased to
closure — including two errata forced by better instrumentation.  This
is the map for the next session.

## What landed (default path)

- **ELS round: −0.90 % instructions on si2-b03m** (`6cdaea11`) — the
  trailing BIG rebuild was unconditionally redundant; the watch rebuild
  reuses its allocation.  Bit-identical (54/54 corpus files).
- **Diagnostic counters** (`81192b11`): the elim ballast anatomy
  (`added=/bw_retired=/otf_shrunk=` per round, `live_orig=` per phase).

## What landed as env-gated arms (all default-off = bit-identical, all
soundness-netted with differential tests + corpus verification)

| arm | mechanism | individual screen | with others |
|---|---|---|---|
| `NIXIE_OTFS` | analyze-time antecedent self-subsumption (`7c7c4623`, after the false-unsat root-cause) | 1.0160× | — |
| `NIXIE_EAGER_SUB` | newest-20 learned-clause subsumption per conflict (`4f51efd7`) | 0.9932× | — |
| `NIXIE_AND_GATES` | structural AND-gate elim recognition (`e0cc947e`) | +~900 vars on Timetable | — |
| `NIXIE_TIERED` | kissat per-mode schedule (`303771ef`) | 1.267× | — |
| **OTFS + EAGER_SUB** | — | — | **0.9645× super-additive; circuit_64in64out 0/5→5/5** |

The amplitude thesis is confirmed — the mechanisms reinforce — but the
aggregate stays short of the default-on bar (sched-vivon: 0.83×), and
every route to arming them adaptively is now **measured dead**:

- seven static features (dec/conf, LBD, restart cadence, clause/var,
  binary mass, duplicate fraction, width stats) — all interleave the
  winner/loser classes (`2026-09-12-class-signature-exhaustion.md`);
- the online A/B probe — early-window deltas sit at 1.0 ± 0.15 for both
  classes; the advantage is a late-trajectory fact (same study, second
  postscript);
- five intervention families land on the same split (margin ladder,
  adaptive margin, tiered, OTFS, eager-sub) — the split is a trajectory
  fact, not a profile fact.

## The two errata (instrumentation forcing truth)

1. **The resolvent ballast never existed** — `num_original` counts
   additions but not elim retirements; live masses match cadical
   (1,648,558 vs 1,626,226 on Timetable).  The elimination economics
   are identical; the residual gap is phase-yield starvation.
2. **Binary subsumers have no mass here** (0–32 clauses/file) — cadical's
   `subsumebinlim` matters on other corpora, not this one.

## Validations landed

- Gent saved-position: **keep** (off = −6 solved, +11.7 % conflicts at 5
  seeds) — the single-seen-screened landings ledger is empty.
- Tails tranche 1: frb65/mp1-Nb7T42 convert at 10 seeds; mdp/mp1-klieber
  stay endurance files.

## Open items for the next session (in recorded priority)

1. **The elim phase-feeder** (Timetable class): candidate starvation
   between elim phases — cadical's denser inprocessing interleave
   (subsume phases −5.5k..−20k between elim events, transred, probing)
   feeds the marked sets.  Our pre-phase rounds yield 0.9–1.4k.  The
   OTFS+eager-sub pair is exactly this feeder when armed; a default
   candidate would need the interleave *schedule* itself rebuilt
   (denser, tick-budgeted) — a heuristic change needing the full screen
   + null machinery.
2. **Portfolio at wider caps**: the only remaining route to the
   circuit-class conversions in evaluations longer than the 60 s
   mini-bench.  Pure scheduling arithmetic; Phase-3's 60 s failure does
   not bind at 300 s+.
3. **CSR watch lists** (architecture): the ELS rewatching study showed
   the current `Vec<Vec<Watcher>>` structure makes local surgery
   entry-major and unprofitable; a CSR representation makes rebuild =
   memcpy and surgery = sorted splice.  Multi-session.

## Store state

`precompile/8082e335` (baseline, 290 cells incl. 10-seed tails),
`303771ef` (tiered), `7c7c4623` (OTFS), `4f51efd7` (eager-sub +
combination), `67b02c80` (gent-off) — all verdict-verified; runners
committed as assets under
`docs/studies/assets/inproc-amplitude-2026-09-12/`.
