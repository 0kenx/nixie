# Gent saved-position re-screen at 5 seeds: the landing validated (2026-09-12)

The tails campaign's remaining discipline item: the Gent saved-position
watch-scan landing (`cc6d3e1e`) was screened single-shot per file (4 arms
× 54 files, 2026-09-11) — predating the 5-seed discipline.  The recorded
one-line revert is `saved_pos_tail_start → 0`.  This re-screen ran the
revert arm at 5 seeds (worktree build at `67b02c80` + the flip,
`dirty: true` in the records) against the standing baseline.

## Result: keep Gent, decisively

| | Gent-ON (default) | Gent-OFF |
|---|---|---|
| solved (seeds 0–4) | **180** | 174 (−6) |
| conflicts geomean (n = 99) | 1.000 | **1.1168** (+11.7 %) |
| verdict disagreements | — | 0 |

The original single-shot screen's verdict (−5 solved then) reproduces at
5 seeds.  Per-file: x9-09054 3→0, mp1-Nb7T42 4→3, rbsat 4→3,
frb45 1→0, mdp 2→0, 700gates 1→0, stable-300/frb65 −1 each; the only
meaningful winner is circuit_64in64out (0→3 — trajectory chaos on the
class where any mass-removing perturbation compounds, the same signature
as every amplitude arm).

The watch-scan position optimization is a real, reproducible default-on
win (+6 cells, −10.5 % conflicts vs off).  Debt closed: the
single-seed-screened landings ledger is now empty.

Cells: `precompile/67b02c80/benchmark/runs/sc24f/` (config `gent-off`,
270 cells, all verified).
