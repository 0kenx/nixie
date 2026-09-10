# j3037 after stale-watch repair and miss-path folds

Screen of current HEAD against ghost-flush `bfa6570b` on
`j3037_10_mdd_bm1`, CPU 15, seed 0, CaDiCaL preset, sweep on,
definitions off.

Search counters are identical: 347882 conflicts, 963791 decisions,
330590727 propagations, 698296203 ticks. Both UNSAT. The stale-watcher
XOR guard and later miss-path folds do not change this trajectory.

| Arm | Wall s | User s | Vol/invol | RSS KiB |
|---|---:|---:|---:|---:|
| Ghost flush `bfa6570b` | 40.40 | 40.15 | 6 / 374 | 34092 |
| HEAD | 44.05 | 43.60 | 235 / 232 | 34800 |

Wall is not a throughput claim: HEAD paid 40× more voluntary switches.
Kissat retained context remains 18.04 s. One seed.
