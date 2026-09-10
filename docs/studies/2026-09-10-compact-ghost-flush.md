# Flush deleted long-watchers at arena compact

Kissat `collect.c` drops garbage watches while rewriting the arena. Nixie
kept deleted hits as tombstone watchers so the next scan would compact
them lazily. That is the suffix garbage-flag path in the delayed-move
profile.

At compact, drop deleted watchers in list order and record the count as
`ghost_debt`. The next propagate of that literal charges
`len + bin_phantom + ghost_debt`, then clears the debt. That was meant to
match lazy tick accounting. On j3037 it did not: search counters moved.

## j3037 vs prefetch `a7397124`

CPU 15, seed 0, CaDiCaL preset, sweep on, definitions off. Both UNSAT.

| Arm | Wall s | User s | Off-CPU | Conflicts | Ticks |
|---|---:|---:|---:|---:|---:|
| Prefetch | 41.75 | 41.52 | 0.36% | 366030 | 725.4M |
| Ghost flush | 39.72 | 39.47 | 0.38% | 347882 | 698.3M |

Conflicts 0.951×. User per conflict is unchanged (~113.5 µs). This is a
search-path change, not a throughput win. One seed; no matched null.
Kissat retained context 18.04 s (~2.2×). SAT lib 823 tests and Clippy
pass. Production still never visits a deleted header after compact.
