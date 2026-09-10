# Kissat assign-time watch-list prefetch

Kissat `inlineassign.h` prefetches `WATCHES(not_lit)` when assigning `lit`,
so the later scan of that list can overlap remaining work. Nixie's earlier
negative prefetch result prefetched *clause payloads during the visit*;
this is a different address, issued at assign, matching Kissat locality 1
(`_MM_HINT_T2`). Empty lists are skipped. Solver state is unchanged.

Prefetch the assigned literal's long-watch `Vec` and, for binary
assignments, its BIG primary span and overflow vector.

## j3037 identity screen

CPU 15, seed 0, CaDiCaL preset, `NIXIE_SWEEP=1`, `NIXIE_DEFINITIONS=0`,
`MAXC=10000000`. Input `j3037_10_mdd_bm1`. Control is Gent `cc6d3e1e`.
Complete stdout search counters are identical (366030 conflicts, 1011819
decisions, 344033227 propagations, 30687 restarts). Both arms UNSAT.

| Arm | Wall s | User s | Off-CPU | Invol |
|---|---:|---:|---:|---:|
| Gent `cc6d3e1e` | 46.34 | 45.93 | 0.73% | 481 |
| Prefetch | 41.75 | 41.52 | 0.36% | 359 |

Wall 0.901× and user 0.904× on this one input, one seed, sequential
window. Not a corpus claim. Kissat retained context remains 18.04 s
(~2.3×). SAT lib all-feature tests (822) and Clippy `-D warnings` pass.
