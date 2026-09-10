# Gent saved-position scan (CaDiCaL `pos` / Kissat `searched`)

## Why this lever

The delayed-move kernel still spends most of its samples in long-watch
scans. Both reference solvers already skip a known-false tail prefix:

- CaDiCaL `src/propagate.cpp` stores `clause->pos` (Gent JAIR'13)
- Kissat `src/proplit.h` stores `c->searched`

Nixie always restarted at `lits[2]`. The 12-byte header pin deferred the
port (`2026-09-propagate-write-elision.md`). Activity already moved out;
`lbd` saturates far above every consumer's ≤10 threshold, so it shrinks
to `u8` and the freed byte holds `searched`. Slot geometry stays 12 bytes.

## Semantics

Match CaDiCaL's parking BCP, not Kissat's "move even if the replacement
is true":

1. Initialize `searched = 2`.
2. On a miss whose other watch is not true, scan `searched..end`, then
   wrap `2..searched`. The wrap-around is the soundness argument: an
   unassigned literal skipped after backtracking is still found.
3. On a non-false hit, store `searched = min(index, 255)`. Longer clauses
   still wrap through the low tail.
4. True replacement: park and refresh the blocker (CaDiCaL). Undefined:
   move the watch. All-false: unit or conflict.
5. Shrink resets `searched` to 2 only when it would fall off the new size
   (CaDiCaL `shrink_clause`).

This changes replacement choice, so it is not trajectory-identical. It is
a missing reference procedure, not a new heuristic. LBD values above 255
saturate; tiering thresholds are ≤10. The debug LBD invariant compares
against the clamped stored width.

## Tests

Arena layout, init, shrink reset, wrap-around hit, and a kernel move that
parks the unassigned tail literal. Session, yield, and observer loops share
`find_saved_pos_hit`, so the exact-state oracle still compares them.

`nixie-sat --all-features` lib + integration tests pass (820 lib tests).
SAT Clippy `-D warnings` and `cargo fmt` pass. Workspace nextest could not
be completed: the shared disk filled during the compile (`No space left on
device`).

## j3037 engineering screen (one seed)

Release `stats_solve` SHA-256 `1718019716a0d2d9975778836e7161ece7f368eb0e9835b1c69e75b9aa1d7470`
cached at `precompile/cc6d3e1e/`. Control is delayed-moves landing
`51f8f19e` SHA-256 `1cecaf3a8a007d3ac99b66398ba7f44159d24efb9f296ebe56d266f9840eebd3`.
CPU 15, seed 0, CaDiCaL preset, `NIXIE_SWEEP=1`, `NIXIE_DEFINITIONS=0`,
`MAXC=10000000`, `PRINT_MODEL=1`. Input
`satcomp2024/bench/07e6413459f92b613498a719125b6239-j3037_10_mdd_bm1.cnf`.
Both arms report UNSAT. No Kissat rerun; retained requested-mode context
is 18.04 s.

| Arm | Wall s | User s | Off-CPU | Conflicts | Ticks/conflict | User µs/conflict |
|---|---:|---:|---:|---:|---:|---:|
| Control `51f8f19e` | 48.13 | 47.42 | 1.27% | 369688 | 2060 | 128.3 |
| Gent `cc6d3e1e` | 63.78 | 53.92 | **15.2%** | 366030 | 1982 | 147.3 |

Candidate wall fails the ≤5% off-CPU gate (8251 involuntary switches).
Conflicts 0.990× and ticks/conflict 0.962× are a single-seed search-path
observation, not a matched-null result. User time per conflict is 1.15×
the control in this window and cannot be attributed with the quality
failure. Kissat remains ~2.2× faster on the retained 18.04 s cell.
No further cost cell was started after the failed wall gate.
