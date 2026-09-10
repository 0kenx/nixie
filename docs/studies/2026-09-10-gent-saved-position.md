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
device`). Wall/Kissat screens were not run under that host load.
