# AVX2 blocker-certificate generation: registered cost screen

The scalar window-certificate prototype was rejected: constructing masks and
maintaining its scan cursor cost more than the avoided blocker checks. This
tests a different implementation of mask generation, using AVX2 gathers on
the available Intel Core Ultra 7 265K. It is not a window-width search or a
claim that the prior scalar prototype worked.

## Mechanism and safety contract

Keep its fixed sixteen-watcher window and exact positive-only certificate
semantics. Generate two eight-lane masks by gathering blocker values and
testing each low byte for +1. Read blocker codes through ordinary Rust field
access, without assuming the layout of Watcher. Retain certified positive
runs in original order; every non-certified watcher still executes the
original scalar check, since earlier propagation may have changed it.
Certificates never survive list exit, conflicts or backtracking. Preserve
arena normalization, compaction, conflict tails, observer events and ticks.
Kissat `src/proplit.h` is the reference for the blocker-before-payload rule.

The gather reads four bytes starting at each literal's value byte. Keep the
value vector's logical length unchanged and explicitly initialize at least
three spare bytes after every creation/growth path. No uninitialized or
out-of-allocation read is permitted. Audit both assignment entry points,
resize, clear and backtrack. Signed gather offsets require every code to fit
i32; use the original scalar kernel for larger variable domains. Dispatch
once per propagation call after runtime AVX2 detection, with a scalar fallback
on unsupported architectures. Debug checks and exhaustive mask tests cover
the lane, index, padding and positive-only contracts.

The ordinary scalar kernel remains a test oracle. Compare actual clause
payload and metadata, trail/watch state, models and LRAT transcripts in
paired solves. Exercise certified runs across units, moves, deletion,
compaction, stale zero-to-true/false changes, conflict tails, partial windows
and backtracking. Independently check small models and UNSAT proofs.

## At most four new cells

Pin a clean committed control based on main `c7f3d93` and its direct-descendant
candidate. Build both with the same ordinary release flags/compiler/lockfile;
no global native-CPU or AVX2 build flags. The runtime-dispatched candidate is
the artifact being measured. Archive both binaries and exact build metadata.

Run circuit scalar then candidate, seed 0, MAXC=40000, CPU 10, CaDiCaL preset,
`NIXIE_SWEEP=0`, model output enabled and other study overrides cleared.
Stop unless cycles/conflict falls by at least **5%**, whole-process user
instructions do not increase, and complete stdout is byte-identical.
Only after passing run j3037 candidate then scalar with the same settings.
Final advancement requires geometric-mean cycles/conflict <= **0.95**,
geometric-mean instructions <= **1.00**, neither input's cycle ratio > **1.03**,
and all identity/correctness gates. No inline, width or dispatch tuning after
the first cost cell. Hardware events require one active PMU and >=99.9%
event scheduling coverage; report branches/misses, verdicts, conflicts and
secondary wall time. Record/reuse every cell once, with a 300-second emergency
timeout that cannot justify a repeat.

This is an early rejection screen, not a broad performance claim. Budget
Unknown is an unsolved prefix, not a certified verdict. A passing candidate
still needs full workspace build/nextest/doctests/clippy/fmt/docs and fresh
Z3 parity before production landing. A failed candidate is archived, removed
from the checkout, and recorded here on main. The overall Kissat gap remains
the objective.
