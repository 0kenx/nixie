# Delayed watch moves inside the complete-list propagation engine

## Registration

Continue closing the wall/cycle gap against Kissat from promoted `ade512da`.
Its release binary is byte-identical to the measured `f5e75a7` prototype
(SHA-256 `69c731e4351f91ae1680df81abf527c11afb096065b800e7854f8c8e5d1cd70a`).
The existing noL profile places 55.31% of sampled cycles in watch scans.
Destination appends still keep a vector directory live and can allocate
inside those scans. Sampled instruction locations do not measure removable
stall time.

The earlier delayed-move prototype flushed on every unit yield and paid a
capacity check and length update per queued move. Combine delayed moves with
the promoted complete-list session: reserve scratch space before entering a
list, append through a bounded cursor, and flush once when the list finishes
or conflicts. The local reference is Kissat `src/proplit.h`'s delayed stack
and FIFO flush. Preserve Nixie's eager normalization, true-tail parking,
first undefined replacement, assignments, reasons and scheduling counters.

Keep a reusable buffer of uninitialized move slots with WatchLists. Its
capacity is physical scratch, never logical solver state: clones start empty,
snapshots do not retain entries, and no raw cursor survives a list. Reserve
at least one slot per input watcher. The scan visits each watcher once and
queues at most one move per visit, so appending cannot reallocate or overrun.
Only the initialized prefix may be read during flushing. Report the scratch
capacity in terminal memory diagnostics.

A replacement is undefined when selected, while the currently watched
literal is false; its destination cannot be the active list. Internal
assignment reads neither destination lists nor the scratch records. Flush
all moves in FIFO order before processing the next trail literal or returning
a conflict, preserving destination-list order and the unvisited conflict
tail. Existing LRAT/HBR/observer paths retain their complete fallback.
These arguments apply equally when the SAT engine runs inside CDCL(T).

Inspect portable Rust 1.96.0 / LLVM 22.1.2 perf assembly before measurement,
using frozen lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Check that destination indexing/growth and scratch capacity checks leave
the scan. Price the extra 12-byte records (16 bytes with observer identity),
flush work, reserve checks, return-value storage and any new register spills.
Do not equate a smaller scan with a full-run improvement or sweep inline
annotations. Default/all-feature SAT tests, doctests, strict SAT Clippy,
formatting and focused strict-provenance Miri precede cost. Extend the exact
scalar oracle with move bursts followed by units and conflicts, repeated
destinations, buffer reuse, clone/snapshot/relocation and Rayon ownership.

At most **three new cost cells**, in order noL, crn, j3037, plus **one noL
cycle/LBR diagnostic**. Reuse controls `248bb59f9b9d9308`,
`625816f9fef3d493`, `ac690061cdf2abbe` from the byte-identical promoted binary;
do not substitute old sweep-OFF or pre-promotion controls. Reuse the existing
requested Kissat 4.0.4 reference cells; no new reference runs or cost repeats.

Use CPU15 Atom, seed 0, CaDiCaL preset, NIXIE_SWEEP=1,
NIXIE_DEFINITIONS=0, MAXC=10000000, PRINT_MODEL=1, cleared study overrides,
portable release, warmed input/binary and anonymous tmpfs output. GNU time
1.10 covers the complete target. Group user cycles/instructions/branches/
misses, with a 300-second cap, >=99.9% PMU coverage, zero major faults,
<=5% off CPU and audited constrained threads. No owned build runs during
cost. Hardware instructions cover the extra memory operations; unchanged
semantic counters alone do not price the new queue. Verify exact complete
stdout and independently check SAT models; unchecked UNSAT remains unknown
in the result store. Save each start/completion and canonical record once.

The diagnostic uses period 10472903, explicit CPU samples, grouped user
cycles/instructions and LBR. Require >=1000 resolved samples, >=99.9% PMU
coverage, zero lost/throttled records and <1% unresolved self weight; no
additional user-mode-IP threshold. Its elapsed time is not a replacement
cost cell. Retain a flamegraph separating scan, buffer and flush work.

Report per-input and aggregate instructions/cycles/wall, completion counts,
memory and the limitations of cached controls. The original study's 3%
per-input wall veto is not reinstated. Apply the repository's productive-step
and enablement rules: a demonstrated component improvement can be useful
with neutral end-to-end results, subject to structural soundness, complete
fallbacks and fresh differential qualification. Clear added cost without
a compensating improvement is a negative finding to archive and diagnose.
Full workspace build/tests/doctests/Clippy/fmt/docs and installed Z3 4.16.0
parity remain required before promoting solver code. This is an execution
change under exact trajectories, not a heuristic or seed-selection study.
