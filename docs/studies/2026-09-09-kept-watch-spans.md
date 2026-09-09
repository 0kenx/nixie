# Compact consecutive kept watch spans

The [delayed-move experiment](2026-09-09-delayed-watch-moves.md) did not
close the wall gap: 8.88 s versus retained ordinary Nixie 8.81 s and
mode-matched Kissat 1.88 s. Its qualified profile prices queue preparation
and flushing at 5.14% while the scan bodies remain 51.28%. Keep the ordinary
implementation and change the compaction work itself, without a queue.

## Algorithm and invariants

Within the existing compaction suffix, defer copies of consecutive kept
watchers. Blocker hits need no immediate write; first/tail refreshes update
the visited source entry's blocker. On the next removed/moved watcher, copy
the pending kept span to the write position and begin a new span after the
hole. Flush the span before every Unit or Done return. On Conflict, copy
the pending span together with the untouched remainder, without reading its
blockers. Retain the existing no-hole prefix, eager arena normalization,
immediate destination appends and bounded prefix-to-suffix transfer.

For a pending source span `[start, end)`, maintain `write < start <= end`
in the suffix and `end <= watches.len()`. The destination ends at
`write + end - start <= end`, so it cannot overwrite an unvisited entry.
Overlap uses Rust's checked `copy_within`. Skip empty spans; copy a singleton
directly to avoid a dynamic memmove call for one entry; use `copy_within`
for longer spans. No allocation, scratch buffer, unsafe indexing or native
recursion is added. Before returning a Unit/Conflict, the pending copies
are complete, and the existing cursor state, watches, reasons and literal
order must be identical to the scalar oracle.

The reference semantics are the local Kissat `src/proplit.h` stable read/write
filter and the existing legacy Nixie loop. This is a different implementation
of that filter, not a change to propagation or watch choice. The old
[blocker-prefix batch](2026-09-07-bcp-blocker-batching.md) constructed masks
from speculative blocker reads and copied only true prefixes. Here all kept
paths join a span, with no mask, speculation or second predicate pass.

Extend the existing exact-state oracle with empty, singleton, overlapping
and long kept spans separated by single and consecutive holes; include
blocker hits, both refresh paths, deleted-but-satisfied hits, orientation,
Unit/Conflict/Done exits, unvisited tails, resumption and backtracking.
Retain the library's model/proof checks and observer-layout tests. Existing
scope/collection tests remain part of full qualification if the screen passes.

## Preflight and registered screen

Start from main `8fe2a71`, Rust 1.96.0 / LLVM 22.1.2, lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Portable release/perf profiles, no native/PGO/RUSTFLAGS overrides. Before a
solver performance invocation, pass default/all-feature SAT library tests
and strict SAT Clippy; inspect optimized code for the intended removal of
per-kept-entry compaction copies/bounds checks. Price span bookkeeping,
small-span dispatch, checked copy boundaries, memmove calls and live-register
spills. Fix an unmet generated-code obligation before timing. Cache committed
source and binary hashes; a prototype is not a qualified production change.

Allow at most **three performance invocations**, with exactly the retained
controls and gates used by the delayed-move screen:

1. Candidate original circuit, CPU 15, seed 1. Reuse ordinary Nixie record
   `ee11cd60c342c2fb` (8.81 s) and requested mode-matched Kissat record
   `6295845397e7a242` (1.88 s). Require complete stdout identity and an
   independently checked original-CNF model.
2. If identity and timing quality pass, one candidate circuit LBR profile,
   regardless of wall outcome. Fixed period 10472903; grouped user atom
   cycles/instructions; sample reads/running time, explicit CPU samples,
   LBR and 128 pages. Terminal memory reporting only, removed for stdout
   comparison. Require >=1000 samples, zero loss/read-loss/throttling,
   >=99.9% scheduling and user-mode coverage, and <=0.1% unresolved self
   attribution. Retain the flamegraph and separate scan/copy/allocator costs.
3. Only if circuit wall/control <=0.95 and its profile qualifies, candidate
   original si2, CPU 15, seed 0. Reuse ordinary record `f0905d230b7f8f76`
   (1.99 s) and Kissat `c3bb0064cbaa9d2d` (1.22 s). Require exact output,
   checked model, timing quality and ratio <=1.03.

All wall cells use CaDiCaL preset, MAXC=10000000, NIXIE_SWEEP=0,
PRINT_MODEL=1, and clear other study flags including NIXIE_RELATION_FACTOR.
Warm input/executable; complete-target GNU time, anonymous tmpfs output,
300-second emergency cap and <=10% off CPU. Audit constrained userspace
threads for CPU 15. Wall is the user's engineering target, never a policy
input. Record every start/completion once; no repeated cells or fresh controls.

Advancement requires circuit <=0.95, the conditional guard and two-input
geometric mean <=0.95, followed by all required workspace correctness gates.
This bounded screen with retained different-window controls is not a
population or factorial interaction claim. A failed candidate must price
short-span/memmove and bookkeeping costs from its profile before a repair
is proposed. No parameter sweep or unregistered extra observation is allowed.
