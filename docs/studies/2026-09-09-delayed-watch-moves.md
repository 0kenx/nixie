# Delayed destination writes at fixed-trail scan boundaries

The ordinary circuit still takes 8.81 s versus retained mode-matched Kissat
1.88 s at seed 1. The explicit relation mode improves that input's total
work, but does not fix the shared per-conflict path. The qualified residual
cache profile attributes 53.68% of sampled cycles to the watch scan phases.
The compact-watch generated-code audit identifies indexed destination stores
and their capacity/allocator paths inside those phases as a concrete cost.
Instruction-pointer samples are not estimates of removable cycles.

Local Kissat `src/proplit.h` queues each large-clause watch move and appends
the queue after the scanned list closes. The old
[flat arena](2026-08-flat-watch-arena.md) included this mechanism and failed
its aggregate gate, after a deep allocator/compaction defect chain. That
measurement did not isolate delayed moves. Keep the current separate Vecs,
direct eight-byte watchers, eager normalization and two scan phases; test
whether moving destination writes out of those loops gives the queue a useful
role without reintroducing the flat arena's machinery.

## Implementation and soundness contract

Give WatchLists one reusable empty move buffer. Within each Cursor advance,
the scan may append `(destination literal, watcher)` records only. It does
not borrow or index the destination-list table. Flush those records in FIFO
order through the same destination append operation before advance returns
Done, Unit or Conflict. In particular, finish the flush before assignment,
proof handling, HBR, backtracking, budgets, observers or any caller can
inspect watch lists. The queue remains empty outside that synchronous scope;
only allocation capacity persists. No arena pointer or stale trail value is
retained. Keep prefix-to-suffix transfer within the same queue scope.

This boundary is deliberately earlier than Kissat's whole-list flush. It
preserves Nixie's exact state at every existing unit/conflict yield and avoids
depending on what future caller-side HBR or proof code might inspect. It is
an implementation change under identical trajectories, not a watch-choice
policy. Preserve list order, reason identities, eager literal swaps, conflict
tails, deleted blocker hits and all accounting. Observer-selected legacy
propagation remains available and receives the same visible state.

Use a closure-scoped internal helper so scan code cannot accidentally return
without flushing. Add boundary tests for move bursts followed by Unit,
Conflict and Done, repeated destinations with existing entries, buffer growth
and reuse, and empty buffers across snapshots/scopes/collection. Compare the
complete existing legacy-oracle states, proof transcripts and independent
models/LRAT checks in both watcher feature layouts. No new unsafe indexing or
unbounded recursion. Allocation failure is not a fabricated solver answer.

## Generated-code gate before measurement

The two optimized scan bodies must no longer index a destination Vec or call
its resize/growth path. They should append sequentially to the move buffer;
destination reads/capacity checks/stores belong to the separate flush loop.
Record queue entry sizes, added stores, empty-flush checks, text size, calls
and register spills. The queue does not remove append work: copying records,
reserving storage and flushing are introduced costs that must be priced.
If the intended separation fails to materialize, repair it before consuming
a solver run or record the failed code-generation obligation without timing.

## Registration: at most three performance invocations

Start from main `da03538`, with Rust 1.96.0 / LLVM 22.1.2 and lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Portable release/perf profiles, no native/PGO/RUSTFLAGS override. Commit the
prototype and cache both binary identities before running. A prototype is
not a qualified source landing.

Use ordinary original CNFs, CPU 15, circuit seed 1 / si2 seed 0, CaDiCaL
preset, MAXC=10000000, NIXIE_SWEEP=0, PRINT_MODEL=1. Clear other study
environment variables, including NIXIE_RELATION_FACTOR. Warm input/executable;
GNU time covers the complete target with anonymous tmpfs output and a
300-second emergency cap. Audit constrained userspace threads for CPU 15;
require <=10% off CPU. Wall is the user's primary engineering metric and
never a policy input. Record every start and completion once; no retries,
fresh controls or extra parameter sweeps.

1. Candidate original-circuit wall. Reuse qualified residual-cache record
   `ee11cd60c342c2fb` (8.81 s) and requested Kissat record `6295845397e7a242`
   (1.88 s). Require byte-identical complete Nixie stdout and a checked model.
2. If timing quality and identity pass, one candidate circuit LBR diagnostic,
   regardless of the wall outcome. Fixed period 10472903, grouped user atom
   cycles/instructions, sample reads/running time, explicit CPU samples,
   128 pages and LBR. Terminal memory reporting only; strip only that line
   for stdout comparison. Require >=1000 samples, zero loss/throttle/
   unthrottle, >=99.9% scheduling coverage and <=0.1% unresolved self cost.
   Retain its flamegraph and separate scan/queue-flush/allocator attribution.
3. Only if circuit wall <=0.95 of the retained control and the profile
   qualifies, candidate original-si2 wall. Reuse residual-cache record
   `f0905d230b7f8f76` (1.99 s) and Kissat `c3bb0064cbaa9d2d` (1.22 s).
   Require exact output, checked model, timing quality and ratio <=1.03.

Advancement requires the two-input geometric mean <=0.95 and all required
source correctness gates. This is a bounded engineering screen with retained
different-window controls, not a population or factorial interaction claim.
Current main's inherited inactive relation-mode check remains present in the
candidate. A negative/neutral outcome must examine the queue's introduced
cost and remaining dependencies using its profile and generated code before
selecting a repair. Do not revive flat storage or masks by assumption.
