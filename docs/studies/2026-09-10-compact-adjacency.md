# Compact owning adjacency buffers and fused binary metadata

## Design and safety contract

The user explicitly permits small, focused unsafe blocks compatible with
Rayon. This experiment changes representation, preserving propagation and
inprocessing order, reasons, tick accounting and all search choices.

Replace the three-word per-list `Vec` header with an owning pointer and
checked u32 length/capacity for non-zero-sized Copy entries: 16 bytes instead
of 24 on a 64-bit host. Allocation/deallocation remains Vec's responsibility;
small unsafe blocks transfer ownership, expose initialized slices and append
within established capacity. Growth never truncates a count. Allocation
failure restores the old owner before reporting failure. No pointer escapes
the owning buffer or survives a safe mutable borrow. Clone is deep.

Fuse each literal's binary span start/live length with its compact overflow
buffer in one 24-byte record, replacing three separate arrays totaling 32
bytes per literal. The start is explicit, so reading code-1's span end and
special-casing literal zero disappear. Long-watch headers also shrink to
16 bytes. Keep the CSR edge pool and each growable list independently owned;
avoid flat-pool relocation/defragmentation and delayed-move costs that failed
previous studies. This first representation retains separate long-watch and
binary directories; it does not claim complete adjacency unification.

Combine this layout with a borrowed binary propagation loop: borrow the CSR
and overflow slices immutably, and the disjoint trail mutably, for the entire
scan. This exposes stable edge extents to the compiler without unchecked
indexing. Binary order, assignment reasons and conflict requeue behavior stay
identical. Observer and LRAT paths retain the instrumented scalar loop.

The wrapper is Send only for Send entries, Sync only for Sync entries. All
mutation requires exclusive access, with no global mutable cache or shared
allocator metadata. Test moving prebuilt solvers into a Rayon pool, parallel
independent solves, deep copies, empty buffers, alignment, growth, bounds,
retain/panic and ownership transfers. Test ordinary and observer watch widths.
Use the existing exact-state and independent LRAT oracle tests, plus a safe
Vec-based container oracle. Consult local Kissat vector/propagation and
CaDiCaL watch semantics; no C/C++ dependency is introduced.

The ownership contract follows Rust's
[Vec raw-parts requirements](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.from_raw_parts)
and [Send/Sync rules](https://doc.rust-lang.org/nomicon/send-and-sync.html).
The public `WatchLists::get_mut` return type becomes `&mut WatchBuffer`;
callers explicitly requiring `&mut Vec<Watcher>` would need to adapt.

Preflight found a preexisting binary compaction contract defect: an individual
retirement leaves slack, so a subsequent bulk compaction must read each old
physical start instead of summing the remaining live lengths. The new stored
starts address this directly. A focused regression mixes individual and bulk
retirement and checks later spans. Count overflow and count/fill mismatch now
raise errors before overwriting neighboring spans. These are invariant tests,
not evidence of an observed wrong solver verdict on the benchmark.

Memory preflight: Miri 0.1.0 (485ec3fbcc, nightly 2026-06-11), seed 42,
strict provenance, passed five buffer tests including growth, alignment,
panic handling and ownership moves across standard threads. Native Rayon
buffer and prebuilt-solver tests pass. Crossbeam epoch 0.9.20 blocks strict
Rayon Miri at its integer/pointer conversions; permissive provenance with
Stacked Borrows fails at its `internal.rs:562` container cast for both this
buffer and a plain-Vec control. With Tree Borrows and scoped worker pools,
both tests finish successfully, but Miri reports 17 unreclaimed Crossbeam
epoch allocations (all at `atomic.rs:200`). This is limited concurrency
evidence, not a clean end-to-end strict-Miri Rayon result. No leak or borrow
checks were disabled to present a passing run.

## Bounded engineering screen

Before execution, inspect generated code for compact header moves and fused
binary metadata loads. Commit/cache exact source, compiler, lock and binary
identities. Portable release/perf, CPU 15, CaDiCaL preset, seed 0,
MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0, NIXIE_DEFINITIONS=0;
clear all other study overrides. Full-process user instructions/cycles,
GNU-time wall, warm input/binary, anonymous tmpfs output, <=10% off-CPU,
>=99.9% counter coverage. No own build overlaps measurement.

At most five new solver invocations: one fresh compatible qualified Nixie
j3037 control if absent from the store; one candidate j3037 cell; one
candidate j3037 LBR profile to diagnose the result; then, only if j3037 wall
improves at least 10% and instructions at least 5%, one candidate si2 cell
and one compatible qualified si2 control if absent. Reuse requested-mode
Kissat records and any compatible controls; never retime a recorded cell.
Require exact complete Nixie output and check every SAT model. Report raw
UNSAT without an original-CNF proof as unverified/unknown in canonical data.

The profile requires zero lost/throttled samples, >=1,000 samples, >=99.9%
coverage/user samples and <=0.1% unresolved self. Retain a negative's cost
diagnosis; no parameter sweep follows. This is a bounded same-trajectory
engineering screen, not a multi-seed heuristic or population claim.

Advance only if both anchors retain exact output, the two-input wall
geomean improves at least 5%, and si2 regresses no more than 3%. Before any
production source landing, complete all workspace build/test/doctest/Clippy/
fmt/doc checks and installed-Z3 4.16.0 parity as a correctness gate. Keep
the target Kissat wall. Archive rejected code and commit its finding.

## Pre-execution audit clarification

The initial preflight stopped before launching any solver because two nxbrain
worker threads are pinned to CPU 15. Both were sleeping in futex waits, with
zero accumulated user/system ticks. Permit already-sleeping futex workers
only with unchanged identity and **exactly zero additional schedstat runtime
nanoseconds** between the preflight and completed invocation. Save both
snapshots; reject any activity. Awake constrained threads remain a blocker.
This checks actual contention without moving or stopping another process.
All other quality thresholds and the five-invocation bound remain unchanged.

## Initial result: compact headers alone fail the gate

Prototype **958a5acb0f5b76e07df2254d8272c7fc1215824e**, portable Rust 1.96.0 /
LLVM 22.1.2, uses the registered lockfile. Release binary SHA-256 is
`6ff04ae67bd9b6cc6aeab477c3e17350cbb048414e853ace205cc6857796646d`;
perf is `292d9eede3e7014c3289b6b191c4f225f55278d5e33909f40725c179aafed577`.
Qualified control c7634ef has identical compiled SAT/core/math/time source to
the starting main. Both complete with byte-identical full stdout, 330565
conflicts and 323390316 propagations.

| j3037, CPU 15 / seed 0 | Wall | User cycles | User instructions |
|---|---:|---:|---:|
| Qualified control | 40.69 s | 185203793294 | 254607462624 |
| Compact owners + borrowed binaries | 40.09 s | 182634750256 | 258266964068 |
| Retained requested-mode Kissat 4.0.4 | 18.04 s | 79144759362 | 121059163625 |

Candidate/control wall is **0.9853**, cycles **0.9861**, instructions
**1.0144**. Neither the 10% wall nor 5% instruction gate passes. This is a
neutral engineering screen, not a demonstrated speedup. The retained Kissat
wall ratio remains **2.2223**, cycles/conflict **2.0020**. Different-window
Kissat timing is context, not a new paired measurement. Both new cost runs
have 100% PMU coverage, below 0.3% off CPU, zero major faults and zero
additional runtime on the two sleeping constrained workers. Peak RSS was
34056/35372 KiB; smaller metadata did not establish a whole-process memory win.

Exactly three performance invocations ran: control, candidate and profile.
No si2 run or repeated cell followed. Canonical records are **fc400b6f4984dcfb**,
**a1b779181b0ba4ef**, and diagnostic **1ae01d63e808adb1**; retained Kissat is
**45a3c8f2e3057841**. Reported UNSAT is unverified without an original-CNF proof;
canonical verdicts remain unknown. The profile has 17538 samples, zero
loss/throttle, full counter coverage and qualifies all registered gates.
Its complete stdout matches after removing only terminal memory reporting.

The [cycle flamegraph](assets/2026-09-10-compact-adjacency.svg) explains a
concrete introduced cost: **WatchLists::add is now out of line, at 9.52% of
whole-process sampled cycles**. Growth arithmetic, allocator error formatting
and directory resize enlarged its generated body to 321 bytes. Every ordinary
watch move pays four callee register saves, a 40-byte local stack frame,
call/return, plus caller saves/reloads. The two scan bodies account for 41.58%
self cycles and the propagation driver 21.29%; propagation including callees
is 74.80%. These percentages are attribution, not removable-cost estimates.

Generated code does implement the intended compact metadata loads and borrowed
binary pointer loops. But a smaller owning representation cannot help if its
rare growth path prevents the common append from inlining. The current result
must not be retried with only a new seed, CPU, or benchmark window.

Preflight passed 1048 SAT tests (one existing skip), strict SAT Clippy and fmt;
Miri limitations are recorded above. Source is not promoted and no full
workspace qualification is claimed. Source bundle/patch, binaries, identities,
raw records, disassembly, profile and logs are retained under
`precompile/958a5ac/`.

## Cost-directed repair registration

Keep the same representation and exact growth policy, but isolate checked
capacity growth, allocation and panic formatting in a cold non-inlined helper.
Keep the common capacity test plus initialized append small enough to inline.
Directory growth is likewise a separate cold helper, with its full bounds and
allocation checks. This changes placement of rare work, not allocation sizes,
watch order or semantic decisions. Reuse the same Vec/Miri ownership contract.

Before timing, require disassembly to show the ordinary destination append
inside the watch scanner and allocator/directory growth outside it. Do not
blindly force the entire old 321-byte function into every call site. A failed
code-generation obligation ends this repair without a solver invocation.

At most four additional performance invocations: one repaired j3037 cell,
one repaired j3037 profile, and only if the original 10% wall / 5% instruction
gates pass, candidate and missing qualified-control si2 cells. Reuse control
fc400b6f4984dcfb and both retained Kissat references. All other output, safety,
quality and two-anchor advancement gates above remain unchanged. This is a
single repair of observed introduced cost, not an inlining-attribute sweep.

## Repair result: placement improved, advancement still fails

Repair **34c6bebd251cae5dcb381e1702a30f8757fc0fcc** passes the generated-code
gate: ordinary append is inlined in both scan phases; the separate checked
reserve and directory-growth bodies are 224 and 120 bytes. The scan bodies
grow from 836/753 to 1095/905 bytes because they now contain the ordinary
append. Growth sizes and list contents are unchanged; no extra unsafe block
was added. All 1048 SAT tests, strict SAT Clippy and fmt pass again.

Release SHA-256 is
`8d0730e9694319ed1c8cf3cac4bb9a5a82286b76bb6da85722e6f1264e41638d`;
perf is `c2d3f7c098c688481096b56c236de34f5fd183439eceee7a3c27a5df9df7ff09`.
The repaired cell **75723a0f98a10705** retains exact complete stdout and costs
**246749805350 user instructions**, **242344923287 user cycles**, **60.79 s**.
Instructions are **0.9691** of qualified control and **0.9554** of the first
prototype. Isolating growth repairs the introduced instruction overhead,
but the resulting 3.09% saving still misses the registered 5% gate.

Wall/control is 1.4940. This invocation had **7.95% off CPU**, 3166 involuntary
switches and 55.81 s user time, versus 0.295%, 115 switches and 40.47 s in the
control. It technically passes the registered <=10% off-CPU bar and has
100% PMU coverage; that does not make all of its wall/cycle deterioration
causal evidence against the source. The two constrained idle workers still
accumulated exactly zero runtime. Broader contention and code-layout/cache
effects are not separated by these records. Do not retime the cell or promote
its profile duration to a replacement wall measurement. There is no evidence
here of the required wall improvement, regardless of that attribution limit.

The [repair flamegraph](assets/2026-09-10-compact-adjacency-repair.svg), record
**fabbbcca3fbdcaf7**, has 19091 samples, zero loss/throttle, full PMU coverage,
99.974% user samples and 0.0262% unresolved self. Complete stdout is unchanged
apart from the registered memory line. Scan self cycles are now **50.80%**,
propagation-driver self **21.60%**. The out-of-line insertion node disappears;
its unavoidable destination loads/stores move into the scanner. Hot addresses
still sit at blocker/clause-header reads, binary span/overflow metadata,
assignment-value access and destination capacity checks. Sample skid and
load dependency mean these are locations of cost, not estimates that every
associated instruction can be removed.

The cost diagnosis supports a narrower conclusion than “unsafe is faster”:
compact ownership is viable under the tested safety contract, and cold growth
is needed to avoid introducing append overhead, but neither removes the
serial watcher → value → clause and destination-memory accesses. A future
representation experiment needs to reduce those dependencies or eliminate
real visits, rather than counting saved header bytes as saved wall time.
The prior negative prefix-sharing and entry-lifetime censuses remain relevant;
this result is not grounds to revive them without new evidence.

**No production compact buffer, fused binary directory or borrowed-binary
prototype is landed.** The measured engineering result is below the gate,
not a population performance claim. Five performance invocations in total
covered both versions: three cost runs and two profiles; no si2, new Kissat,
seed sweep or repeated cell. The second version's source bundle/patch, binary
identities, disassembly, codegen audit, raw results, profiles and validation
logs are retained under `precompile/34c6beb/`.

The independently demonstrated CSR defects are extracted into the existing
safe representation: preserve old physical boundaries during bulk compaction,
reject count/total overflow before layout mutation, and bound fill writes by
the selected span rather than the entire edge pool. Focused regressions cover
mixed retirement with an empty middle span and overflow entries, repeated
compaction, count overflow without mutation, and neighbor-overwrite rejection.
The fix undergoes the full qualification gate separately from these rejected
performance prototypes.
