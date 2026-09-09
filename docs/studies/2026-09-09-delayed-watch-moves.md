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

## Result: no demonstrated wall gain; source not promoted

The committed prototype is `7e244e644333977dd4cc2adf213c39194e2a31a3`.
Release SHA-256 is
`11c1c8d361cb4765d4d8e7886724f918a72185efc6f6774d1b92632f1363c6eb`;
perf SHA-256 is
`85d40f8ad7c0a2a076370f30317ef46b84992809694e0a5468cf52109d60deab`.
The registered compiler, lockfile and portable settings match. The queue
record is 12 bytes in ordinary builds, 16 with observer identity fields.

The pre-measurement assembly gate passes. The suffix shrinks from 1120 to
959 bytes and the prefix from 938 to 813; both local stack reservations
shrink from 88 to 72 bytes, with six saved registers still pushed. The
separate flush body is 257 bytes with 40 local stack bytes. Neither scan
indexes or grows a destination list. The new fast move path instead performs
three sequential 32-bit stores plus a length update and a queue-capacity
check. Queue growth remains an out-of-line call. The flush uses a 12-byte
input stride and an eight-byte watcher load/store, with destination bounds,
resize and target-capacity checks. A smaller scan has not removed that work.

| Original circuit, seed 1 / CPU 15 | Wall | Conflicts | Wall/conflict |
|---|---:|---:|---:|
| Retained qualified ordinary Nixie | 8.81 s | 186114 | 47.34 us |
| Delayed-move candidate | **8.88 s** | 186114 | **47.71 us** |
| Retained requested mode-matched Kissat 4.0.4 | 1.88 s | 167929 | 11.20 us |

Candidate/control is **1.00795**, candidate/Kissat **4.72340**. The 5%
advancement gate fails. This is no demonstrated improvement, not evidence
of a precise 0.8% source regression: the controls are retained from another
window. Complete Nixie output is byte-identical, its SAT model independently
checks against the original CNF, and the timing-quality gate passes. User
time is 8.83 s, system 0.02 s, off CPU 0.338%; 49 involuntary switches,
one voluntary switch and zero major faults. Peak RSS is 36460 KiB versus
retained control 37512 KiB; this whole-process figure does not separately
measure the queue allocation. Only circuit wall and its registered profile
ran: **two performance invocations**, no repeated cells, no new controls and
no si2 run.

## Candidate cost diagnosis

The [interactive flamegraph](assets/delayed-watch-moves.svg) retains all
sampled cycle weight, with truncated caller chains labelled. The profile
passes its registered thresholds: **3814 samples**, all on CPU 15, zero
loss/read-loss/throttle/unthrottle and 100% scheduling coverage. There are
3813 user-mode samples and one kernel-labelled sample; unresolved self cost
is 0.0262%, below the 0.1% limit. There are 492 nontrivial LBR caller chains.
The sampled prefix ends at 39.944 G cycles / 67.716 G instructions; these
are diagnostic prefix counters, not complete-solve costs or a control ratio.
The profiled search/model matches the wall solve after removing only the
registered terminal memory line.

| Candidate self attribution | Cycles | Instructions attributed by sample deltas |
|---|---:|---:|
| Watch suffix | 33.062% | 28.345% |
| Watch prefix | 18.222% | 15.904% |
| Move flush | 3.015% | 2.615% |
| Subsumption | 13.450% | 18.083% |
| Search body | 5.375% | 4.741% |
| Propagation driver | 4.012% | 3.534% |

The queue preparation/store address regions inside the scans receive
**2.124% of whole-profile cycle attribution** (suffix 1.914%, prefix 0.210%).
The separate flush receives 3.015%: destination store/loop 1.521%, target
index/capacity 0.944%, entry/exit 0.446%, queue read 0.079% and destination
extent 0.026%. Its growth-call block receives no samples; this is not proof
of zero allocations, and out-of-line allocator bodies are separate. The
ordinary destination append still occurs once per move, with an extra queue
write/read and boundary flush around it. This explains the unresolved cost
term that scan text-size savings alone ignored. It does not assign the tiny
historical-window wall difference to a specific instruction.

Larger reserve capacity is therefore not the supported repair. Fusing
adjacent equal-destination moves could reduce target-header work while
preserving per-list order, but the whole flush is only 3.015% here, its
index/capacity region 0.944%, and this profile does not record run lengths.
Do not add grouping, sorting or a second index without demonstrating that
enough append operations disappear to pay for it. Removing a reason-header
validation is also a small local opportunity: the recorded reason-validation
regions total about 0.787% of whole cycles. Neither fact licenses a new
benchmark or predicts a 5% full-run saving.

The larger unresolved cost remains the 51.284% scan bodies. Even after
destination indexing leaves them, each visit retains dependent blocker,
header and value reads, compaction bookkeeping and short scans. Several hot
sampled PCs follow deleted-header loads or test the compaction write index;
they are not measurements of branch misses or removable safety-check cost.
The old eager-normalization study already tested conditional pair stores:
reverting its landed branchless normalization is not a fresh idea. A next
core rewrite must remove repeated work or make cursor/span invariants visible
to the compiler while preserving their proof, and price introduced checks,
copies and call boundaries. Repeating delayed appends or mask construction
around the unchanged consumer has no demonstrated margin.

## Verification, evidence and disposition

The prototype passes **1005 default SAT tests** and **1032 all-feature SAT
tests**, one skipped in each configuration, plus their doc tests and strict
SAT Clippy. New tests cover 97-move bursts ending at each scan exit, existing
and repeated destinations, unvisited tails, queue growth/reuse, clone and
packed snapshots, arena compaction and push/pop. The existing exact-state
legacy oracle, exhaustive small-state/budget cases, independently checked
models and LRAT transcripts remain in those suites. No new unsafe code is
introduced. Full workspace/parity qualification was not run for this failed
prototype and is not claimed; its production code does not land.

Canonical records are **`da44e9229488e460`** (wall) and
**`e78ab4f5ba678547`** (profile), under `precompile/7e244e6/benchmark/runs/`.
Adjacent `delayed-watch-moves-wall/` and `delayed-watch-moves-profile/`
retain once-only runners, starts/completions, thread affinities, full outputs,
profile data, audit/attribution JSON and weighted stacks. The build identity,
binaries, source bundle/patch, test logs and assembly are cached; source
inspection is under `delayed-watch-moves/preflight/`. The temporary worktree,
branch and scratch logs are removed after recording this result on main.
