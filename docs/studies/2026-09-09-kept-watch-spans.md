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

## Result: wall gate failed; source not promoted

The committed prototype is `57e025d064aa9ccd626f459bd49caa5a7ff2c2dd`.
Release SHA-256 is
`ed2d030e083b64d3d314901ea56be975ca370440c7f081c1f186d54bf0c8db82`;
perf SHA-256 is
`e73da7c010f5640f82c54dd060403a51251ae8b1cefdee109d0ba93ad5ee8c4d`.
Compiler, lockfile and portable build settings match the registration.

| Original circuit, seed 1 / CPU 15 | Wall | Conflicts | Wall/conflict |
|---|---:|---:|---:|
| Retained qualified ordinary Nixie | 8.81 s | 186114 | 47.34 us |
| Kept-span candidate | **9.64 s** | 186114 | **51.80 us** |
| Retained requested mode-matched Kissat 4.0.4 | 1.88 s | 167929 | 11.20 us |

Candidate/control is **1.09421**, candidate/Kissat **5.12766**. The registered
0.95 advancement gate fails. Complete Nixie stdout is byte-identical and its
SAT model independently checks against the original CNF. Timing quality
passes: user 9.57 s, system 0.04 s, off CPU 0.311%, zero major faults,
46 involuntary switches and two voluntary switches. Peak RSS is 37504 KiB
versus the retained control's 37512 KiB. The different measurement windows
limit causal attribution: this is a failed engineering screen with worse
observed elapsed time, not proof of a precise 9.4% source regression.

Exactly **two performance invocations** ran: circuit wall and its registered
diagnostic. The conditional si2 cell is skipped. No repeated cell, fresh
control, parameter sweep or replacement profile ran.

## Generated code and exploratory cost diagnosis

The intended local transformation is present. In the suffix, a blocker hit
now loads only the blocker, checks its value and advances the read cursor;
it neither loads/copies the reference word nor checks the compaction output
index. First/tail refreshes update the source entry's blocker. Empty spans
copy nothing, singleton spans use one 64-bit load/store, and longer spans
call checked overlapping `memmove`. The prefix remains unchanged at
938 bytes with 88 local stack bytes.

The price is visible in the suffix: **1583 bytes versus 1120** (+41.3%),
**104 local stack bytes versus 88**, and **five static memmove call sites
versus one**. Both old and new suffixes save six registers. The inlined span
helper adds count dispatch and range checks at holes and exits; calls save
live state and reload arena/list/cursor information. Immediate destination
appends and eager clause-pair normalization remain. Removing per-hit copies
has not removed the per-visit dependent reads or the moved-watch work.

The [exploratory flamegraph](assets/kept-watch-spans.svg) preserves the
capture, explicitly labelled **quality gate failed**. It has 3994 samples
on CPU 15, zero loss/read-loss/throttle/unthrottle, 100% scheduling coverage
and 417 nontrivial LBR caller chains. However, four samples are kernel-labelled
and unresolved: user-mode coverage is **99.89985%**, below 99.9%, and unresolved
self cycle attribution is **0.100148%**, above 0.1%. These narrow misses remain
failures; the thresholds are not relaxed after seeing the result.

The profiled output/model matches the wall solve after removing only the
registered terminal memory line. Sampled prefix counters end at 41.829 G
cycles / 65.229 G instructions. They are neither complete-solve counters
nor an accepted comparison with a retained profile. The following shares
are exploratory IP attribution, not qualified cost estimates:

| Candidate self attribution | Cycles | Instructions attributed by sample deltas |
|---|---:|---:|
| Watch suffix | 37.256% | 30.779% |
| Watch prefix | 18.127% | 15.590% |
| Subsumption | 12.969% | 18.436% |
| Search body | 5.408% | 4.703% |
| Propagation driver | 3.655% | 3.090% |
| All libc memmove callers | 1.552% | 1.565% |

Disjoint suffix span-dispatch/copy/cursor regions receive **1.227%** of whole
sampled cycles: Done 0.426%, Unit 0.300%, moved holes 0.300%, shared singleton
copy/advance 0.125%, deleted holes 0.050%, Conflict 0.025%. Captured immediate
suffix callers account for **0.951%** in libc memmove, for 2.178% combined.
Other libc copy callers are separate; attributing the entire 1.552% memmove
body to this change would be incorrect. These small regions do not explain
the whole wall delta. Static frame/text growth is established, but the
incremental cost of spills, branch behavior and layout is not isolated.

Within the suffix, remaining header/pair-normalization regions receive
12.669%, immediate moves/destination appends 9.689%, the blocker loop 5.183%
and the literal-tail scan 4.907%. These are not removable-cycle budgets:
samples after dependent loads and stores cannot identify the cost of the
following branch or reload. The two scans together still receive 55.383%.
The capture supports an exploratory map of retained work, not a claim that
deleting checks or changing copy widths will recover the elapsed gap.

## Repair and combination assessment

The stable filter still visits and eventually copies the same kept entries;
this prototype amortizes loop operations but neither reduces watch visits
nor shortens the blocker-to-payload dependency. Small-span specialization
already handles lengths zero and one. Tuning another length threshold or
moving the helper out of line needs evidence that dispatch/call overhead is
large enough to repay the new branches/calls. This failed-quality capture
does not provide it. A compact scalar loop could trade the libc calls back
for repeated entry copies, but that alone returns to the old cost rather
than demonstrating an algorithmic advantage.

Combining kept spans with delayed destination writes is also unsupported.
Both keep the consumer's dependency chain and every destination append;
one adds span state/copy calls, the other queue writes/reads and flushes.
The earlier delayed-move capture prices queue preparation plus flush at
5.14%, and its wall screen was neutral. Those different-build shares cannot
be subtracted from this candidate's 9.689% move region to predict a combined
gain. A worthwhile combination must actually share preparation or remove
append operations, with preserved destination order and enough measured
reuse to cover grouping. Neither experiment measures that reuse.

Keep the ordinary compact two-phase kernel. The practical structural route
already supported on this circuit remains the
[direct exact relation mode](2026-09-09-direct-relation-solve.md): 3.61 s
whole path versus retained ordinary 8.81 s and Kissat 1.88 s, still with a
material per-conflict gap. Its representation reduces work before the
same scalar consumer. Further kernel work should remove a named dependency
or visit, rather than append another neutral mechanism and assume synergy.
This diagnosis authorizes no additional performance cell.

## Verification, evidence and disposition

Preflight passes **767 default SAT library tests**, **792 all-feature SAT
library tests**, strict SAT Clippy with all features/targets, and formatting
of the touched files. The new 42-case oracle covers empty/singleton/long
overlapping spans, consecutive and alternating moved/deleted holes, all
kept paths, both watch orientations, Unit/Conflict/Done, unvisited tails,
resumption and backtracking. Existing yield-boundary tests now also check
the compacted prefix after each unit. The retained exhaustive state/budget
oracle and independent model/LRAT checks pass in both library layouts.
No unsafe code or allocation is added. Full workspace/integration/parity
qualification was not run for this rejected prototype and is not claimed.
Its production source does not land.

Canonical records are **`a6bff0028e46b4cb`** (wall) and
**`d035f321a010f98d`** (failed-quality profile), under
`precompile/57e025d/benchmark/runs/`. Adjacent `kept-watch-spans-wall/` and
`kept-watch-spans-profile/` retain starts/completions, runners, affinity audit,
outputs, raw profile, quality audit, weighted stacks and address attribution.
Build hashes, binaries, source bundle/patch, test logs and assembly are
cached; preflight evidence is under `kept-watch-spans/preflight/`. Only this
result, its review entry and the labelled flamegraph land on main. The
temporary worktree, branch and owned scratch logs are removed afterward.
