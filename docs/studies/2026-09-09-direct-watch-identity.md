# Direct 8-byte watches with cold activity

The [direct wall comparison](2026-09-09-kissat-wall-gap.md) leaves Nixie
1.73× slower than mode-matched Kissat on the original circuit, despite
fewer conflicts. The two-phase kernel's 3.52% wall reduction missed its
5% advancement gate. Its retained flamegraph shows watch copies and live
metadata remaining in both phase bodies.

This experiment combines two previously neutral layouts with that kernel.
The old [8-byte watcher](2026-08-watcher-8byte.md) removed direct addressing;
the old [cold activity header](2026-09-arena-8byte-header.md) only improved
clause density. Here an ordinary watcher retains `(arena reference, blocker)`.
The stable clause ID replaces activity in the existing 12-byte header, and
activity moves to a stable allocation-indexed f32 side table. Clause geometry
and eager watch normalization stay unchanged. This removes the ID-to-ref
lookup tradeoff and gives the vacated header word a purpose. It is a
hypothesis about execution cost, not a prediction obtained by multiplying
old benchmark ratios.

## Representation obligations

- Ordinary watches are 8 bytes; builds with group, region or clause-traffic
  observers retain a 12-byte entry to attribute deleted blocker hits. Both
  layouts need tests. Live reason IDs come from the arena header.
- Garbage collection prepares the destination table and allocates capacity
  before mutating references. Validate every watch, rewrite it while its
  old header is readable, then move clauses. Deleted hits remain in list
  order at the shared tombstone; no eager ghost purging or tick changes.
- All four detachment sites first establish a live clause, then remove its
  two watches by direct reference before deleting or replacing it.
- Probing reads direct references after its blocker check. Sweep occurrence
  counts still exclude deleted/learned clauses. Environment construction
  keeps a position for every ghost and keeps the same limit checks; only
  stable IDs survive calls which mutate the database.
- Lucky's packed snapshot restores the exact entry sequence. Propagation
  may append HBR binaries, so header IDs and activity indices must remain
  stable across arena growth as well as compaction. No collection occurs
  inside a lucky attempt.
- Preserve f32 activity arithmetic and common-tombstone behavior. Account
  for activity storage retained for historical IDs, and for the temporary
  relocation table. These costs can outweigh the saved watcher bytes on
  binary-dense or long-running inputs. Safe side-table bounds checks remain;
  an invalid reference must not become an unchecked activity read.

Kissat `watch.h` confirms direct references and blockers as the long-watch
representation; CaDiCaL `watch.hpp` detaches by clause address. Their memory
management cannot be copied directly: Nixie also exposes stable clause IDs,
lazy ghosts and observer attribution.

## Registered bounded engineering screen

Source work occurs in an isolated worktree. Before any performance run,
pass SAT tests for both ordinary and all-feature layouts, including focused
repeated-collection, ghost, detach/restore and invalid-reference checks.
Build portable ordinary release and symbolized perf binaries with the same
lock, Rust 1.96.0 and build settings as the retained controls. Identify the
exact source snapshot and binary hashes. An unqualified prototype is not a
production landing.

At most **five new solver invocations**, all on CPU 15 after confirming no
competing pinned process. Reuse existing cells; no repeated starts:

1. Candidate on original circuit, seed 0, MAXC=10000000, `NIXIE_SWEEP=0`,
   CaDiCaL preset and printed model, with the same GNU-time / anonymous-tmpfs
   output method as the retained wall comparison. Require a checked SAT
   model and byte-identical output to `b9ae745` record `0a722720460f919a`.
   Compare wall against that retained 9.58 s, and Kissat record
   `dffd0cb6beb45f5f` (5.55 s). Require <=10% off CPU. No retiming either
   control merely because its result is inconvenient.
2. If timing quality passes, collect one candidate circuit LBR profile,
   whether the candidate wins or fails. This prices introduced costs before
   interpreting a negative result. Use the qualified atom cycle period
   10472903, 128 pages, user-only grouped cycles/instructions with sample
   reads/running time, LBR stacks and explicit CPU samples. Adapt only the
   CPU qualification from 10 to 15. Require zero loss/throttle, >=99.9%
   scheduling coverage, >=1000 samples and <=0.1% unresolved self samples.
   A failed profile remains failed; no retry. Its timing is diagnostic.
3. Only if candidate circuit wall / retained kernel wall <=0.95 with exact
   output identity and timing quality, run original si2 seed 0 to verdict:
   candidate, mode-matched Kissat, then `b9ae745`, otherwise stop. Use the
   same cap/output/timer protocol; stop on any failed off-CPU gate.

Wall time is the primary engineering target per the user's instruction.
For a positive landing require the two-input geometric mean candidate/kernel
wall <=0.95 and si2 ratio <=1.03, exact Nixie outputs, checked models and all
required source correctness gates. Report Nixie/Kissat wall and wall/conflict
as well as candidate/kernel; two inputs establish only a bounded screen.
Never use elapsed time as solver policy. A negative result must retain its
profile/code-cost diagnosis and identify a specific repair or opportunity
limit before abandoning the mechanism. Do not infer superadditivity without
matched component data.

Before measurement, the ordinary SAT suite passed **999 tests** and the
observer layout passed **1026**, each with one explicitly skipped test. The
first ordinary run caught a malformed interior reference being treated as
an activity index; checked side-table reads now refuse it. The regression
also verifies that set/add/scale operations on that reference preserve the
real clause. A separate initial corpus-path failure was resolved by linking
the primary checkout's ignored corpora into the isolated worktree. It was
not a solver verdict failure. The new collection tests cover repeated GC,
activity bits, ghost order, detach/restore and rejection before relocation.

The single registered profile also prints terminal memory composition.
Remove only that diagnostic line when comparing its output to the ordinary
wall cell; keep full byte identity for the wall comparison itself. This
adds no search-policy or in-search diagnostic work. Preserve peak RSS in
the wall cell and the side table's allocation in arena memory accounting.

## Measured result: bounded wall screen passes

Prototype source `02cc03cc10df995f484499e69183b5333439f524` (not yet a
qualified production landing at the time of measurement) uses the pinned
lock SHA-256 `3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Ordinary release binary SHA-256:
`da75c82761caaa4d58fc8d32b24416c2376ff5d77ac8af09f5a3ed197f23738d`.
Symbolized perf binary SHA-256:
`206a7835828b855db1bdf1e16d09ca61ab2b5ab17dccfedf8b998a495063a830`.
Neither uses native CPU flags or other optimization overrides.

| Input | Kernel `b9ae745` wall s | Compact watches wall s | Kissat wall s | New/kernel | New/Kissat |
|---|---:|---:|---:|---:|---:|
| original circuit | 9.58 (retained) | 7.98 | 5.55 (retained) | 0.83299 | 1.43784 |
| original si2 | 2.09 | 2.02 | 1.22 | 0.96651 | 1.65574 |

The two-input geometric mean new/kernel wall ratio is **0.89727**, an
observed **10.27% reduction**. The si2 change alone is only 3.35%, inside
the neutral band. The registered combined gate passes: geometric mean
<=0.95, si2 <=1.03, identical full Nixie outputs and checked SAT witnesses
for both arms on both inputs (2/2 solved at cap). Circuit conflicts remain
162529 versus Kissat's 277061; si2 remains 39246 versus 51823. New wall per
conflict is 49.10 µs and 51.47 µs, versus Kissat's 20.03 µs and 23.54 µs.
The Kissat throughput gap therefore remains substantial.

All four new wall cells have zero major faults and off-CPU fractions
0.38%, 0.50%, 0.82%, 0.48% (circuit candidate; si2 candidate, reference,
control). Their user/system times are 7.92/0.03 s, 1.91/0.10 s,
1.03/0.18 s and 1.97/0.11 s. Si2 peak RSS is 156696 KiB for the candidate,
158228 KiB for the kernel and 111116 KiB for Kissat. Circuit candidate peak
is 33228 KiB; its retained control did not record RSS.

This is a small engineering screen, **not a population speedup estimate**.
In particular, circuit controls were retained rather than remeasured in the
candidate's time window; the off-CPU check cannot eliminate clock/cache or
other shared-resource differences. Report the per-input observations and
this limitation with the aggregate. No claim about superadditive interaction
is supported by these data. Exactly five new solver invocations ran: four
wall cells and one profile, with no repeated starts.

## Candidate profile and remaining cost

The [interactive flamegraph](assets/direct-watch-identity.svg) is from the
original circuit. It contains **3468 user-cycle samples**, all on CPU 15,
with zero lost samples/records, zero throttle/unthrottle records, 100%
group scheduling coverage and zero unresolved self samples. LBR supplied
1003 caller stacks; incomplete callers are grouped explicitly. Sample-read
counters end at 36.320 G cycles and 59.887 G instructions and are **sampled
prefix diagnostics**, not complete solve counters or a comparable control
ratio. Do not compare its function shares to the earlier *factored* circuit
profile as if the workload were identical.

| Self component | Cycle share | Instruction attribution share |
|---|---:|---:|
| watch compaction suffix | 29.90% | 25.89% |
| watch prefix | 19.61% | 17.46% |
| subsumption round | 18.54% | 21.43% |
| search body | 4.67% | 4.04% |
| outer propagation driver | 3.81% | 3.36% |

The generated kernel uses eight-byte strides and preserves direct arena
loads. The prefix still loads only the blocker on a hit. However, LLVM
emits **two 32-bit loads/stores**, rather than a single 64-bit entry copy,
on suffix blocker hits and destination insertion. The reference and blocker
therefore still consume separate registers. The suffix's hot destination
blocker store receives 7.04% of its cycle attribution; the first watch-pair
swap's nearby reload receives 7.52%; the write-bound branch receives 5.79%.
The deleted-flag branch remains prominent (12.44% of suffix, 16.76% of
prefix), as do the prefix reference-null compare (13.68%) and blocker-value
load (8.53%). These are instruction-pointer samples, **not measurements of
misprediction probability or savings from deleting checks**.

The stable-ID recovery validates the header again at a unit/conflict exit.
That keeps identity out of blocker hits and watch movement, but adds code:
the two scan bodies are 1120 and 938 bytes, versus the kernel's 983 and 803;
`ClauseDatabase::get` grows from 187 to 225 bytes. Inlining a safe accessor
is not free. A next change must price this recovery and cold metadata path,
not treat every remaining branch as removable overhead.

Terminal circuit memory also shows the cost side of the combination:
3977896 arena bytes used, 8685520 total arena/activity capacity, 1342148
bytes of historical ID references, and 1154232/2606528 watch bytes/capacity;
13 collections ran. The side table retains historical IDs, and each
collection prepares a temporary four-byte destination per historical ID.
Eight-byte watches do not imply lower total memory on every input. Si2's
measured peak changed little despite narrower entries.

Two concrete follow-ups are suggested by the generated code, without a new
benchmark registration yet: a safe packed-u64 entry that can make unchanged
entry copies one operation, and a validated live-clause view that can return
its reason ID without repeating header validation. Both must preserve full
32-bit literal/reference encodings, ghost semantics and collection lifetimes.
Packing must be judged with its decode/bit-update cost included; caching a
validated view must end before assignment/HBR can grow the arena. Subsumption
is also now a substantial wall-cost target, independent of those watch
representations. No additional variant was run in this study.

## Result store

New canonical records: circuit wall `a64df562525fa2df`, circuit profile
`a85e80129a282bea`, si2 candidate `68494a8004e0cdca`, si2 Kissat
`c3bb0064cbaa9d2d`, si2 kernel `c504f08be43e25bf`. Retained circuit records
are `0a722720460f919a` and `dffd0cb6beb45f5f` as registered. Binaries are
cached under their source commits; each cell's immediate completion, full
output, model check and timer data is stored beside it. Candidate raw
artifacts are under `precompile/02cc03c/benchmark/direct-watch-identity*`,
including the runner, adapted CPU-15 raw perf audit, phase addresses,
symbol/disassembly files, folded stacks and detailed instruction samples.
The generated SVG was parsed as XML. Source qualification is recorded below
when complete; passing this screen alone does not authorize a production
landing.

## Source qualification and landing

The complete source qualification passed on `02cc03c`, after the two-input
screen and before the production landing:

- all-features workspace build;
- workspace nextest: **10811 passed, 12 skipped**;
- workspace doctests: **111 passed, 29 ignored**;
- strict all-features/all-targets clippy, formatting and rustdoc;
- installed **Z3 4.16.0** differential canary: **174 agreements, zero
  disagreements and one inconclusive result out of 175**. `array_unique`
  remains Nixie UNSAT / comparator Unknown; it is not counted as agreement.

These are correctness gates, not performance comparisons. Their exact
commands, source/version metadata, immediate statuses and logs are retained
under `benchmark/direct-watch-identity/qualification/`. The ignored Linux
parity snapshot is copied there rather than overwriting another checkout's
snapshot. The default compact layout also passed its separate 999-test SAT
suite; the all-features workspace run alone exercises the wider observer
layout and is not substituted for that test.

All five new canonical measurement records were independently revalidated
against their content-addressed paths, source/binary identities and output
hashes. The final commit adds documentation and the flamegraph to the tested
source; cached ordinary/perf/CLI binaries retain their actual build identity.
The source change is enabled for ordinary builds and qualifies for landing
under the registered engineering gate. This closes this experiment, while
the broader Kissat wall-time gap remains open.
