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
