# Fixed propagation queue and separate binary spans

## Registration

Continue toward Kissat wall/cycles per conflict using the first complete
engine (`a5854e4`), without the rejected persistent-header or directory
representations. Its ordinary fixpoint still uses a growing `Vec` queue:
assignments load pointer/length, check capacity and publish length; dequeues
reload the published length and update the external head. Its binary loop
also selects primary versus overflow and checks the selected array for each
edge. The retained engine profile identifies binary metadata/edge accesses;
it does not assign all of that cost to these removable operations.

The complete engine's exclusive domain permits a different queue contract.
Before borrowing, reserve space for the existing length plus the variable
count. Do not assume all existing trail entries are distinct: general Trail
assignment APIs permit repeated entries. During this fixpoint only currently
undefined variables are assigned, at most once each, so at most `num_vars`
new entries can be appended. Keep a fixed backing pointer and local initialized
length/head; publish the resulting Vec length and head when the view ends,
including early conflict and unwind. Values, reasons, levels, trail indices,
queue order and every statistic/tick remain unchanged. Do not change general
Trail assignment, variable metadata layout or queue behavior outside this view.

The reservation is a real memory/growth cost and belongs inside the measured
solver. Ordinary unique trails can require room for up to twice the variable
count before Vec growth rounding; repeated prefixes use the conservative
length-plus-domain bound. No full scan of values is allowed at entry just to
count undefined variables. A private unsafe assignment method must state and
check in debug its valid-domain, undefined-variable and initialized-prefix
contract; only the two propagation paths with proven undefined values call it.
Raw queue reads/writes and final length publication get narrow safety comments.
No custom Send/Sync, global pointer, deferred clause mutation or callback.

Also borrow the existing primary and overflow slices once and traverse them
in that order with two span loops. This reuses the fixed-domain ownership,
without compacting or replacing the binary graph. Preserve physical CSR
starts after deletion, first binary conflict, primary-before-overflow and
binary-before-long semantics. Read an edge's reason only on a non-satisfied
exit. Keep eager clause normalization, immediate watch moves and old optional
mode fallbacks exactly. This is an exact-trajectory representation change,
not a branching/search heuristic or a claim about fewer required propagations.

Reference audit: Kissat `src/array.h` uses an allocated begin/end trail with
unchecked append; `inlineassign.h` publishes exactly one literal per undefined
assignment and `propsearch.c` keeps a local propagation cursor. Nixie's repeated
prefix possibility needs the stronger reservation bound above. Rust 1.96.0's
local `alloc/src/vec/mod.rs` documents `as_mut_ptr` without materializing a
slice and initialized raw writes followed by `set_len`. The queue's exclusive
borrow forbids reallocation or element references while its pointer is used.
The retired `compact-trail-metadata` and `inline-trail-assignment` studies
changed record footprint/inlining only, not this queue contract. The compact
adjacency experiment borrowed binary slices together with a different owner
representation; here the unchanged graph is combined with the complete engine.

Preflight: focused trail/engine tests for empty/full queues, appended entries
being consumed in the same pass, duplicate initial entries, early conflicts,
head requeue, backtracking, growth between borrows and unwind publication.
Compare complete state with the scalar oracle, default/all-feature SAT tests,
strict SAT Clippy/format, focused strict-provenance Miri and native Rayon owner
moves. Inspect portable perf assembly: no queue grow call/capacity test at
assignment, local queue cursors, no primary/overflow choice or array bounds
check per binary edge, and reason loads off the satisfied path. Local stack
must not exceed the first engine's 248 bytes and text must stay below 4096
bytes. One source-directed preflight repair may fix a missed transformation;
no annotation or parameter sweep. Failed preflight ends without a cost run.

Use Rust 1.96.0 / LLVM 22.1.2 and the retained lock, ordinary portable
release/perf, and once-only `header-lookahead-engineering-v1` records. Reuse
qualified fd01d0b j3037 `0ec1f4bfcfe8f5f9`, first engine `d368266c5252a0db`,
and mode-matched Kissat 4.0.4 `45a3c8f2e3057841`. CPU 15, seed 0, CaDiCaL
preset, sweep/definitions off, MAXC=10000000, printed model, warmed input/binary,
anonymous tmpfs output, whole-process user instructions/cycles, 300-second
emergency cap. Verify source/lock compatibility, exact stdout, >=99.9% PMU
coverage, <=5% off CPU, and unchanged runtime/identity of any constrained
sleeping threads. No own build overlaps a cost run; foreign load remains an
attribution limitation. Never retry an existing or failed-quality cell.

After passing preflight, spend one candidate j3037 cell. Advance with >=5%
fewer instructions than the first engine and no usable wall regression
against qualified production, or >=10% lower usable wall/cycles than both
with no extra instructions against the first engine. Then allow one paired
si2 confirmation (reuse any existing compatible control): exact stdout and
independently checked original-CNF model, <=3% instruction/wall regression,
>=5% two-input wall improvement. This is a bounded engineering screen, not a
new suite geomean. Full workspace build/tests/doc-tests/Clippy/fmt/docs and
fresh installed-Z3 parity precede any production landing.

A cost rejection gets one qualified LBR diagnostic to locate introduced cost.
Allow at most one measured repair only if the profile/code identifies a
specific removable term and its design is recorded before measurement; no
second profile or repeated cost. Archive all rejected source/findings on main,
retain the result store and remove owned idle worktrees/temporary files.

## Initial codegen and the one preflight repair

The initial implementation passes its three focused native and strict-provenance
Miri tests (18.70 s under Miri). Rust 1.96.0 perf assembly has a 3454-byte
engine at `0x63e20`, but a 264-byte local frame, exceeding the registered
248-byte ceiling. Queue assignment has no capacity check/grow call. LLVM
unrolled the two spans into separate edge loops; satisfied edges branch
before loading the reason. However, `BinaryImplicationGraph::get` has no
inline annotation and became a call at `0x63f0e` on every dequeued literal.
Its 32-byte returned view occupies stack space and the call forces base
reloads. Queue length is held in a register with stores to the view's local
initialized field for exit/unwind publication; the external Vec length is
only updated at exit. No performance cell was run.

Use the single registered source-directed preflight repair: mark this small
existing accessor `#[inline]`, like `span_of` and `edge_at` alongside it.
Inspect whether this removes the call and its returned-view stack storage
while meeting the original stack/text gates. No layout, unsafe contract,
search order or bounds-check change. If it misses the gate, archive both
versions without a cost run; do not try another annotation or rearrangement.

## Verdict: stopped at the code-generation gate

The one repair (`5f6e52307dd332858eed452d6bc9ed314fa5ba50`) removes the
accessor call, but its frame remains **264 bytes**, above the registered
248-byte maximum. Text is 3707 bytes at `0x63d70`, below the 4096-byte
ceiling but larger than the first engine's 3615 bytes. No cost cell, profile,
new control/Kissat run or si2 confirmation was launched. This is a failed
engineering preflight, **not measured evidence of a slowdown**. No wall,
cycle, instruction or suite-geomean improvement is claimed. Production SAT
source remains unchanged.

The useful transformations did compile:

- The primary and overflow scans are separate loops. Their satisfied exits
  (`0x63f77`, `0x64026`) precede reason loads (`0x63f79`, `0x64028`).
  No storage selection or edge bounds check occurs per edge. The checked
  span construction remains once per dequeued literal.
- Queue appends at `0x63fdc`, `0x6408c`, `0x642f6`, `0x646b4` and
  `0x64974` have no capacity comparison or grow call. Remaining `grow_one`
  calls belong to destination watch buffers.
- Local length/head stay in registers through the fixpoint, with writes to
  the view fields. External Vec length/head publish at `0x64aa7` and
  `0x64aaf`; the loop no longer reloads external Vec length to dequeue.

However, the accessor call was only one cause of live-state pressure.
Inlining removes the returned-view scratch space but brings all the graph
base/length fields into the driver, with a 264-byte frame again. The fixed
queue pointer reloads from stack at every append (`0x63fd7`, `0x64087`,
`0x642f1`, `0x646af`, `0x6496f`). Each append also writes the view's local
initialized field, even in this panic-abort build. The driver retains value
and metadata lengths for checked assignment stores and compiles three long
scan bodies (prefix plus two suffix contexts). Removing queue growth did
not eliminate that shared state or the suffix duplication. Assembly shows
the operations; without a dynamic run it cannot rank their actual costs or
predict whether the removed work would outweigh them.

Do not repeat the accessor annotation experiment or relax the frame ceiling
after observing this output. A further complete-engine design needs an
explicit reduction in state kept across binary/long scans and in per-unit
publication, with a new safety argument and preflight. Merely putting a raw
queue behind the existing checked views is insufficient to obtain the
registered machine-code shape. The conservative queue-capacity contract
and focused tests are reusable results, independent of this cost verdict.

## Safety evidence and archive

The reservation proof does not assume uniqueness of the existing prefix.
Only undefined variables can append within the view, and nothing within it
can unassign or grow the domain. The two unsafe call sites are reached only
after proving an in-domain literal's value is zero. Allocation/reservation
precedes pointer creation; no backing-slice reference or queue reallocation
occurs while it is used. The initialized count advances after the raw write;
Drop publishes only that prefix and the consumed head. An empty queue never
dereferences its dangling empty-allocation pointer. No pointer is stored in
Solver, shared with a worker, or given a custom Send/Sync implementation.

The scalar oracle compares queue/values/reasons/levels/indices, clauses,
watches, binary graph, propagation statistics, ticks and conflict-prefix
state. Focused regressions exercise duplicate initial entries, empty queues,
new implications consumed in the same pass, growth between borrows,
backtracking, unwind publication, and first conflicts in both binary spans
without touching unvisited overflow. The existing owner test moves solvers
before variable growth, arena compaction and propagation/requeue, both
locally and through a native Rayon pool. Optional mutating/bounded modes
retain the prior complete-engine gate and scalar fallback.

Verification completed:

- Initial default SAT nextest: **1019 passed**, one existing skip.
- Repaired all-feature SAT nextest: **1046 passed**, one existing skip,
  including the exhaustive small-state oracle and native Rayon ownership.
- Strict-provenance Miri, seed 42: **three queue/span tests passed**
  (18.70 s); **one moved-owner/compaction/requeue test passed** (75.95 s).
  Miri 0.1.0 / Rust 1.98.0-nightly-2026-06-11; native/perf compiler remains
  Rust 1.96.0 (`ac68faa20`), LLVM 22.1.2.
- Strict SAT all-feature/all-target Clippy and workspace format check passed.
- Full workspace build/tests/doc-tests/docs and fresh Z3 parity were not
  run: no solver code is being landed after this preflight rejection.

The [archived source patch](assets/2026-09-10-fixed-propagation-queue.patch)
applies to reachable registration `e3c85e7f`; it contains the complete
repaired prototype, including tests. Removing only the added `#[inline]`
on `BinaryImplicationGraph::get` reconstructs initial `7e68b78f`. This is
archival source, not a production patch recommendation.

`precompile/7e68b78/` and `precompile/5f6e523/` retain both verified source
bundles, patches, perf binaries, lock, compiler/binary identities and
preflight logs/disassembly. Both bundles require reachable `e3c85e7f`.
Lock SHA-256 is
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
The repaired bundle also contains the initial commit. The experimental
worktree, branch, owned corpus links and temporary logs are removed after
archiving. There were **zero new performance invocations**.
