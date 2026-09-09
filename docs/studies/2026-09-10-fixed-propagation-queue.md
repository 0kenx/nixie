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
