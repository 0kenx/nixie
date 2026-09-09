# Complete propagation engine

## Registration

The user requested a complete engine to reduce the remaining Kissat wall
gap. Ordinary propagation will borrow fixed trail value/assignment metadata,
the watch directory and clause storage through a full fixpoint. Long-clause
units are assigned inside the scan, without returning a `Step::Unit` to
`Solver`. Binary propagation uses the same borrowed trail. This changes the
ownership boundary, beyond the rejected flag specialization and forced
assignment inlining. Individual watch buffers and the assignment queue may
still grow; their growth must not invalidate the fixed value/metadata views.

Reference audit: Kissat `src/proplit.h`, `fastassign.h`, `inlineassign.h`
and `propsearch.c` retain value/assignment bases through assignment. Preserve
Nixie's semantics: binary primary then overflow, binaries before long
watches, eager pair normalization, immediate destination append, stable
prefix/suffix filtering, first conflict and untouched conflict tail. Keep
requeue, reasons/levels/trail positions, conflict-free prefix and every tick
charge exact, including phantom binary entries. No search policy changes.

Entry eligibility excludes bounded propagation, LRAT, lazy HBR, reason
diagnostics and active BCP observers. Their existing complete path remains
available. The scalar test oracle must bypass the new engine as well. No
variable creation, arena compaction or directory growth occurs inside the
ordinary engine; only existing literals/clauses are traversed. Borrowed
storage belongs to one solver, with no globals or custom Send/Sync promises.
Any unsafe access needs a local validity argument and strict Miri coverage.

Before timing, run default/all-feature SAT tests, strict SAT Clippy and
format; compare complete propagation state against the scalar oracle across
units, moves, deletion, conflicts, queue rewinds, backtracking, growth and
mode fallbacks. Include independently checked proofs and native Rayon owner
moves. Inspect release/perf code to verify internal assignment, fixed bases
and removal of the per-unit scanner return; repair missed transformations
before spending a performance cell.

Use Rust 1.96.0 / LLVM 22.1.2, the retained lockfile and ordinary portable
release/perf. Reuse compatible fd01d0b j3037 cost `0ec1f4bfcfe8f5f9` and
Kissat 4.0.4 `45a3c8f2e3057841`; verify DIMACS source compatibility first.
Use the existing once-only `header-lookahead-engineering-v1` protocol:
CPU 15, seed 0, CaDiCaL preset, sweep/definitions disabled, MAXC=10000000,
printed model, warmed input/binary, anonymous tmpfs output, whole-process
user instructions/cycles and 300-second emergency cap. Clear unrelated
overrides, record constrained-thread/load evidence and overlap no own build.
Require exact stdout, >=99.9% PMU coverage and <=5% off-CPU for usable wall.
Retain quality failures without retries; unchecked UNSAT stays unverified.

Start with one candidate j3037 cell. Advance to one paired si2 confirmation
only with >=5% fewer instructions and no usable wall regression, or >=10%
lower usable wall/cycles with <=1% extra instructions. Confirmation requires
exact output, an independently checked original-CNF SAT model, <=3% si2
instruction/wall regression and >=5% two-input wall improvement. This is a
bounded exact-trajectory engineering screen, not a population estimate or
a new Kissat-suite geomean. Full workspace build/nextest/doc-tests/Clippy/
fmt/docs and fresh installed-Z3 4.16.0 parity precede production landing.

A failed screen gets one LBR cost diagnosis with the retained profile quality
checks. At most one measured repair is allowed when code/profile identifies
removable overhead, with its design recorded before timing. Diagnose why the
ownership change failed and whether it combines usefully with a prior neutral
mechanism; do not add historical percentages or launch parameter sweeps.
Archive rejected source and findings on main and remove idle worktrees.

## First complete-engine result

Prototype `a5854e4301723ba9ce3ed95c1a55e5bddb214973` retains fixed trail,
watch-directory and arena borrows through ordinary propagation. Its two
watch phases inline into one 3615-byte engine with 248 bytes of local stack.
There is no scanner or assignment call in that body; remaining calls handle
growth, conflict-tail copying, deallocation and panics. Optional modes keep
the prior path. The engine still takes/restores a Vec owner per literal.

| j3037, seed 0 | Qualified fd01d0b | Complete engine |
|---|---:|---:|
| Whole-process user instructions | 254596496994 | 215038292878 |
| Whole-process user cycles | 164287697694 | 167238370939 |
| Wall | 36.13 s | 36.72 s |
| Off CPU | 0.332% | 0.300% |
| Conflicts | 330565 | 330565 |
| Propagations | 323390316 | 323390316 |

Complete stdout is byte-identical. Instructions fall **15.54%**, but wall
rises **1.63%** and cycles **1.80%**, failing the advancement gate. Both
counters have 100% coverage, zero major faults and 271 involuntary switches.
Foreign work remains possible; a passing off-CPU gate does not isolate cache
or frequency interference. These small wall differences are not a reliable
population regression estimate. Cost record `d368266c5252a0db` retains the
unchecked UNSAT as unverified. No si2 or new Kissat cell ran.

The [flamegraph](assets/2026-09-10-complete-propagation-engine.svg), record
`271ea7c983b9e25a`, passes the diagnostic gates: 20801 samples, zero
loss/throttle, 100% coverage, seven kernel-labelled samples and 0.0337%
unresolved self weight. The engine has 70.24% self weight. Its prefix blocker
read (`0x64169`) has 7.59%; prefix/suffix branches following the deletion
byte tests (`0x64184`, `0x6447b`) have 5.99%/6.98%. Binary overflow metadata
(`0x63f27`) has 4.13%, destination capacity (`0x64559`) 3.17%, and watch-owner
transfer (`0x640ad`) 2.05%. Skid prevents interpreting these as cache-miss
counts or directly removable cost. Assembly does establish a deletion-byte
load/branch followed by a separate length load on each live payload, and
three owner-clearing stores plus restoration per dequeued literal. The
profile's sampled-prefix counters and elapsed time are diagnostic only;
they do not replace the original cost cell. Terminal storage geometry and
output are unchanged (apart from the registered terminal memory line).

Preflight: 1016 default SAT tests pass across the original run and a focused
rerun of the one missing-corpus setup failure; 1043 all-feature SAT tests
pass, with one existing skip. Strict SAT Clippy and format pass. The native
oracle includes 1296 generated states and full solved-model/LRAT checks;
new tests cover mixed primary/overflow chains, growth, compaction, requeue,
mode gates and prebuilt owners moved into Rayon. The focused ownership test
passes strict-provenance Miri (75.56 seconds, nightly 2026-06-11). A
supplementary 1296-case Miri run was stopped after several minutes for cost;
it is **incomplete, not a pass**. Source bundles, binaries, identities,
assembly, logs and once-only raw results are cached under `precompile/a5854e4/`.

## One cost-directed combined repair

Keep the complete engine and change two remaining access patterns together.
First, split the fixed watch directory around the current literal and borrow
its Vec in place. Moves may append only to the disjoint prefix or suffix:
their replacement literal is undefined, whereas the current trigger is true,
so a move back into the current list is impossible. Assert this condition;
do not silently drop a move. This removes owner take/clear/restore/drop work.
The old per-unit Solver callback prevented retaining this borrow; the full
engine makes it possible. Price the extra destination-side branch and any
additional live pointer state rather than assuming an automatic saving.

Second, read the current header's first eight initialized bytes as one word
and decode length/deletion from that value. Reuse the native-endian encoding
from the rejected raw-header pipeline, with offset/alignment assertions and
decoding tests. There is no future-header preparation, pending watcher or
distance choice. This combines that representation with the complete engine
without importing the previous pipeline's bookkeeping. Preserve the actual
header layout, liveness checks, literal mutation order and reason validation.

Before the one repair cost cell, require no take/restore/deallocation in the
engine, one current-header word read supplying both length and deletion, no
second length read after its branch, and no increase beyond 248 bytes of
local stack. Run default/all-feature SAT and focused strict-Miri coverage of
the changed access paths, strict Clippy and format. Keep the original cost
and confirmation gates. No second profile, ablation, distance search or cost
retry. A passing combined result would not isolate either component's effect.

### Repair preflight: narrow the directory borrow representation

The safe two-slice implementation removes owner transfer and reads one header
word at `0x6423c` / `0x644b5`, with length reused from its low word. However,
its engine grows to 4022 bytes and 264 local stack bytes, failing the 248-byte
preflight bound. No cost cell was spent. It retains both destination slice
bases/lengths and selects/rebases the target on every move.

Refine the same disjoint-borrow operation to a checked directory view with
one excluded row: retain a raw base, total length and excluded index, plus
an exclusive lifetime marker. Derive the base before creating the current
row reference, never form a slice covering that row, and reject out-of-range
or excluded targets before creating a mutable destination reference. This
requires two small unsafe blocks for reference creation; no unchecked public
API or Send/Sync assertion. The view never leaves ordinary propagation.
This removes the second base/length and target rebasing while preserving the
same ownership rule. Re-run strict Miri on simultaneous current/destination
borrows, growth on both sides, repeated directory borrows and rejection paths,
plus native Rayon/exact-state tests. The original assembly/cost gates stand.
