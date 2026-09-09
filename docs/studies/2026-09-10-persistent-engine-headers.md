# Header preparation across internal assignments

## Registration

Continue the complete propagation engine toward the Kissat wall/cycle gap.
Recover prototype `a5854e4`, whose fixed arena and value-array borrows survive
ordinary assignments, and combine it with immutable next-header preparation.
The later `69a9c69` directory/header repair saved only 0.051% instructions
against that engine while adding a checked raw directory view; exclude that
extra mechanism. This choice is about representation cost, not treating its
historical wall difference as isolated causal evidence.

Source audit: the engine only changes clause literals; arena allocation,
lengths, deletion and identity remain fixed until its borrow ends. Assignment
queue and destination Vec growth cannot invalidate that arena. Kissat's
`src/proplit.h` / `fastassign.h` establish the fixed value/arena ownership
pattern, but do not supply this pipeline. Retain Nixie's binary-first order,
eager normalization, immediate moves, stable filtering, ticks and conflict
tail exactly. No search policy change or new heuristic claim.

Reuse the raw-header experiment's one-entry consecutive-miss loop. Prepare
only the next non-satisfied blocker's first initialized header word, without
classifying its contents before current literal work. Keep that private word
through an internal unit assignment and consume it without rereading. A true
blocker stays true during this fixpoint; after assignment recheck a previously
non-true next blocker before consuming its preparation. Never retain false or
undefined truth across assignment, or cache any payload literals. Discard
preparation at conflict, list end and prefix/suffix transfer. Duplicate refs
may change literals but cannot invalidate header metadata. Keep the existing
Vec take/restore and the complete engine's optional-mode fallbacks.

Before timing: focused exact-state regressions for assignment changing the
prepared next blocker, duplicate refs, deleted/null headers, queue growth and
conflict tails; default/all-feature SAT tests, strict SAT Clippy/format,
focused strict-provenance Miri and native Rayon owner moves. Inspect portable
release/perf code: next header load before current payload, no next-header
content branch before it, consumption without reread, no per-unit scanner
return, no pending dispatch on ordinary blocker hits. Price live state:
allow at most 32 extra local stack bytes over the first engine's 248, covering
the pending word/ref and next-hit state. A failed assembly gate permits one
source-directed preflight repair, not a parameter search or timing cell.

Use the retained Rust 1.96.0 / LLVM 22.1.2 lock and the once-only
`header-lookahead-engineering-v1` harness. Reuse fd01d0b j3037 control
`0ec1f4bfcfe8f5f9`, first-engine `d368266c5252a0db`, and Kissat 4.0.4
`45a3c8f2e3057841`. Verify source/lock identities. CPU 15, seed 0, portable
release, CaDiCaL preset, sweep/definitions off, MAXC=10000000, printed model,
warm input/binary, anonymous tmpfs output, 300-second emergency cap and
whole-process user instructions/cycles. Record constrained-thread evidence;
no own build overlaps cost runs. Require identical complete stdout, >=99.9%
PMU coverage and <=5% off-CPU for usable wall; retain failures without retry.
Cached observations do not isolate host-load/frequency effects.

Spend one candidate j3037 cost cell only after preflight. Advancement needs
at least 5% fewer instructions than the first engine, or at least 10% lower
usable wall and cycles than that engine with at most 2% extra instructions.
It must also beat qualified production control's instructions by at least 5%
without a usable wall regression. Then allow one paired si2 confirmation:
exact stdout, independently checked original-CNF model, <=3% instruction/wall
regression, and >=5% two-input wall improvement. Full workspace gates and a
fresh installed-Z3 parity run precede any production landing. This bounded
exact-trajectory screen cannot establish a suite geomean.

If the cost screen fails, use one LBR diagnostic with the established loss,
coverage, sample-count and symbolization gates; inspect introduced costs and
underlying algorithm implications. No measured repair or second profile in
this registration. If assembly fails after its one repair, stop without a
cost run. Archive source/evidence and the finding on main and clean idle
worktrees/artifacts. Do not repeat old lookahead width/distance/inline sweeps.

### Assignment-local blocker refresh

Before code generation or measurement, strengthen the source argument: one
internal unit makes exactly `first` true, its opposite false, and changes no
other value. A prepared miss becomes a hit iff its blocker equals `first`.
Use this literal-code equality after assignment instead of rereading the
value array. Previously true blockers remain true. This is an exact
consequence of the assignment operation, not a speculative truth cache.
Cover both the newly true and newly false blocker in the same regression.

## Initial preflight and one lifetime repair

The initial engine compiles to 5923 bytes and 312 local stack bytes, failing
its 280-byte bound. No cost run. Prefix metadata loads at `0x642b8` precede
payload loads at `0x642de`; post-assignment refresh is the literal-code
comparison at `0x644da`. However, pending metadata is written back into the
outer arena object at phase/list exits (`0x64550..0x64567`,
`0x64580..0x64597`). Keeping those fields in a fixpoint-wide mutable object
makes their state flow beyond the intended useful lifetime, with extra
spills and copies. The ordinary hit loop still has no pending dispatch.

Use the one registered source repair to put pending metadata in a private
phase-local wrapper borrowing the fixed arena. Assignments remain internal,
so the preparation still survives units. Prefix/suffix transfer and list
exit end the wrapper and cannot write its pending fields back to the arena.
This enforces the registered discard boundary in the ownership structure.
Keep the distance, blocker rule, scan algorithm and all cost/assembly gates.
Recheck focused strict Miri after the borrow change. No inlining/distance or
parameter search is added.
