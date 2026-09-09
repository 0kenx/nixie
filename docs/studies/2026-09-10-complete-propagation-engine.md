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
