# Fixed-domain assignments and borrowed propagation reasons

## Registration

Continue the complete propagation engine toward the mode-matched Kissat wall
and cycles-per-conflict gap. The preceding fixed-queue prototype (`5f6e523`)
removed queue growth and per-edge storage selection but failed its 248-byte
frame gate (264 bytes). It was not timed; that verdict remains closed.

This experiment changes the internal access contracts rather than tuning
its accessor annotation. Reuse the fixed-queue capacity proof and split binary
spans, but eliminate checked assignment stores inside the already-unsafe
`assign_undefined` operation. Its caller must prove an in-domain, undefined
literal. The exclusive view prevents resize/unassignment; both literal-value
slots and the variable metadata slot are therefore in bounds. Keep debug
checks of the domain, undefined value and reserved queue space. Use small
unchecked accesses under that explicit contract; do not change general Trail
APIs, VarInfo representation, queue publication or reason encoding.

Replace the engine's separate `live_lits`/`live_identity` operations with a
live-clause borrow. It holds mutable literals and an immutable borrow of the
same slot's stable identity, in disjoint payload/header bytes. Only the arena
view can construct it, after the existing liveness check. A reason is read
through that borrow on unit/conflict; there is no second lookup, header
copy, or repeated extent/identity/liveness validation. Arena-issued references
are required just as for the existing hot payload access. Allocation bounds,
identity initialization and compaction/ref relocation must be audited, with
focused tests covering identity across mutation, deletion and compaction.
Keep extent/identity diagnostics in debug builds at construction. No unchecked
public interface, global state, custom Send/Sync, overlapping header/payload
reference, or pointer persisting outside the exclusive propagation pass.

Kissat's `inlineassign.h` and `fastassign.h` retain value/assignment bases and
operate under undefined-literal/valid-reason invariants. Nixie's identity is a
stable clause ID, not Kissat's binary/reference reason encoding; preserve
Nixie's original IDs and current-level assignments. The 12-byte arena header
is initialized by `ClauseArena::alloc`, which assigns a checked fresh ID;
compaction copies that header with its payload and synchronously relocates
watch references. A live-clause borrow prevents either operation while the
payload/identity are used. General reason lookup and minimization guards are
outside this change.

This preserves binary-primary/overflow order, binary-before-long order,
eager normalization, immediate watch moves, first conflict/unvisited tail,
levels/reasons/trail indices, requeue, ticks and every diagnostic. Keep the
original mode gate and fallback for bounded propagation, LRAT, HBR and active
observers. It is a representation experiment under exact trajectory checks;
no search heuristic, extra choice or seed selection.

Preflight: focused identity/payload disjoint-borrow and relocation tests,
existing complete-state scalar oracle, default/all-feature SAT suites,
strict SAT Clippy and format, strict-provenance Miri on the new borrows and
fixed queue, and native Rayon owner moves. Portable perf assembly must remove
assignment bounds branches and the second reason-validation sequence, keep
reason loads off satisfied binary edges, and retain no queue grow or per-edge
span selection. The same maximum local frame of 248 bytes and text below
4096 bytes applies. One source-directed preflight repair is allowed if a
specific transformation fails; no annotation/parameter sweep and no relaxing
the gate after inspection. Failed preflight ends without timing.

Use retained Rust 1.96.0 / LLVM 22.1.2 and Cargo.lock, no custom/native flags,
and the once-only `header-lookahead-engineering-v1` protocol. Audit the newer
parser-only changes since qualified production as outside stats_solve's DIMACS
path. Reuse fd01d0b j3037 record `0ec1f4bfcfe8f5f9`, first-engine `d368266c5252a0db`
and mode-matched Kissat 4.0.4 `45a3c8f2e3057841`. CPU 15 Atom, seed 0,
CaDiCaL preset, sweep/definitions off, MAXC=10000000, printed model, warm
input/binary, anonymous tmpfs output, whole-process user instructions/cycles,
300-second emergency cap. No own builds during timing. Require exact stdout,
>=99.9% PMU coverage, <=5% off CPU and unchanged runtime/identity for constrained
sleeping threads. Foreign host load remains an attribution limit. Never rerun
an existing or failed-quality cell.

Spend one candidate j3037 cost cell after preflight. Advance with >=5% fewer
instructions than the first engine and no usable wall regression against
qualified production, or >=10% lower usable wall/cycles than both with no
extra instructions against the first engine. Only then allow a paired si2
confirmation (reuse any compatible control), exact stdout and independently
checked original-CNF model, <=3% instruction/wall regression and >=5% two-input
wall improvement. This is a bounded engineering screen, not a suite geomean.
Full workspace build/tests/doc-tests/Clippy/fmt/docs and installed-Z3 parity
precede any production landing. Z3 is a correctness gate only.

A cost rejection gets one qualified LBR diagnostic. At most one measured
repair is allowed if it removes a specific introduced cost identified by
profile/assembly and is recorded before timing. No second profile, ablation
or repeated cost. Archive rejected source and findings on main, retain the
result store and remove all owned idle worktrees and temporary artifacts.
