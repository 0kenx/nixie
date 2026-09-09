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

## Preflight findings

The initial source achieves the registered shape without a preflight repair.
The final perf build has a **3098-byte** engine at `0x63cc0`, with **216
local stack bytes** (six saved registers are additional, as in the previous
comparisons). The closed fixed-queue prototype was 3707/264 and the first
complete engine 3615/248. No speedup follows from code size alone.

Binary satisfied exits at `0x63e84` and `0x63f11` precede their reason loads;
assignments contain no array-length comparison. The long unit path at
`0x64144` reads the borrowed identity and writes values/metadata/queue with
no second header or extent validation. No queue-growth call or per-edge span
selection remains. The queue pointer now stays in a register through the
binary and long scans; destination-buffer growth may spill it. The view's
initialized-length publication per unit remains. Later measurement must
price the whole combined implementation, including conservative reservation.

The new disjoint identity/payload test passes strict-provenance Miri in
3.83 s; the three fixed-queue tests pass in 18.73 s and the moved-owner,
compaction/growth/requeue test in 76.12 s (seed 42, nightly 2026-06-11).
The default SAT suite passes all 1020 tests, one existing skip. Strict SAT
all-feature/all-target Clippy and workspace format check pass.

Safety audit: Trail construction and general growth allocate both value
signs together with each variable metadata slot. The unsafe append's
in-domain/undefined contract therefore covers all three unchecked stores;
its borrow excludes resize and unassignment. Arena allocation checks extent
and ID exhaustion before initializing `header.identity` from the cold
identity-table length. Shrink writes payload/length/glue only. Compaction
copies the whole initialized header/payload, after preparing relocation;
ClauseDatabase rewrites watches through that plan before applying movement.
Live-clause construction excludes NULL/deleted slots before borrowing the
identity. Its shared four-byte header field and mutable payload beginning
at byte 12 do not overlap, including when sharing one backing u64. The type
system excludes arena mutation while those borrows live; Miri exercises
simultaneous identity reads across payload writes and subsequent relocation.
General checked arena/reason APIs and minimization guards are unchanged.

The latest baseline-source differences outside this prototype are four
nixie-core arithmetic/parser files. `stats_solve` uses nixie-sat's DIMACS
parser directly; these changed SMT-LIB/AST rewrite paths are outside the
measured invocation. The retained compiler/lock and portable profiles remain
the same as the qualified cached control.

The all-feature SAT suite also passes **1047 tests**, one existing skip,
including the exhaustive state oracle and native Rayon owner test. Release
and final perf builds complete. All owned compilation/test processes finish
before the cost screen. No preflight repair or performance cell was spent
while establishing these conditions.

## Cost result: instruction improvement, wall qualification unavailable

Candidate source is `d8e78052eeb17f319c5408efde5a1daea72749cd`, based on
reachable registration `b16bd925`. One j3037 cost invocation produced record
`ad734ce0e041b521`. Complete stdout is byte-identical to qualified production:
330565 conflicts and 323390316 propagations. The observed UNSAT is retained
as **unknown/unverified** in the result store because this cost invocation
did not independently check a proof.

| Arm | User instructions | User cycles | Wall | Off CPU |
| --- | ---: | ---: | ---: | ---: |
| Qualified production `fd01d0b` (reused) | 254596496994 | 164287697694 | 36.13 s | 0.332% |
| First engine `a5854e4` (reused) | 215038292878 | 167238370939 | 36.72 s | 0.300% |
| Borrowed reasons `d8e7805` | 203854720117 | 374190576943 | **136.18 s, unusable** | **34.866%** |
| Mode-matched Kissat 4.0.4 (reused) | 121059163625 | 79144759362 | 18.04 s | retained qualified record |

The candidate executes **19.93% fewer instructions than production** and
**5.20% fewer than the first engine**. This clears the instruction portion
of the registered screen. Kissat has a different search trajectory, with
286784 conflicts and 218808022 propagations; the table is not a comparison
of identical work between solvers or a suite geomean.

The candidate fails wall quality: user time is 87.90 s, system time 0.80 s,
with 19885 involuntary and 691 voluntary context switches. Counter coverage
is 100%, major faults zero and peak RSS 34668 KiB. The two constrained
sleeping threads keep their identities and consume no additional runtime,
but that guard does not exclude unpinned competing work. After the cost run,
host load is 54.26 on the 20-core machine, with concurrent foreign Rust
builds, linking and solver sweeps. All owned builds/tests had already ended.

**Neither a wall gain nor a source-induced wall regression is established.**
Cycles and cycles per conflict from this run are also unsuitable for
attributing an implementation effect under that contention. Passing PMU
coverage does not repair timing quality. No si2 confirmation, fresh control,
Kissat rerun or replacement cost invocation is authorized by this result.
Keep this failed-quality cell permanently; do not rerun it or substitute
the diagnostic run's elapsed time.

## Required diagnostic and the remaining cost

One LBR diagnostic produced record `53e7cd2e73fdc8a7` and the
[candidate flamegraph](assets/2026-09-10-borrowed-propagation-reasons.svg).
Its 28365 samples have no lost or throttled records, 100% PMU coverage and
0.02468% unresolved self cycles, meeting the diagnostic quality thresholds.
All samples are on CPU 15. The output matches the cost run after removing
exactly the profile's terminal memory-statistics line. Its 93.825 s elapsed
time and sampled-prefix counters belong to a diagnostic invocation and
are not replacement cost evidence.

The complete engine receives **72.90% of sampled self cycles**. Search,
backtracking, subsumption and clause shrinking/minimization receive 4.21%,
3.40%, 2.99% and 2.60% respectively. Offline address attribution gives:

| Address group | Whole-process sampled self-cycle share |
| --- | ---: |
| Borrowed identity pointer preparation in the three scan bodies | 0.226% |
| Borrowed identity pointer/value reads on unit/conflict paths | 0.021% |
| Prefix blocker value comparison and satisfied exit | 9.455% |
| Prefix/suffix deleted-header tests and following branches | 18.498% |
| Binary overflow pointer load and immediately following spill | 5.814% |

The largest individual IP is the suffix branch following the deleted-byte
test (`0x6430c`, 11.045%); the prefix blocker comparison (`0x64093`) receives
8.740%. These are sampled IP attributions, subject to skid, not cache-miss
counts, exclusive cause measurements or removable-time ceilings. LBR was
captured with `USER|CALL_STACK|NO_FLAGS|NO_CYCLES`; it does not supply a
branch-misprediction diagnosis. Host contention can also change these shares.

The candidate has removed the repeated reason validation, assignment bounds
branches and queue growth identified in preflight. The profile supplies no
dominant introduced cost that justifies spending the optional measured
repair. In particular, rewriting the borrowed identity into another raw
pointer representation would target only a small observed address group
while adding another safety contract. No repair was implemented or timed.

The combination is nevertheless productive at the instruction level:
fixed-domain assignment access removes lengths/checks that the fixed queue
alone kept live, and the live-clause borrow removes a second header/identity
lookup. Together they meet the original stack gate and reduce executed
work. This does not eliminate dependent watcher/blocker/header accesses,
overflow metadata or destination appends. Another header-lookahead,
directory-width or owner-layout variant cannot claim those costs as savings
by adding percentages from earlier profiles. A future structural change
needs to remove an access or consumer and price its replacement; it also
needs uncontended timing before it can establish progress on the user's
wall target.

## Archive and disposition

This experiment used **two performance invocations: one cost, one diagnostic**.
The instruction result is positive; production promotion remains unqualified.
Do not classify the implementation as a demonstrated slowdown or silently
turn the failed-quality cost cell into a fresh retry. Any future attempt to
qualify wall requires a separately registered comparison and a quiet host,
with this failed-quality record still included in the study history.

The [archived source patch](assets/2026-09-10-borrowed-propagation-reasons.patch)
reconstructs the complete tested candidate, including its regressions, from
`b16bd925`. It is archival source, not a production patch recommendation.
The patch is checked against both current main's SAT source and the original
base using a temporary Git index, whose resulting tree must equal the
candidate tree. The live production SAT implementation is unchanged.

`precompile/d8e7805/` retains the verified source bundle and original patch,
release/perf binaries, Cargo.lock, compiler and binary identities, preflight
logs/disassembly, canonical records, raw cost/profile output, scripts and
offline address attribution. The bundle requires reachable `b16bd925`.
Lock SHA-256 is
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
The experimental worktree, branch, corpus symlinks and owned `/tmp` artifacts
are removed after archiving; the result store and foreign work remain.

The completed SAT preflight is recorded above: 1020 default tests, 1047
all-feature tests, five strict-provenance Miri tests, native Rayon ownership,
strict SAT Clippy and workspace formatting. Full workspace build/tests,
doc-tests/docs and fresh Z3 parity were not run because no solver change is
being promoted. They remain required before any future production landing.
