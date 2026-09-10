# Long-list propagation with internal assignments

## Registration

Target the mode-matched Kissat wall and cycles-per-conflict gap. The production
work ledger on crn records 115235008 long-watch visits and 3337228 long-clause
assignments. The current scanner yields to Solver for every assignment. The
archived complete engines removed these yields and reduced instructions, but
failed wall qualification; their wider live state and hot arena-base reloads
are concrete costs to avoid. Combine their fixed-domain assignments and
borrowed live-clause identities with a narrower, non-inlined long-list scan.
Keep the outer trail/BIG loop in production. This tests the combination, not
an unchanged rerun of a rejected complete engine.

One exclusive assignment view covers one nonempty watch list. It reserves
enough additional queue capacity for the variable domain, retains fixed value
and metadata slices, and publishes only initialized assignments on exit. It
does not own or advance the propagation head. A live-clause borrow supplies
the stable reason without a second header validation. Prefix and compacting
suffix are separate non-inlined scans; their only transition is the first
removal, so native call depth is bounded by two. No callback, variable growth,
arena relocation, backtracking or cross-worker pointer can occur inside them.
The existing scanner remains responsible for LRAT, reason statistics and HBR;
active observers retain their existing fallback. No new runtime option.

Preserve literal/watch order, true-tail parking, eager watched-pair
normalization, assignment levels/reasons/indices, first conflict and unvisited
suffix, binary-before-long order, budgets, all work-ledger events and scheduling
ticks. This is an execution experiment with exact-state and stdout checks;
there is no new heuristic or choice requiring a matched null. Reference
inspection: CaDiCaL propagate.cpp/search_assign and Kissat inlineassign.h /
fastassign.h establish the undefined-literal assignment invariants; Nixie's
existing semantics, including its stable reasons and callback timing, prevail.

Preflight: default/all-feature SAT suites, explicit fast-path and callback
gate checks, the exhaustive scalar state oracle, assignment-view unwind and
duplicate-prefix tests, borrowed-identity relocation tests, strict-provenance
Miri on the new unsafe boundaries and native Rayon owner moves. Strict SAT
Clippy and formatting must pass. Inspect portable perf assembly for internal
units with no queue growth, bounds branches or repeated reason validation;
each scan's local frame must be at most 160 bytes and their combined text at
most 4096 bytes. Account separately for entry reservation/view setup and
publication. One source-directed preflight repair is permitted; no annotation
sweep or gate relaxation after inspection. Failed preflight ends before cost.

Retain Rust 1.96.0 / LLVM 22.1.2, the root Cargo.lock (SHA256
3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439),
portable release/perf profiles and CPU 15 Atom. The once-only manifest is crn
seed 0 first, then j3037 seed 0 only after promotion; CaDiCaL preset,
MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0, NIXIE_DEFINITIONS=0.
Warm input/binary, anonymous tmpfs output, GNU time 1.10 and grouped user
cycles/instructions/branches/branch-misses; 300-second emergency cap. No owned
build during timing. Record every start/completion and canonical benchstore
cell; reuse existing cells and never retry failed quality. Require exact
stdout, PMU coverage >=99.9%, no major faults, off CPU <=5%, and unchanged
identity/runtime of constrained sleeping threads. Other host load and older
controls limit wall attribution; this is a short engineering screen, not a
suite-wide speed claim.

Reuse crn production record 0840cab28aa276cb (11003252708 instructions,
6547224939 cycles, 1.44 s wall). The new ordinary production binary at 38e4f53
has byte-identical executable text to that fd01d0b control. Advance only with
at least 5% fewer instructions and at least 5% lower usable wall and cycles,
and RSS <=110% of control. Held-out j3037 reuses 0ec1f4bfcfe8f5f9 and must
not regress instructions/wall/cycles by more than 3%; require >=5% two-input
wall improvement. Retain mode-matched Kissat 4.0.4 record 45a3c8f2e3057841 as
the j3037 target context; do not rerun references. Allow one ledger-only crn
invocation to check all counters against 760297a9084a5f60 if cost promotes.
The ledger is a work-equivalence check, not a machine-cost oracle.

A cost rejection gets one cycle/call-stack profile and assembly diagnosis;
no measured repair or second profile this experiment. Record whether the
cost lies in setup/publication, assignments, hot loads or other work, and what
would have to change before a new combination is worth testing. Archive the
rejected source and findings on main. Full workspace qualification and fresh
installed-Z3 parity are required before any production promotion. Z3 is a
soundness gate only. Clean owned worktrees, branches and idle scratch files;
retain source/binary identities and once-only results in the cache.
