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

## Preflight repair: retain the fixed watch-directory domain

The initial scan has 788/1007 bytes of text and 88/120-byte local frames.
Units inline without assignment checks, queue growth or repeated reason
validation. However, the general WatchLists::add still exposes directory
resize through Vec::extend_with, even though all destination literals belong
to the fixed domain. The suffix reloads its arena base twice per clause miss
and value base per tail probe. Smaller frames alone have not removed the
introduced hot reloads. Use the one preflight repair to pass an exclusive
mutable slice of destination Vecs, preserving each list's normal checked
index and Vec::push but structurally excluding directory resize. This is a
borrow-contract correction, not an annotation sweep. Keep the initial
assembly and qualification logs; final-source tests/codegen must be rerun.

## Final preflight

The repaired prefix is 677 bytes with a 56-byte local frame; the suffix is
916 bytes with a 104-byte frame. Six saved registers are additional, and the
bounded prefix-to-suffix call retains the prefix frame. The directory-growth
call is gone. Unit paths at 0x63e21 and 0x64d00 read the borrowed reason and
store values/metadata/queue directly: no assignment bounds branch, queue
growth or second header validation. Each unit still publishes the local
initialized-length field; each list reserves/checks capacity, builds views
and publishes the real Vec length on return. The suffix still reloads its
arena base from [rsp+0x18] at 0x64bc5/0x64bd1 and its value base from
[rsp+0x8] at 0x64c4d on tail probes. The repair reduces frame/text and removes
an impossible resize path; it has not eliminated all hot reloads. Price these
costs in the registered whole-process screen.

Final source passes 1018 default SAT tests and 1051 all-feature SAT tests,
one existing skip in each, including the 1296-state scalar oracle, exact
ledger comparisons, callback gates and native Rayon owner moves with domain
growth/rebuilds. Strict SAT all-feature/all-target Clippy and workspace format
pass; SAT doctests pass 2 with 1 ignored. Five focused strict-provenance Miri
tests pass (nightly 2026-06-11, seed 42): two assignment-view cases, disjoint
live identity/payload across relocation, unit resumption/conflict suffix and
first-hole compaction. The initial suites also passed; reruns follow the one
source-directed repair, not performance resampling. Full workspace gates
are reserved for promotion and have not been claimed.

Safety audit: the assignment view reserves domain-size *additional* space,
so repeated entries in the old prefix cannot invalidate its capacity proof.
Every new assignment requires an undefined in-domain variable, consumes one
such variable and cannot be undone through the view. Both truth signs and
VarInfo are fixed exclusive slices; Drop exposes only initialized queue
entries and leaves the propagation head untouched. Arena allocation checks
size and identity exhaustion before initialization. Shrink preserves identity;
compaction relocates references together with initialized headers/payloads.
A borrowed live identity excludes deleted/null slots and occupies disjoint
bytes from mutable literals. WatchLists::propagation_lists fixes the directory
size; checked indexing still diagnoses any violated destination-domain
invariant. No new Send/Sync implementation, shared raw pointer or native
recursion of input-dependent depth is introduced. Callback and active-observer
paths remain complete. No production promotion follows from these tests alone.

For the single conditional rejection diagnostic, use the existing grouped
user-cycle/instruction LBR capture with cycle period 4194301, 128 mmap pages,
sample CPU/period/read and running-time audit. Require zero loss/throttle,
CPU 15 only, >=99.9% PMU coverage and >=1000 resolved samples. Its elapsed
time is diagnostic only; it is not another wall observation for the screen.

## Held-out rejection and diagnostic selection

Crn passes its screen (record 2963f46b6fbec7b5): 10341053204 instructions,
5897352419 cycles, 1.30 s wall, versus retained 11003252708 / 6547224939 /
1.44 s. The held-out j3037 fails (61e1dc00d8f1cb07): 240848667915 instructions,
171361547817 cycles and 37.66 s wall, versus 254596496994 / 164287697694 /
36.13 s. Both stdout streams match their controls exactly; both captures
have 100% PMU coverage, zero major faults, <1% off CPU and unchanged audited
sleepers. Other host activity and noncontemporaneous controls remain limits.
The registered <=3% held-out cycle/wall regression rule fails, as does the
>=5% two-input wall rule. There is no production promotion.

Spend the single registered rejection profile on **j3037**, the input which
actually rejects the combination, rather than on passing crn. Keep the
registered 4194301 cycle period and all quality checks. The cached profile
runner is adapted to this input before invocation. No crn diagnostic, ledger
capture, control rerun, second profile or measured repair will be spent.

## Verdict and cost diagnosis

**Reject this combination for production.** It clears the short anchor and
fails the registered held-out wall/cycle gate. The two-input wall ratio is
0.9701 (3.0% lower), short of the registered 5% screen; this two-cell result
is not a suite geomean or a statistically established speedup.

| Input | Instructions / production | Cycles / production | Wall / production |
| --- | ---: | ---: | ---: |
| crn | 0.9398 | 0.9007 | 0.9028 |
| j3037 | 0.9460 | 1.0431 | 1.0423 |

J3037's cycles per retired instruction increase by 10.26%, despite fewer
instructions. Against the retained mode-matched Kissat 4.0.4 record, its
37.66 s is 2.088x the reference's 18.04 s; production was 36.13 s. Kissat's
conflict/propagation trajectory differs, so this is elapsed-time context,
not equal-work pricing. Nixie's candidate/control trajectories match:
87939/330565 conflicts and 3817687/323390316 legacy propagations on crn/j3037.
Both cost runs report UNSAT without independently checked proofs; canonical
records correctly classify them as unknown/unverified.

The one diagnostic, c00bfaceb697a362, captured 39695 leader samples on CPU 15,
100% PMU coverage, zero lost records and 0.0126% unresolved self weight, but
**2923 throttle and 2923 unthrottle records**. It therefore fails the stated
quality gate. Its 36.89 s instrumented elapsed time is not a replacement cost
cell, and sampled function/address weights cannot establish cycle shares or
causality. The [throttled call-chain visualization](assets/2026-09-10-long-list-internal-assignment-throttled.svg)
is retained explicitly as exploratory evidence. No replacement capture was
run. For a subsequent study, return to the previously qualified 10472903
cycle period; this host has a 2000/s maximum sample rate, and this more
aggressive grouped capture failed its throttle check.

Static assembly provides firmer evidence of costs to remove:

- The ordinary list path at 0x4b3d2..0x4b409 executes nine mode-check
  instructions, including the reason-statistics OnceLock checks, for every
  nonempty list. The following setup/call block at 0x4b409..0x4b4c7 has 32
  instructions; publication/return handling has another ten. These are
  straight-line static counts, not measured dynamic totals or all incremental
  overhead against the old caller. They show that the fixed-domain proof is
  paid afresh per list even when no unit is produced.
- In the suffix, 0x64bc5 and 0x64bd1 reload the arena base before header/payload
  access, and 0x64c4d reloads the value base for every tail probe. The retained
  yielding scanner compiled in the **same binary** uses an already live arena
  base at 0x64046 and value base at 0x640ed. Internal assignment adds state
  which competes with these hot bases. The narrower boundary did not prevent
  the added dependent loads; a frame-size ceiling was insufficient.
- The outer propagate function still has a 296-byte local frame. Prefix and
  suffix frames are additional to that caller and to saved registers. Small
  individual callees do not establish a smaller live call chain. The setup,
  unit, and suffix paths all need to be priced together.

These instructions are concrete implementation costs, but the failed profile
and older controls do **not** establish how much of the observed regression
any one causes. There is no defensible Amdahl percentage to quote from this
capture. The source-level transform remains promising on crn; it is not a
blanket argument that internal units, fixed borrows or narrow kernels fail.

The next distinct combination should amortize the fixed-domain view and
callback gate over one **propagation session**, retaining the narrow long-list
call boundary. Put assignment-only metadata work behind a small internal
assignment leaf if that keeps arena/value bases live through both scanning
phases; this leaf need not return a Unit event to Solver or revalidate the
reason. The full-engine prototypes already supply a sound session capacity
proof, and this study supplies the narrow-list boundary. Their combination
must demonstrate removal of per-list setup **and** hot base reloads in assembly
before another cost screen. Keep scheduling ticks, event counts, unit order,
callbacks and the complete legacy path unchanged. Do not retry this exact
per-list view, sweep inline annotations, or select a list-length threshold
from these two outcomes.

Candidate source 7842303bd99e90b95612a8f6402d29f3ed1a848d is preserved as a
[reconstructible patch](assets/2026-09-10-long-list-internal-assignment.patch)
against e4ef34c9, with [qualification/codegen/profile audit](assets/2026-09-10-long-list-internal-assignment-audit.json).
Cached release SHA256 is
e19abe8cad03a79d9e02661a9ab0d49c9d5d57ac93056a7e5501d9d1dcb84f47;
perf SHA256 is
0a955071eddc6bb02717c9fb1ba18746ffe4e3d5c3e201a8074454ee4a57daef.
The cache at precompile/7842303 retains the exact lock, bundle, patch, binaries,
preflight logs, raw outputs and once-only records. An archive-manifest setup
error and a missing profile-auditor copy were corrected before their respective
solver invocations; neither started an extra solver cell. Total performance
budget spent: two cost cells and one rejected-quality diagnostic, no reference
reruns. No solver code is promoted to main, so the production wall gap remains.
