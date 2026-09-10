# Bounded traversal cursors inside a propagation session

**Final verdict: do not promote.** The selected implementation reduces
four-input instructions by 11.45% and cycles by 5.05%, but observed wall
improves only 4.18% and noL regresses 5.88%, failing its 3% guard. Complete
Nixie output remains identical. Six new cost cells and one diagnostic ran;
the source, measurements and flamegraph are archived below.

## Registration

Continue closing Nixie's wall/cycle gap against Kissat. The archived session
and assignment leaf (ebaef56) removed per-list setup and truth-owner loads,
but retained an arena-plus-tail base and indexed traversal coordinates. Its
tail index overwrote the arena register, requiring restores on tail exits.
This experiment changes traversal representation, retaining that session,
the assignment leaf and the complete callback/observer fallback.

Split the two watched literals from the clause tail and walk disjoint tail
slots directly. Replace indexed watch compaction with bounded read/write/end
cursors; compute the kept count only at the outer list boundary. Exclusive
slice ownership must exclude reallocation and aliased element references.
Each consumed entry may be kept once or removed; write never overtakes read.
Preserve the unvisited suffix on conflict, including overlap and empty lists.
Keep small unsafe operations inside the cursor primitive, with no custom
Send/Sync or persistent raw pointers. Retain a no-removal prefix and at most
one transition to compacting suffix, so call depth is independent of input.

Kissat proplit.h and CaDiCaL propagate.cpp are the local cursor/end traversal
references. Do not import their saved clause-search positions or different
replacement/normalization policies. Preserve exact Nixie clause order, eager
normalization, blocker updates, true-tail parking, first undefined watch move,
unit/reason order, conflicts, budgets, scheduling ticks and work ledger.
This is an implementation screen, not a heuristic change or a seed search.

Before cost, inspect portable Rust 1.96.0 / LLVM 22.1.2 perf assembly using the
frozen lock 3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439.
Require cursor/end traversal and direct truth/arena bases on blocker and
nonassigning tail paths: no repeated owner dereferences, saved derived-tail
base load per miss, or arena restore after ordinary true-tail exits. Calls
may preserve bases on units or destination growth; record those costs.
Record text/frame sizes without treating size as speed. Permit one specific
source-directed repair if the intended representation fails to lower; stop
at preflight if it still fails. Do not sweep encodings or inline annotations.

Run default/all-feature SAT tests, doctests, strict SAT Clippy and formatting
before cost. Extend the scalar oracle across tail truth patterns and both
compaction phases. Test cursor empty/end/overlap/early-conflict cases,
assignment queue publication and borrowed arena identity with strict-
provenance Miri; retain native Rayon owner-transfer and callback checks.
Full workspace verification and installed-Z3 4.16.0 parity remain mandatory
before production promotion. Z3 is a soundness gate, never the perf target.

Use default Nixie sweeping ON explicitly (NIXIE_SWEEP=1), definitions OFF,
CaDiCaL preset, seed 0, MAXC=10000000, PRINT_MODEL=1 and cleared other study
overrides. Reuse production fd01d0b's constraints cell 14d6f38d3c5c5cb9
(53147102832 instructions, 45156742562 cycles, 10.01 s). Run candidate
constraints first, requiring at least 5% lower instructions and qualified
wall/cycles. Only if it passes, run production/candidate crn and candidate/
production j3037, reusing any compatible cells; require no input regression
above 3% and at least 5% three-input wall improvement. Finally allow one noL
candidate against sweep-ON 36990e8006fa9aac, with the same 3% regression cap.
At most six new cost cells; no repeated cells or reference reruns. Reuse
Kissat 4.0.4 with the user's disabled-pass options as target context. Never
join sweep-OFF Nixie cells into this default-mode comparison.

Use the retained CPU15 Atom setup, portable release, warmed input/binary,
anonymous tmpfs output, GNU time 1.10, grouped user instructions/cycles/
branches/misses, 300-second cap and no owned builds during timing. Require
at least 99.9% PMU coverage, zero major faults, at most 5% off CPU and audited
idle guards. Instructions are the primary execution counter; scheduling
ticks establish workload equivalence and remain untouched. Cached-control
age and shared-host interference limit wall attribution. Store every start,
completion, exact output/model comparison and canonical record once.

A cost rejection permits one CPU15 cycle/LBR diagnostic on the rejecting
input, period 10472903, requiring at least 1000 resolved samples, 99.9% PMU
coverage, zero lost/throttled records and less than 1% unresolved weight.
Its time is not a replacement cost cell. No measured repair or second
profile. Archive any rejection with its source, generated code and causal
limits on main; clean the owned worktree and build artifacts afterward.

## Initial code generation and one preflight repair

The bounded entry-token API scalarizes: no cursor-owner load remains in the
watch loops. Prefix/suffix bodies are 620/577 bytes with 72/56 local stack
bytes, plus six saved registers each. The suffix loads its three cursor
coordinates once at entry; prefix passes it an aggregate only at the first
hole. The tail iterator lowers to a moving slot pointer and remaining byte
bound, two coordinates instead of base/length/index. It retains the same
truth tests and selected-literal order.

Both truth and arena bases now remain live on blocker, first-watch and
true-tail paths. Prefix uses rcx/r14; suffix uses rdx/r9. The old suffix
per-tail-entry derived-base stack load and ordinary true-tail arena restore
are absent. Prefix still restores a destination-directory argument at
0x64242 and recomputes arena+16 at 0x6424a after true tails. The suffix
restores its derived base after a watch move, and assignment/growth calls
still preserve state. Those remaining costs must be measured, not hidden
behind the representation improvement.

Use the single preflight repair on a newly exposed finish-path defect:
LLVM emits memmove at 0x6509c after every completed suffix even though its
remaining length is zero. Add an explicit read==end return before suffix
copying. This is a specific failed empty-copy elimination, not a source
encoding sweep or a measured repair. Preserve overlapping memmove for actual
unvisited conflict tails and rerun the affected Miri/code-generation gates.
No cost invocation has occurred.

## Pre-cost amendment: withdraw the optional empty-copy change

The explicit empty-copy exit grows the suffix to 584 bytes and does remove
the zero-length memmove. It also changes register allocation: 0x64f67 now
loads arena+16 from `[rsp+0x30]` on every miss reaching the tail. The original
577-byte suffix held this derived base in r13. The main arena and truth
bases remain direct in both versions, but the optional change violates the
registered derived-base requirement. It is not eligible for the cost screen.

Withdraw that optional repair and freeze the **original cursor implementation**,
which already passed the required traversal shape. Retain its zero-length
memmove as a cost to price. This explicitly amends the earlier instruction
to stop after a failed repair: the failed repair is discarded before timing,
and the already eligible initial implementation receives the single cost
screen. Both source forms and their assembly are archived. No cost has run,
no thresholds or instance order change, and neither timing both variants nor
a further code-generation repair is permitted. Repeat affected final-source
qualification, including the wider observer-layout Miri tests, before cost.

An initial all-feature test build also found that the new fixture constructed
Watcher directly without its observer-only identity field. Use the existing
Watcher::new constructor; this changes test setup only. Native all-feature
qualification then passes 1,054 tests, and the guarded-copy source passes
eight focused Miri checks. These passes are labelled by source form rather
than silently transferred to the selected unguarded-copy implementation.

## Selected source and correctness qualification

The measured source is `f5e75a749d03701dd07e404b0aefcd8e4ad45e63`, tree
`f99d4355079f580cd3b393cd89843e3a62d5370a`, based on `7437a6d3`.
The [source patch](assets/2026-09-10-bounded-propagation-cursors.patch)
includes the earlier session/assignment leaf, the bounded watch cursor,
disjoint clause-tail traversal and their tests. Applying it to the recorded
base reconstructs the exact committed tree. It also applies to main at
`7fda78e0`; neither applicability nor a test pass licenses production use.

The final perf rebuild is byte-identical to the initial eligible cursor
binary. Release SHA-256 is
`69c731e4351f91ae1680df81abf527c11afb096065b800e7854f8c8e5d1cd70a`;
perf SHA-256 is
`47064e58e9c8e53c6b3624282c4bb310e12caea215b49c49c796c8b5d2c90cda`.
The registered compiler, frozen lock and portable build settings match.
The [assembly](assets/2026-09-10-bounded-propagation-cursors-codegen.txt)
retains the selected scan bodies, assignment leaf and outer driver.

The cursor owns one initialized mutable slice. A consumable entry token
prevents a second keep of the same entry; advancing the read cursor and
keeping an entry preserve `write <= read <= end`. Pointer arithmetic stays
inside that allocation, including the one-past endpoint. Conflict completion
uses overlap-safe copying of the unvisited suffix. The two clause-head slots
and mutable tail are disjoint borrows. No custom Send/Sync implementation or
input-dependent native recursion is introduced. Assignment publication and
borrowed arena identity retain their previously tested ownership contracts.

Selected-source checks passed before cost:

- 1,021 default SAT tests and 1,054 all-feature SAT tests, one existing skip
  in each configuration; two doctests passed and one remained ignored.
- Strict SAT all-feature/all-target Clippy and workspace formatting.
- The existing 1,296-state scalar oracle and 6,534 additional tail patterns,
  with complete clause/watch/trail/reason/work comparisons; native Rayon,
  independent model and LRAT checks remain in the suite.
- Eight focused strict-provenance Miri checks: two cursor tests in the
  observer layout, two work-ledger cases, unit/conflict resumption, two
  unchanged queue publication/duplicate/unwind checks, and unchanged
  borrowed-arena relocation/identity. The last three component checks are
  retained unchanged-component evidence, not reruns of different source.

Full workspace build/nextest/Clippy/docs and installed-Z3 parity were **not
run after the cost rejection**. These remain required before any solver
promotion. Only this study and its archival assets land on main.

## Cost result and unchanged workload

Both Nixie arms explicitly use sweep ON. Production is the cached
`fd01d0b` binary; the earlier sweep-OFF panel is excluded. The two cached
controls are constraints `14d6f38d3c5c5cb9` and noL `36990e8006fa9aac`.
Fresh cost order is constraints candidate, crn control/candidate, j3037
candidate/control, then noL candidate. Every cell completed; there were no
repeats, replacement controls or reference invocations.

Ratios below are candidate / production; lower is better. The Kissat column
reuses the requested disabled-pass configuration solely as target context.

| Input | Production wall | Candidate wall | Retained Kissat wall | Instructions ratio | Cycles ratio | Wall ratio |
|---|---:|---:|---:|---:|---:|---:|
| constraints | 10.01 s | 8.83 s | 4.63 s | 0.93461 | 0.88233 | 0.88212 |
| crn | 1.44 s | 1.44 s | 0.68 s | 0.89772 | 0.99952 | 1.00000 |
| j3037 | 49.34 s | 44.54 s | 18.04 s | 0.82390 | 0.90292 | 0.90272 |
| noL | 50.99 s | 53.99 s | 16.69 s | 0.88944 | 1.02087 | **1.05884** |
| First three geometric mean | | | | 0.88420 | 0.92688 | 0.92689 |
| Fresh pairs only: crn, j3037 | | | | 0.86002 | 0.94999 | 0.95011 |
| All four geometric mean | | | | **0.88551** | **0.94954** | **0.95824** |

Constraints clears its instruction/cycle/wall gate. Crn is flat in wall
despite 10.23% fewer instructions. J3037 improves observed wall by 9.73% and
instructions by 17.61%; the first-three geometric mean clears 5%. NoL then
fails its 3% wall regression cap. Its cycle increase is 2.09% and instruction
decrease 11.06%. The four-input wall result is inside the 5% neutral band;
the fresh-pair wall ratio also narrowly misses 0.95 before rounding. Do not
select only the first three, substitute cycles for the failed wall guard,
or promote on instruction savings alone.

All new costs have 100% PMU coverage, zero major faults and at most 1.51%
off CPU; idle guards pass. NoL's 53.99 s comprises 52.71 s user and 0.47 s
system, with 959 involuntary switches. Passing these guards does not remove
cached-control age, clock/frequency variation or shared-host interference.
The failed engineering gate is established; a precise source-caused 5.88%
wall regression is not. No new control or repeated cell was used to resolve
that uncertainty.

For every input, complete Nixie stdout is byte-identical between arms,
including the reported model and all counters. Conflicts/propagations are
40,004 / 6,060,215 (constraints), 91,677 / 3,419,615 (crn),
369,688 / 356,572,135 (j3037), and 1,727,396 / 70,174,865 (noL).
Consequently each within-input cycle or wall ratio is also its per-conflict
and per-propagation ratio. SAT models are independently checked against the
input CNFs. The two UNSAT inputs agree across arms, but these benchmark
invocations emit no independently checked proof; their canonical verdicts
remain `unknown`, with the reported UNSAT retained separately.

Kissat 4.0.4 remains the target, with
`--probe=0 --preprocess=0 --factor=0 --substitute=0 --sweep=0 --vivify=0
--transitive=0 --backbone=0 --congruence=0`.
The four retained reference records have matching input hashes, seed and
CPU, and come from earlier measurement windows. J3037's reference PMU group
has two counters instead of four. These observations show substantial
remaining gaps; they are not a fresh suite-wide ratio or evidence that the
original e6d1ddda comparison has improved. Reference identities and the six
new/two reused Nixie records are in the
[audit](assets/2026-09-10-bounded-propagation-cursors-audit.json).

## One noL diagnostic and its limits

The [interactive flamegraph](assets/2026-09-10-bounded-propagation-cursors.svg)
and [attribution](assets/2026-09-10-bounded-propagation-cursors-profile.json)
come from the single actual profile invocation, record `89ad311a4c7c5334`.
An earlier setup attempt failed with ENOSPC while writing its start marker,
before Popen: no solver PID, completed record, output or profile existed.
That failed setup is preserved under `setup-failure-0/`. After archiving and
removing owned duplicate binaries and the source worktree, the permitted
first actual invocation completed. The transient filesystem condition is
not diagnosed as a solver defect.

The capture has 21,180 samples, all on CPU 15, 100% PMU coverage, zero lost,
read-lost, throttle or unthrottle records, and 21,158 user-mode sample IPs.
The other 22 IPs are kernel-labelled/unresolved, receiving 0.10387% of self
cycle weight, below this study's registered 1% limit. The copied helper
additionally enforces 99.9% user-mode IPs, an older study's threshold that
was not registered here, and reports `quality_passed: false`. That original
helper result and canonical metric remain unchanged. The separate offline
assessment explicitly reports **registered gates passed, copied extra gate
failed**; no threshold changed after capture and no replacement profile ran.

The profiled model/output agrees after removing only terminal `memstat`.
Its enclosing diagnostic elapsed time is 49.528 s and its sampled-prefix
counters are 221.816 G cycles / 346.137 G instructions. Neither replaces
the 53.99 s cost cell. Release and perf executable `.text` differ: 997,191
versus 998,135 bytes, with distinct hashes recorded in the audit. Source,
instrumentation, generated layout and host effects are not separated by
this one capture; it cannot prove the wall difference was only host noise.

| Candidate self attribution | Whole-profile cycle share |
|---|---:|
| Compacting watch suffix | 45.099% |
| No-hole watch prefix | 10.212% |
| Subsumption | 8.739% |
| Search body | 7.139% |
| Clause shrinking/minimization | 3.555% |
| Antecedent analysis | 2.502% |
| Propagation driver | 1.941% |
| Assignment leaf | 0.401% |

Disjoint instruction regions attribute 9.434% to deleted-header loads/tests,
7.644% to tail traversal, 3.952% to normalization/first-truth checks and
3.513% to true-tail publication. Several hot suffix IPs are stores: destination
blocker at `0x64fd3` (4.953%), clause tail at `0x64f99` (4.717%), and kept
blocker at `0x64ef3` (3.140%). Destination capacity comparison `0x64fc1`
receives 3.097%. These are sampled instruction-pointer locations subject to
skid, **not** isolated stall costs, branch miss rates or removable time.
There is no paired production profile identifying a regression site.

The six new cost cells show branch misses almost unchanged between arms
(ratios 1.00376, 0.99822, 0.99850 and 0.99872) despite fewer instructions
and branches. The cursor representation removes bookkeeping but does not
demonstrate removal of the expensive dependent read/write work. Assignment
call/publication regions receive only 0.099%, the empty-copy call-site region
0.179%, all sampled libc memmove 0.869%, and RawVec growth itself 0.042%.
The call-site shares exclude callee work; zero or small samples do not prove
zero allocations. Still, these observations give no supported large margin
for another assignment-inline or empty-memmove micro-experiment.

## Combining earlier mechanisms: conditional next direction

The [delayed-move study](2026-09-09-delayed-watch-moves.md) already removed
destination indexing from the old scan and was neutral at 8.88 versus
8.81 s on circuit. It flushed at every Unit/Conflict/Done yield and added
a capacity check plus three stores and a length update per queued move.
Its qualified profile priced queue preparation at 2.124% and flushing at
3.015%. Reserving more capacity alone did not remove those costs.
The [kept-span study](2026-09-09-kept-watch-spans.md) also failed: its suffix
grew 41%, with five memmove sites and more state preservation. The
[packed-watch study](2026-09-09-packed-watch-live-view.md) already examined
copy width and generated-code repairs. None is an untouched easy lever.

A structurally different combination to investigate is delayed moves inside
this complete-list session, with a bounded preallocated append cursor and
one FIFO flush after the entire list. Reserving the maximum move count
before scanning would remove per-move scratch capacity/growth from the loop;
internal assignment would no longer cause a flush at every unit. This could
remove destination-directory liveness and allocation boundaries from the
scan that now dominates. It still writes and rereads a 12-byte move record
(16 bytes with observer identity), and actual destination appends still
occur. Neither text-size reduction nor adding percentages from different
profiles establishes a net saving.

The necessary correctness argument is specific: a replacement is undefined
when selected, while the currently watched literal is false, so its target
cannot be the active list. Callback-free assignment must not inspect the
destination directory. All moves must publish in FIFO order before the next
queued literal is processed, including on conflict, preserving existing
per-destination order and the unvisited tail. LRAT, HBR and observers need
the existing complete fallback. These obligations and buffer traffic must
be checked before a new registration or cost invocation. This combination
is **unimplemented and unmeasured**, not the explanation for the present
result or a promised improvement against Kissat.

## Retained evidence and cleanup

`precompile/f5e75a7/` retains both selected binaries, frozen lock, build
identity, verified source bundle, all selected/guarded preflight logs and
assembly, frozen screen harness, exact outputs, canonical records and raw
profile. The [offline attribution script](assets/2026-09-10-bounded-propagation-cursors-diagnose.py)
reconciles cycle weights and labels generated-code regions without another
solver invocation. Asset hashes, qualification counts, source reconstruction
and both profile-quality assessments are recorded in the audit.

The throwaway source worktree has been removed. Delete its unused branch
and owned `/var/tmp/nixie-bounded-cursors-target-7437a6d3` build directory
after landing this archive; retain the shared binary/result cache. No
production solver change is part of this step.
