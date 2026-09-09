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

### Repaired assembly passes, with a real remaining code cost

Making the preparation phase-local removes its exit writebacks. Local stack
falls **312 -> 264 bytes**; the engine shrinks **5923 -> 5296 bytes**. The
264-byte frame passes the 280-byte bound, but text is still 1681 bytes larger
than the first complete engine. LLVM emits two suffix bodies for different
first-hole transfers; do not count source-level specialization as smaller
machine code without inspecting it.

Next-header loads at `0x6426b`, `0x6464f`, `0x64b00` precede current payload
loads at `0x6429e`, `0x64682`, `0x64b36`. Their contents are not classified
before that work. Consumption uses the saved stack words; unit continuations
retain them, with code-equality blocker refresh (prefix `0x64479`). There is
no scanner/assignment call or ordinary-hit pending dispatch. Remaining calls
are growth, conflict-tail copies, owner restoration/deallocation and panics.
The three focused strict-Miri tests pass again; strict SAT Clippy and format
pass. Complete default/all-feature SAT preflight is required before the one
candidate cost cell. The cost gate prices the extra state, branches and text;
assembly establishes the transformation, not its benefit.

## Cost result: the combination does not qualify

Final prototype `f5d906e65374740c3d03dc4dbc79299912c30285` has exactly the
same complete j3037 stdout as both qualified production and the first
complete engine. Conflicts remain 330565 and propagations 323390316.

| j3037, seed 0 | Qualified fd01d0b | First engine a5854e4 | Persistent headers f5d906e |
|---|---:|---:|---:|
| Whole-process user instructions | 254596496994 | 215038292878 | 231143261197 |
| Whole-process user cycles | 164287697694 | 167238370939 | 218781276385 |
| Wall | 36.13 s | 36.72 s | 52.31 s |
| Off CPU | 0.332% | 0.300% | 1.281% |

Record `d35e26a9cc202b49` has 100% coverage on both counters, zero major
faults, 1053 involuntary and 54 voluntary context switches. User/system
CPU time is 51.51/0.13 seconds. The constrained CPU-15 threads remained
asleep with unchanged identity and runtime. No own build overlapped the
measurement. Other host work remains a limitation: passing off-CPU and PMU
gates does not isolate cache/frequency effects, so the observed 42.46% wall
increase over the first engine is not a causal population regression estimate.
The complete instruction cost is **7.49% higher than that engine**, consuming
part of its saving against production (now **9.21% fewer** instructions).
Both advancement alternatives fail. No si2 or fresh control/Kissat cell ran.
Unchecked UNSAT remains unverified in the result store.

## Diagnostic cost and underlying implication

The [flamegraph](assets/2026-09-10-persistent-engine-headers.svg), record
`d1be0dc820efcfb6`, passes its diagnostic gates: **22579** samples, zero
lost/throttled records, 100% PMU coverage, ten kernel-labelled samples and
0.0443% unresolved self weight. Terminal arena/watch/BIG geometry matches the
first engine. Its elapsed time and sampled-prefix counters are diagnostic
only; they never replace the cost cell above.

The engine has **73.01%** self weight. The prefix blocker read (`0x641dc`)
has 7.81%. The suffix spill immediately after the prepared-header load
(`0x64653`, following `0x6464f`) has 7.37%; the corresponding prefix spill
(`0x6426f`) has 2.06%. A mask materialization following the first current
header load (`0x64205`) has 5.39%. Binary-overflow setup (`0x63fa1`) has
4.70%, destination capacity (`0x64798`) 3.17%, binary reason loading
(`0x64066`) 2.82%, and owner-capacity spilling (`0x6412d`) 2.20%.
Instruction skid prevents treating those locations as cache-miss counts,
individual stall causes or additive removable fractions.

Assembly and profile together identify the trade, rather than merely a
negative elapsed ratio. The lifetime repair removed real dead writebacks
and 48 stack bytes, but the remaining pipeline still keeps a current ref,
pending ref/header and next-hit state live through payload scan, immediate
watch moves and assignment. The value-array base is consequently loaded
from the stack inside the tail loops (`0x64348`, `0x6474d`, `0x64be8`).
The sampled suffix reload itself has 0.74% self weight; its downstream
literal/value chain remains as well. LLVM also duplicates the suffix body
for different first-hole transitions, increasing text by 46.50% over the
first engine. Neither detail alone establishes the whole cycle delta, but
both are concrete introduced costs absent from an abstract lookahead model.
The tested literal-equality refresh avoids a second value lookup after units;
it does not remove the extra preparation/dispatch on other misses.

The fundamental limitation here is that this implementation **adds a second
entry's state without removing any clause visits or current-clause work**.
It can overlap only immutable header access. Blocker truth, watched-pair
normalization, tail truth, watch moves and assignments retain their ordered
dependencies. The complete engine makes header persistence sound and removes
the old unit-yield boundary; this measured combination shows that those
facts are insufficient to make the one-entry pipeline worthwhile. Do not
retry its old width/distance, watcher-copy or inlining variations. A further
engine design needs to remove a named dependency/work item or reduce required
live state, with a cost model beyond carrying more future metadata. The
separate 1.478x j3037 propagation-work ratio against Kissat remains relevant;
this exact-trajectory experiment cannot reduce it.

## Verification, archive and closure

Final default SAT nextest passes **1019** tests; all-feature SAT nextest
passes **1046**, with one existing skip in each. These include the scalar
full-state oracle, independent solved-model/LRAT checks, mode fallbacks and
native Rayon owner moves. Three focused strict-provenance Miri tests pass
before and after the lifetime repair (final 26.33 seconds), covering native
header decoding, duplicate/deleted/null metadata, fresh arena borrows and
unit-induced blocker changes in both scan phases. Strict all-feature,
all-target SAT Clippy and workspace format pass. An initial test-only failure
queried the final model before solving; the assertion was corrected to read
the trail, and its failed log is retained alongside the passing preflights.
No solver verdict disagreement was observed in these checks.

Full workspace and fresh Z3 production gates were not run after the cost
rejection. **No production solver change or Kissat wall-gap improvement is
landed.** Exactly **two performance invocations** ran: one candidate cost
and one diagnostic profile. The initial 312-byte-frame prototype was untimed;
there was one source-directed preflight repair and no measured repair.

`precompile/0ed7b47/` retains the first prototype's source bundle/patch,
perf binary, lock, identity and preflight logs. `precompile/f5d906e/` retains
the final source bundle/patch, release/perf binaries, lock, identity,
qualification, assembly, scripts and once-only raw benchmark/profile data.
Both bundles require reachable registration `d517a294`. Experimental branch,
worktree and owned temporary files are removed after archival; the result
store is the retained evidence.
