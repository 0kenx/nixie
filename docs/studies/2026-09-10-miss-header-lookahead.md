# Miss-only clause-header lookahead

## Registration (before implementation and performance runs)

Goal: reduce Nixie's wall cost against mode-matched Kissat by overlapping
independent clause-header loads in the fixed-assignment long-watch scan.
This follows the [source audit](2026-09-09-miss-header-lookahead-audit.md) and
the [compact adjacency rejection](2026-09-10-compact-adjacency.md). Smaller
directories and cold growth paths did not remove the dependent memory work.

The candidate prepares at most one following entry, only on a live blocker
miss. It reads that entry's blocker and, if nontrue, its header. The actual
visit consumes this work without repeating those reads. Literal reads,
normalization, watch movement, reasons, tick charges, and assignment order
stay at their original positions. Discard preparation at every scanner
return and prefix-to-suffix transfer. No policy or search-order change is
intended; any trajectory difference fails the experiment.

The arena owns pending metadata inside an exclusive scan borrow. No cached
length or pointer token is exposed to callers. Growth, shrink, deletion and
relocation are inaccessible during that borrow; mutable literal slices
borrow the scan itself, preventing overlap even for duplicate references.
The only new unsafe operation may form a literal slice from metadata read
by this same scan. Solver instances retain ordinary ownership and Rayon
compatibility; no global state, custom Send/Sync assertion or shared raw
pointer is permitted.

Before performance: default and all-feature SAT tests, exact scalar-oracle
state comparisons (ghosts, duplicate refs, stable compaction, units,
conflicts, growth between yields and backtracking), focused Miri for the
arena API, strict SAT Clippy, format, and generated-code inspection. The
assembly must issue the next header read before current-clause work and
consume it without a second read. Record code size, stack and dispatch
cost. A failed preflight is a result; do not time known-broken code.

Use seed 0, the existing CaDiCaL preset, disabled sweep/definitions, CPU 15,
the same warmed-input whole-process user cycles/instructions protocol as
the compact adjacency study, and the existing Kissat 4.0.4 reference cells.
First run one qualified control and one candidate on j3037. The control
binary is fd01d0b (the qualified binary-span repair); subsequent main edits
are arithmetic/quantifier code outside this DIMACS execution path. Record
all raw cells once with benchstore. Require identical complete solver
stdout, at least 99.9% PMU coverage and at most 5% off-CPU time for a usable
wall comparison. Failed measurement quality is inconclusive, not a license
to repeat the cell. No own build may overlap performance measurement.

Advance only at at least 10% lower wall with no instruction regression,
or at least 5% fewer instructions without a usable wall regression. A
passing screen permits one paired si2 confirmation (check the SAT model)
before full workspace qualification and landing. A negative/neutral screen
gets one LBR profile to explain its cost. One code-directed repair is
permitted only if that profile and assembly identify removable overhead;
otherwise stop and archive the candidate. No distance/width sweep, seed
search, rerun or cross-profile counter ratio. These are bounded engineering
screens, not population estimates or a new Kissat-suite geomean.

## First implementation: rejected

Prototype `72427b39f900b81ef11ce05d56fa2b46bad24391` is archived, not
production. Its scoped arena stores private pending `(reference, length)`
metadata; the scanner separately carries `Option<bool>` for the prepared
blocker result. No additional unsafe Send/Sync assertion is involved.

Default SAT library tests: 782 passed. All-feature SAT tests: 1046 passed,
one existing ignored; two doctests passed, one ignored. The final corpus
test initially failed because the worktree lacked the ignored SAT corpus;
linking the primary corpus and rerunning that test passed. SAT Clippy and
format passed. Three focused arena tests passed standalone Miri with strict
provenance (nightly 2026-06-11), including duplicate references and owning
thread moves. Native Rayon ran prebuilt solver/scalar-oracle pairs. The
source, harnesses, logs and both binaries are in `precompile/72427b3/`.

The generated next-header reads precede current literal reads and are not
repeated on consumption. The price is two pending-state discriminants,
more live values and spills. Prefix/suffix bodies grow from 938/1120 to
1205/1381 bytes; local stack grows from 88 to 120 bytes, with six saved
registers unchanged. The assembly reference is cached a64b285, whose
kernel, arena, trail and watch-list source matches the qualified control.

| j3037, seed 0, CPU 15 | Wall | User cycles | User instructions | Conflicts |
|---|---:|---:|---:|---:|
| Qualified fd01d0b control | 36.13 s | 164287697694 | 254596496994 | 330565 |
| Lookahead 72427b3 | 37.94 s | 172701951302 | 290068669597 | 330565 |
| Retained mode-matched Kissat | 18.04 s | 79144759362 | 121059163625 | 286784 |

Candidate/control: **1.0501 wall, 1.0512 cycles, 1.1393 instructions**.
Complete Nixie stdout is byte-identical (323390316 propagations). Both cost
cells have 100% PMU coverage, zero major faults and under 0.34% off-CPU
time. Record IDs: control `0ec1f4bfcfe8f5f9`, candidate `497e2be874360640`;
retained Kissat `45a3c8f2e3057841`. This is a failed bounded screen, not
evidence of a precise population regression. These raw UNSAT runs lack a
checked original-CNF proof and remain unverified/Unknown in benchstore.

The one diagnostic profile (`d5410d1afabb8f5a`) passes: 15959 samples,
100% counter coverage and no loss/throttle. Scan self samples total
50.96%, driver 21.59%. The prefix's pending-state test at `0x63f7d`,
immediately after an unconditional reference load, receives 4.59% of total
sampled cycles; next-header/pending-spill and destination-append regions
are also visible. Sample skid and preceding loads prevent interpreting a
single instruction's samples as its removable cost. The
[flamegraph](assets/2026-09-10-miss-header-lookahead.svg) and address table
preserve that distinction; profile-prefix counters are not solver-cost
ratios. Terminal memory geometry and solver stdout match the cost run.

### One justified repair

The ordinary true-blocker path must not dispatch a pending enum or load a
reference it will not use. Replace the mixed loop with an ordinary hit
loop and an inner consecutive-miss loop. The latter consumes prepared
headers directly; when lookahead finds a true blocker, retire that already
checked entry once and return to the hit loop. Keep the same private arena
API, eager normalization, stable filtering and yield boundaries. This
changes the control flow that carries the state, rather than selecting a
new distance or adding more prediction. Inspect assembly and rerun the
affected correctness checks before using the one registered repair cell.

## Consecutive-miss repair: also rejected

The final repair is `f24cf17e4044d8b9f12a64e806d6f8b848942850`. Before
timing, assembly exposed another problem: checking `is_live` and then
consuming the header retained a redundant current-state check. The final
API takes the current metadata once, then invokes an inlined callback to
prepare the next entry. Deleted entries never invoke that callback. This
keeps metadata private and avoids an impossible-state panic in the kernel.
The intermediate assembly was retained but that intermediate binary was
never timed.

Default library tests again pass (782); all-feature nextest passes all
1046 SAT tests, one existing skip; strict SAT Clippy and format pass.
The three arena Miri tests pass again with strict provenance. The final
assembly has the ordinary prefix hit loop at `0x64061..0x64078`: blocker
load/value test and cursor advance, without a pending-state test or clause
reference load. The next header is still loaded before current literals.
Prefix/suffix bodies are 1328/1527 bytes, local stack 104/120 bytes, six
saved registers. More miss-loop continuation and range checks remain;
removing hit dispatch did not make the entire scanner smaller or cheaper.

| j3037 repair, same full work | Control | Repair | Repair/control |
|---|---:|---:|---:|
| Wall | 36.13 s | 38.75 s | 1.07252 |
| User cycles | 164287697694 | 176591934047 | 1.07489 |
| User instructions | 254596496994 | 269859257057 | 1.05995 |
| Cycles/conflict | 496990.60 | 534212.44 | 1.07489 |

Repair record `29febe52bb5ffd47` has 100% PMU coverage, zero major faults,
0.310% off-CPU time and 228 involuntary switches. Full stdout matches the
same retained control byte for byte, including all 330565 conflicts and
323390316 propagations. Versus the first implementation, instructions fall
**6.97%**, but wall is 2.13% higher. Neither implementation passes the
registered advancement gate. Different measurement windows still limit
precise attribution of wall/cycle deltas; neither wall number establishes
a gain. Repair/Kissat wall is 2.1481 on this one input, not a suite geomean.

### Remaining cost and limits of the conclusion

The final [flamegraph](assets/2026-09-10-miss-header-lookahead-repair.svg)
comes from `428603197ee69bc4`: 15946 samples, 100% counter coverage, no
loss/throttle, two kernel-labelled samples and 0.01254% unresolved self
weight. Scan self samples total 49.97%, driver 21.40%. Hot sites include
the ordinary blocker-value read (4.93% at `0x64069`), current-header
deletion branch (4.00% at `0x64098`), next-header deletion branch (3.36%
at `0x63c0e`), and destination capacity/store instructions (3.01%/2.85%
at `0x63d03`/`0x63d11`). These are sampled locations, not additive,
independently removable latency estimates. Complete memory geometry is
unchanged. Profile output matches the cost run after its registered
terminal memory line is removed.

There is a deeper limitation than enum dispatch. `prepare` classifies the
next header immediately: its deleted-flag branch precedes current pair
loads. Thus early loading alone does not establish useful overlap; the
generated path also inserts next-entry dependent control flow before
current work. Speculation may overlap some reads, but the result does not
measure how much. The current preflight established ordering and reuse,
not latency hiding. The repair removed real instruction overhead while
retaining this issue, pending metadata, extra continuations, and all
destination appends.

Do not repeat either implementation with different lookahead distances or
infer a gain by combining its profile percentages with the compact-buffer
result. A distinct follow-up would have to carry an **unclassified raw
header** inside the same exclusive arena scope, delaying its liveness
decision until the actual visit. Its code-generation gate would need to
show both the early load and absence of a next-header-dependent branch
before current work, plus bounded state/spill cost. It must retain the
null/deleted, duplicate-reference, yield and relocation invariants. This
is an unimplemented hypothesis, not a speedup claim or authorization to
expand this completed experiment.

Exactly **five performance invocations** ran: one control, two candidate
cost cells and their two diagnostics. No si2 cell, new Kissat cell, seed
sweep, repeat or full-workspace qualification was added. Production SAT
source remains unchanged; the prototypes are archived rather than landed.
Source bundles, lockfiles, binaries, measurement scripts and raw evidence
remain in `precompile/72427b3/` and `precompile/f24cf17/`. A concurrent
external rebase changed main's commit IDs during the experiment; binaries
and records retain their actual original source identities. Both bundles
include the old registration/control ancestry back to still-reachable
`f0031009`, so cleanup does not strand their prerequisites. The owned
worktree, branch and temporary files are removed after recording the study.
