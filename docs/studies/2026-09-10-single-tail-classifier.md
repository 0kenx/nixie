# Search the false tail before classifying its replacement

## Registration

The [precise branch audit](2026-09-10-propagation-branch-attribution.md)
places 25.37% of whole-process branch-miss sample IPs at the contiguous
engine's two-stage tail classifier. Header null/deleted guards receive no
samples. The next implementation targets that classifier, preserving the
ordinary signed-byte truth representation and the archived complete engine
with contiguous binary spans. This is a changed combined implementation,
not retiming an unchanged rejected candidate.

Scan tail literals in order until the first value >=0, carrying its index,
literal and value out of the loop. Then classify that one result: a true
literal parks the existing watch and updates its blocker; an undefined
literal moves the watch. If all tail literals are false, use the already
read other-watch value for unit/conflict. Preserve exact clauses, eager pair
normalization, assignments, reasons, watch order, conflict tails, ticks,
budgets and observers. Local Kissat proplit.h is the nonfalse-search reference;
retain Nixie's true-literal parking, which differs from Kissat's moving rule.

This removes the positive/undefined classifier from false-prefix iterations.
It does not remove the selected-result distinction, length bounds, literal
value loads or any propagation obligation. Short tails bound saved work.
Price any new result dispatch, register state or reload instead of treating
the previous 25.37% event share as removable wall. No sentinel, SIMD, batching,
search policy, new adjacency tuning or additional unsafe block is added.

Before cost, compare the complete engine with the scalar exact-state oracle,
all truth patterns on bounded tails, selected-literal positions, prefix/suffix
watch phases, all-false unit/conflict, true parking, undefined moves and
unvisited tails. Reuse independent original-model/LRAT checks and native
Rayon owner movement. Run default/all-feature SAT nextest, SAT doctests,
strict SAT Clippy, workspace formatting and six focused strict-provenance
Miri span/queue tests. Full workspace build/tests/doctests/Clippy/fmt/docs
and installed Z3 4.16.0 parity remain mandatory before production promotion.

Portable release/perf assembly must show one sign test per false-prefix
iteration, no reread of the selected literal's truth, and classification
outside the scan backedge. Record text/local stack sizes against the previous
2,769/184 bytes. Permit one source-directed preflight repair; stop without
cost if those sizes increase or the intended loop does not materialize.
No measured repair or alternative classifier encoding after the result.

At most THREE new performance invocations beyond the closed branch audit:
candidate j3037 whole-solve cost; one candidate j3037 LBR cycle profile after
an output-identical completed cost, regardless of win/fail; and candidate
crn only if j3037 instructions and usable wall are both <=0.95 qualified
production and peak RSS <=1.10. Confirm crn instructions/wall <=1.03 and
two-input wall geomean <=0.95. These are rejection/advancement screens,
not a suite-wide or multi-seed performance claim.

Reuse fd01d0b j3037 record 0ec1f4bfcfe8f5f9 and crn 0840cab28aa276cb;
the previous contiguous cost fe075d2cf545b689 is additional implementation
context. Reuse requested-mode Kissat 4.0.4 record 45a3c8f2e3057841 as context.
No new baseline/reference, repeated cell or profile-as-cost substitution.
Use CPU15 Atom, seed0, MAXC=10000000, PRINT_MODEL=1, NIXIE_SWEEP=0,
NIXIE_DEFINITIONS=0, cleared unrelated study overrides, identical Rust
1.96.0 / LLVM22.1.2 and lock hash 3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439.
Portable profiles, no native/PGO/RUSTFLAGS overrides. Instructions are primary,
wall/cycles secondary, never policy inputs. Warm executable/input; anonymous
tmpfs output, GNU time1.10, cap300s, no owned build during cost. Require exact
stdout, >=99.9% PMU coverage, no major faults, <=5% off CPU and unchanged
constrained sleeper runtime. Shared cache/load/frequency and older controls
remain limits. LBR uses period10472903, 128 pages, grouped user Atom cycles/
instructions, CPU/read/running-time records, >=1000 samples, no loss/throttle
and <=0.1% unresolved self weight.

Store each start/completion and canonical result once with source/binary/input
identities. Unchecked UNSAT stays unknown/unverified. Land productive code
only after all promotion gates; otherwise archive source, profile and diagnosis
on main. Clean the owned temporary checkout, branch and disposable artifacts;
retain binary/source/result caches.

## Implementation and qualification

Candidate **cd766ecafe1211fb3069dc56d05a9fb96468b49f** changes only the
tail-search block and adds one regression relative to archived contiguous
engine 7100112. A labelled block returns the first `(index, literal, value)`
whose value is nonnegative. Parking/moving happens after that block. An
all-false tail follows the existing unit/conflict code. No new unsafe code,
truth representation, graph policy, watch selection or result dispatch at
the Solver boundary is introduced.

The new oracle checks **6,534** states: every three-valued pattern on tails
of length one through five, all three other-watch values, both watched-pair
orientations, and no hole / an earlier move / an earlier deleted entry.
A following watch checks conflict-tail preservation. Each case compares
the result, individual clause literals and metadata, complete trail/watch/
graph state, counters and scope-related state with the independent scalar
engine. Existing model/LRAT, budget, owner movement and scope checks remain.

With the registered lockfile, preflight passes **1,051 all-feature SAT tests**,
**1,024 default SAT tests** (one existing skip each), **two doctests** (one
ignored), strict SAT all-feature/all-target Clippy, workspace formatting,
and **six strict-provenance Miri tests**, seed 42 / nightly 2026-06-11.
These are scoped qualification; full workspace/parity qualification has
not yet been performed.

The matching perf engine is **2,731 bytes / 184 local stack bytes**, compared
with contiguous engine **2,769/184**. Its three false-prefix loops are
`0x63ad0..0x63ae1`, `0x63d20..0x63d31` and `0x63f40..0x63f51`.
Each uses one memory-byte comparison and sign backedge; the selected-result
branches at `0x63ae3`, `0x63d33` and `0x63f53` reuse those flags. No selected
truth reload or classifier remains on the false backedge.

One preflight repair was used. Clippy requested replacing range indexing
with `enumerate().skip(2)`; that expanded the generated engine to 2,889 bytes
in the initial build, despite reducing its stack to 168. Restore the direct
checked index loop with one local `needless_range_loop` allowance and an
explanation of the generated-code constraint. That body restores 2,731/184.
Neither variant had a performance invocation at this stage.

The build-identity check also caught a regenerated **ignored Cargo.lock** in
the fresh worktree: SHA-256 4ede1ce0b46ed97cfb1db3df29f1294e845312679b35412726a6fb4220916ecd,
instead of the registered 3699f4ea... lock. Those preliminary builds/tests
are explicitly ineligible as matched evidence. Copy the exact retained lock,
rebuild with `--offline --locked`, and repeat **all** scoped qualification
above, including Miri. The matching build independently passes the assembly
gate. No binary with mismatched dependencies is benchmarked; the runner now
checks cached lock and executable hashes before any target start.

Qualified release SHA-256 is
`7fa7259a62c806725ed7310d3e4c54eb9808637f1b6ee1266c1f787240c9d19a`;
perf SHA-256 is
`ee8722d0eeec4ca4871071c91b7a58ca32db72d2a066c8587e11232606d7ed13`.
The source tree is `1d26134897467475eec33688bbb627d74730e773`, with
registration base `7a5c47a578fc71083ebfb9b26573d7d1b53d9384`. The ignored
lockfile is retained separately beside the cached binaries; a Git source
tree alone does not specify this build's dependency versions.

## Cost: fewer instructions and branches, more misses and wall

The one cost record is **5397d273b6ab8367**. Full stdout is byte-identical
to qualified production and contiguous engine 7100112: **330,565 conflicts**,
**323,390,316 propagations**, **695,639,361 ticks**, SHA-256
`a904b7f02cd4dc6ac5abd11a0754072e9f32af0ab18409dc293edf1242c1cb9b`.
The unchecked UNSAT is unknown/unverified in the result store.

| Arm | Whole-process user instructions | User cycles | Wall | Peak RSS KiB |
| --- | ---: | ---: | ---: | ---: |
| Qualified production fd01d0b, reused | 254,596,496,994 | 164,287,697,694 | 36.13 s | 34,236 |
| Contiguous engine 7100112, reused | 195,675,300,186 | 159,868,361,922 | 35.28 s | 35,000 |
| Single tail classifier cd766ec | 191,229,727,387 | 176,308,035,215 | **38.65 s** | 35,076 |
| Candidate / production | **0.75111** | **1.07317** | **1.06975** | **1.02454** |
| Candidate / contiguous | **0.97728** | **1.10283** | **1.09552** | **1.00217** |

The combination removes 24.89% of production instructions but observes
6.97% more wall; the registered advancement gate fails. Against the earlier
contiguous engine, another **4,445,572,799 instructions (2.27%)** and
**1,602,080,503 branches (3.76%)** disappear. Nevertheless branch misses
increase by **117,500,722 (5.78%)**, from 2,032,301,753 to 2,149,802,475.
The whole-process miss/branch ratio rises from **4.7725% to 5.2457%**.
Those are observed event totals, not per-site miss rates or isolated evidence
that every additional miss came from the tail classifier.

The cost passes timing-quality checks: PMU 100%, zero major faults, user/system
38.42/0.10 seconds, **0.336% off CPU**, 306 involuntary and 14 voluntary
switches, unchanged constrained sleepers. All owned builds/tests had ended.
Host load was 11.95/16.67/12.71 on 20 cores. Shared cache/frequency/foreign
load and the older controls still prevent a source-only wall attribution.
No crn cell runs and no source promotion follows this failed screen. Reused
Kissat context remains 18.04 seconds; no new reference or suite ratio is claimed.

## Profile, introduced cost and next algorithm boundary

The required cycle/LBR diagnostic is **8df4957b65a26b4e**:
**15,924 samples**, CPU 15 only, PMU 100%, zero loss/throttle and **0.02512%**
unresolved self weight. Output matches cost after exactly one terminal memory
line is removed. Its elapsed time and sampled-prefix counters are diagnostic
only and do not replace the 38.65-second cost. The
[flamegraph](assets/2026-09-10-single-tail-classifier.svg) puts **69.94%** of
self cycles in the complete engine, 4.87% in search, 3.28% in shrinking/
minimization, 2.98% in subsumption and 2.59% in phase-saving backtracking.

The [reconciled address report](assets/2026-09-10-single-tail-classifier-addresses.json)
attributes 5.187% of whole-process self-cycle weight to the three false-prefix
loop regions and 0.301% to their selected-result branches. Blocker regions
receive 6.594%; deleted-header test/branch locations receive 10.305%.
The last number remains **a sampled location, not a misprediction count**.
The precise branch audit was on 7100112; no per-site branch-miss attribution
for cd766ec is claimed from this call-stack capture.

Generated code identifies a remaining cost that a smaller text/frame total
would hide. The frequently used suffix entered after a prefix watch move now
loads the arena base from `[rsp+0x60]` at **0x63ec5**, immediately before its
header test at 0x63eca and branch at 0x63ecf. That branch gets 5.589% self-cycle
weight. The prior contiguous engine's corresponding move-entered suffix
tested its header directly through its already-live arena register at 0x63c96.
The new stack load adds another dependency on that miss path even though the
frame stays 184 bytes and the complete engine gets smaller. This is a concrete
code-generation cost; the capture does not isolate its latency or prove it
accounts for the entire wall delta. Three generated scan bodies also remain.

The memory report is exactly unchanged from contiguous engine 7100112:
arena 3441696/7684864 bytes, 16 waste bytes, refs 1914480,
watch 821424/2316608, BIG 511456/851296 and 27 arena compactions.
There is no new allocation or maintenance algorithm in this classifier.
Whole-process memset/memmove self shares are 1.551%/0.239%, graph/watch rebuild
0.207%, and Vec growth 0.038%; these routines are shared with other work and
are not isolated prices for this change.

The false-first scan removes a repeated classifier but retains all three
semantic outcomes: continue past false, park on true, move on undefined.
A selected true literal now passes the negative test and then the result
classification. Short tails limit the false-prefix savings. Reordering that
decision tree changes the branch outcome sequences seen by the predictor;
the observed total misses increase despite fewer executed branches. The
monolithic engine also keeps binary-directory, queue, watch and clause state
live across all of these paths. The positive instruction result therefore
does not rescue this combination, and percentages from earlier mechanisms
must not be added to it.

A distinct follow-up worth a **separate** registration would keep assignment
inside a whole-watch-list scanner, but put that scanner behind one function
boundary per nonempty list. Binary-directory and outer-loop state could then
leave the scanner's live register set. This differs from the rejected fixed-
trail scanner that yielded on every unit and from adding persistent lookahead
state. It must price every call, borrow setup and result writeback, preserve
the complete fixed-domain ownership contract and exact list state, and show
in assembly that hot base reloads actually disappear. This study does not
establish that such a boundary wins. These event percentages alone do not justify sentinel traversal or
combining unrelated neutral mechanisms.

## Closure and archive

Reject the single tail classifier. Do not tune its encoding, invert more
branches, replay the same candidate or broaden this failed screen. Exactly
**two candidate performance invocations** ran: one cost and one profile.
The preceding independently registered branch audit used one additional
cached-binary diagnostic, for **three solver performance invocations this
turn**, no controls/references/held-out cells.

The [source patch](assets/2026-09-10-single-tail-classifier.patch), SHA-256
`2ba89c7e4920034063c1bf8ed91f05cbce4bd48546fb661c5e61439b581a6447`,
reconstructs the recorded tree from 7a5c47a5 with `git apply --cached
--whitespace=error-all` in a temporary index. The source bundle also verifies.
Cache `precompile/cd766ec/` retains the matching lock, qualified release/perf
binaries, source bundle/full patch/narrow delta, build identities, scoped
qualification, assembly and raw/canonical measurements. Earlier wrong-lock
preflight metadata is explicitly marked ineligible; its disposable binaries
are removed. Production solver source stays unchanged. Full workspace and
fresh installed-Z3 parity were not run for this rejected prototype.

Land this record and artifacts on main, then remove the owned checkout,
branch, corpus symlink and scratch directory. Keep the result/binary caches
and leave foreign work untouched.
