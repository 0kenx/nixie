# Connected residual payloads for forward subsumption

The [last candidate profile](2026-09-09-packed-watch-live-view.md) places
36.39% of subsumption self-cycle attribution in occurrence-ID/ref/header
lookup and validation (6.91% of the whole original-circuit profile).
Membership scanning accounts for another 32.14% / 6.10%. The previous
watch-copy/live-view combination did not pass its wall gate. This follow-up
changes the work represented by the subsumption index rather than adding
another filter in front of the same database lookup.

## Algorithm and lifetime contract

After a scheduled clause has survived its own deletion/strengthening step,
copy its literals into a compact, round-owned word pool. Store its stable
database ID for promotion and current proof-ID lookup. Occurrence entries
remain four bytes, now offsets into records of
`[residual_length, database_id, residual_literal_codes...]`.

Omit exactly one occurrence of the connection literal. The query bucket's
key supplies that literal's signed mark once. For a positive key mark, the
remaining literals decide the same subset/SSR test. For a negative mark,
seed the one allowed complementary literal with the key; any second negative
still rejects. An absent key rejects while retaining the same clause-check
count. This also handles the scalar test's negative/absent-key cases without
assuming a positive mark to elide work. Residual literal order is preserved.

No arena pointers, proof IDs, tags, truncated literal codes or unsafe casts
are stored. Pool offsets and lengths have checked conversions; record slices
remain bounds checked. Connection policy, sorting, candidate order, binary
edge liveness checks, clause-check budgets and dirty/random scheduling are
unchanged. This is a representation/algorithm engineering comparison under
identical trajectories, not a new heuristic or a matched-null claim.

The semantic reference is local CaDiCaL `src/subsume.cpp`: process a candidate,
then connect it for later candidates. The relevant Nixie mutation audit is:

- The schedule contains each ID once. Only the current candidate can be
  retired or strengthened; it is copied after that decision and after watch
  reordering, including a ternary-to-binary transition.
- Later queries may promote an already-connected subsumer's learned flag,
  but cannot mutate its payload. Proof emission resolves the current proof
  ID from its stable database ID rather than caching a proof ID.
- `remove_literal_opts` changes the candidate and resets the propagation
  head; it does not propagate or collect during the round. `retire_clause`
  purges only that candidate's edges/reasons and sets its deleted flag.
- Every processed candidate is unmarked before a normal/budget exit. Clear
  occurrence and payload contents before the round returns. Retain only
  their allocation capacity, fixing the old normal-exit scratch-drop defect.
  Empty buffers cannot supply stale evidence after push/pop or compaction.

Debug builds compare every cached residual against the live database.
A test-only database-index oracle retains the old lookup/deletion checks and
old normal-exit scratch lifetime. Independent signed-set tests guard the
shared membership helper. Paired round/search tests must compare clauses,
metadata/activity bits, trail, watches, BIG, counters, dirty state and proof
transcripts. Cover promotion, strengthening, budgets, repeated rounds, spilled
lists, scopes, collection and exact SAT models/independent LRAT checks.

## Pre-measurement cost obligations

Inspect the ordinary optimized binary before executing a screen: connected
queries must use the pool rather than resolving through the clause database.
Include bounds checks, key-mark seeding, copy preparation and retained memory
in the cost. Record construction copies each connected residual once and
removes one literal per record; this is not free when a record has few future
queries. Reuse capacity and avoid both a clear-at-return and redundant full
clear-at-entry pass. The iterator/lookup representation may be repaired before
measurement if the generated code fails these obligations.

## Registration: at most five new solver invocations

The preceding wall screen used historical controls. Its broadly increased
cycle attribution did not isolate a local source regression, despite an
identical trajectory and fewer instructions. Here original circuit uses
**fresh seed 1** so control, candidate and Kissat are new cells run in the
same time window. Inspection found no existing CPU-15/original-circuit/seed-1
cell for qualified compact control `02cc03c` or Kissat `8af8e56`. Do not repeat
any cell if one appears before execution.

Use the cached qualified compact control `02cc03c` (`d1290db` equivalent
production source), pinned Rust 1.96.0 / LLVM 22.1.2 and lock SHA-256
`3699f4eaec582b0243463999e3bc784461764ec2e2e78d5aedcf37cbc60c1439`.
Candidate starts from main `8cf8850`; its additional inherited SAT change is
an inactive terminal CNF-dump environment check from `ac13904`. Record exact
immutable source/binary hashes. Portable release/perf profiles, no native
flags, PGO or RUSTFLAGS override. A prototype is not a production landing.

CPU 15 (atom), MAXC=10000000, `NIXIE_SWEEP=0`, CaDiCaL preset, printed model
and 300-second emergency cap. Clear other study variables. Warm input and
executable reads, GNU time covering the complete target, anonymous tmpfs
output and <=10% off-CPU fraction; confirm no competing constrained userspace
thread includes CPU 15. Every start/completion is recorded immediately and
once, with full output and a checked model. Wall is primary per the user's
instruction, never a solver policy input.

1. Original-circuit control at seed 1.
2. Original-circuit candidate at seed 1. Require complete output identity
   with the control, a checked model and timing quality. Stop on a failed
   correctness or timing-quality check; no retiming.
3. Mode-matched Kissat 4.0.4 at seed 1, using exactly
   `--probe=0 --preprocess=0 --factor=0 --substitute=0 --sweep=0 --vivify=0
   --transitive=0 --backbone=0 --congruence=0`, plus statistics and the same
   seed/conflict cap. Check its model and timing quality.
4. If circuit quality/identity passes, one candidate circuit LBR diagnostic
   at seed 1 regardless of win/failure. Fixed atom cycle period 10472903,
   grouped user cycles/instructions, sample-read/running-time data, explicit
   CPU samples, LBR and 128 pages. Require zero loss/throttle/unthrottle,
   >=99.9% scheduling coverage, >=1000 samples and <=0.1% unresolved self
   attribution. Print terminal memory; remove only that line for output
   comparison. Failed profiles remain failed; profile time is diagnostic.
5. Only if candidate/control circuit wall <=0.95 and the profile qualifies,
   candidate original-si2 seed 0. Reuse control record `68494a8004e0cdca`
   (2.02 s) and Kissat `c3bb0064cbaa9d2d` (1.22 s), rather than rerunning
   them. Require identical Nixie output, checked model, timing quality and
   candidate/control <=1.03. This guard retains the historical-window caveat.

A positive source landing requires circuit wall <=0.95, the conditional si2
guard and two-input geometric mean <=0.95, plus every required repository
correctness gate. Report per-input wall/Kissat and wall/conflict, exact
outputs and solved-at-cap. This is a bounded two-input engineering screen,
not a population speedup or a superadditive interaction measurement. A
negative result must retain its candidate flamegraph and identify introduced
work, an opportunity limit or a concrete repair before abandoning it. No
sweeps, seed matrices or configuration tuning are registered.


## Measured result: bounded wall screen passes

Prototype source `a64b285d670f1be24167f5920f769d0c040e701c` uses Rust 1.96.0
/ LLVM 22.1.2 and the registered lock. Release binary SHA-256 is
`d1fbf1afa2c333b27d9ae4ba324878f1772d7043c917ccaa907717148abdd52e`;
perf binary is
`4551f8146a0494ddbd5cc679bf615d2728cc4877c62af77aba601adf3f773309`.
The generated connected-query loop uses checked pool offsets directly;
the stable ID is loaded only after a successful membership check. Empty
buckets bypass the key-mark load. Subsumption text grows from 12196 to
13449 bytes (10.3%); prefix/suffix watch bodies remain 938/1120 bytes.

| Input / seed | Compact control wall s | Residual cache wall s | Mode-matched Kissat wall s | New/control | New/Kissat |
|---|---:|---:|---:|---:|---:|
| original circuit / 1 | 9.63 | 8.81 | 1.88 | 0.91485 | 4.68617 |
| original si2 / 0 | 2.02 (retained) | 1.99 | 1.22 (retained) | 0.98515 | 1.63115 |

Circuit improves **8.51%** in this same-window comparison. Si2 is neutral
at this resolution and keeps its historical-window limitation. No si2
profile was registered or collected, so this guard does not identify the
component costs on that input. The two-input
geometric mean is **0.94934849**, narrowly passing the registered <=0.95 gate;
si2 also meets <=1.03. This is a bounded engineering result, not a population
speedup estimate. The fresh seed changes the reference workload relative to
older seed-0 reports: do not multiply these ratios by historical improvements
or attribute differences between old and new Kissat timings solely to seed.
Off-CPU qualification cannot eliminate clock/cache/shared-resource noise.

Complete Nixie output is byte-identical to the control on both inputs,
including its model and counters. Both solvers solve both inputs within the
cap, and every returned model was checked against every original clause.
Circuit conflicts remain 186114 versus Kissat's 167929; si2 remains 39246
versus 51823. Circuit wall/conflict is **47.34 us** (control 51.74 us), versus
Kissat's **11.20 us**. Si2 is **50.71 us** (control 51.47 us), versus
**23.54 us**. The throughput gap remains large even after this improvement.
Ticks retain their historical definition and exact values; they do not price
the new copying work or replace the complete-target wall measurements.

The four new wall cells have off-CPU fractions 0.42%, 0.34%, 0.53%, 1.01%
(control circuit; candidate circuit; Kissat circuit; candidate si2), and
zero major faults. User/system seconds are 9.57/0.02, 8.75/0.03, 1.84/0.03,
and 1.87/0.10. Circuit peak RSS rises from 32972 to **37512 KiB**; Kissat
uses 32160 KiB. Si2 candidate peak is **159240 KiB**, compared with retained
control 156696 KiB and Kissat 111116 KiB. Retained cache capacity costs
memory even though no logical connections escape the round. RSS measures
the complete process; the existing terminal arena/watch report does not
separately account for subsumption scratch or its high-water allocation.

Exactly **five new performance invocations** ran: four wall cells and one
profile, with no repeats or additional parameter search. Registered circuit
seed-1 control/reference cells were absent before execution. Canonical IDs:

- circuit control `bfccdfbc70e8baf3`, candidate `ee11cd60c342c2fb`,
  Kissat `6295845397e7a242`;
- candidate profile `49d1f9ace3d1a16c`;
- si2 candidate `f0905d230b7f8f76`, retained control `68494a8004e0cdca`,
  retained Kissat `c3bb0064cbaa9d2d`.

Raw starts/completions, exact outputs, commands, binary/input hashes, model
checks, affinities and GNU-time records are retained under the corresponding
`precompile/<sha>/benchmark/connected-residual-payloads-wall/` directories;
canonical records are under `benchmark/runs/`. Candidate preflight, code
inspection and qualification live beside them. These are cached artifacts,
not committed binaries or a substitute for this report.

## Profile, introduced costs and remaining opportunity

The [interactive flamegraph](assets/connected-residual-payloads.svg) contains
**3787 user-cycle samples**, all on CPU 15, with zero loss/throttle/unthrottle,
100% scheduling coverage and zero unresolved self attribution. LBR supplies
388 nontrivial caller stacks; incomplete chains are explicitly labelled.
Sample-read totals are **39.661 G cycles and 65.782 G instructions**, covering
a sampled prefix rather than the complete solve. The single candidate
profile is diagnostic; there is no same-seed control profile and no measured
instruction/cycle reduction claim. Earlier seed-0 attribution is a source of
hypotheses, not a denominator for this seed-1 result.

| Self component | Cycle share | Instruction attribution share |
|---|---:|---:|
| watch compaction suffix | 34.80% | 29.54% |
| watch prefix | 18.88% | 16.31% |
| subsumption round | 14.15% | 19.14% |
| search body | 5.39% | 4.82% |
| outer propagation driver | 4.07% | 3.60% |

Within subsumption, the residual membership region receives 22.20% of its
self-cycle attribution (**3.14% of the whole profile**). Iteration plus
checked pool lookup receives 22.01% / **3.12%**, and the per-entry saturating
subcheck load/update/store receives 7.65% / **1.08%**. Key seeding/residual
setup is another 4.10% / 0.58%; bucket setup is 1.87% / 0.26%. These are
instruction-pointer attributions, not branch-miss probabilities or savings
obtainable by deleting safety checks. The generated-code address ranges and
weighted samples are preserved in `address-attribution.json`.

Construction still searches for the omitted literal and copies up to two
slices, after capacity checks. Its straight-line/loop fast path alone
receives 0.21% of whole-profile cycle attribution; this excludes out-of-line
copy/allocation bodies and cold reserve blocks, so it is not a complete
construction-cost estimate. Three pool bounds checks remain per query,
including the residual extent check at `0xab7b7`, the hottest sampled
instruction inside subsumption. Keeping checked accesses is part of the
lifetime contract; a smaller representation or a compiler-visible immutable
scan boundary must remove work without making invalid offsets unchecked.

One possible follow-up is to return the number of visited connections from
an immutable bucket scan and charge `subchecks` once at the existing bucket
boundary. That would remove repeated stack traffic while preserving the
saturating count and the current overshoot/early-match semantics. Its local
opportunity is limited: the observed counter region is only 1.08% of whole
cost. Register-pressure improvements would need generated-code evidence.
Another is to prepare residual records and occurrence ranges together, so
bounds validation can be shared over a contiguous scan rather than repeated
through offsets. It must preserve the exact connection order and price
packing, rebuilding, spill and memory overhead. Neither is implemented or
measured here.

The larger remaining target is the **53.68%** watch-loop share. Previous
whole-word copying and certificates did not establish a wall gain; this
subsumption result does not rescue them by assumption. A follow-up must
remove a named per-visit cost or share work with necessary propagation, then
price its setup and miss paths. Simply stacking neutral mechanisms or
multiplying their old ratios is not evidence. The present combination has
a specific interaction: round-lifetime immutability enables lookup removal,
and restored scratch ownership amortizes the pool/index allocation. The
screen measures their combined implementation, not a factorial interaction
coefficient.

## The wall gap also contains more work per conflict

The same retained outputs show **19391470 Nixie propagations versus 6684415
Kissat propagations** on circuit seed 1. Nixie increments its counter when
`Trail::next_to_propagate` yields a literal (`solver/propagate.rs`); Kissat's
`src/propsearch.c` charges the difference between trail propagation cursors,
with other propagation modes also contributing to its aggregate. These
count processed trail literals, not long-watch visits, and their aggregate
phase coverage is not identical. They still rule out treating similar
conflict counts as evidence of similar propagation work.

Nixie processes **104.19 literals/conflict** versus **39.80** for Kissat
(a 2.618x ratio). Whole-solve wall amortized over that counter is **0.4543 us
versus 0.2813 us** (1.615x). Their product gives the observed roughly 4.228x
wall/conflict gap. This is an accounting decomposition, not an isolated
measurement of either propagation kernel. The cache changes execution cost
while preserving Nixie's entire trajectory and work counters.

Under the exact requested flags, Kissat reports **1130 eliminated variables**
(40%) and five elimination rounds; Nixie reports **228**. Disabling probing
and preprocessing does not disable all of Kissat's in-search elimination.
Nixie also reports 23036 restarts versus Kissat's 9710. Either can affect
repeated propagation work; these aggregates do not establish causation.
A next algorithm audit should distinguish redundant root replay, database
size/propagation strength and restart replay before buying another narrow
instruction saving. Audit the counters and existing phase instrumentation
first. Do not silently alter the comparison flags, infer an elimination
policy win from this one seed, or start a heuristic sweep without matched
nulls. No extra solver invocation was used to obtain these observations.

The first source audit gives concrete distinctions to investigate: Nixie's
`ELIM_OCC_LIMIT` is 100 and rejects using raw, unflushed list lengths;
Kissat's default `eliminateocclim` is 2000. Nixie's functional-definition
elimination remains default-off, while the reference reports 6591 embedded
kitten solves with sweep disabled. The [definition audit](2026-09-09-kitten-sweep-audit-closure.md)
already records a positive descriptive screen but no matched-null enablement
result, and identifies missing cheap structural gate detectors ahead of the
embedded solver. Repeating a blind definitions toggle would waste that
finding. Shared gate/occurrence preparation and exact inexpensive structural
recognition are algorithmic cost targets; a change to eligibility or policy
still needs the appropriate controls. None of these differences alone
proves the cause of the propagation-volume gap.

## Source verification

Before measurement, ordinary SAT tests passed **1003**, with one skipped;
the final all-feature payload/kernel subset passed **11**. Independent
signed-set tests exercise every connection key across 81 x 81 four-variable
candidate/subsumer patterns. Full literal codes, pool growth, promotion,
strengthening, exact budgets, repeated empty buffer reuse, spilled lists,
scopes, forced collection, search state, models and LRAT are covered.
Initial test-development failures were a delimiter typo and a wrong test-only
`add_learned` arity; both are retained in the preflight logs. They did not
produce a solver verdict or consume a performance cell.

The performance snapshot is integrated with main `c9b581c` as `ce4320c`
for full source qualification. The intervening main changes are outside
`nixie-sat`, `nixie-core` and the workspace manifest, leaving the measured
standalone SAT source unchanged. The complete qualification passed:

- all-feature build;
- **10824 workspace tests passed**, 12 skipped;
- **111 documentation tests passed**, 29 ignored;
- strict all-feature/all-target Clippy, formatting, and warning-free docs;
- installed **Z3 4.16.0** correctness canary: **174 decisive agreements,
  zero disagreements, one inconclusive** (`array_unique`: Nixie Unsat,
  Z3 Unknown). Unknown is not counted as agreement.

The canary is solely a required correctness gate; all performance claims
in this study target Kissat. Exact commands, completion statuses, logs,
source hashes and the environment snapshot are cached in the qualification
directory. The generated 81517-byte SVG was parsed as XML, all seven cited
canonical benchmark records validate, and the final source diff is clean
under `git diff --check`. No production source repair was needed after the
screen. The source and tests now qualify for main under the registered
bounded engineering gate. Cached standalone SAT binaries retain their
measured hashes; the release CLI built during qualification is cached with
the landing as well. Neither guard time nor profile counter is remeasured
for the documentation/qualification commit.
