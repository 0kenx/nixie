# Binary extension-field performance study

The pre-registered workload, controls, counter-coverage argument, acceptance
bar, and run-once protocol are in `bench/ff_extension_perf/README.md`.
The [feature audit](2026-09-22-binary-extension-fields.md) documents the
representation, supported fragment and proof modes. Production baseline is
`df564313`; the benchmark-only commit adds no solver
changes. CPU instructions, not elapsed time, are the primary metric.

## Preflight finding, before measured cells

Untimed functional checks validate all 13 generated cases at seed zero.
The initial budget probe used a depth-64 shared square/add expression over
F256; it produced no verdict within the external 120-second safety cap.
A short sampled profile of that running process concentrated on one tight
loop, but the cached release executable is stripped, so that sample does
not identify a source-level cause. Preserve it as diagnostic evidence,
not a completed performance cell or an instruction ratio.

The measured budget probe is fixed at depth 16, which returns Unknown.
The depth-64 input is retained as a separate diagnostic and must be
investigated with a symbol-enabled build. No measurement or benchmark cell
was rerun; these were functional checks without cost collection.

## Results

All 130 baseline cells (13 cases x seeds 0..9) completed and were checked
by the independent harness. Baseline records belong to benchmark-only
`a2698f3c`, whose production code and release CLI are identical to `df564313`.

The symbol-enabled diagnostic identifies `track_theory_vars` as the deep
DAG bottleneck: its FF compound arms omitted the scope-journalled memo used
by other compounds. A depth-n shared square/add chain was revisited once per
path (exponential), before the bounded FF evaluator could run. The sampled
stack profile lost samples under IO load and is used only for source-level
identification, not cost percentages. A separate zero-loss instruction
profile (410 samples) also identifies BigUint shift/XOR and allocation in
the binary evaluator as material costs.

Before collecting treatment cells, the candidate is fixed to two changes:
use the existing scope-journalled memo for FF compounds, setting the honesty
flag before a memo hit; and use checked u32 operands/u64 intermediates for
degree <=32 shift-and-reduce multiplication. Coefficient-loop budget charges
remain identical, including multiplication by zero. Wide fields retain the
original BigUint loop. No variable/child/enumeration order changes and no
heuristic policy are introduced. The acceptance bar and workload matrix are
unchanged. The depth-64 diagnostic will additionally become a regression;
no capped baseline is converted into a made-up speed ratio.

## Paired results

The first isolated comparison was `a2698f3c` versus `de5fe7f1` (130 cells
per arm, then 130 fresh cells per arm). Both sets passed. After concurrent
theory fixes landed, the final matched comparison rebuilt **`4a773b8f`
versus `2285fc37`** with identical workspace release flags and lockfile.
Their production difference is exactly the two optimizations and tests above.
All 260 paired outputs are byte-identical: 220 SAT, 20 UNSAT, 20 Unknown
per arm. Unknown remains unsolved and unverified. No lost cells.

| Case | Treatment/control, seeds 0..9 | Fresh seeds 10..19 |
|---|---:|---:|
| Shared F256 depth 16 | 0.3364 | 0.3360 |
| Certified SAT, same equations | 0.3378 | 0.3379 |
| Two-variable F256 | 0.5807 | 0.5806 |
| Exhausted F256 budget (Unknown) | 0.3847 | 0.3847 |
| No-root F256 quadratic | 0.8221 | 0.8110 |
| F256 square | 0.8370 | 0.8415 |
| Two-variable F16 | 0.9047 | 0.9030 |
| F4/F8/F16 squares | 0.9931–0.9996 | 0.9890–0.9914 |
| Prime control | 0.9950 | 1.0043 |
| Wide-field control | 0.9996 | 1.0012 |
| Non-control geometric mean, including fixed-budget work | **0.6849** | **0.6828** |

Both seed sets meet the pre-registered bar. The unchanged implementation is
the matched computation control: these are allocation/representation and
DAG-memoization changes, with no search policy, enumeration order or budget
change. Baseline and treatment min/median/max distributions for every case
and seed set are in the [aggregate CSV](2026-09-22-ff-extension-perf.csv).
The solved-only extension aggregate excludes the Unknown budget case and
is **0.7256** initially and **0.7231** on fresh seeds (27.4% and 27.7%
fewer instructions); the budget reduction is not a solved speedup.
The original depth-64 diagnostic now reaches the bounded solver and returns
Unknown promptly; no quantitative ratio is claimed for its capped baseline.

## Z3 reference

At the user's request, Z3 **4.16.0** is a separately measured reference arm.
The [upstream release](https://github.com/Z3Prover/z3/releases/tag/z3-4.16.0)
points to `ddb49568d3520e99799e364fb22f35fc67d887b1`. The installed Nix
package binary is pinned by its full path and SHA-256 in every record.
`bench/ff_extension_perf/README.md` records the amendment made before
reference cost collection; `z3_reference.py` implements the exact BV
encoding, with the prime control expressed by bounded modular integers.
Both Z3 random seeds follow the same 0..19 seed matrix. This is a complete
CLI comparison across different representations, not native finite-field
support in Z3. Translation generation is outside both measured invocations.

The [reference CSV](2026-09-22-ff-extension-z3.csv) reports complete
instruction distributions and per-case Nixie/Z3 ratios. Nixie decides
240/260 logical cases; Z3 decides 260/260. Every SAT model is independently
checked and every no-root UNSAT is independently exhaustive. The jointly
solved non-control geometric mean Nixie/Z3 is **0.3608**, but this aggregate
must be read alongside two material limits:

- Two-variable F256 costs Nixie **13.14x** Z3's instructions (median
  243.84 million versus 18.72 million). Enumeration remains the bottleneck.
- Nixie returns Unknown on all 20 budget cases, after a median 1.357 billion
  instructions. Z3 finds verified models at a median 70.41 million.
  These partial Nixie runs are excluded from solved cost ratios.

Tiny cases favor Nixie (about 2.7 million versus 10.5–11.0 million
instructions); startup/parsing dominates much of this difference. The
workload deliberately concentrates on generated squares and tiny systems.
It is not evidence about general polynomial systems or all SMT solving.
A stronger binary linear-algebra procedure is a separate future opportunity;
this change preserves the existing bounded solver and proof support.

### Reference record correction

The shared and certified-SAT labels translate to identical Z3 input/options.
The initial reference runner loaded existing records only once, so it
mistakenly measured the certified label again within the same invocation.
The store's filename includes the label even though its join key does not,
allowing both records through. This is a run-once protocol violation, not
additional evidence: all 20 second attempts were moved intact to
`precompile/ddb49568/benchmark/ff-extension-z3-duplicate-attempts/`, outside
canonical runs. All raw input/output remains preserved. Only each first
shared measurement is used, including for the certified label; no cell was
rerun to repair the report. There are **240 unique reference measurements**
covering 260 logical labels, and the CSV explicitly marks the reused rows.

The runner now adds newly recorded cells to its in-memory reuse index. A
mocked-counter regression requires one invocation for two identical labels;
another rejects wrong-width and incorrect models. The measured harness is
preserved at `279af11e`; subsequent edits only fix reuse, not the encoding.
The reporter verifies each translated input hash against each Nixie logical
input and never treats Unknown as an agreement or a solved result.

## Verification and artifacts

Integration snapshot `0a7e76ab` cleanly merges concurrent main commit
`df8017a2`. Its all-feature build, 114 doctests (31 ignored), Clippy,
formatting and warning-free rustdoc passed. Its compiled ignored soundness
canary passed in 254.551 seconds. Z3 parity again had 176 decisive matches
and one inconclusive result; the performance gate passed all 12 verdicts
with nine nontrivial conflict/decision ratios exactly 1.000. The initial unrestricted run on
`2285fc37` was not a passing gate: 9,726 tests passed before one integer
regression returned Unknown at its explicit 20-second timeout and seven
other tests exceeded their time limits; 2,559 tests were not reached after
fail-fast cancellation. The queued isolated retry was canceled before it
could obtain the build lock. No incorrect SAT/UNSAT appeared. A complete four-worker, no-fail-fast run on `0a7e76ab` reached all
12,333 tests: 12,328 passed and five hit external runner limits (the four
long scope-state tests and `odd_width_identity_pairs_hold`). The qlock
regression passed in 5.141 seconds. These are recorded failed attempts;
no solver timeout or search policy was changed to accommodate the machine.
The first Z3 parity run had 176 decisive matches, no mismatches and one
Z3 Unknown (`array_unique.smt2`), counted as inconclusive.

The initial 150-second perf landing gate also failed: eight counter pairs
were identical, but `f371fb73...WS_500_16_90_70.apx_1_DS-ST` had no candidate
verdict by the external cap. The gate's first diagnostic line carries the
previous filename; its following line identifies this one failed case.
A separate captured diagnostic with a 600-second external cap completed
SAT (exit 0) in 185.66 seconds, 86,080 KiB peak RSS, with 2,242,490 conflicts.
That is timeout evidence, not a replacement passing gate or a wall-time
performance claim. Both the failed run and the diagnostic are retained. Completed focused checks cover
all tiny-field products through F256 against both the old BigUint path and
the independent core evaluator, degrees 31/32/33/128 and budget boundaries,
prime/binary DAG tracking and push/pop rollback, all eight extension solver
integration tests, exhaustive reference translation checks, and two Python
harness regressions.

Canonical Nixie records and raw inputs/outputs are under
`precompile/<full-source-sha>/benchmark/{runs/ff-extension,ff-extension-raw}/`.
Reference records use `precompile/ddb49568/benchmark/runs/ff-extension-z3/`;
reference raw artifacts use the full upstream SHA directory. Profiles and
preflight evidence are under `precompile/a2698f3ca742160a2dce3ad9f9c88a17bdf96e9a/benchmark/`.
All prior cells are preserved and reused, never selectively replaced.

Arithmetic audit: `eval` checks every computed/cached element against the
field's canonical range before any caller can multiply it. For degree <=32,
a shift and the monic modulus need at most 33 bits, so u64 intermediates are
exact; all conversions are checked. Coefficient charging and zero operands
are compared against the old implementation at budget boundaries. The
independent core convolution/division evaluator, inversion, irreducibility,
prime polynomial algorithms and certificate checker remain unchanged.
Enumeration visits coefficient vectors; it does not assume that the
polynomial residue class is a primitive multiplicative generator.
Tracking uses the existing trailed compound memo, with the FF honesty flag
set before a memo hit; focused tests exercise both prime and binary fields,
repeated roots, all four FF compound kinds and two push/pop cycles.

The integrated benchmark snapshot is **`1a354d75`**, after merging concurrent
CP/model-replay main commit `ade87ad3`. The only overlapping conceptual
layer is concrete model replay; its new Boolean cache is local to an
immutable model snapshot and does not call the optimized field arithmetic.
The independent field evaluator and the field-tracking changes are intact.
Following the verification wrapper already documented for that main revision,
a temporary nextest configuration gives the default external runner 600
seconds and replaces the existing convergence override with 1,200 seconds.
Existing other overrides are preserved; the qlock test reserves all four
workers because it contains its own 20-second timeout. Test inputs,
assertions, seeds, and solver budgets are unchanged. The exact configuration
is retained with the final verification artifacts, not installed as a
repository-wide policy change.

A final 20-seed benchmark confirmation on the integrated binary reuses all
existing baseline and Z3 cells. The original `4a773b8f`/`2285fc37` comparison
remains the isolated estimate of these optimizations; unrelated main changes
are not attributed to them. All 260 integrated outputs match the baseline exactly and both seed sets
meet the registered bar again. Non-control instruction ratios, including
fixed-budget work, are **0.6871** and **0.6868**; solved-only ratios are
**0.7281** and **0.7278** (about 27.2% fewer instructions). Full distributions
are in the [integrated distribution CSV](2026-09-22-ff-extension-integrated.csv).
The [integrated Z3 CSV](2026-09-22-ff-extension-z3-integrated.csv) gives a
jointly solved extension ratio of **0.3626**. The two-variable F256 gap and
all 20 budget-limited Unknowns remain. These small changes from the isolated
candidate lie within the neutral band; they are not attributed to this work.

The shared-target verification build then failed before running tests with
`No space left on device`; a following parity build failed for the same
reason. The shared target directory was subsequently absent when inspected.
No benchmark records or cached release binaries were lost: both integrated
seed sets had completed. Verification moved to an exclusively owned target
inside the worktree, with `CARGO_INCREMENTAL=0`, development/test debug
information disabled, and four build/test workers. Optimization levels,
features, assertions, inputs and solver budgets remain unchanged. The
private all-feature build, all **12,335 tests** (17 skipped), **114 doctests**
(31 ignored), Clippy, formatting, and warning-free rustdoc passed. Z3 4.16.0
parity had 176 decisive matches and one inconclusive result; the performance
gate passed with nine counter pairs exactly 1.000 and all 12 verdicts matching.
The private release executable is byte-identical to the benchmarked executable
(SHA-256 `9bb91dabe07e44ddecf72fc52ef593fa55e555b73f9cace0c2179b5d84fde809`).
The compiled ignored trajectory canary also passed (149.765 seconds).
Build/runner failures and exact commands remain archived.

Integration **`bc69fe5f`** includes concurrent theory
completeness/SAT scope fixes from `ee169c92`. Those changes do not modify
the extension-field arithmetic, evaluator or compound memo. Inspection of
the current repository guide also found its new release-only verification
requirement. Its all-feature release build and Z3 4.16.0 parity passed (176 decisive
matches, one inconclusive); its performance gate passed all 12 verdicts
with nine conflict/decision ratios exactly 1.000. Its release-test compilation was restarted
from four to twelve build workers, retaining four test workers, then stopped
before any tests ran when the concurrent graph/FSM change landed. The first
exact-process cancellation check failed, so compilation ran briefly across
the merge; that unfinished attempt is excluded. The affected private
`nixie-theories` and `nixie-solver` release artifacts were invalidated before
rebuilding. Previously completed
measurements remain attributed to their exact source snapshots; no new
performance improvement is attributed to unrelated main changes.

All **1,540 canonical study records** pass schema, content identity, path and
uniqueness checks (five Nixie revisions at 260 cells each, plus 240 unique Z3
cells). The 20 duplicate reference attempts remain excluded and archived as
described above.

A subsequent main integration is **`9e989fbf`**, including graph/FSM commit
`f667e809`. Its source delta is confined to graph certificates, graph
callback diagnostics and the FSM benchmark; it does not modify field
arithmetic, dispatch or independent model evaluation. Its standard-LTO release suite passed all **12,350 tests** (18 skipped),
plus **114 doctests** (31 ignored). The ignored trajectory canary passed
from the same compiled release test executable (69.40 seconds). This
verification used the checked-in
nextest configuration and four test workers. The all-feature build passed
with twelve compilation workers. Test compilation was resumed with twenty
workers before any tests ran after checking spare CPU/memory capacity; no
source or compiler/link flags changed and completed artifacts were reused.

Release Clippy found one pre-existing configuration mismatch:
`env_flags::check_fixpoint` was declared in release unit-test builds although
its only caller is guarded by `debug_assertions`. Its declaration now uses
the same guard. This removes an unused debug probe, not a solver operation
or a lint suppression. The debug configuration is separately compile-checked
to ensure that the diagnostic caller still resolves.

The final verification additionally integrates the independent set-pair
budget change `345ecfec`. Its reduction and model survey use the same new
cap; pure finite-field dispatch does not enter that layer. To verify this
last integration without repeating fat LTO for hundreds of test executables,
the complete release suite is repeated with `CARGO_PROFILE_RELEASE_LTO=off`
in a separate private test target. Optimization remains level 3, with the
same features, assertions, inputs, budgets and four test workers. Production
all-feature/default builds, Z3 parity, and the performance landing gate retain
the standard release profile including LTO. The earlier standard-LTO full
suite and ignored canary remain independent evidence, not replacement gates.

The next source snapshot is **`31357514`**. The first no-LTO test pass hit the
external 180-second limit in `f4_and_buchberger_bases_agree` (that same test
passed the earlier standard-LTO run in 71.645 seconds). It was stopped after
7,550 completed passes and that one timeout, with four tests still running;
it is not a passing full-suite result. The full suite is repeated using a
retained temporary configuration with a 600-second default, 1,200 seconds
for the four scope-state regressions, and four-worker reservation for the
qlock test. Existing other overrides remain; no assertion, input, seed or
solver budget changes. No compiled test needs rebuilding for this wrapper.


That rerun passed **12,350 tests** (18 skipped, 594.077 seconds), all doctests,
release Clippy, formatting, and warning-free rustdoc. The ignored trajectory
canary passed in 60.119 seconds. Both standard-LTO production builds passed.
These results remain attributed to `31357514`, not to the following fix.

## Dispatch lifecycle defect found during the final audit

A scope-transition probe on `31357514` exposed an invalid model in **both
prime and binary fields**:

```smt2
(set-logic ALL)
(declare-const x (_ BinaryField 7))
(assert (= (ff.mul x x) (as ff1 (_ BinaryField 7))))
(check-sat)
(declare-const i Int)
(assert (= i 1))
(check-sat)
(get-value (x i))
```

It returned `sat`, `sat`, then `x = 0, i = 1`, violating `x² = 1`.
The prime-field variant (`(_ FiniteField 5)`) did the same. These are invalid
models of satisfiable formulas; this probe alone does not demonstrate an
unsatisfiable formula being declared SAT. Raw inputs and outputs are archived
under `precompile/31357514.../benchmark/ff-extension-verification/`.

The FF dispatcher cleared the scope-trailed `ff_terms_unconstrained` flag
when a check succeeded. A later foreign-theory assertion made the dispatcher
decline, while that stale cleared flag allowed generic CDCL to publish a
model without field semantics. Re-tracking a directly encountered FF compound
on a memo hit was insufficient: a new integer assertion need not revisit any
field term. This bug predates the compound-memo optimization.

The fix separates persistent, scope-trailed field presence from **per-check
FF ownership**. Only a successful complete FF dispatch grants ownership;
every core check resets it. Neither eager nor Boolean/UF field solving clears
the presence flag. Unsupported mixed goals therefore return Unknown after
prior successful checks, including after scope changes and cache hits.

The remaining layers were inspected independently:

| Layer | Evidence and scope |
|---|---|
| Tracking/memo | FF presence persists across checks; the existing trail retracts both compound claims and presence with their assertion scope. Duplicate assertions cannot erase presence. |
| Dispatch | Shape rejection, quantifier rejection and binary UF rejection do not grant ownership. Eager, Boolean and prime UF SAT all pass through the single ownership-granting caller. |
| Rechecking/scopes | Regression crosses pure SAT → mixed Unknown → pop → pure SAT, repeats cached checks, then reasserts a memoized field formula and adds another integer assertion. Covers prime/binary, conjunctive/Boolean, normal/certified modes. |
| General CDCL/model readback | There is no field engine in the generic path. Missing field variables can be completed to zero; that is not a witness for field assertions. The presence gate must reject this path before publishing SAT. The arithmetic model evaluator is fragment-limited and is not a substitute for the gate. |
| Independent certification | Core AST evaluation reads assignments only for variables/applications and computes interpreted nodes. A direct validator regression forges x=0, x²=1 and the equality=true simultaneously, bypassing dispatch. Both prime and binary certificates must reject it. |
| Exact arithmetic | The original exhaustive tiny-field, independent convolution, wide-boundary and identical-budget tests remain applicable; this fix changes no arithmetic or enumeration order. |
| Reference semantics | cvc5 `theory/ff/theory_ff.cpp::postCheck` marks incomplete checks model-unsound; Z3 `smt_context.cpp::check_preamble/check_finalize` separates query state and optional model validation. Neither reference is linked. |

The first focused run passed the memo and forged-certificate tests but
failed the Boolean transition. The conjunctive lifecycle fix therefore did
not establish correctness of the Boolean dispatcher. A second, independent
root cause was present: the shape gate checked structured assertions, but
skipped checking the field vocabulary of top-level equality literals. If
another assertion contained an `or`, DPLL(FF) accepted a separate integer
equality. Its Tseitin encoder silently minted an atom for that equality;
field slicing then gave it no theory constraints.

This yielded an actual **false SAT**, without any preceding check:

```smt2
(set-logic ALL)
(declare-const x (_ BinaryField 7))
(declare-const i Int)
(assert (or (= (ff.mul x x) (as ff1 (_ BinaryField 7)))
            (= (ff.mul x x) (as ff2 (_ BinaryField 7)))))
(assert (= (+ (* i i) 1) 0))
(check-sat)
```

`31357514` returned SAT with i=0. The integer conjunct is impossible over the
integers; installed Z3 4.16.0 independently returns UNSAT for that conjunct.
The raw counterexample and reference input/output are archived beside the
scope probes. The outer shape gate now validates literal assertions too.
Independently, the shared FF/UF Boolean encoder checks that equality operands
and distinct arguments have the same finite-field sort before minting atoms.
A direct encoder unit test bypasses the dispatcher, and an end-to-end
regression protects the false-SAT case in both prime and binary fields.
The prime UF entry already checked every assertion with
`dag_is_ufff_boolean`; its combinations remain covered by the full oracle.
Certified validation independently rejected the forged compound/atom model;
no evaluator defect was found in that path.

Final verification and performance confirmation for these fixes are recorded
below when complete. Earlier measurements are retained with their exact source
identities; no old cell is overwritten or rerun.
