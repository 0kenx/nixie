# Next performance targets

Source audit dated 2026-09-05, against Nixie `bdd4206` and the local Kissat,
CaDiCaL, and Z3 reference trees. This records the performance opportunities
identified in the project review. **No new benchmarks were run for this audit;
the proposed gains are hypotheses, not measured speedups.** The inspection
focused on the SAT core, CDCL(T) integration, arithmetic, and bit-vector encoding;
it is not an exhaustive review of every theory.

## Recommendation

Start with linear-time theory replay and arithmetic-term collection, then measure
indexed simplex row updates and a signed-literal BV circuit representation.
For SAT memory, the largest clear structural target is eliminating duplicate
binary-clause storage. Repairing incremental theory invariants is a larger,
correctness-led project that could eventually remove expensive full rebuilds.

| Order | Target | Main benefit to investigate | Scope / risk |
|---|---|---|---|
| 1 | Stable, linear-time theory replay | Eliminate repeated assignment-trail scans | Small; preserve replay order and scope boundaries |
| 2 | Indexed arithmetic-term deduplication | Eliminate quadratic vocabulary collection | Small; preserve first-occurrence order |
| 3 | Indexed sparse simplex row updates | Reduce coefficient lookup and allocation work | Medium; exact arithmetic and transactional updates are load-bearing |
| 4 | Signed BV signals and structural gate sharing | Reduce variables, clauses, and repeated circuit construction | Medium/large; encoding, model, and scope contracts change |
| 5 | Compact binary-clause representation | Reduce standing SAT memory on binary-heavy inputs | Large; reasons, proofs, deletion, and preprocessing must agree |
| 6 | Reliable incremental theory state | Avoid reset-and-replay work across candidates/checks | Large; correctness prerequisite before removing any backstop |
| 7 | Live-clause-oriented maintenance | Avoid scans proportional to all historical clause allocations | Medium; preserve stable IDs and traversal order |

The order reflects implementation value and tractability, not a measured ranking
of end-to-end speedups. A profile on the intended workload may change it.

## Existing performance evidence

The latest committed worker-memory study reports this paired standing table:

| Solver | Solved / 54 at a 60-second cap | Nixie/reference wall-time ratio on both-solved files |
|---|---:|---:|
| Nixie | 50 | — |
| CaDiCaL 3.0.1 | 51 | 1.239x |
| Kissat 4.0.4 | 50 | 1.411x |

These are historical results on a selected corpus, not general solver parity or
evidence that any proposed optimization works. The preceding rebaseline split
the Kissat gap into a 1.332x conflict-count factor and a 1.093x per-conflict wall
factor on its counter-covered subset. Search length and execution cost both
matter; the subset decomposition must not be treated as an exact factorization
of a different table.

Sources:

- [Standing gap and subsequent corrections](docs/studies/2026-09-01-standing-vs-kissat-gap-decomposition.md)
- [Committed worker-class memory landing and paired standing table](docs/studies/2026-09-05-worker-class-memory-landing.md)

At audit time, the shared checkout also contained uncommitted walk-on-BIG,
arena-slack, and BVE-scan work, plus a draft memory slice-2 study. That work
already targets several transient allocations; do not duplicate it. Its draft
results were not independently verified here and are not the committed baseline
above. Check current history and ownership before starting a memory change.

## 1. Make theory-state replay linear

**Observed:** `TheoryManager::resync_theory_state` snapshots the assignment trail,
then loops over every decision level and filters the entire trail for that level.
With `A` assignments and `D` decision levels, filtering costs O(A*D), independently
of the theory assertions themselves.

**Proposed change:** construct a stable grouping by level once, then replay in
O(A+D). A counting pass plus prefix offsets and a stable scatter into reusable
storage can preserve exactly the current order within each level. Preserve empty
levels and every push boundary as well.

The shadow trail uses swap-removal on backtrack, so it must not simply be assumed
to be sorted by level. Keep replaying Boolean mirrors and theory constraints in
the existing order, including the behavior after the first detected conflict.

This optimization retains the full soundness rebuild. It does not depend on
solving target 6.

**Measure:** trail entries examined, atoms replayed, replay allocations, and
instructions on deep function-bearing QF_UF/QF_UFLIA inputs. Verify identical
replay events and outcomes before claiming trajectory neutrality.

Source: [theory_manager.rs](nixie-solver/src/solver/theory_manager.rs),
`resync_theory_state` and `on_backtrack`.

## 2. Remove quadratic arithmetic-term collection

**Observed:** `propagate_euf_equalities_to_arith` gathers unique arithmetic terms
using `arith_terms.contains()` for each occurrence. The later grouping by EUF
root and representative-chain sharing already avoid all-pairs equality
construction, but the initial vocabulary collection remains worst-case quadratic.

**Proposed change:** retain the ordered vector and use a membership set for
deduplication. Preserve first-occurrence order so the representative choice and
downstream equality assertion order do not change. Only consider a persistent
vocabulary cache after defining its assertion/scope invalidation contract.

Z3's broader architecture delivers shared equalities through a propagation queue
to attached theories. Moving Nixie toward merge-driven notifications is a later
project; a local membership index is the first slice.

**Measure:** term occurrences, unique terms, membership comparisons, and
combination instructions. Validate unchanged ordered term and equality streams.

Sources:
[Nixie theory manager](nixie-solver/src/solver/theory_manager.rs),
`propagate_euf_equalities_to_arith`;
[Z3 context](../temp/z3/src/smt/smt_context.cpp), `propagate_th_eqs`.

## 3. Index sparse simplex row updates

**Observed:** `Simplex::pivot` substitutes the pivot row into each affected row
using `LinExpr::try_add_term_mul`. That helper linearly searches the destination
row for each coefficient; cancellation uses another vector scan. Wide row
substitutions therefore pay multiplicative row-width lookup cost in addition to
the exact rational arithmetic. Affected rows are also cloned into transactional
replacement rows.

**Reference:** Z3's sparse matrix builds a variable-to-row-offset workspace,
updates coefficients through that index, then removes zero entries. Nixie already
has a column index and targeted assignment updates; adding those again would
duplicate completed work.

**Proposed first slice:** use reusable indexed scratch for destination coefficient
locations, preserving the existing coefficient-operation order and resulting
term order where possible. Handle insertion and cancellation explicitly so an
offset never names a removed or relocated term. Keep all checked arithmetic and
the validate-before-commit contract; an overflow must not expose a partial row
update or fabricate a feasible tableau.

**Measure:** coefficient comparisons, row entries visited, replacement-row
allocations, rational operations, and instructions. Pivot count alone cannot
establish an improvement. Include narrow-row workloads to detect indexing
overhead and wide/degenerate systems to exercise the intended benefit.

**Later slice:** `ensure_scope_snapshot` clones the tableau map, basic set,
column map, and assignment vector once per mutated level. Rows/columns are
already `Arc`-shared, so these are not deep copies of every coefficient. Precise
undo records could reduce map/vector snapshot costs, but require a separate
rollback design and proof of scope consistency.

Sources:
[Nixie simplex](nixie-theories/src/arithmetic/simplex/mod.rs),
`try_add_term_mul`, `pivot`, and `ensure_scope_snapshot`;
[Z3 sparse matrix](../temp/z3/src/math/lp/static_matrix_def.h),
`scan_row_strip_to_work_vector` and `pivot_row_to_row_given_cell`.

## 4. Use signed BV signals and share circuit gates

**Observed:** the production `BvSolver` gate layer uses `Sig::Var(Var)`.
`gate_not` allocates a fresh SAT variable and emits two clauses for a nonconstant
negation. `gate_and` folds constants and identical inputs, but otherwise emits a
new gate without a structural gate-cache lookup. `wire` can add equivalence
clauses between a gate result and a preallocated output variable.

Term-level memoization exists. The opportunity is to share internal circuit
signals and repeated gates below that layer. The separate `AigBvBuilder` API is
not evidence that the production dispatch already performs this sharing.

**Proposed slices:**

1. Represent internal signals using signed literals/complemented edges so NOT
   changes polarity without allocating a gate.
2. Intern canonical gate signatures to reuse identical subcircuits.
3. Where the public bit-vector mapping permits it, map output bits to aliases
   instead of allocating and wiring an additional result variable.

Start in the pure-BV dispatch. Cache entries must remain valid across assertion,
push/pop, reset, and abstraction-refinement boundaries. Model extraction must
evaluate aliases correctly. Preserve exact wide-BV and zero-divisor semantics;
an encoding refusal must still fail closed or use the existing sound fallback.

**Reference:** Z3 carries polarity through Boolean-to-SAT conversion and includes
sharing/AIG processing in its QF_BV tactic pipeline.

**Measure before search:** variables, clauses, literal occurrences, gate-cache
hits, duplicate signatures, and encoding instructions. Then evaluate search with
the required controls: a smaller encoding can change trajectories and is not by
itself an end-to-end speedup.

Sources:
[Nixie BV solver](nixie-theories/src/bv/solver.rs), `Sig`, `gate_not`, `gate_and`,
and `wire`;
[pure-BV dispatch](nixie-solver/src/solver/dispatch_pure_bv.rs);
[Z3 Boolean-to-SAT conversion](../temp/z3/src/sat/tactic/goal2sat.cpp);
[Z3 QF_BV tactic](../temp/z3/src/tactic/smtlogics/qfbv_tactic.cpp).

## 5. Eliminate duplicate binary-clause storage

**Observed:** the current SAT representation pays approximately 44 bytes per
binary clause before allocation slack and other metadata:

| Component | Bytes |
|---|---:|
| Aligned arena slot: 12-byte header + two literals | 24 |
| Two `(Lit, ClauseId)` implication edges | 16 |
| Clause-ID-to-arena-reference entry | 4 |

The production implication graph is the private structure in `solver/mod.rs`,
not the separately exported graph in `big.rs`.

**Reference:** Kissat creates watch-resident binaries without allocating an
ordinary arena clause; `new_binary_clause` returns `INVALID_REF`. Its assignment
representation distinguishes binary reasons. CaDiCaL retains clause pointers in
watches, so Kissat is the relevant representation reference for this target.

**Proposed change:** introduce an explicit binary reason/handle representation,
then avoid the redundant normal arena slot. Work through every holder and
consumer: conflict analysis, learned minimization, locked reasons, duplicate
binaries, deletion, proof IDs, BVE/ELS, model extension, incremental scopes, and
walk participation/order. Do not replace the clause ID with a literal until all
those contracts have a representation.

**Measure:** bytes per live binary, steady-state and peak memory, preprocessing
transients, and instructions on worker/shuffling and adjacent non-binary-heavy
families. Stable edge visitation order is essential for any trajectory-neutral
claim. Account for the already in-flight walk/transient changes first.

Sources:
[Nixie clause database](nixie-sat/src/clause.rs),
[arena layout](nixie-sat/src/memory.rs),
[production BIG](nixie-sat/src/solver/mod.rs),
[trail reasons](nixie-sat/src/trail.rs);
[Kissat clause creation](../temp/kissat/src/clause.c),
[Kissat watches](../temp/kissat/src/watch.h),
[Kissat assignment representation](../temp/kissat/src/inlineassign.h);
[CaDiCaL watches](../temp/cadical/src/watch.hpp).

## 6. Repair incremental invariants before removing rebuilds

**Observed:** `TheoryManager::final_check` rebuilds state for selected
function-bearing cases because incremental EUF can lose congruence or
disequality information. `resync_theory_state` resets EUF, arithmetic, BV, and
difference logic, then replays surviving assignments. Public checks also rebase
theory state to prevent prior branch facts from leaking into later checks.

**Opportunity:** reliable scoped state could avoid repeatedly reconstructing
congruence closure, arithmetic state, and BV definitions. Z3's reference shape
uses scoped trails, theory push/pop callbacks, and propagation queues.

**Prerequisite:** turn incremental-versus-fresh replay into an invariant oracle.
Exercise late interning, merges, disequalities, branch backtracking, repeated
checks, and user push/pop; compare explained equalities, conflicts, and concrete
models. Fix the actual divergences before changing the production backstop.

Do not merely replace reset with pop or retain the arithmetic rows. The existing
source records a failed attempt: keeping rows during replay severely regressed
`read6` and `fb_var_5_12`, with the replay-state cause not isolated. Preserve this
finding when designing another attempt.

**Measure first:** rebuild count, replayed atoms, recreated rows/circuits, and
their work share. This target has the highest correctness risk and an unmeasured
payoff; targets 1 and 2 can proceed independently.

Sources:
[Nixie theory manager](nixie-solver/src/solver/theory_manager.rs),
`resync_theory_state` and `final_check`;
[Nixie check orchestration](nixie-solver/src/solver/mod.rs),
`rebase_theory_state` and `check_core`;
[Z3 context](../temp/z3/src/smt/smt_context.cpp), scope and propagation handling.

## 7. Keep maintenance tied to live clauses

**Observed:** arena compaction now reclaims clause bytes, but IDs and the
reference table remain append-only. `ClauseDatabase::iter_ids` scans every
historically allocated slot, and arena compaction traverses that reference table.
Consequently, some maintenance work still scales with historical allocations
rather than the live database. The learned-clause reduction list already removes
deleted entries; do not confuse it with the historical reference table.

**Proposed first slice:** maintain an ordered live-clause index for suitable
whole-database traversals, preserving allocation-order visitation and stable IDs.
Measure the added update/storage overhead. This does not reclaim historical
reference entries; ID reuse or remapping is a separate, more invasive project
involving proofs, reasons, and every ID-indexed table.

**Measure:** historical/live slot ratio, slots visited per maintenance pass,
reference-table bytes, and maintenance instructions during long searches.

Sources:
[clause database](nixie-sat/src/clause.rs), `iter_ids` and `refs`;
[arena compaction](nixie-sat/src/memory.rs), `compact`;
[learned database maintenance](nixie-sat/src/solver/learn.rs).

## Avoid repeating closed or already completed work

- Arena compaction, BIG-authoritative propagation, several allocation fixes,
  targeted simplex assignment updates, and pure-BV eager dispatch already exist.
- Smaller watchers, flat watch arenas, and blocker-load splitting have already
  been tested without a worthwhile gain. The BCP profile is workload-specific;
  it does not prove every possible propagation improvement is exhausted.
  [BCP experiment record](docs/studies/2026-09-02-propagate-profile-closure.md)
- Generic retention-signal tuning has a corrected neutral result. Earlier large
  reported gains included unsound runs and are invalid evidence.
  [Retention correction](docs/studies/2026-09-02-retention-signal.md)
- Multiplication CEGAR already landed. Division abstraction and the simplified
  SOI driver already exist behind opt-in switches with negative/neutral results.
  Read the corrections inside the studies rather than relying on their oldest
  diagnosis or a stale research-priority list.
  [BV CEGAR](docs/studies/2026-08-bv-mul-cegar.md),
  [SOI](docs/studies/2026-08-soi-simplex.md)

## Execution and acceptance

Follow [AGENTS.md](AGENTS.md) and [BENCHMARKING.md](docs/BENCHMARKING.md).

- Establish whether each change preserves the search trajectory. For a claimed
  preservation, verify relevant ordered event streams and solver counters;
  matching verdicts alone is insufficient.
- Use deterministic work counters that cover the changed work. Conflict counts
  cannot measure the value of removing scans, allocations, or coefficient
  lookups when the search is identical. Record memory for representation work;
  wall time is supporting context, not the primary metric or a policy input.
- For changes affecting search, pre-register a matched null, use at least ten
  seeds per cell, report baseline distributions, and replay hindsight-selected
  configurations at fresh seeds. Define whether ratios represent cost or
  speedup so their direction is unambiguous.
- Reuse existing result-store cells and record new cells once. Include
  neighboring workload families to expose overhead and regressions.
- Keep exact arithmetic, explanation validity, model validation, proof handling,
  and scope consistency intact. Run the full verification bar and Z3 parity
  required by the agent guide before landing solver changes.
- Commit finished code/tests or a documented negative result to `main`, stage
  only owned files, and remove only the worktrees/artifacts created for that
  completed step.

## Research addendum: candidates for surpassing Kissat

Literature and source review dated 2026-09-05. The target here is single-threaded
SAT on the same CNF input, including all analysis and preprocessing costs.
These are proposed experiments, **not established novel algorithms or demonstrated
Kissat wins**. A literature search can identify collisions; it cannot establish
that nobody has tried the remaining mechanism.

The [existing research agenda](docs/2026-08-novel-research-agenda.md) already covers
representation morphing, clause-retention control, phase sources, portfolios,
and CNF recovery/re-encoding. Repeating those proposals with new names would not
answer the request. Two narrower candidates survive this review; only the first
has a plausible route to a substantial algorithmic advantage.

### A. Synthesize a relation from recurring conflict regions

**Bet:** repeated conflicts sometimes expose a small interface between a difficult
local subproblem and the remaining formula. Learn a compact, proved relation on
that interface, so later search can reason about the whole relation without
rediscovering its consequences separately.

The proposed novelty is the specific feedback loop: recurring conflict support
selects an interface; counterexamples refine a bounded circuit describing a
derived relation; an exact proof admits it; subsequent propagation work determines
whether that representation earns its cost. Merely learning multiple clauses,
recovering an XOR, introducing extension variables, or building a BDD is not new.

**Concrete first design:**

1. Sample bounded conflict-analysis slices and record recurring clause support.
   Select a small region of justified clauses `F_R(B, I)`, where `B` is an
   interface of initially at most 8–12 Boolean variables and `I` contains the
   remaining local variables. Do not require the whole formula to decompose.
2. Use exact local models and certified infeasible interface assignments to fit
   a small relation `R(B)`. Begin with a strictly bounded Boolean circuit grammar;
   include non-affine relations so the experiment does not reduce to XOR recovery.
   Limit circuit nodes, local search work, and retained regions deterministically.
3. Independently establish `F_R(B, I) => R(B)` by checking
   `F_R AND NOT R` is UNSAT with a checkable derivation. A local countermodel
   refines the candidate; a budget exhaustion rejects it. A failed global branch
   is not evidence that its projection onto `B` is locally impossible.
4. Keep the original CNF. Add definitions for the circuit and the proved assertion
   of its output through a supported proof format. Fresh definitions alone do
   not justify asserting the output. If a relation depends on assumptions `g`,
   prove and retain `g => R`, with correct scope support.
5. First use ordinary CNF propagation of the added circuit. Native propagation
   with clausal explanations is a separate experiment, after proof admission and
   incremental state handling work. Measure whether definitions actually compress
   repeated reasoning after accounting for their own watch traffic.

For example, a relation involving several boundary bits might summarize the
combined effect of many overlapping constraints, even when no corresponding gate
occurs syntactically in the input or learned clauses. A parity example would
illustrate the mechanism but would not establish novelty.

**Why it could surpass Kissat:** a compact derived circuit can expose consequences
that would otherwise require many separate conflicts. The upside is a reduction
in search and proof work, potentially much larger than a faster watcher loop.
That is a hypothesis about structured instance families, not an asymptotic result
for this design or a prediction of a competition win. Certification might consume
all the work it was intended to save.

**Nearest prior art and the remaining uncertainty:**

- [Learning from BDDs in SAT-based bounded model checking](https://bpb-us-w1.wpmucdn.com/sites.usc.edu/dist/c/321/files/2019/03/Gupta03BddLearn-2ap2wmd.pdf)
  already learns multiple consequences of local Boolean relations.
- [BDD-guided clause generation](https://www.andrew.cmu.edu/user/vanhoeve/papers/cpaior15-bddclausegen.pdf)
  already generates consequences using exact or approximate BDDs, including
  clauses stronger than one application of ordinary conflict analysis.
- [Extended resolution using BDDs and quantification](https://fmv.jku.at/papers/JussilaSinzBiere-SAT06.pdf)
  already supplies a proof framework for symbolic reasoning. BDD projection plus
  proof logging is therefore not the novelty claim.
- [Dual implication points](https://lmcs.episciences.org/18269) already select
  extension definitions from conflict graphs.
- [Factoring Learned Clauses, SAT 2026](https://program.floc26.org/SAT-2026-07-20)
  already includes global XOR/ITE factoring of learned clauses; its
  [artifact](https://zenodo.org/records/20154935) is a required comparator.

The remaining contribution would have to be demonstrated in the **selection and
synthesis of useful derived relations across recurring conflict slices**, beyond
these methods. Originality confidence is provisional, and prior-art overlap is
substantial. If implementation collapses to BDD clause learning or gate factoring,
describe it as an application of that existing method.

**Nixie starting points:** [conflict analysis](nixie-sat/src/solver/learn.rs),
[binary factoring](nixie-sat/src/solver/factor.rs), and
[extension definitions](nixie-sat/src/extended_resolution.rs). The last provides
representations, not evidence that this search/proof integration already exists.
Kissat's [sweeping](../temp/kissat/src/sweep.c) is a local semantic-reasoning
baseline; the proposal needs to add value beyond backbone/equivalence discovery.

**First experiment and rejection conditions:**

- Start with observation only: measure repeated support, interface sizes, and
  whether independently certified relations remain compact. Use untouched
  families for evaluation; selecting only appealing traces would bias the study.
- Compare conflict-selected regions against permuted region scores with the same
  extraction, synthesis, and certification budgets. Report acceptance-rate and
  candidate-size differences instead of pretending this fully matches injection.
- Separately isolate selection value using a shared pool of verified candidates:
  treatment and null inject the same number and size distribution of definitions
  at the same events, with utility scores permuted for the null. Random invalid
  formulas that are all rejected are not a matched null.
- Compare with BDD-derived clauses and XOR/ITE factoring, as well as ordinary
  Nixie and a pinned Kissat. Include all synthesis, proof, and propagation work.
- Reject if local proof cost dominates, useful interfaces are too large, circuit
  size explodes, or advantages disappear against the valid-candidate null or
  established methods. An offline oracle win only justifies trying an online
  selector; it does not count as solver performance.

### B. Share an exact blocker check across a contiguous watch span

**Bet:** some watch spans repeatedly contain many entries whose blockers belong
to the same very small set. One exact guard can certify that the entire span will
take the ordinary blocker-hit path.

In [the current propagation loop](nixie-sat/src/solver/propagate.rs), every entry
loads and checks its blocker separately. Build bounded metadata for an unchanged
contiguous span of, for example, 32 entries with at most four distinct blockers.
If all four literals are currently true, every original blocker test would pass.
With valid metadata and `write == read`, advance both cursors across the span.
Otherwise execute the existing loop. Do not reorder watches to manufacture runs
in the first experiment; that changes the search and its causal question.

**Correctness contract:** metadata identifies the exact span and blocker set,
not a probabilistic signature. Any change to membership, order, blockers, or span
storage invalidates its generation. A fresh guard checks current literal values,
so a previously true guard cannot survive backtracking unchecked. Restrict the
first slice to `write == read`; otherwise compaction copies remain necessary.
Preserve counter updates, budgets, and ordered search events. Clause deletion,
watch movement, arena maintenance, and scope changes must respect invalidation.

This reuses a proof of *no effects from this group of checks*. It does not reuse
assignments from an earlier trail, as in
[Trail Saving on Backtrack](https://pmc.ncbi.nlm.nih.gov/articles/PMC7326469/).
The narrow candidate contribution is cross-entry guard sharing with unchanged
watch order and search behavior. No exact match was found in the reviewed sources;
that is weaker than establishing originality.

**Headroom is limited.** The
[mrpp propagation profile](docs/studies/2026-09-02-propagate-profile-closure.md)
reports 66% blocker hits, about 50 instructions per watch visit on average, and
roughly 6–10 instructions per blocker-hit visit. On those approximate figures,
even removing every blocker-hit instruction would save only about 8–13% of
watch-processing instructions. Combining this loosely with the 74.8% propagation
cycle share suggests roughly 6–10% overall headroom, before guards and maintenance.
The instruction/cycle mixture makes this an order-of-magnitude estimate, not a
measured bound. Real eligible spans cover less. This is a supporting optimization,
not a credible standalone route across the historical 1.411x corpus gap.

**First experiment:** collect blocker-diversity histograms for unchanged spans,
guard-hit frequency, metadata lifetime, and eligibility under `write == read`.
Count construction, guard misses, invalidations, fallback, and skipped scalar
operations. Reject before implementing acceleration if an optimistic savings
estimate cannot clear a pre-registered worthwhile threshold after those costs.
Do not infer guard coverage from the scalar blocker-hit percentage.

For a prototype, compare baseline, metadata/guard execution with scalar replay,
and actual span skipping. Require identical ordered search traces and legacy
scheduling ticks. Use a separate deterministic work account covering the new
operations; unchanged scheduling ticks cannot measure the optimization. Hardware
instruction counts can corroborate that the work reduction survives compilation.
If watch reordering is later introduced, it becomes a separate heuristic requiring
its own matched null and seed distribution.

### Ideas screened out and research order

Do not claim the following as new: extension learning from conflict dominators;
XOR/ITE factoring of learned clauses; clause transfer between similar subgraphs
([FMCAD 2021](https://ofers.dds.technion.ac.il/publications/fmcad21.pdf)); or keeping
more assignments by changing backtracking
([Graph Backtracking, SAT 2026](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2026.14)).
Applying inprocessing above the root also has direct prior art in Backtrackable
Inprocessing in the [SAT 2026 program](https://program.floc26.org/SAT-2026-07-20).
Transporting search state through formula rewrites might leave a narrower open
question, but this review did not establish a sufficiently distinct mechanism to
recommend it as a third novel approach.

Run B's inexpensive observation screen first. Allocate the larger research effort
to A only if its observation screen finds compact, reusable, cheaply certified
relations. Follow the execution protocol above: at least ten seeds per heuristic
cell, matched nulls, fresh-seed replay, complete deterministic work accounting,
and held-out families. Cross-solver tick definitions are not interchangeable;
report their work counters explicitly instead of dividing unlike tick totals.
Pin reference revisions and preserve a broad corpus containing SAT and UNSAT
instances. A family-specific win should be called that. Neither proposal has been
implemented or benchmarked for this addendum.
