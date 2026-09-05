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
