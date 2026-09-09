# Using a large mathematical library inside Nixie

Status: proposed architecture; no implementation or performance claim. Repository
surfaces inspected at `7dcfacd`. The design uses **200,000 lemmas as a capacity
assumption**, not a measured count for a particular mathlib revision.

## Decision

Build a library compiler and a demand-driven inference service. Keep the entire
library searchable, but bring only a small, changing set of typed inference plans
into a solver session. Treat theorem selection, substitution selection, and clause
admission as three different decisions with separate costs and diagnostics.

Make a small learned **application policy** the central research hypothesis: given
the current problem and concrete applicable steps, predict which step makes the
remaining problem cheaper to solve. Library retrieval supplies alternatives; theorem
relevance alone does not determine the next action. Symbolic retrieval and selection
remain essential baselines and fallback policies, rather than prerequisites that
must fail before investigating learned application selection.

Porting individual statements should be generated data work. Do not create a Rust
function per theorem, scan the library on every solver event, or register the whole
library as quantified assertions. The engineering investment belongs in shared
translation, indexing, matching, scheduling, and checking machinery. Supporting
a new logical encoding or proof rule remains substantive work even when exporting
another theorem that uses an existing encoding is mechanical.

The main hypothesis is that learned selection can exploit library knowledge to
shorten reasoning by recognizing useful transformations in context. The competing
hypothesis is that retrieval, matching, model inference, checking, and added clauses
cost more than the search they save. This is a proposal, not a demonstrated gain.

## Semantic contract: two clients of one service

**Ordinary SMT acceleration.** For a query `F` in background theory `T`, every
admitted library instance `L` must satisfy `T |= L`, or carry an explicit derivation
of `T, F |= L`. Library selection changes search, not the input's meaning. A
user-declared function named `sin` or `gcd` is still uninterpreted unless an explicit
semantic binding establishes otherwise. Names and retrieval similarity never
establish a binding.

**Library mathematics.** A frontend supplies a goal, local hypotheses, declaration
identities, and the mathematical environment in which they are interpreted.
Search refutes hypotheses together with the negated goal, using selected library
facts. A checked refutation can prove the goal. A model of an incomplete selected
axiomatization does not establish a counterexample to the original mathematics;
the frontend returns `Unknown` unless the model can be lifted and validated in the
original semantics. A separate prover API may report `Proved`/`Unknown`.

This distinction prevents a common mistake: library selection may omit optional
theorems, but it may not silently discard mandatory input assertions, definitions,
or model-validation obligations. In ordinary SMT, an independently validated model
of the original input remains sufficient even if the optional lemma service stops.

## Dataflow and ownership

```text
Pinned Lean/mathlib environment
          |
     library compiler                    offline tooling
          |
   +------+-------------------+
   | catalog + indexes        |          immutable, all lemmas
   | typed templates          |          loaded on demand
   | proof/definition archive |          shared dependency DAG
   +------+-------------------+
          |
Query + declaration bindings + solver events
          |
   typed retrieval + bounded graph expansion
          |
   candidate pool -> cost-aware plan activation
          |
   delta matching / goal-directed application
          |
   concrete actions + bounded consequence previews
          |
   learned application policy / remaining-work estimate
          |                         |
   selected action                  continue base solver
          |
   certificate checker
          |
   scoped clause admission -> CDCL(T) -> checked result
          |                                  |
          +--- work/usefulness feedback ------+
```

The catalog is shared across sessions. Plans, substitutions, event queues,
assumption dependencies, and emitted clauses belong to the solver session.
Proof checking has its own immutable verified objects and does not trust retrieval
or mutable search state. All executable solver and checker components are Rust;
Lean is optional offline export/verification tooling or an external proof consumer.

## 1. Compile the library into plans and indexes

Export elaborated declarations, rather than parsing pretty-printed statements.
Retain stable declaration identities, universe/type parameters, structure-instance
arguments, hypotheses, conclusions, definition dependencies, proof dependencies,
source provenance, and transitive axiom dependencies. Preserve the source license
and version information in generated packs.

Build a shared typed expression DAG. Use distinct representations for source-level
identity, normalized retrieval features, and the formula whose semantics is checked.
Retrieval may use lossy fingerprints; inference must use the exact typed formula.
Do not put process-local `TermId`, `SortId`, or interned symbol handles in pack files.

A conceptual record is:

```text
LemmaRecord {
    declaration_id, source_environment_digest,
    statement_digest, semantic_binding_requirements,
    type_parameters, structure_parameters,
    hypothesis_patterns, conclusion_patterns,
    statement_ref, plan_refs, certificate_ref,
    definition_dependencies, proof_dependencies,
    retrieval_features, applicability_class, cost_features
}
```

Classify a theorem into zero or more executable plans:

| Plan | Application strategy |
| --- | --- |
| Reducing equality | Directed normalization with a checked equality justification |
| Guarded equality | Watch side conditions; rewrite only with their explanations |
| Implication/Horn consequence | Join existing terms and facts, then emit an implication |
| General first-order clause | Selective instantiation and ordinary SAT handling |
| Goal-directed theorem | Match a conclusion, producing explicit premise obligations |
| Witness/existential theorem | Separate checked witness or Skolem-extension plan |
| Unsupported encoding/proof | Searchable metadata with a specific ineligibility reason |

An equivalence may produce two implication plans. Associativity and commutativity
belong in canonical normalization or checked equality reasoning, not unrestricted
bidirectional rewriting. Expanding equalities require explicit term-growth budgets.
Sharing or deduplicating equivalent statements must retain their assumptions,
semantic bindings, and certificates; similar retrieval fingerprints are insufficient.

Keep polymorphic templates compact. Specialize only for concrete type and structure
substitutions demanded by a query. Cache by theorem identity, exact specialization,
binding environment, and compiler/checker version. A second ring structure on the
same carrier type is a different specialization. Do not precompute the Cartesian
product of 200,000 theorems and every known type.

The compiler reports counts and sizes for exported, lowerable, independently
certifiable, and executable declarations separately. Catalog size is not usable
theorem coverage. Every omitted declaration or dependency has an explicit reason.

## 2. Make the full library cheap to search

Use three working sets, with independently enforced byte and work limits:

| Set | Contents | Initial capacity experiment, not a tuned default |
| --- | --- | --- |
| Catalog | All metadata, postings, and archive offsets | 200,000+ declarations |
| Candidate pool | Relevant typed templates and alternative plans | Up to 2,048 candidates |
| Active plans | Compiled matching programs and subscriptions | Start with 64, widen up to 256 |

Candidate and active limits count specializations/plans explicitly: one polymorphic
theorem can otherwise evade a theorem-count cap. Also cap total plan instructions,
partial substitutions, watched facts, certificate bytes, and newly created terms.

A hypothetical 256-byte fixed record for 200,000 declarations costs 51.2 MB decimal
before postings, strings, templates, proofs, and allocator overhead. This is a sizing
example, not an estimate of the complete library. Keep variable-size bodies and
proofs in separately addressable chunks; loading 64 plans must not deserialize the
entire proof archive. Desktop use can share read-only pages across sessions;
constrained targets can install smaller packs through the same abstract store API.

Build these complementary indexes:

* Typed symbol-to-theorem postings, with document frequency and bounded iterators.
* Discrimination/fingerprint indexes for conclusion and trigger structure.
* Separate premise and conclusion indexes, including polarity and argument positions.
* Type/structure requirements and semantic-binding eligibility indexes.
* Definition and theorem relationship adjacency lists for bounded expansion.
* Optional learned premise vectors/rankers, versioned independently of logical data.

Generic symbols such as equality, addition, or order are poor standalone keys.
Prefer rare typed symbols, operator combinations, subterm paths, shared-variable
patterns, and role-specific features. In arithmetic-only goals, structural features
must carry the load; rare-symbol selection alone is inadequate. Namespace proximity
can be a soft feature but cannot be a hard exclusion of useful cross-domain facts.

Selectivity is not guaranteed: a common-symbol posting or matching output can be
linear in library size. Bound posting visits, keep resumable cursors, and widen in
deterministic rounds. Budget exhaustion is visible; never advertise a universal
`O(log N)` lookup bound. Optional missed candidates affect proving power, not validity.

## 3. Retrieve around the current problem, then expand carefully

Construct the initial query from typed subterms, assertion polarities, hypotheses,
and the negated goal when one exists. For general `check-sat`, use assertion
neighborhoods rather than inventing a distinguished theorem goal. Later queries
can use unresolved atoms, theory conflicts, bounds, and candidate-model disagreement.
Model values and current assignments are search hints, not unconditional premises.

Candidate selection combines:

1. Exact applicability and semantic-encoding checks.
2. Structural conclusion/trigger matches and rare-feature retrieval.
3. Bounded symbol-relevance expansion, following SInE/MePo-style ideas.
4. Optional learned ranking using both the target and current hypotheses.
5. Diversity reservations across conclusion families, types, and bridge paths.

Use both forward and backward relevance. A theorem whose conclusion would help may
need premises absent from the initial query. Put those premises into a bounded
obligation frontier and retrieve producers for them. Conversely, available premises
identify forward consequences. This permits short theorem chains without flooding
the solver with every theorem sharing `+`.

For example, if the query contains `u = v` and `Q(f(u))`, while the library provides
`Q(f(x)) -> R(x)` and `R(x) -> P(x)`, a backward request for `P(v)` discovers `R(v)`
and then `Q(f(v))`. Equality-aware matching connects the latter to the existing
fact, with equality explanations. Looking only for the literal shape `P(v)` among
ground terms would miss this chain.

Maintain three different graphs. A **proof-dependency graph** tells the checker what
must be verified. A **definition graph** tells translation which meanings are needed.
A **premise/conclusion graph** suggests useful inference chains. Loading a theorem's
proof closure does not mean asserting every theorem in that closure into CDCL(T).
Conversely, a useful bridge theorem need not occur in another theorem's source proof.

Use deterministic symbolic retrieval as the measured baseline. Optional learned
retrieval ranks templates for candidate recall; the application policy below ranks
concrete actions for their effect on remaining work. These are different learning
tasks and need separate ablations. Both stay outside the trusted base. Use pinned
models and deterministic Rust inference, with stable tie breaks and accounted work.
Test whether retaining source names actually helps ordinary SMT inputs, whose user
symbols often have no meaningful names.

## 4. Activate a theorem as a query plan

Retrieval estimates relevance. Activation additionally estimates whether an instance
can be obtained cheaply and usefully in the current state. Evaluate binding coverage,
posting cardinalities, unresolved hypotheses, expected join sizes, term growth,
proof-checking cost, duplication, and whether the consequence addresses an unresolved
constraint. A theorem that is relevant but has millions of substitutions can be a
worse next action than a modest theorem with one decisive instance.

Do not match every active theorem against every term. Compile compatible patterns
into shared discrimination programs and index subscriptions by typed head/shape.
Use relational joins for multi-patterns, keyed by shared variables. Begin with the
most selective bound pattern, then extend consistent partial substitutions. Avoid
enumerating every pair of terms merely because they share a sort.

Maintain distinct indexes for **terms that exist** and **facts currently justified**.
The occurrence of `P(a)` as a subterm does not establish `P(a)`. A pattern may bind
from an existing term while leaving `P(a)` as a clause guard.

New terms, equality-class merges, bound changes, and relevant truth assignments
produce deltas. Process only affected subscriptions and join rows, with an initial
catch-up pass when a plan activates. New matches caused by congruence can occur
without a new term, so merge events and parent-use information are essential.
Backtracking splits equality classes again; merge-derived caches must be trailed
or invalidated at their precise dependency boundary.

Arithmetic atoms need operator-aware patterns and normalized polynomial/bound
features, not just the existing `Apply`-symbol index. Canonicalization used by a
match must either preserve exact structure or supply a checked equality. All DAG,
substitution, compiler, and certificate walks use explicit heap stacks.

An application proceeds as follows:

```text
catalog candidate
  -> checked type/structure specialization
  -> active pattern or goal-directed plan
  -> consistent, fully bound substitution
  -> guarded consequence and equality explanations
  -> bounded action preview and learned application selection
  -> independently checked instance
  -> canonical clause deduplication
  -> scoped SAT/theory admission
```

For `H1 ∧ H2 -> C`, the normal product is `¬H1 ∨ ¬H2 ∨ C`. Dropping the guards
requires proofs of the hypotheses, including any branch or assertion dependencies.
A multi-pattern must agree on every shared variable and bind every variable needed
by the instance. Missing variables are not assigned guessed defaults. Unresolved
goal-directed premises remain obligations; they never become assumptions asserted
as true. Witness creation requires a checked conservative extension and separate
symbol lifetime tracking, rather than the universal-instance path.

## 5. Learn which application makes the problem easier

The motivating analogy is mathematical problem solving: recognize a structure,
recall a potentially useful theorem, and choose an application that simplifies the
remaining task in light of the hypotheses. Here **simplification means lower
remaining reasoning cost**, not fewer expression nodes or a more similar theorem
statement. A transformation may temporarily expand the expression or introduce an
intermediate obligation while making the final proof much easier.

For example, over the reals:

```text
Hypotheses: x^2 = y^2, x + y != 0
Goal:       x = y

Difference of squares: (x - y) * (x + y) = 0
No zero divisors and the second hypothesis: x - y = 0
Linear arithmetic: x = y
```

The value of factoring depends on the available nonzero hypothesis. This example
illustrates contextual application selection; it does not claim a performance gap
in Nixie's existing nonlinear procedures. Every identity and conditional inference
still needs its ordinary exact justification.

### Action and state representation

An action is a theorem identity, exact type/structure specialization, term
substitution, permitted direction, application location, and execution mode
(rewrite, guarded consequence, or goal decomposition). Two applications of the
same theorem are different actions. The action set also contains `ContinueBase`,
which gives the existing SMT engine a fixed deterministic work slice. Include
bounded retrieval-widening or deferred-application actions only with explicit costs.

The policy scores a variable-size set of actions, not a fixed 200,000-way theorem
classifier. Shared theorem/term representations allow an exported declaration to
be scored without assigning it a newly trained output class. This permits library
growth structurally; generalization to new declarations still requires measurement.

Use a compact encoder over the typed term DAG and its relevant neighborhood, plus
a shared action scorer. Inputs include assertion/goal polarity, justified local
hypotheses, equality and bound information, remaining obligations, recent work,
candidate binding structure, predicted join cost, and generated-term growth. A
bounded preview describes the replacement expression or guarded consequence and
**all** side conditions introduced by the action. Encode exact constants in a way
that retains relevant arithmetic structure; compressed learned features never
replace the exact constants used by the symbolic checker.

For a plain SMT query there may be no distinguished goal. Score changes to the
active constraint state and its unresolved theory obligations. For library proof
search, include the entire outstanding obligation set, with local neighborhoods
as attention inputs. A small local feature window can miss useful global structure;
evaluate this limitation rather than assuming locality is sufficient.

A plausible first model is a small structural encoder with policy and value heads.
Its capacity, context budget, and inference frequency are experimental choices.
Its job is preference prediction; symbolic components supply exact matching,
instantiation, and proof checking. The 200,000 lemmas remain in the external catalog
and do not have to be memorized in model weights.

### Objective and execution

The intended action value is:

```text
Q(s, a) = cost of executing and checking a
          + expected remaining work from the resulting state

Choose a low-cost action, including ContinueBase.
```

This is a learning objective, not an available oracle. Charge retrieval, candidate
construction, previews, neural inference, speculative search, and final certification
in end-to-end evaluation, even when their already-paid costs are shared across the
current action choices. Reward reaching a certified terminal result; do not reward
stopping at `Unknown` or refusing useful work simply because it is inexpensive.

Apply one or a few checked actions, update the state, and rescore. Compare greedy
selection with a small beam or bounded lookahead so that a useful sequence can
survive an initially unfavorable step. Case splits and theorem applications can
create multiple mandatory child obligations: a value estimate must account for
solving all of them. Alternative derivations are choices, while required subgoals
are cumulative work; do not score only the easiest child. Shared subproofs and
cross-obligation constraints also affect the actual cost.

An action preview is speculative data. A selected rewrite may replace an expression
only with a checked equivalence under explicitly justified conditions. A useful
one-way consequence normally adds a guarded clause while retaining the original
constraints. Goal decomposition requires a checked proof-composition rule, and
transformations used for SMT `sat` require the appropriate model reconstruction.
The model cannot drop a constraint or a difficult subgoal to improve its score.
Speculative alternatives use isolated reversible state and the existing scope rules.

### Training data and credit assignment

Existing proof traces can bootstrap legal application prediction and useful
structural representations. However, human proof length and proof-assistant tactic
frequency are not labels for Nixie runtime. Fine-tuning must measure Nixie's own
reasoning costs and obligations.

Capture reproducible solver states. From the same state and matched solver seed,
try different checked actions, including `ContinueBase`, then execute a specified
continuation policy under a fixed work budget. Record action/preparation costs,
all residual obligations, result certification, and total subsequent work. Keep
the continuation policy fixed within comparisons and version it when changed.
Sampling the policy's own preferred actions alone biases the data; reserve bounded
exploration and include plausible, expensive, and unhelpful legal alternatives.

Use pairwise action preferences and a remaining-work value target as initial
learning tasks. Longer rollouts can train sequence-level credit assignment. A run
that exhausts its budget supplies a censored cost observation, not its true solve
cost; compare solved fraction at fixed limits and use explicit timeout/censoring
handling. A reduction in term count, an immediate propagation, or appearance in a
final proof can be an auxiliary signal, but cannot substitute for the total-work
objective. Preserve the seed controls and leakage exclusions in the evaluation
section for both data generation and held-out assessment.

## 6. Control saturation and feed useful information back

Run the service at deterministic safe points: initial preprocessing, queued
structural changes, and explicit work-budget milestones. Cheap subscriptions may
run frequently; global retrieval and reranking must be much less frequent. Do not
run a library query per Boolean propagation or use elapsed time to decide when to
activate a theorem.

Use fixed, measured budget slices for retrieval, matching, checking, and admission,
while reserving progress for the ordinary solver. An illustrative widening schedule
is 64 -> 128 -> 256 active plans, with deterministic retirement and replacement.
These numbers are experimental configurations, not promised optimal settings.
Retiring a plan stops future matching; admitted justified clauses and referenced
proof objects follow the solver's ordinary clause/proof lifetime rules.

Enforce caps on join tuples, attempts per plan, generated-term depth and bytes,
instances per epoch, total retained clauses, and obligation-frontier growth. Detect
repeated instances and expansion cycles. Preserve resumable state where practical.
Prevent one frequently firing theorem from monopolizing the budget; reserve a small
deterministic exploration slice for underused candidates and bridge obligations.

Collect feedback at different strengths: matches found, clauses admitted, unit
propagations caused, participation in conflicts, and use in a final checked proof.
Counting emitted clauses alone rewards spam. Final proof use is stronger evidence
than firing frequency but is still biased by the search policy and is not causal
proof of a speedup. Keep per-query updates reproducible; train cross-query ranking
offline from versioned traces rather than mutating a global policy between runs.

Deduplicate instances by exact schema identity, specialization, substitution, and
semantic environment. Deduplicate clauses by checked canonical content with full
equality on hash collisions. Equality-class representatives can accelerate lookup,
but are neither durable cross-scope identities nor cross-session cache keys.

## 7. Certificates and the actual trust boundary

The checker accepts an instance only after establishing the source theorem, the
semantic translation, the specialization, the substitution, and every discharged
side condition. Keep certificate verification independent of the matcher. A compiled
plan, source theorem name, signed pack, or content hash is not a mathematical proof.

There are two certification paths with different scope:

* **Native certificate path:** the translated lemma has a proof in Nixie's explicit
  logical/theory certificate language, using previously checked declarations. The
  Rust checker verifies that derivation. The Lean source is provenance and an
  additional cross-check, not a new trusted axiom. This is the first delivery path.
* **General library path:** accepting arbitrary exported Lean proofs requires a
  compatible independent proof checker, including the supported dependent-type,
  inductive/recursor, universe, and quotient rules, plus semantic translation proofs.
  A Rust implementation is a substantial separate component. Unsupported proof
  rules keep a declaration ineligible for inference. An external Lean reconstruction
  route can certify a Lean-facing goal, but is not standalone pure-Rust verification.

An offline Lean-checked pack could instead be treated as trusted compiled content,
but that adds its production pipeline to the trusted base. It is not equivalent to
independent certificate checking and is not the selected default design. Do not
claim that arbitrary mathlib proof checking reduces to a small arithmetic checker.

For each semantic binding, establish the required model relationship. Refutation
soundness needs every source model to satisfy the translated constraints in an
appropriate target interpretation. Returning a source-level countermodel additionally
needs a validated reverse model construction; mere equisatisfiability of a subset
of selected instances is insufficient. In native SMT mode, establish validity in
the actual SMT theory, not merely in Lean's chosen interpretation of a symbol.

Examples of binding obligations include natural-number domain restrictions and
truncated subtraction, integer division conventions, division at zero, finite-index
types, mathematical versus IEEE floating-point arithmetic, and structure laws.
Explicitly track source axioms; reject `sorryAx`, arbitrary user axioms presented as
library truths, and unsupported computational-oracle assumptions. Legitimate
background logical axioms require a documented compatibility policy.

Check shared proof dependencies once per immutable verified environment and keep
compact theorem handles for applications. Persisted caches require validation
against the complete environment and checker identity; a hash identifies data but
does not establish that it was verified. First-use dependency-checking cost belongs
in cold-query accounting. Large closures can exhaust the checker budget and defer
activation even when a statement is small.

The final refutation must connect admitted library instances, their certificates,
their Boolean encodings, and the original assertions. Library-derived clauses
require checks even when an existing solver configuration would bypass optional
result certification. If a consumed certificate is unsupported or invalid, no
result may rely on it. Failure before admission can leave ordinary SMT solving
running; unresolved source semantics or an uncertified result yields `Unknown`.

## 8. Scope, cancellation, and cache lifetimes

| State | Required lifetime |
| --- | --- |
| Catalog, verified closed theorem | Immutable environment/version |
| Semantic bindings and local theorem declarations | Frontend session and assertion scope |
| Active plans, ground-term rows, obligation frontier | Solver-owned, with scoped entries |
| Truth/bound/equality-dependent matches | Relevant SAT/theory decision scopes |
| Emitted clauses and their dedup keys | Retract in lockstep with clause scope |
| Explanation/proof objects | Until all dependent clauses/proofs release them |
| Model, unsat core, exported result | Invalidated by assert/push/pop/reset |

Use undo journals and generation-stamped identities, not wholesale memo clears or
retention based solely on reusable numeric scope depth. Session objects must outlive
temporary `TheoryManager` instances and MBQI rounds. Activation includes catch-up
for existing terms; reactivation after pop must not be blocked by a stale dedup key.
Unconditional theorem knowledge may survive a pop, but handles into popped local
declarations or terms may not. Logical cache contents cannot depend on other users'
or other sessions' workloads. Cancellation leaves only fully checked, fully admitted
transactions; partial compilation or checking cannot publish a valid handle.

## 9. Fit into the current codebase

These are integration surfaces, not claims that the complete service already exists:

| Existing surface | Proposed relationship |
| --- | --- |
| `nixie-core/src/ematching/index.rs` | Reuse concepts; add typed builtin/shape postings and stable pack identities |
| `nixie-core/src/ematching/` | Audit reusable matcher primitives before selecting one authoritative implementation |
| `nixie-theories/src/quantifier_code_tree.rs` | Candidate compiler baseline; replace whole-bucket rescans with delta work where used |
| `nixie-solver/src/mbqi/patterns.rs` | Reconcile multi-pattern binding semantics and cache invalidation with the new engine |
| `nixie-solver/src/mbqi/integration/` | Coordinate optional library instances with mandatory quantified obligations |
| `nixie-solver/src/solver/trail.rs` | Extend explicit scope journal and restoration invariants |
| `nixie-solver/src/solver/theory_manager/derived_reasons.rs` | Solver-owned explanation lifetime and certificate-log precedent |
| `nixie-solver/src/solver/certification.rs` | Extend typed library-instance certificates and the independent exit gate |
| `nixie-proof/src/lean.rs`, `lean_enhanced.rs` | Proof-export consumers; not a trusted import checker |

Inspection found separate matching implementations, including symbol-indexed nested
loops in `quantifier_code_tree::find_matches` and structural matching limitations
documented in `mbqi::patterns`. The new service must not presume they already supply
one fully integrated, incremental equality-aware matcher. Trace active call paths
and test their contracts before reuse. This design inspection is not a full
soundness audit and makes no claim that any observed component is bug-free.

The Lean exporters contain `axiom`/`sorry` generation paths. Their existence does
not satisfy the certificate requirements above. The current certification code
has EUF/LIA checking surfaces; support for those does not automatically cover general
library facts.

Proposed module boundaries: a new `nixie-lemmas` crate for immutable packs, template
IR, retrieval, and plan compilation; session orchestration under `nixie-solver`;
matching primitives shared through the selected core/theory implementation; typed
certificate rules under `nixie-proof`. Keep dependency direction acyclic and do not
let the catalog depend on solver internals. Keep the application policy behind a
replaceable scorer interface, with symbolic and learned implementations sharing the
same candidate actions and executor. Training consumes versioned traces outside
the runtime. No solver runtime dependency on Lean, C/C++, or FFI.

## 10. Evaluation that can reject the architecture

First distinguish three questions: can the needed facts be represented and checked,
can retrieval find them, and can execution exploit them profitably? Test each in
isolation and end to end. A library-scale test must include a real exported catalog;
duplicating a hundred theorems 2,000 times does not model its symbol distribution,
polymorphism, dependency structure, or join behavior.

Use separate corpora for existing SMT workloads, translated mathlib goals, adversarial
common-symbol queries, and incremental push/pop sequences. Establish oracle-premise
experiments using known valid proof dependencies to diagnose retrieval versus search
limits; these are diagnostic experiments, not deployable performance or strict
upper bounds. Sufficient premises do not specify their best application sequence.

The central pilot uses a bounded, representative executable lemma family while
retrieving against the full real catalog. Compare the base solver, relevance-only
selection, a symbolic application-cost policy, and the learned application policy.
Hold candidate generation and execution machinery equal when isolating the policy.
Evaluate learned retrieval separately; an application policy cannot rescue an
action that retrieval or bounded matching never produces.

Ablate current-hypothesis inputs, consequence previews, the value head, and
lookahead. Distinguish gains from recognizing useful actions from gains caused by
extra search compute: every lookahead treatment needs a control with the same
branch count and work budget. Replay the same model architecture with permuted
action scores as a matched-null policy; ranking-only, structure/cost features, and
full state-conditioned scoring should be separately measurable steps.

Measure:

* Export/encoding/certificate coverage and rejection reasons.
* Required-premise recall, useful-chain coverage, and executable-instance recall.
* Application-ranking quality on measured alternatives, value calibration under
  censoring, and the frequency and utility of choosing `ContinueBase`.
* Posting visits, type-specialization work, join tuples, matcher instructions,
  new term nodes/bytes, clause count, and proof-checking work.
* Total deterministic work through the final certificate, solved fraction at fixed
  work limits, memory, and proof size. Charge bignum work by operand size and any
  learned inference by its actual operations. Report cold and warm behavior separately.

Compare no-library solving, symbolic selection, and additional ranking/graph/activation
policies. Every heuristic comparison uses at least 10 seeds per cell, a baseline
distribution, and a matched null following `docs/BENCHMARKING.md`. A ranking null
permutes priorities among logically admissible candidates while preserving candidate
count, score distribution, scheduling, code path, and choice count. Stratify by
binding coverage, term growth, clause size, and checking cost where those determine
the physical perturbation. Never scramble formula semantics or inject false lemmas.
If actual matching/admission counts or cost diverge, the control is not fully matched;
report the imbalance and withhold the corresponding causal claim. Matched admission
opportunities need their own controlled experiment rather than pretending a weak
random-theorem baseline is sufficient. Define benefit using higher-is-better work
reduction, so `benefit(treatment) / benefit(null) > 1` has an unambiguous meaning.

Freeze library, policy, encoding, and checker versions. Exclude the target theorem,
its aliases, and declarations that depend on it from theorem-proving benchmarks.
Split training/evaluation by dependency-aware chronology and related theorem families
to limit leakage. Recheck hindsight-selected settings on fresh seeds. Record and
reuse each measured cell through the repository benchmark store.

Required correctness regressions include incompatible type/structure bindings,
division-zero differences, absent guards, conflicting multi-pattern substitutions,
partial variable bindings, merge-created matches, split/pop invalidation, reassertion
after pop, witness freshness, proof corruption, unsupported axioms, deep DAGs, exact
wide arithmetic, and budgets exhausted at every pipeline boundary. Small finite
domains permit exhaustive cross-checks of the generic matcher and guarded instances.
Run the repository's complete implementation gates, including Z3 parity with the
actual installed version, before shipping solver changes. Also replay admitted
theorems/instances in Lean where applicable; Z3 parity alone cannot validate a new
source-language translation.

## 11. Delivery sequence and stop conditions

1. **Catalog and semantic inventory.** Export and index the whole pinned library,
   retaining unsupported records. Measure sizes, posting skew, dependency closures,
   and executable coverage. Deliver the format, compiler diagnostics, and reproducible
   corpus manifest. No inference is enabled yet.
2. **Retrieval harness.** Implement typed structural selection, bounded relevance
   expansion, and premise/conclusion queries over the real catalog. Evaluate recall
   and cost against known proofs, including common-symbol and renamed-symbol cases.
3. **Checked execution slice.** Implement generic specialization, certificate-backed
   activation, delta joins, and guarded admission for a supported family. Exercise
   the entire catalog for retrieval even while certificate coverage grows. This is
   validation of shared machinery, not a plan to hand-code a small theorem list.
4. **Application-policy pilot.** Capture reproducible states and concrete actions,
   including consequence previews and `ContinueBase`. Train a small shared action
   scorer/value model on a bounded family, using full-catalog retrieval. Test
   relevance-only, symbolic-cost, learned, and matched-null policies before expanding
   coverage. Charge preparation, model inference, and all residual obligations.
5. **Incremental solver integration.** Connect solver-owned session state, events,
   rollback, policy scheduling, and final proofs. Verify correctness and compare
   end-to-end work with matched controls. An independently verified consequence is
   mandatory at admission.
6. **Broader proof/encoding coverage.** Extend generic translation and checking
   capabilities to unlock more generated declarations. Decide from coverage data
   whether a general Lean-compatible Rust checker is justified; do not hide that
   investment inside a claim of mechanical lemma porting.
7. **Selection and search refinement.** Extend learned retrieval, context encoding,
   and bounded multi-step search where diagnostics identify lost opportunities.
   Require matched-null wins after charging all inference and checking costs.

Record a negative result for the tested configuration if the policy cannot beat its
matched control after all costs, or useful coverage requires an unjustified
proof-kernel investment. Failure with known sufficient premises alone does not
refute application learning: test known useful application sequences where available
to separate execution benefit from order/substitution mistakes. If supplied useful
sequences help but the policy does not find them, investigate action recall and
selection. If even those sequences do not repay their execution/checking cost,
reconsider that workload. If retrieval succeeds but joins explode, focus on binding
and activation. These are distinct findings, not claims about all possible models.

## References and what is borrowed

The architecture above is a proposal for Nixie; the following sources support its
constituent techniques, not a performance prediction for this repository.

* [SInE: Axiom Selection for Large Theory Reasoning, author presentation](https://www.cs.man.ac.uk/~hoderk/sine_pres.pdf):
  symbol-driven selection from large theories.
* [MaSh: Machine Learning for Sledgehammer](https://www.cs.vu.nl/~jbe248/mash.pdf):
  learned premise selection and combination with symbolic relevance filtering.
* [Premise Selection for a Lean Hammer](https://arxiv.org/abs/2506.07477):
  context-aware learned premise selection integrated with translation and proof
  reconstruction. Its reported improvements are not Nixie measurements.
* [TacticZero: Learning to Prove Theorems from Scratch with Deep Reinforcement Learning](https://arxiv.org/abs/2102.09756):
  precedent for learning proof actions, subgoal selection, and search/backtracking
  decisions in HOL4. It motivates application-policy experiments but does not
  establish their performance or required model size in SMT.
* [lean-auto](https://github.com/leanprover-community/lean-auto): dependent-type
  monomorphization, explicit translation stages, and reconstruction architecture.
* [Lean elaboration and compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
  and [axioms](https://lean-lang.org/doc/reference/latest/Axioms/): kernel checking
  and explicit axiom dependencies.
* Z3 read-only source: `../temp/z3/src/smt/mam.cpp` (relative to repository root),
  inspected for compiled matching, filters, equality-class traversal, and generation
  tracking. Public source: [mam.cpp](https://github.com/Z3Prover/z3/blob/master/src/smt/mam.cpp).
* cvc5 read-only source: `../temp/cvc5/src/theory/quantifiers/ematching/trigger.cpp`
  and `quant_relevance.cpp`, inspected for trigger specialization, ground-term
  preprocessing, and symbol relevance. Public source:
  [trigger.cpp](https://github.com/cvc5/cvc5/blob/main/src/theory/quantifiers/ematching/trigger.cpp).

Document validation: repository integration surfaces and read-only reference code
inspected; local Markdown file links and whitespace checked before landing. No
solver code changed and no solver benchmarks or implementation tests were run.
