# Genuinely Novel Research Agenda for OxiZ

Date: 2026-08-22
Status: novelty hypotheses after a targeted collision screen, not publication claims

This document contains the ideas from the six supplied reports that survive a strict
split from established work. “Novel” here means that the specific mechanism and
integration point were not found in the cited baseline literature or reference-solver
descriptions reviewed for the synthesis. It does **not** establish worldwide academic
or patent novelty; each project needs a fresh systematic search before publication.

Established algorithms that should be implemented first are in
[`2026-08-established-research-candidates.md`](2026-08-established-research-candidates.md).

## Ranking

| Rank | Hypothesis | Novel delta | OxiZ fit | Risk |
|---:|---|---|---|---|
| 1 | Conflict-slice selective lowering for BV/FP | Materialize only the exact bit dependency cone implicated by a spurious model/conflict | High | High |
| 2 | Pivot-delta care frontier | Drive equality-candidate refresh from exact simplex row/column mutations, with mandatory full final reconciliation | High | Medium |
| 3 | Theory-lemma vivification | Shorten over-specific theory lemmas through SAT probing plus exact owning-theory re-certification | High | High |
| 4 | Downstream-aware theory explanations | Choose among independently valid explanations by deterministic CDCL utility and re-derivation cost | High | Medium-high |
| 5 | Activation-supported simplification certificates | Reuse checked transformations across non-linear incremental context histories by minimal activation support | High | High |
| 6 | Learned exact-cut aggregation | Use a frozen scorer to select exact tableau-row combinations, while exact arithmetic proves every cut | Medium-high | High |
| 7 | Propagation-debt maintenance | Schedule SAT maintenance by sampled deterministic future-BCP debt rather than a fixed conflict cadence | Medium | Medium |
| 8 | Reversible representation morphing | Promote/demote bounded regions among CNF, gates, and XOR with proof-carrying equivalence | Medium | Very high |

The first five are plausible OxiZ research projects after their established prerequisites
land. N6 begins with an oracle study because OxiZ has not yet demonstrated useful cut
aggregation headroom. The last two are measurement-first projects: do not build their
full systems until an oracle/probe study demonstrates headroom beyond a matched null.

## N1. Conflict-slice selective lowering for BV/FP

### Hypothesis

For a wide expensive operation, most candidate failures depend on a small subset of
output bits and their carry/borrow/dataflow cone. Refining exactly that cone will avoid
more Boolean materialization than operator-wide lemma tiers without sacrificing the
complete bit-blast fallback.

### Mechanism

Start with the established CEGAR abstraction from
[Scalable Bit-Blasting with Abstractions](https://doi.org/10.1007/978-3-031-65627-9_9).
For an abstract term `y = f(xs)` whose candidate value is inconsistent:

1. compute the exact discrepancy bit set `B` between `y` and `f(xs)`;
2. walk backward iteratively through the word-level DAG and Boolean reason graph;
3. construct the minimal supported dependency cone `D(B)` for the selected operator;
4. emit the exact projection circuit/clauses for `B` plus required internal
   carry/borrow nodes;
5. remember the slice by stable term identity and scope; and
6. geometrically widen the slice after repeated failures, ending in full bit-blasting.

Every emitted constraint must be entailed by full BV semantics. A slice is never used
to declare `Sat`; the candidate model still undergoes exact full-term validation.

### Prior art and delta

Published BV abstraction refines with operator lemma schemes, value instantiation, and
eventual full lowering. The supplied Manus report's CSSL proposal contributes the
specific proof/reason-slice signal and partial-circuit granularity. GLM's neural CEGAR
selector attacks the same selection problem but adds an unnecessary learned model
before a deterministic slice baseline exists.

### First experiment

Instrument `bvmul` first on the established abstraction baseline. Log the full circuit
cone and the selected cone without changing solving. If multiplier slices immediately
densify, prototype the mechanism on `bvadd`/`bvsub` as a deliberately separate extension,
not as a claimed part of the CAV'24 operator set. The project proceeds only if the median
selected cone is materially smaller and repeated failures do not immediately densify it.
Then enable exact slice clauses behind a flag and compare against random slices of
identical size and widening schedule.

### Falsification

Reject if full lowering occurs nearly as often as the established abstraction baseline,
if slice bookkeeping adds comparable gates/memory, or if the semantic slice does not
beat its size-matched random control.

## N2. Pivot-delta care frontier for theory combination

### Hypothesis

After an incremental simplex repair, only interface equalities in the dependency
neighbourhood of changed basic/non-basic columns can have changed model status or
entailment status. Maintaining that dirty frontier will remove repeated care-pair scans
from UF+arithmetic combination.

### Mechanism

OxiZ already has model-based reconciliation, care-atom encoding, sparse simplex
columns, and bidirectional equality propagation. Extend the production path with:

- a monotonically deduplicated set of interface terms touched by bound updates,
  entering/leaving columns, and assignment deltas;
- a row/column dependency expansion limited to shared terms;
- care-pair indexes from each shared term to existing equality atoms and live EUF
  disequalities;
- refresh of only the dirty candidates during intermediate theory-propagation rounds;
  and
- a **mandatory uncapped full reconciliation before `Sat`**, and whenever a scope
  operation invalidates the dependency summary.

The dirty frontier is an acceleration hint only. Missing a dirty edge may delay a
propagation; it must never permit a final model to bypass the complete combination
check.

### Prior art and delta

[Model-based theory combination](https://doi.org/10.1016/j.entcs.2008.04.079)
reconciles theory models, and care graphs restrict equality pairs. OxiZ already
implements both ideas. The proposed delta—derived from opus P1—is to key incremental
candidate invalidation to the exact simplex pivot/update trace rather than rescanning
the whole care population after each repair.

### First experiment

Add read-only telemetry: per theory round, record all tested pairs and the subset whose
model/entailed status changed; attribute each change to the last pivot/update support.
No optimization should be implemented until this audit demonstrates high recall from a
small frontier.

### Falsification

Reject if the frontier approaches the full care graph, if status changes routinely
occur outside the tracked dependency closure, or if candidate tests are not a material
part of deterministic QF_UFLIA/QF_UFLRA work.

## N3. Theory-lemma vivification with exact re-certification

### Hypothesis

Theory conflict and propagation clauses can become over-specific as the Boolean search
evolves. A theory-aware vivifier can remove redundant antecedents that pure Boolean
probing cannot see, producing cheaper reusable lemmas without changing the theory's
trusted consequence relation.

### Mechanism

Begin with theory lemmas carrying an owning theory, assertion-scope support, and exact
derivation provenance. At a safe vivification point:

1. select only inactive, non-reason theory lemmas whose assertion supports are live;
2. falsify a bounded prefix using the SAT propagator;
3. permit the owning theory to propagate under that prefix, requiring an exact
   explanation for every theory propagation;
4. construct a candidate shortened lemma from the resulting contradiction;
5. re-certify the candidate as entailed by the active theory/assertion base;
6. install the certified replacement before retiring the old clause; and
7. retain the old lemma whenever proof production cannot justify the replacement.

No assumed literal, popped assertion, or provisional model fact may enter the permanent
support. Under proof modes lacking the needed theory-proof chain, the pass stays in
telemetry-only mode.

### Prior art and delta

[Revisiting Clause Vivification](https://cca.informatik.uni-freiburg.de/papers/PollittFleuryBiereSakallahHeuleChenFisseha-POS25.pdf)
is a pure-SAT technique. Theory propagation and theory-lemma minimization are established,
but the additional local study's proposal to run a scheduled vivification pass over
already-learned theory lemmas, with later owning-theory re-certification, was not found in
the targeted collision screen. This is medium-confidence novelty only; a systematic SMT
lemma-minimization and proof-production search is required before publication.

### First experiment

Run in shadow mode on EUF and linear-arithmetic lemmas. Record how often a strictly
shorter lemma can be certified, the exact theory work required, and whether the removed
literals later matter. Do not alter search until shrinkable lemmas are common enough to
repay the checks.

The additional study's proposed random-redundant-clause control is not a matched null:
it changes clause population and semantic strength differently. A behavioral study must
use the same candidate lemmas, prefixes, theory calls, and number of committed removals.
Where multiple equal-cardinality certified shortenings exist, compare the semantic
selector with a permuted valid-choice selector. Cases without an equivalent valid control
cannot support a treatment-versus-null claim and must be reported separately.

### Falsification

Reject if certified shortening is rare, theory re-checking dominates the saved work,
proof obligations cannot be emitted, or no defensible matched-control population exists.
The one-instance observation that learned clauses account for 31.6% of OxiZ reasons is
motivation for measurement, not evidence that theory vivification will help.

## N4. Downstream-aware theory explanations and lemma economics

### Hypothesis

When a theory solver can produce multiple independently valid explanations, the best
one is not always the locally smallest. A deterministic secondary choice based on
prospective LBD, decision-level spread, overlap with retained lemmas, and exact
re-derivation cost can improve CDCL reuse and database economics.

### Mechanism

Separate logical validity from selection:

1. generate a small bounded set of alternative exact explanations—for example,
   alternative valid Farkas supports or redundant-bound proofs;
2. validate each candidate through the existing exact theory checker/proof path;
3. minimize each candidate using only sound implication checks;
4. score the surviving candidates with deterministic SAT-layer features;
5. learn the selected clause with provenance (`Boolean`, `EUF`, `LRA`, `LIA`, mixed)
   and a deterministic derivation-work estimate; and
6. use provenance/re-derivation work in clause retention only after explanation choice
   itself is evaluated.

The original explanation remains the fallback. Activity or model features may select
among proofs; they may never validate one.

### Prior art and delta

Farkas explanations, conflict minimization, LBD, and clause tiers are established.
Pure-SAT learned deletion metrics are also established. Opus P2/P3 and GLM proposal 2
identify the gap: selecting among theory-valid explanations and managing their lifetime
for downstream CDCL cost is not the same as minimizing one fixed explanation or applying
a theory-blind deletion model.

### First experiment

Before changing behavior, quantify multiplicity: on arithmetic conflicts, attempt to
enumerate up to four valid supports and record whether their size, decision-level set,
and overlap differ. If alternative explanations rarely exist, stop. If they do, compare
a deterministic low-prospective-LBD selector to a permutation of the same candidate
scores. Both arms must generate the same number of candidates and validations.

### Falsification

Reject if proof enumeration dominates theory time, candidate diversity is low, or the
semantic selector does not beat its matched permutation null in theory-heavy UNSAT
families. Lower observed LBD alone is not success; require reduced complete-work cost.

## N5. Activation-supported simplification certificates

### Hypothesis

Incremental SMT repeatedly revisits equivalent assertion contexts. Caching a
transformation with a checkable local proof and its minimal activation support can
avoid broad replay while remaining scope-correct across sibling push/pop branches.

### Mechanism

Represent a reusable transformation as:

```text
certificate id
source term/formula ids
transformed result
equivalence or one-way implication proof
minimal activation/assertion support
parent certificate ids
model-reconstruction action
scope/version fingerprint
```

Maintain a version DAG. A certificate is active only if all support literals and parent
certificates are active. On a context change, invalidate the support-intersecting
sub-DAG; revalidate reusable boundary nodes with the local checker rather than replaying
the entire preprocessing sequence. Evict by deterministic reuse-work-saved per byte.

### Prior art and delta

[On Incremental Pre-processing for SMT](https://doi.org/10.1007/978-3-031-38499-8_3)
provides the retention/rewrite/replay calculus. Proof-producing preprocessors and lemma
caches also exist. The novel delta, most clearly formulated as Manus ASSC and overlapping
opus P10, is a dependency-minimal proof-carrying object reused across a **non-linear
context history**, with selective sub-DAG revalidation and model reconstruction.

### First experiment

Implement certificates only for one expensive equivalence-preserving BV or arithmetic
rewrite. Replay recorded BMC/symbolic-execution context trees. Compare against an
identical memo keyed by the entire assertion context; this isolates support minimization
from ordinary caching.

### Falsification

Reject if minimal supports are usually the whole context, checking costs approach
recomputation, or metadata exceeds the saved work. Any stale reuse is a soundness bug,
not an experimental loss.

## N6. Learned exact-cut aggregation for LIA

### Hypothesis

For an integer-infeasible relaxation, combining a small number of exact tableau rows can
yield a stronger reusable cut than selecting a single conventional row. A frozen cheap
scorer may find useful combinations without placing learned arithmetic inside the trust
boundary.

### Mechanism

At a cut checkpoint, enumerate a tightly bounded set of exactly eligible rows and pairs.
A deterministic offline-trained model ranks them from structural features such as
fractionality, coefficient sparsity, variable overlap, bound distance, and recent exact
cut use. The arithmetic engine then constructs the Gomory/Chvatal-style aggregate using
exact rationals and independently validates its entailment and proof certificate. An
unproved candidate is discarded; the baseline cut path remains complete.

The model may prioritize candidates only. It must not use wall time, floating-point
feasibility, or an unverified score to admit a cut. Weights are frozen in released builds
and model loading is deterministic.

### Prior art and delta

[Learn2Aggregate](https://doi.org/10.1609/aaai.v39i25.34900) learns cut-row aggregation
for mixed-integer programming. Exact SMT cutting planes, branching, and proof-producing
arithmetic are established. The proposed delta is transferring bounded learned row
combination to an incremental CDCL(T) engine while treating exact entailment/proof as the
sole admission criterion. The targeted screen found no matching SMT implementation, but
this cross-domain novelty claim needs a dedicated MIP/SMT prior-art search.

### First experiment

Before training, instrument the existing LIA path and compute an offline oracle over
bounded row pairs: how often does an exact aggregate dominate the chosen single-row cut,
and does that dominance reduce deterministic downstream work on replay? Stop if the
oracle has little headroom. If it does, compare a frozen scorer against permuted weights
with identical enumeration, exact construction, validation budget, and cut count.

### Falsification

Reject if useful aggregates are rare, exact aggregation causes prohibitive coefficient
growth, the oracle fails on fresh families, or the learned selector does not beat its
matched permutation null. A stronger relaxation violation by itself is not success;
require lower complete solver work without proof or model regressions.

## N7. Propagation-debt maintenance

### Hypothesis

SAT maintenance should run when a deterministic lower-bound estimate of future watch
traffic avoided exceeds the measured transformation work, rather than at a fixed
conflict count.

### Mechanism

At sampled watch events, collect deterministic counts such as blocker hits, scan length,
reason reuse, clause touch age, and repropagation after restart. At safe checkpoints,
probe a fixed-size candidate bucket and estimate future BCP debt until the next database
epoch. Run vivification/subsumption/reduction on a bucket only when a conservative
event-count ROI is positive.

No live cycle counter, cache-miss counter, CPU time, or wall time may affect the policy.
Hardware measurements may calibrate constant weights offline; the online policy uses
only deterministic logical event counts.

### Prior art and delta

Tick-budgeted inprocessing, clause activity, and scheduled vivification are established.
The Manus PDM proposal's delta is an explicit future-propagation-debt objective measured
at bucket granularity. This is more specific than GPT/GLM's generic learned inprocessing
controllers and does not require ML.

### First experiment

Instrumentation only: determine whether sampled bucket features predict subsequent
watch scans before the next epoch on a held-out run. Then compare the debt policy with
a matched policy whose bucket scores are permuted while preserving action count, target
sizes, and trigger points.

### Falsification

Reject if prediction does not transfer to fresh seeds, if instrumentation costs more
than one percent of deterministic work, or if treatment/null is not better than one.
This bar is intentionally severe because recent OxiZ inprocessing policies have repeatedly
failed matched-null evaluation.

## N8. Reversible representation morphing

### Hypothesis

A solver can detect that a bounded clause region is repeatedly reconstructing parity or
gate reasoning, promote that region to a native representation, and later demote it
without losing proof provenance or learned consequences.

### Narrow version

Restrict the first system to `CNF <-> AND/XOR gate objects`:

- gate/XOR detection proposes a region;
- an exact equivalence checker validates the promotion;
- the native object propagates alongside CNF with explicit reason clauses;
- learned consequences are valid in the original vocabulary;
- demotion restores/retains an equivalent clause encoding; and
- every transition carries proof and model-reconstruction provenance.

Promotion is based on deterministic counts of repeated clause work, not a neural score.

### Prior art and delta

SBVA, clausal congruence, XOR extraction, CDCL(XOR), AIG rewriting, and BV abstraction
are established. GPT's “adaptive representation morphing” is novel only in the online,
reversible, telemetry-driven manager spanning representations. That is a large systems
hypothesis, not a new proof system.

### First experiment

An oracle study should replay traces and ask whether knowing the best fixed
representation per region would reduce complete work after paying translation cost. Do
not build reversible infrastructure unless this oracle clears a substantial margin over
preprocessing-only extraction.

### Falsification

Reject if regions switch often, proof/model mappings dominate memory, or fixed
preprocessing captures nearly all oracle value.

## Ideas that do not qualify for this agenda

| Supplied idea | Disposition |
|---|---|
| SOI, SBVA, MBTC/care graphs, BV abstraction, split Gröbner bases, local-search phases | Established; moved to the implementation document |
| Vivification 4.0 | Established for SAT clauses; only its N3 extension to re-certified theory lemmas remains a novelty hypothesis |
| Relevant-domain MBQI | Established prioritization; moved to the implementation document. Model-disequilibrium ranking is an unvalidated ordering heuristic, not yet a standalone research direction |
| Theory-variable freeze set | Established correctness prerequisite for safe preprocessing, folded into the incremental-preprocessing implementation project |
| Offline configuration/portfolio selection | Established SATzilla/MachSMT pattern; useful engineering, not novel research |
| Profile-adaptive incremental retention | Too broad by itself; the certificate/support mechanism in N5 is the research contribution |
| Theory-aware clause tags alone | A low-cost experiment, but provenance metadata by itself is not a novel algorithm; folded into N4 |
| Neural CEGAR abstraction masks | Possible future selector, but it must beat N1's deterministic semantic slice and a matched null |
| BV local-search/disagreement refinement order | A competing selector after the established BV CEGAR baseline, not an independent flagship. It must beat N1 and a random/permuted priority control under the same refinement budget |
| Sequential heterogeneous-slice portfolio with lemma carryover | Configuration switching and portfolio state migration have substantial prior art; retaining sound same-instance theory lemmas is ordinary lemma persistence, while transporting theory hints is underspecified. Treat as engineering until a narrower delta is established |
| Proof-graph distillation | Interesting supervision source, but collision risk with proof-based clause utility and learned deletion is high; needs a dedicated review |
| GPU shadow-database inprocessing | The concurrency arrangement may be new, but GPU inprocessing exists and OxiZ has not shown a GPU-sized kernel bottleneck |
| Hazard-rate portfolios, receiver-specific routing, proof-overlap partitioning | Plausible distributed research; OxiZ has no distributed substrate, so they are not current OxiZ projects |
| Online code evolution/hot-swapping | Rejected: nondeterministic, operationally unsafe, difficult to certify, and incompatible with reproducible solver behavior |
| Online differentiable CDCL/theory embeddings | Rejected for now: hot-loop overhead, stale asynchronous state, weak UNSAT value, and no OxiZ soundness story |
| “Causal” implication-graph rewiring | Rejected: the reports provide no identifiable causal estimand, valid intervention design, or proof-system semantics |
| Float simplex with conflict-only exact checking | Known mixed-precision idea, not clearly novel; correctness cost is too high before SOI is measured |

## Cross-cutting research protocol

All eight proposals are search/performance research, so the local methodology overrides
the reports' generic competition protocols:

- Use deterministic ticks/instructions/events as the primary metric. Wall time is a
  secondary sanity check and never a policy input.
- Compare any semantic selector against a matched null with identical work, action
  count, timing, and perturbation magnitude.
- Use common-random-number pairing and at least ten seeds per cell where the search is
  stochastic.
- Replay hindsight-selected policies at fresh seeds.
- Report per-family and SAT/UNSAT results; never rely on a grand average.
- Validate all SAT models, check every available proof, and run the Z3 parity suite for
  theory/BV work.
- Require a complete fallback. If a novel optimization cannot justify a consequence or
  complete a model, OxiZ returns `Unknown` or continues through the trusted baseline.

## Recommended sequence

1. Land the established BV abstraction baseline.
2. Run the N1 slice-size telemetry study on that baseline; evaluate BV local-search
   disagreement only as a competing refinement selector.
3. Run N2 read-only pivot/frontier telemetry; it is cheap and directly targets current
   combination code.
4. Run N3 theory-lemma vivification in shadow mode and resolve its proof/null design
   before changing behavior.
5. Quantify alternative-explanation multiplicity before building N4 scoring.
6. Implement the established incremental-preprocessing slice, then compare whole-context
   memoization with N5 activation supports.
7. Land and profile the established SOI/cut baseline before running N6's row-pair oracle.
8. Run N7 and N8 as oracle/instrumentation studies only after the theory/BV work.

This ordering makes every novel proposal compete with the strongest known baseline,
rather than earning an apparent win by filling a missing established feature.
