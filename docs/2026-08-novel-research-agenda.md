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
| Logic-contract validation and body-derived engine routing | Established conformance/setup architecture and a correctness prerequisite; added as Priority 0 in the implementation document |
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

---

# 2026-09 addendum: competition targeting and five further hypotheses

Date: 2026-09-01
Status: next-steps document. Targeting decisions are arguments; N9–N13 are hypotheses at
the bottom of the §*Escalation ladder* (`BENCHMARKING.md` §10.1) — telemetry/oracle first,
nothing default-on.

The eight proposals above are unchanged and keep their ranking. This addendum adds what
the ranking did not cover: **which competition we are actually playing for**, **which
statistic decides it**, and five hypotheses that did not exist when N1–N8 were written —
each grounded in a measurement already sitting in this repo, unfollowed.

## A. Targeting: SATComp main track is the worst medal-per-effort target we have

Three facts, each already recorded here:

1. The standing table is **145 vs 162 against CaDiCaL**
   ([`studies/2026-08-satcomp-standing-gap.md`](studies/2026-08-satcomp-standing-gap.md)).
2. CaDiCaL is the **parity source, not the bar** — recent SAT Competition main tracks are
   won by kissat and its derivatives (`BENCHMARKING.md` §12, added same day). The real gap
   is therefore larger than 145/162 suggests, and unmeasured until the standing table gets
   its kissat column.
3. The one entry in living memory that won a main track on a *new idea* did it with a
   **preprocessing pass on an unmodified backend** (SBVA, 2023), not a search heuristic.

Read together: no single novel search heuristic closes a SATComp main-track gap of that
size in one cycle, and the search-heuristic lever is exactly the one this repo has already
worked hardest (four CaDiCaL policy ports, an inprocessing schedule, probe ranking, chrono
reuse, the used-shield — all null-neutral or null-beaten; see the studies index).

**SMT-COMP is the winnable competition, and not because our solving power is better.**
Its scoring shape is different: per-division across ~40 divisions and several tracks, and
the non-single-query tracks are thinly populated. The `AGENTS.md` invariants — never `sat`
without a concretely verified model; stale models/cores/proofs invalidated on
`push`/`pop`/`assert`; no fabrication — are a *structural* advantage in exactly the tracks
where entrants lose points to output correctness rather than to search power:

| track | why we are positioned | what is missing |
|---|---|---|
| Model Validation | model construction is already verify-or-`Unknown` by policy | per-division MV dry runs; the QF_* model printer under adversarial inputs |
| Unsat Core | `oxiz-sat/src/unsat_core.rs` + scope-consistent invalidation | core minimisation quality measurement; no study exists |
| Proof Exhibition | Alethe/LFSC/DRAT already emitted (`oxiz-proof`) | end-to-end external checking of emitted proofs at competition scale |
| Incremental | push/pop discipline is an enforced project rule | incremental-track benchmark runs; none recorded |

None of that is research — it is verification work on machinery that exists, aimed at the
tracks where the field is thinnest. It should be scheduled **ahead of** N1–N13, because it
converts existing invariants into score, whereas every entry below is a hypothesis that may
falsify. Confirm the 2026 rules and track list before committing effort.

Corollary for the SAT side: keep it, but aim it at **preprocessing/encoding**, per fact 3
and per N13 below — that lever is measurable deterministically, composes with any backend,
and is the one that has actually produced a competition win.

## B. Measurement: two changes to how the studies above get scored

Both landed in `BENCHMARKING.md` on the same day as this addendum; recorded here because
they change the verdicts N1–N8 will produce.

- **§11.1–11.2 — score is `P(solve < T)`, not geomean.** Every study above pre-registers a
  geomean bar. That bar governs *cost* claims only. A cost-neutral change with a paired,
  repeatable solved-at-cap gain is landable; a variance-increasing change is not
  automatically worthless when we are the trailing player on the class it targets. Both
  numbers must now be reported, from the same paired runs.
- **§11.3 — oracle-agreement screening.** Where ground truth for the decision under test
  can be obtained offline, candidates can be screened at a fraction of the ~1 791 runs
  §5's power table demands. This is the single biggest lever on the *rate* at which this
  agenda can be executed, and N11 below is its first application.

## N9. Trajectory re-seeding with monotone clause carryover

### Hypothesis

The 7.31× seed swing is not only measurement noise; it means the runtime distribution is
heavy-tailed, and for a heavy tail a single trajectory held for the whole budget is not the
optimal use of that budget. Periodically resampling the *chaotic* state while retaining the
*monotone* state (learned clauses) will improve survival at the cap without discarding work.

### Mechanism

At a cutoff derived from the empirical survival function, reset every trajectory-carrying
structure — saved/target/best phase arrays, VMTF/VSIDS scores, restart and mode schedules,
tier ages, the RNG stream — while **retaining the learned clause database**. Learned clauses
are entailed by the input, so carryover is sound and monotone by construction; the reset
touches only heuristic state, and no consequence is ever fabricated across it.

Cutoffs are fitted, not universal: the 261-file × multi-seed corpus already in the result
store (`BENCHMARKING.md` §9) is enough to estimate the survival function and derive a
schedule, rather than falling back on a universal Luby-style sequence.

### Prior art and delta

Optimal restart under heavy tails is classical (Luby–Sinclair–Zuckerman; Gomes et al. on
heavy-tailed behaviour in backtrack search), and rapid randomised restarts predate clause
learning. Modern CDCL abandoned *solver-level* restarts because clause carryover makes
successive runs dependent — the delta here is that the dependence is precisely what we
keep, and the resampled component is isolated to heuristic state.

This is **not** the §*Ideas that do not qualify* entry "sequential heterogeneous-slice
portfolio with lemma carryover", which was correctly deprioritised as config switching with
substantial prior art. N9 changes **no configuration**: same config, resampled trajectory.
The justification is our own 7.31× number, which says the trajectory alone is worth more
than any config difference we have measured. It also needs no distributed substrate, which
is the stated reason "hazard-rate portfolios" were ruled out of scope.

### First experiment

Offline, from stored cells only: fit the per-family survival function, compute the optimal
cutoff under the competition cap, and estimate the achievable gain assuming *independent*
resampling. If the idealised gain is small, stop — no code is written. If it is large,
measure the actual post-reset trajectory divergence (do retained clauses simply re-derive
the same path?) before building the policy.

### Matched null

Identical reset at identical cutoffs and identical action count, but the RNG re-seeded to
the **same** seed — isolating "resampling the trajectory" from "performing the reset", which
perturbs plenty on its own and would otherwise take the credit.

### Falsification

Reject if retained clauses reconstruct the pre-reset trajectory (divergence measured
directly), if the idealised survival gain is inside the noise of the standing table, or if
treatment/null on solved-at-cap is ≤ 1.

## N10. In-run successive halving over pre-search compositions

### Hypothesis

The pre-search composition (BVE / ELS / inprocessing, ~8 points) is an unpredictable
lottery per instance, and cannot be predicted statically — but it can be *measured* in-run
from a short probe, cheaply enough to pay for itself inside a competition budget.

### Mechanism

The standing-gap taxonomy's category 1 is verbatim: *"solved by disabling exactly one
pre-search pass (BVE=0 or EQUIV=0) or enabling inprocessing … Not a family property: single
files, opposite fixes."* That is a description of a lottery over a small discrete space.

Run 4–8 compositions as bounded probes at ~2% of budget each, rank them by a deterministic
**trajectory-health surrogate**, and commit the remaining budget to the winner. Probes
double as N9's reseeds, so the two compose rather than compete for budget.

Candidate surrogates, all already instrumented or trivial to add: decisions per conflict,
LBD distribution shape, learned-clause-sourced propagation share (see N12), trail-depth
distribution.

### Prior art and delta

Static per-instance configuration selection is established (SATzilla and successors), as is
parallel portfolio. Successive halving / Hyperband is established in AutoML. The delta is
the transfer: *sequential, in-run* successive halving over pre-search composition, selected
by a search-health surrogate rather than by a predicted runtime, with clause carryover
between probe and commit. The established-candidates document classes offline configuration
selection as engineering, not research — this is a different mechanism with a different
information source (the instance's own early trajectory, not its static features).

### First experiment

Pure oracle study, on stored cells: does any cheap surrogate measured at ~5 k conflicts
correlate with final solvability under each composition? If nothing correlates, the idea is
dead and the negative result is worth recording on its own — it would also constrain N7.

### Matched null

Identical probes at identical cost, winner selected by **permuted** surrogate scores. Same
number of selection opportunities (§2's rule 2), same committed budget.

### Falsification

Reject if no surrogate predicts on held-out instances, if probe cost exceeds the selection
gain, or if the permuted-score arm selects equally well — which would mean the gain came
from best-of-k variance, exactly as it did in the rephase study.

## N11. Reduction as a closed-loop controller on learned-clause propagation share

### Hypothesis

Our clause database is regulated by an **open-loop schedule** (fixed 12 000-conflict
interval, fixed tier percentages); CaDiCaL's is closer to closed-loop. The observable that
schedule is implicitly trying to regulate varies by orders of magnitude across instances,
which is precisely the situation in which a fixed schedule is the wrong control structure.

### The unfollowed measurement

From the established-candidates document, recorded and never chased: on `6s167-opt`,
learned clauses supplied **31.6%** of OxiZ's propagation reasons versus **7.6%** in the
instrumented CaDiCaL reference. Downstream, all measured in the standing-gap study:

| observable | oxiz | cadical |
|---|---|---|
| propagation reasons from learned clauses | 31.6% | 7.6% |
| reduction deletions / conflict | 96.2% | 76.3% |
| literals at shrink entry | 34.7 | 43.9 |
| chronological backtracks | 0% | 26% |

These are one phenomenon, not four: over-aggressive deletion keeps the database small and
learned-clause-dominated, which shallows the trail, which starves both chronological
backtracking (trails never span the 100-level threshold) and the shrink fallback, which is
where the twice-rejected `.rev()` fix keeps dying. The study's own conclusion names the
clause-length gap as the upstream cause that must be closed *first*.

### Mechanism

Do not ship another deletion heuristic — several have already died at the matched null.
Change the control structure: make deletion aggressiveness a **feedback controller** holding
a measured observable at a setpoint, rather than a fixed schedule. Observable: learned-clause
propagation share, or mean trail depth. Setpoint: calibrated from the instrumented reference
(7.6%), per family, not a constant guessed here.

Cross-domain: this is congestion control / process control, and it is the standard answer
whenever a fixed schedule is asked to regulate a quantity that varies by orders of magnitude
across inputs. The tier-promotion ladder stays; only the deletion *target* becomes regulated.

### Testable side effect

If the mechanism is right it predicts a consequence that costs nothing to check: trails
deepen, **chronological backtracking starts firing** (currently 0% against CaDiCaL's 26%,
with the feature enabled and semantics verified identical), and the shrink-fallback
landscape changes. That is a falsifiable prediction distinct from the headline metric, and
per §10.2 it should be pre-registered as such. It would also make a third `.rev()` retest
legitimate for the first time — the study says relanding requires closing the clause-length
gap first, and this is the named upstream cause.

### Matched null

Same controller, same action magnitudes, same trigger points and same action count, driven
by a **permuted or phase-shifted** signal. This is the §2 clause-deletion row: delete the
same number of clauses on the same schedule, chosen by a scrambled score.

### Falsification

Reject if the setpoint cannot be held without pathological database growth, if the predicted
side effects (trail depth, chrono firing rate) do not move, if the controller's benefit does
not survive per-family reporting, or if treatment/null ≤ 1 on both cost and solved-at-cap.

## N12. Phase sources screened by oracle-agreement, starting with message passing on the learned database

### Hypothesis

The model-finding loss class is a **phase-guidance** deficit with a known correct answer,
so candidate phase sources can be screened against ground truth instead of against runtime
— and the learned-clause database is a materially better substrate for estimating that
answer than the input formula.

### Why the setup is unusually clean

Already measured, in the standing-gap study's phase-oracle experiment on `worker_550`:

| arm | result |
|---|---|
| oracle phases + default 2% random polarity | 100 k conflicts, no model |
| oracle phases + `RANDPOL=0` + `REPHASE=0` | **sat with 0 conflicts** (28 987 decisions, pure descent) |

The machinery is sound and the correct decision is *known* for these instances. That makes
oracle-agreement (`BENCHMARKING.md` §11.3) available as a per-instance, near-deterministic
screening metric — no seeds, no matched null, no cap — for any candidate phase source.

### Mechanism

Screen candidate phase sources on held-out oracle-agreement, then promote survivors to the
normal ladder. First candidate, and the novel one:

**Belief propagation over the union of original and learned clauses.** BP and survey
propagation are established for random k-SAT and known to be weak on structured CNF — but
the object they are usually run on is the *input formula*. The learned-clause database is a
different distribution, materially more informative about the region the search is actually
in, and it evolves; running message passing over it periodically (at restarts, deterministic,
cheap) as a target-phase source does not appear in the reviewed baselines. The loss class in
question — dense combinatorial 3-CNF (`noL`, `frb`, `Ptn`) — is BP's home turf.

Further candidates worth screening under the same metric, cheaper to build: the local-search
best assignment weighted by learned-clause participation (our walk plateaus at 74 broken
clauses on `noL-11-14`, so its *output* is being discarded rather than exploited), and a
backbone estimate from probing.

### Prior art and delta

BP/SP phase initialisation is established, as are target/best phases, rephasing and
walk-based phases — all of which we already implement and which the standing-gap study
confirmed are firing. The delta is the **substrate** (learned clauses rather than the input
formula, re-run as the database evolves) and the **evaluation protocol** (oracle-agreement
screening rather than a runtime A/B). The second half is reusable by every other entry here.

### First experiment

No solver change. Compute oracle-agreement for each candidate phase source on the loss class,
held out from any instance used to tune it. Report agreement, not runtime.

### Matched null

At the screening stage: a phase source with the same marginal polarity distribution and zero
dependence on the formula (the §2 "any learned model" row — preserve the output distribution,
sever the input→output mapping). At the ladder stage: the standard rephase-action null.

### Falsification

Reject if agreement does not exceed the distribution-matched null, if it does not transfer
to held-out instances, if message passing does not converge on structured instances within a
deterministic budget, or if agreement gains do not convert to solved-at-cap at the ladder
stage. Per §11.3, agreement is a screen — a source that agrees and still loses is falsified.

## N13. Lift–optimise–lower: CNF re-encoding as a compiler pipeline

### Hypothesis

Structure recovery from CNF is currently used only to *simplify in place*. Recovering the
structure, optimising at that level, and **re-lowering with a deliberately chosen encoding**
is a strictly larger transformation space, and it is the space in which the one recent
competition-winning idea (SBVA) sits.

### Relation to N8

This is N8 with the reversibility removed, and that removal is the point. N8 is rated *very
high* risk because it wants online, reversible, proof-carrying transitions between
representations while the search runs. N13 is **offline preprocessing only**: lift, optimise,
lower, then hand a plain CNF to an unmodified backend. No runtime morphing, no proof-carrying
transition machinery, no reversibility — and therefore none of N8's cost. N8's oracle study
remains the right gate for the *online* version; N13 does not depend on it.

### Mechanism

Treat CNF as an object file and run decompile → optimise → recompile:

1. **Lift.** Recover cardinality, at-most-one, PB, XOR and gate structure. Substantial
   machinery exists: `oxiz-sat/src/cardinality.rs`, `xor.rs`, `gate.rs`,
   `solver/bva.rs`, `solver/congruence.rs`.
2. **Optimise at the recovered level**, where the constraint is a first-class object rather
   than a clause set.
3. **Lower with a chosen encoding.** A recovered cardinality constraint can be re-emitted as
   totalizer, sequential counter, commander, or others; the encoding the input happened to
   use is an artefact of whatever produced the file, not a decision anyone made with this
   solver in mind.

Every step is equivalence- or equisatisfiability-preserving with an explicit derivation, and
model reconstruction is mandatory — the existing preprocessing rules apply unchanged.

### Prior art and delta

Cardinality detection and re-encoding, BVA, SBVA, XOR extraction, gate extraction and AIG
rewriting are all established. The delta is running the **full pipeline** — recover, optimise
at the higher level, re-lower with an encoding chosen for the downstream solver — rather than
the usual single-step in-place simplification. SBVA is one narrow instance of it, and it won
a main track.

### Why it suits this repo specifically

- Preprocessing effects are measurable **deterministically** (variables, clauses, encoding
  size, propagation strength) *before* paying the §1 trajectory-chaos tax. Most of the
  evaluation happens outside the regime that has killed this repo's last several studies.
- It composes with any backend, including an unmodified reference — so the effect can be
  isolated from our search heuristics entirely by measuring it in front of kissat (§12).
- It is the lever fact 3 in §A identifies as the one that has actually won.

### First experiment

Telemetry only, over satcomp2024/2025: how much recoverable structure is present, of which
kinds, and how much of it was encoded in a form other than the one we would choose? If
recovered structure is rare or already well-encoded, the pipeline is dead before any lowering
code is written.

### Matched null

An encoding change of the same magnitude (same constraints re-emitted, same clause/variable
delta) with the target encoding chosen arbitrarily rather than by the selection rule. This
separates "we re-encoded" from "we re-encoded *well*" — and given §1, the first alone will
move results.

### Falsification

Reject if recoverable structure is rare, if the arbitrary-encoding null matches the chosen
one, if re-encoding inflates the formula without a propagation-strength gain, or if the gain
does not survive in front of an unmodified reference backend.

## Revised sequence

The §*Recommended sequence* above governs the theory/BV work and is unchanged. This addendum
inserts work ahead of and alongside it:

1. **Verification, not research, first** (§A): SMT-COMP Model Validation / Unsat Core / Proof
   Exhibition / Incremental dry runs. Converts existing invariants into score; nothing here
   can falsify.
2. **Re-measure the standing table with a kissat column** (`BENCHMARKING.md` §12). Until it
   exists, the size of the SAT gap is unknown and every SAT-side priority is a guess.
3. **N11** — the strongest technical entry, because it is the only one grounded in a
   quantified, unexplained, four-way-consistent divergence from the reference that nobody has
   chased. Costs one instrumented run to confirm the observable before any policy is written.
4. **N12's screening protocol** — cheap, and it lowers the cost of everything after it.
5. **N9 and N10 offline studies** — both are analysis over cells already in the result store;
   neither writes solver code to reach a go/no-go.
6. **N13 telemetry** — a structure census over the competition corpora.
7. Then the established sequence (BV abstraction baseline → N1 → N2 → …).

Entries 2, 5 and 6 write no solver code at all, and 1 writes none either. That is deliberate:
after the negative-result run this repo has had on search heuristics, the next several steps
should be ones that cannot be reshuffled into looking good.
