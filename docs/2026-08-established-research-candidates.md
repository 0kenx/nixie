# Established SAT/SMT Research Worth Implementing in Nixie

Date: 2026-08-22
Status: research synthesis and implementation backlog; no performance claims

This document distils the six supplied research reports into work that has a
published algorithm, a reference implementation, or credible competition evidence.
It deliberately excludes ideas whose main contribution is still hypothetical; those
are in [`2026-08-novel-research-agenda.md`](2026-08-novel-research-agenda.md).

The result is Nixie-specific. A technique is not a candidate merely because it is
state of the art: it must fill a real gap in the production solve path, respect the
pure-Rust constraint, and have a sound fallback. Estimated speedups and week counts
from the reports are not evidence and are not repeated here.

## Executive decision

Before any performance project, Nixie should land a **logic-contract and structural-routing
layer**. Today `set-logic` changes engines and preprocessing through substring tests, while
the asserted formula is not checked against the declared logic. A wrong or unknown header
can therefore suppress a complete backend and turn a solvable input into `Unknown`. The
fix is to infer required capabilities from the complete parsed script, validate those
capabilities against an exact declared-logic specification, and route engines from the
capabilities rather than from a guessed logic name.

The best established implementation bets, in order, are:

1. **CEGAR abstraction for expensive bit-vector arithmetic** (`bvmul`, `bvudiv`,
   `bvurem`), with exact model checking and full bit-blasting as the terminal
   refinement.
2. **Sum-of-infeasibilities simplex** as an alternate exact LRA feasibility engine,
   preserving the current terminating repair path as fallback.
3. **Vivification 4.0 as an isolated replacement pass**: trie-shared decisions,
   on-the-fly subsumption, and quality-tiered deterministic budgets. Do not re-enable
   the already-rejected full inprocessing stack around it.
4. **Production structured BVA**, followed only then by **bounded clausal
   equivalence sweeping**. Nixie has gate congruence and ELS, but not these production
   transformations.
5. **The published incremental-SMT preprocessing calculus**, initially to enable
   sound reuse of selected rewrites across `push`/`pop` without weakening the current
   theory-variable freeze rules.
6. **Split Gröbner bases for a real finite-field theory**, if ZK verification is an
   intended product direction.

Levelwise NLSAT cells and stabilization-based string solving are credible later
projects. ML configuration selection, GPU work, distributed SAT, and another round
of isolated CaDiCaL policy ports should not displace the six items above.

## What Nixie already has

The reports describe the field, not the current tree. As of this document's date,
the following are already implemented in the production or opt-in solver paths and
must not be proposed as greenfield work:

| Report recommendation | Current Nixie state | Consequence |
|---|---|---|
| Chronological backtracking and trail reuse | Both exist in `nixie-sat`; trail reuse has already had controlled studies | Improve only from a concrete reproducer or reference delta |
| Target/best phase saving, rephasing, and local-search phases | CaDiCaL-style target/best arrays and ProbSAT `walk` are wired into `solver/decide.rs` and `solver/walk.rs` | Do not build another phase framework |
| BVE, ELS, probing, vivification, transitive reduction | Implemented; broad mid-search inprocessing remains opt-in after negative measurements | A new pass needs an isolated mechanism and matched control |
| Clausal gate congruence | AND/XOR gate extraction and congruence augmentation exist in `solver/congruence.rs` | The remaining published delta is equivalence sweeping, not “add congruence closure” |
| Model-based theory combination and care pairs | Production `TheoryManager` has bidirectional Nelson–Oppen propagation, model-based reconciliation, arrangement splitting, and static care-atom encoding | Optimize or complete this path; do not replace it with a second framework |
| Exact incremental simplex with anti-degeneracy fallback | Production arithmetic uses exact `Rational64`/delta rationals, sparse columns, a violated-variable loop, and Bland fallback | SOI is a distinct global objective, not a reason to rewrite exact arithmetic |
| Wide-BV exactness and word-level helpers | Models use `BigUint`; word-level BV reasoners exist, but the complete production route is still eager bit-blasting | Reuse the helpers inside a complete abstraction/refinement driver |
| DRAT/LRAT and SMT proof formats | `nixie-proof` and the SAT core already contain proof infrastructure | New transformations still need explicit derivations; format support alone is not proof coverage |

The local studies are decisive context:

- [`2026-08-sat-cadical-policy-ports-negative.md`](studies/2026-08-sat-cadical-policy-ports-negative.md)
  found two policy ports and a stabilization schedule null-neutral or null-beaten.
- [`2026-08-inprocessing-schedule.md`](studies/2026-08-inprocessing-schedule.md) found the
  full scheduled stack broad-suite negative even after fixing its scheduling pathology.
- [`2026-08-probe-scheduling.md`](studies/2026-08-probe-scheduling.md) rejected the probe
  ranking signal against its matched null.
- The supplied local study, `docs/studies/2026-08-sota-survey-performance-proposals.md`,
  consolidates those negative results. Its combined verdict rejects single-policy
  CaDiCaL ports, restart-boundary/rephase learning, inprocessing-arm tuning, probe
  ranking, elimination as a default, and chrono-reuse trail retention as current
  implementation priorities. It also records one especially relevant measurement: on
  `6s167-opt`, learned clauses supplied 31.6% of Nixie's propagation reasons versus 7.6%
  in the instrumented CaDiCaL reference. This is a one-instance mechanism clue, not
  evidence that any particular clause-maintenance proposal will win.
- [`BENCHMARKING.md`](BENCHMARKING.md) requires deterministic work metrics,
  matched nulls, common-random-number pairing, and at least ten seeds per cell for
  trajectory-changing heuristics.

## Priority 0: logic contract and structural engine routing

### Problem

In current Nixie, `set-logic` is not merely a performance hint:

- [`Solver::set_logic`](../nixie-solver/src/solver/config.rs) stores an arbitrary string
  and uses substring tests such as `contains("NIA")` to replace the arithmetic engine;
- nonlinear dispatch auto-detects formula shape only for `ALL` or a missing header;
- assertion-time UF/arithmetic purification is also gated by substrings in the declared
  name; and
- the later `StaticFeatures` walk refines a small set of search knobs but does not
  validate the body against the declaration or generally select complete backends.

Consequently, the same parsed formula can take different completeness paths solely because
of its header. For example, a nonlinear term declared as `QF_LIA` does not engage the NIA
backend and may return `Unknown`; an invented name containing `NIA` can engage it. Nixie also
accepts declarations and terms outside the named fragment instead of returning a logic
error. `Unknown` remains an honest solving result, but allowing an unchecked string to
cause it is behavior-changing routing, not harmless advisory metadata.

### Established basis

The [SMT-LIB 2.7 logic catalog](https://smt-lib.org/logics-all.shtml) defines each logic by
its theory signature and language restrictions. For example, QF_LIA permits multiplication
only by concrete coefficients, while AUFLIA-family declarations constrain the allowed
array signatures. Z3 separately implements a syntactic `check_logic` walk and a
formula-feature `static_features` setup path. Both implementations are incomplete and
leaky in places, but the architectural separation is correct:

1. a declared logic is a contract over the permitted input language; and
2. formula features determine which solver capabilities and heuristics are actually
   needed.

The exact logic name cannot be reconstructed from the body. One formula may belong to
several logics, the author may deliberately declare a strict superset, and some feature
combinations have no unique smallest named logic. What can be recovered reliably for the
supported SMT-LIB language is a structural **required-capability profile**.

### Required design

Represent the three concerns independently:

```text
DeclaredLogic = Known(LogicSpec) | OpenAll | Missing | Unsupported(name)

RequiredCapabilities = {
    quantifiers,
    theory families,
    arithmetic fragment: IDL | LIA | NIA | RDL | LRA | NRA,
    UF and free-sort use,
    recursive array signatures,
    BV/FP parameters,
    datatype/string/sequence features,
    ...
}

EnginePlan = complete theory engines, combination path, and safe preprocessing
```

Then apply these rules:

| Input state | Required behavior |
|---|---|
| Known header, conforming body | Validate the contract; route from `RequiredCapabilities` |
| Known header, non-conforming body | Return a logic/command error, not `Unknown` |
| Missing header or explicit `ALL` | Route entirely from `RequiredCapabilities` |
| Unsupported name | Return `unsupported`/an error without partially reconfiguring solver state |

If compatibility with mislabeled benchmarks is desired, expose an explicit permissive
mode that warns, ignores the incompatible header, and routes structurally. Silent widening
must not be the default.

### Collector requirements

The trusted collector must walk the parsed representation, not the tolerant raw-token
detector in `nixie-smtcomp`. It must:

- validate declaration and definition signatures, including unused symbols;
- recursively inspect array domains/ranges, parametric sorts, datatypes, BV widths, and
  FP formats;
- inspect original assertion DAGs **before** any header-dependent purification or rewrite;
- expand or account for `let` and `define-fun` bodies;
- distinguish concrete-coefficient multiplication from nonlinear multiplication and
  recognize exact IDL/RDL shapes;
- use an explicit heap stack and report malformed/missing terms or sorts as errors;
- update before each incremental assertion and roll scope-dependent feature state back
  exactly on `pop`; and
- produce a capability profile directly, without first guessing a logic-name string.

For batch SMT-LIB files, Nixie may pre-scan the complete parsed script. For an incremental
API, theory activation must be lazy and replay-safe, or the open configuration must install
a conservative complete superset. Swapping an engine after assertions have already been
purified under another policy is not sufficient.

### Nixie reuse and delta

[`StaticFeatures`](../nixie-solver/src/solver/static_features.rs) already provides a safe
explicit-stack assertion-DAG walk and recognizes theory families, nonlinearity, and
difference-logic shape. It is a useful foundation, but its current `inferred_logic` covers
only a few shapes, it sees post-assertion terms, and it records only array presence rather
than recursive signature restrictions. The `nixie-smtcomp` `TheoryBits` scanner is useful
for scheduling metadata but is intentionally tolerant and must not become the validation
or soundness boundary.

The implementation delta is therefore an exact `LogicSpec` registry plus a broadened,
pre-rewrite capability collector shared by declarations, assertions, validation, and
engine planning. Standard logics and Nixie/competition extensions such as `QF_ANIA` need
explicit separate registry entries; their semantics must never be decoded from substrings
of their names.

### Acceptance tests

At minimum, the completed layer must demonstrate:

1. `QF_LIA` plus `(* x y)` is rejected as outside the declared logic;
2. the same nonlinear body under missing/`ALL` routing engages the complete nonlinear
   path rather than falling through because of its header;
3. disallowed nested array signatures are rejected even when all array terms type-check;
4. a linear body declared under a broader nonlinear logic may use the linear engine;
5. an unsupported name neither behaves like a substring-matched known logic nor leaves a
   partially changed engine configuration;
6. a second illegal `set-logic` is rejected instead of silently replacing live solver
   state; and
7. compatible broad headers over the same body produce the same capability-derived engine
   plan and verdict.

This is primarily a conformance, correctness, and completeness fix. Performance evaluation
comes only after those invariants hold; it does not need a matched-null experiment because
rejecting out-of-logic input and preventing header-induced incompleteness are semantic
requirements, not heuristic claims.

## Priority 1: bit-vector arithmetic abstraction/refinement

### Established basis

Niemetz, Preiner, and Zohar's
[Scalable Bit-Blasting with Abstractions](https://doi.org/10.1007/978-3-031-65627-9_9)
is a concrete CEGAR procedure implemented in Bitwuzla. Expensive operators are
over-approximated, spurious models are eliminated by sound lemma tiers, and full
bit-blasting is the final fallback. The 2026 SMT-COMP QF_BV results continue to show
the strength of Bitwuzla-family specialization: the official table lists
Bitwuzla-MachBV first and Bitwuzla second among eligible sequential entries.

### Nixie delta

Nixie has strong term rewriting, a production bit-blaster, exact wide constants, and
word-level propagation modules. It does not have a production loop that:

1. replaces selected wide `bvmul`/`bvudiv`/`bvurem` terms with abstractions;
2. checks a candidate model against exact SMT-LIB operator semantics;
3. adds only proved refinement lemmas; and
4. eventually lowers the exact operator circuit if refinement stalls.

This is a better first BV project than generic “neural CEGAR”: the published baseline
must exist before a new refinement selector can be evaluated.

### Safe implementation slice

- Start with quantifier-free `bvmul` at widths at least 32.
- Abstract only terms whose exact circuit has not already been simplified cheaply.
- Treat `Unsat` of the over-approximation as sound; treat `Sat` as provisional until
  every abstraction is exact under the candidate model.
- Use exact `BigUint` arithmetic for consistency checks.
- Add published tier-1 lemmas first, value instantiation second, and exact
  bit-blasting as the guaranteed terminal refinement.
- Keep every tier deterministic and scope-aware. Exhaustion returns `Unknown`, never
  a provisional `Sat`.

### Go/no-go

Count abstracted terms, refinement iterations, terms eventually bit-blasted, emitted
gates/clauses, and solver ticks. Continue only if the implementation reduces terminal
bit-blasting on multiplication-heavy QF_BV families without losing adjacent families.
Every SAT model is independently checked; every UNSAT result runs the normal proof or
differential gate.

## Priority 2: sum-of-infeasibilities simplex

### Established basis

King, Barrett, and Dutertre's
[Simplex with Sum of Infeasibilities for SMT](https://www.cs.utexas.edu/~hunt/FMCAD/FMCAD13/papers/73-Simplex-Sum-SMT.pdf)
defines SOISIMPLEX: a global objective over bound violations, with a heuristic mode
and a degeneracy-escape mode. One supplied report incorrectly names Tinelli as the
third author; the primary paper names Dutertre.

### Nixie delta

`Simplex::make_feasible` currently selects one violating basic variable and repairs it
with a sparse-column heuristic, switching to Bland after repeated degeneracy. That is
not SOI. The existing exact tableau, column index, scope snapshots, conflict
explanations, and pivot resource limit make a second feasibility driver feasible
without replacing the trusted representation.

### Safe implementation slice

- Add an alternate SOI driver behind a configuration flag.
- Define the objective entirely over exact delta rationals; approximate weights may
  rank candidates only after exact eligibility is established.
- Preserve the published degeneracy/termination discipline and retain the current
  one-violation path as fallback.
- Never turn pivot exhaustion or arithmetic overflow into feasibility. They remain
  resource limits and therefore `Unknown` at the solver boundary.
- Generate conflicts through the existing exact explanation path, not from objective
  values.

### Go/no-go

Use QF_LRA first. Primary metrics are pivots, row/column visits, exact arithmetic
operations, and deterministic solver ticks. A reduced pivot count is insufficient if
row work or coefficient growth increases. Require Z3 parity and adversarial degenerate
tableau tests before expanding to LIA.

## Priority 3: Vivification 4.0 as an isolated replacement

### Established basis

Pollitt et al.'s
[Revisiting Clause Vivification](https://cca.informatik.uni-freiburg.de/papers/PollittFleuryBiereSakallahHeuleChenFisseha-POS25.pdf)
adds on-the-fly subsumption, shared decision prefixes, and quality-tiered budgets to a
production vivifier. The supplied repository study reports roughly one-third fewer
vivification decisions from prefix sharing in the upstream evaluation.

### Nixie delta

Nixie has SAT-clause vivification, but not the complete POS'25 mechanism. The local
inprocessing experiments reject the **bundle** and its schedules; they do not test a
faithful replacement vivifier with shared prefixes and tier budgets. The learned-clause
reason measurement makes clause maintenance worth investigating, while proving nothing
about the direction of the effect.

### Safe implementation slice

- Port trie/prefix decision sharing without changing candidate order or commit rules.
- Add on-the-fly subsumption with the existing original/learned promotion and live-reason
  deletion invariants.
- Preserve deterministic tick budgets and separate irredundant/core/tier/local work.
- Keep theory lemmas out of this established slice; theory-aware vivification is a
  separate novelty hypothesis in the companion agenda.
- Do not couple the pass to BVE, probing, transitive reduction, or a new reduce policy.

### Go/no-go

First compare old and new vivifiers on identical candidate sequences: decisions,
propagations, clauses strengthened, literals removed, and deterministic complete-work
cost. Then test the search effect with a matched no-signal ordering/control. Reject if
prefix savings do not survive end-to-end work or if they merely reshuffle the search.

## Priority 4: structured BVA, then equivalence sweeping

### Established basis

[Structured Bounded Variable Addition](https://doi.org/10.4230/LIPIcs.SAT.2023.11)
uses structural tie-breaking to make auxiliary-variable introduction robust. The
SAT 2024
[Clausal Congruence Closure](https://doi.org/10.4230/LIPIcs.SAT.2024.6)
and FMCAD 2024
[Clausal Equivalence Sweeping](https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_29)
show the value of recovering circuit structure from clauses.

### Nixie delta

`Preprocessor::bounded_variable_addition` is a dead, pairwise overlap routine; it is
not production SBVA. Nixie's production solver already extracts AND/XOR gates for
congruence and runs equivalent-literal substitution. The missing work is therefore:

1. a production structured candidate generator and 3-hop-style tie-break;
2. model reconstruction for introduced variables;
3. incremental/proof policy for the transformation; and, after that is sound,
4. bounded SAT sweeping of equivalence candidates not found syntactically.

### Safe implementation slice

- Begin with one-shot, pre-search, non-incremental CNF and no attached theory.
- Make additions equisatisfiable by construction and retain a reconstruction record.
- Do not enable under LRAT until every introduction and retired clause has a valid
  proof story. DRAT acceptance is not a substitute for missing LRAT antecedents.
- Use the native Nixie SAT core as a bounded embedded solver; linking Kissat/Kitten is
  forbidden by the pure-Rust policy.
- Add the same pass at the QF_BV boundary only after the CNF pass is independently
  validated.

### Go/no-go

Measure formula-size change, propagation work, introduced-variable count, and
instructions/ticks to verdict on multiplier/equivalence, crypto, and broad negative
controls. A matched null must introduce the same number and shape of variables with
candidate semantics scrambled. Do not infer value from raw BVA-versus-baseline alone.

## Priority 5: incremental preprocessing calculus

### Established basis

Bjørner and Fazekas's
[On Incremental Pre-processing for SMT](https://doi.org/10.1007/978-3-031-38499-8_3)
classifies transformations by what can be retained, how new constraints must be
rewritten, and when earlier assertions must be replayed. This is stronger than a
generic instruction to “cache more.”

### Nixie delta

Nixie correctly gates destructive SAT transformations when theory variables,
assumptions, proofs, or multiple scopes make them unsafe. The immediate established
project is to implement the calculus for a narrow rewrite class, not to remove those
gates. A freeze set for SAT variables mapped to theory terms is the prerequisite
identified in [`2026-08-cdclt-gates-audit.md`](studies/2026-08-cdclt-gates-audit.md).
The additional SOTA study's “freeze-set collapse” proposal is therefore an enabling
slice of this established project, not a separate novel algorithm.

### Safe implementation slice

- First freeze every theory-mapped, assumption, and activation variable.
- Support equivalence-preserving rewrites with explicit substitution/replay maps.
- Version each transformation by assertion scope and roll all indexes back in lockstep.
- Re-encode a new assertion through retained substitutions only when the calculus's
  preconditions hold; otherwise retain the current conservative path.
- Keep satisfiability-preserving but non-equivalent transformations out of the first
  slice because model reconstruction and replay obligations are larger.

### Go/no-go

Use real BMC/symbolic-execution-style traces, not repeated single-query files. Measure
cumulative deterministic work across the whole trace, replayed assertions, retained
transformations, and peak metadata. Exercise arbitrary push/pop trees, not only
monotone growth.

## Priority 6: split Gröbner bases for finite fields

### Established basis

[Split Gröbner Bases for Satisfiability Modulo Finite Fields](https://doi.org/10.1007/978-3-031-65627-9_1)
uses multiple smaller bases and specialized bitsum propagation rather than one global
basis. It is implemented in cvc5 and targets a clear ZK/cryptographic workload.

### Nixie delta

Nixie has generic polynomial and Gröbner infrastructure, but no production SMT-LIB
finite-field theory. This is a new theory, not an optimization patch. The reports are
right that Rust's field-arithmetic ecosystem may help, but adding `ark-ff` or another
crate is a dependency decision, not a free implementation shortcut.

### Safe implementation slice

- Specify the supported SMT-LIB finite-field syntax and exact model representation.
- Implement prime fields first with checked characteristic/sort separation.
- Build a complete ground conjunction solver before CDCL(T) propagation.
- Add split bases and bitsum recognition only after plain basis correctness is
  differential-tested against cvc5.
- Scope every basis, substitution, core, and model artifact across `push`/`pop`.

This ranks sixth because its upside is strategic rather than broad. Promote it only if
QF_FF/ZK is an explicit product target.

## Later established projects

| Project | Why credible | Why not first |
|---|---|---|
| Levelwise/open single-cell NLSAT improvements | [Levelwise single-cell construction](https://doi.org/10.1016/j.jsc.2023.102288) builds on the MCSAT/NLSAT architecture | Nixie already has a sound sign-abstraction cell certifier; the remaining delta is mathematically deep and needs focused NRA profiling |
| Stabilization-based strings | [Z3-Noodler](https://doi.org/10.1007/978-3-031-57246-3_2) and the [official 2026 string results](https://smt-comp.github.io/2026/results/qf_strings-single-query/) provide strong evidence | Replacing the string core is a major automata project and should follow a dedicated Nixie string gap study |
| BV propagation-based local search | Established as a SAT-only front end in Bitwuzla | It cannot prove UNSAT and Nixie should first land the complete BV abstraction baseline |
| Used-aware clause deletion/unlearning | [Learn to Unlearn](https://doi.org/10.4230/LIPIcs.SAT.2025.14) makes unconditional critical retention plus recent-use signals a credible alternative to activity-heavy deletion | Nixie first needs a faithful telemetry comparison against its existing tiers; changing deletion is chaotic and requires a matched null |
| Relevant-domain-first MBQI enumeration | [From MBQI to EI and Back](https://arxiv.org/abs/2506.22584) prioritizes existing formula/model terms before minting arbitrary constants | Implement after profiling Nixie's useless-instantiation and term-pollution rates; model-disequilibrium ranking is a separate unvalidated heuristic |
| Certified PB/MaxSAT preprocessing | VeriPB/CakePB work shows feasibility and bug-finding value | Nixie's immediate performance gaps are SAT/BV/arithmetic; proof coverage must be scoped separately |
| Portfolio/configuration selection | SATzilla/MachSMT-style selection is established and can help heterogeneous suites | It hides component deficits, introduces training/evaluation leakage risks, and local policy studies show that trajectory variance can overwhelm apparent gains |

## Explicit non-priorities

- **Do not add C/C++ solver FFI.** Suggestions to hand CNF to Kissat or reuse Kitten
  violate the repository's pure-Rust requirement.
- **Do not implement an `f64` simplex fast path yet.** It is known engineering, not
  novel, and rigorous forward-error bounds plus exact conflict verification make it a
  larger correctness project than SOI.
- **Do not tune isolated SAT policies against PAR-2 or wall-clock.** Four recent local
  experiments found effects no better than matched nulls. First explain the measured
  late-search decision-depth collapse.
- **Do not treat SATLUTION or GaloisSAT as established Nixie components.** Both are
  recent preprints. Their headline results are author-reported and do not establish a
  deterministic, pure-Rust, proof-preserving integration path.

## Reference-parity backlog from the additional study

These are bounded engineering candidates, not independent research directions:

1. on-the-fly subsumption during conflict analysis;
2. `collect.cpp`-style satisfied-clause cleanup and falsified-literal removal;
3. out-of-order propagation of newly discovered units; and
4. eager array read-modify-write chain reduction.

Each needs a separate reference-code audit and experiment. The earlier local work warns
against assuming that a faithful CaDiCaL port transfers performance. Tick-accounting
changes are excluded from this list because they change schedules globally and therefore
need their own matched-null study before being considered an “engineering” improvement.

## Quality assessment of the supplied reports

Scores use a five-point scale. “Novelty discipline” means distinguishing a new
combination from a genuinely new algorithm and avoiding universal absence claims
without a dedicated literature search.

| Report | Coverage | Source quality | Calibration | Nixie fit | Novelty discipline | Overall |
|---|---:|---:|---:|---:|---:|---:|
| **opus** | 5 | 4 | 4 | 3 | 3 | **3.8/5** |
| **gpt** | 5 | 3 | 3 | 2 | 2 | **3.0/5** |
| **grok** | 3 | 2 | 1 | 1 | 1 | **1.6/5** |
| **manus** | 3 | 5 | 5 | 4 | 4 | **4.2/5** |
| **glm** | 4 | 2 | 2 | 2 | 2 | **2.4/5** |
| **local SOTA study** | 4 | 4 | 4 | 5 | 3 | **4.0/5** |

### opus

The best broad survey. It separates established, under-exploited, and speculative
ideas; acknowledges that its speedups are hypotheses; and correctly emphasizes
structure recovery, exactness, theory combination, and offline rather than hot-loop
ML. Weaknesses are breadth-driven: some citations are only textual, several 2026
claims are provisional, many percentage forecasts have no empirical basis, and its
“novel” section often combines known components. It also misattributes the SOI paper
and suggests Kissat FFI for P11 despite Nixie's explicit ban.

### gpt

Strong architecture and evaluation thinking, with useful emphasis on proof boundaries,
representation choice, temporal holdouts, and ablation. Its supplied citation tokens
(`turn...`) are unusable outside the generating session, however. The plan is sized for
a 10–14-person lab rather than this repository, and much of its novelty is a broad
systems synthesis. More importantly, its five-seed minimum and competition-style
wall-clock/PAR-2 focus conflict with Nixie's measured need for at least ten seeds,
matched nulls, and deterministic primary work metrics. Official 2026 SMT tables do
support several of its competition claims, but competition rank does not validate its
proposed mechanisms.

### grok

Useful as a trend memo, not as an engineering or novelty review. It correctly surfaces
the SATLUTION and GaloisSAT preprints, but treats their author-reported numbers and
mechanism descriptions too confidently. The proposed live code evolution, online
continuous/CDCL coupling, and “causal” implication rewiring have no credible
soundness, determinism, overhead, or prior-art analysis for Nixie. Citations are absent,
expected gains are unsupported by evidence in the report, and the implementation priority contradicts the
repository's pure-Rust and reproducibility constraints.

### manus

The highest-quality research brief for this task. It uses direct references, limits its
scope, phrases novelty as a collision review rather than proof, gives exact mechanisms,
and makes each proposal falsifiable. Its four hypotheses are more useful than its SOTA
summary. Two cautions remain: PDM's hardware-cost terms may only be offline-calibrated
constants—live hardware timing/counters cannot affect Nixie's decisions—and the official
SMT-COMP page's implausible “30720 GB” memory label should not be repeated as a literal
resource fact without resolving the site's unit error.

### glm

Good at identifying possible feedback signals and at keeping learned inference outside
the logical trust boundary. It is much weaker on evidence: citation tokens are unusable,
several absence/first-ever claims are unsupported, and GPU/neural speedups are presented
with unjustified precision. Its “learned inprocessing policy” also ignores this repo's
matched-null results, while the theory-aware clause and conflict-slice ideas become
valuable only after being reformulated more rigorously in the novel agenda.

### local SOTA study

The supplied `docs/studies/2026-08-sota-survey-performance-proposals.md`
has the best Nixie fit: it reuses the repository's negative studies, follows the matched-null
protocol, distinguishes adoption from novelty in several proposals, and identifies concrete
code deltas. Its local measurements are much more actionable than generic competition
forecasts. The main weaknesses are novelty overreach (“no paper/solver does X” after a
targeted rather than systematic search), an inadequate proposed null for theory vivification,
and the closing claim that all proposals are soundness-neutral. BV abstraction, theory-lemma
replacement, learned cuts, and freeze-set preprocessing all change logical state and require
full soundness proofs. It also describes CAV'24 BV abstraction as covering wide addition; the
published operator set is multiplication, unsigned division, and unsigned remainder. Its
“near-certain” parity-backlog payoff is not supported by Nixie's repeated neutral reference
ports.

## Verification notes on time-sensitive claims

- The [SAT Competition 2026 site](https://satcompetition.github.io/2026/) confirms
  that results and sources were published and later corrected after two omitted
  solvers were added. Exact rankings copied before 2026-08-10 are therefore stale.
- The official [SMT-COMP 2026 QF_BV table](https://smt-comp.github.io/2026/results/qf_bitvec-single-query/)
  confirms Bitwuzla-MachBV's QF_BV lead, but also records three Yices2 errors; solved
  counts without error scores are misleading.
- [SATLUTION](https://arxiv.org/abs/2509.07367) and
  [GaloisSAT](https://arxiv.org/abs/2603.28796) exist, but both headline comparisons
  remain preprint author claims. They are inputs to a research watchlist, not settled
  baselines.

## Common implementation gate

Every candidate above must ship as a small falsifiable slice. Before a default change:

1. add an exact regression for every soundness-sensitive rule;
2. compare with the strongest relevant Nixie path and the reference implementation;
3. use deterministic complete-work metrics;
4. add a matched null for any trajectory-changing selection policy;
5. use at least ten common-random-number seeds when randomness matters;
6. validate every SAT model and independently check/probe every UNSAT path available;
7. run the full verification bar and Z3 parity suite from `AGENTS.md`.

No report's forecast can waive this gate.
