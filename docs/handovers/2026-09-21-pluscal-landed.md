# Handoff landed: the PlusCal wall is down (2026-09-21, late)

**From:** the session that implemented
`docs/handovers/2026-09-21-pluscal-handoff.md`. Read that handover first —
this document only records what it got wrong, what was built, and what the
next owner inherits.

## What landed

A complete PlusCal translator in `nixie-tla-syntax::pcal`, ported phase by
phase from the reference (`tla2tools`' `pcal` package, consulted as source
only): extraction from the comment stream, the grammar (both p- and
c-syntax) over the front end's own TLA+ lexer and expression parser,
required-label insertion, cluster splitting, symbol disambiguation
(`l0` → `l0_`), the control-flow explosion (`while`/labeled `if`/`either`/
`goto` → `pc` guards and updates, with the reference's `pc`-elision
optimisation for single `while TRUE` bodies), and text generation
(`VARIABLES`/`vars`/`ProcSet`/`Init`/per-label actions/`Next`/
`Terminating`/`Spec` with `fair process` weak fairness). Macros expand
before translation. Procedures are **declined** with a named error —
nothing in the corpus uses them, and a half-implemented stack machine would
be a silent wrong answer.

Entry point: `nixie_tla_syntax::pcal::translate_file`. CLI:
`nixie-tla-syntax` example `pcaltrans` (in-place rewrite with `.old` backup
and a `.cfg` sidecar, like `pcal.trans`; or `-o FILE` to leave the input
alone).

## The verification (all green, tla2tools 1.7.4)

`bench/tla_pcal/run_parity.sh` — four gates, each catching what the
previous cannot (see its `METHODOLOGY.md` for the full tables):

1. **Translate**: 32 corpus files, the oracle accepts the same set.
2. **Parse+levels**: every translated module parses and level-checks here,
   and SANY resolves all 32 with matching levels.
3. **Definitions**: same names, same levels as the oracle's translation
   (compared through the parser — the oracle's column-0 `LET` layout fools
   a grep).
4. **States**: TLC explores models of the golden and of ours; *both*
   translations' `Init`/`Next` hold on *both* dumps. 5 models, 287,647
   agreeing evaluations (DijkstraMutex alone: 282,810), 394 symmetric
   declines (MultiPaxos's `CHOOSE`/`filter` — the evaluator refuses them
   identically on the golden).

BMC smoke (`nixie-tla` CLI, `bench/tla_bmc` contract): our translation of
TeachingConcurrency/Simple gives `NoViolationWithin` on `Inv` at depth 6,
and a `Violation` (0 steps) with independent replay + ITF trace on a false
invariant; our DiningPhilosophers (NP = 2) gives `NoViolationWithin` on
`ExclusiveAccess` at depth 4 — the classic's safety property, on the
classic. QueensPluscal's `Next` hits the standing enumerable-domain wall,
DijkstraMutex the typechecker's occurs-check, and KVsnap an
Init-encoding decline — the first two **identically on the oracle's
translation**, all pre-existing front-end walls, not translation defects.

The two standing parity gates were re-run on the landed tree and stay
green: `bench/tla_parity` 4 422 definitions / 0 mismatches;
`bench/tla_eval` 362 agreeing / 0 mismatches.

The three TLA crate suites are green (503 tests, 17 new in
`nixie-tla-syntax/tests/pcal.rs`); clippy and fmt clean.

## Corrections to the handover's record

- **The corpus is 35 PlusCal files, not 7.** The handover grepped for
  `(* --algorithm` on one line; multi-line comment openings hide most of
  them (Bakery, Boulanger, TLCMC, all of LoopInvariance, the byzpaxos
  family, …). This matters for every future claim about PlusCal coverage:
  the corpus exercises `goto Done`, `+`/`-` label modifiers,
  `\in`-initialized variables, `defaultInitValue`, single `= id`
  processes, `--fair` uniprocess algorithms, and `pc` elision — none of
  which the 7-file survey could see.
- **The inline `\* BEGIN TRANSLATION` blocks in the corpus are stale**
  (older pcal versions). Generate goldens with the actual jar — the fresh
  oracle output differs in more than checksums (e.g. no `Terminating`
  disjunct for while-TRUE bodies, `VARIABLES` ordering with `pc` last).
- **`pcal.trans`'s no-fairness flag is `-nof`**, not `-nofairness`, and
  the default already emits no fairness except for `fair process`
  declarations and `--fair` algorithms.

## Bugs the gates caught (each a class worth remembering)

1. Process-local variables were not *declared* when the algorithm had no
   `define` block (gate 3 caught it as a level mismatch on an invariant
   outside the translation).
2. The substitution walk dropped quantifier **bound domains** —
   `\E x \in S : P` re-emitted with the domain as the body.
3. A `with` inside an `either` clause indented *left of its binder*: the
   statement renderers' column arithmetic disagreed with the bullet
   drawing, and SANY read the conjunct lists as one.
4. Unary minus printed as `-.` (the AST's distinguishing spelling, which
   the lexer takes as two tokens).

All four are pinned by unit tests or would be re-caught by the gates.

## Where this leaves the TLA+ open map

1. ~~PlusCal~~ (this landing).
2. The `Bag`-sort bridge / lambda-shaped function encoding — **still the
   top item**, now with a wider entry path: every PlusCal algorithm's
   variables are functions (`pc`, process-local state), so the
   enumerable-domain wall the BMC smoke hit on QueensPluscal is the same
   wall as the bag-BMC declines.
3. The delta-propagation proof obligation (study item 85).

**Follow-up session (2026-09-22), landed:** pinning the translate→BMC path
as a permanent test found a **solver soundness bug** — the upward aliased
read-over-write loop in `nixie-solver/src/solver/array_axioms.rs` iterated
*conditional* aliases (any `var = store(...)` inside an `or`, which every
multiprocess translation's `pc' = [pc EXCEPT ...]` is) and asserted the
unguarded miss-case lemmas as facts, producing false `unsat` / false
`NoViolationWithin`. Diagnosed by dumping the per-depth assertion set and
cross-checking the identical formula with Z3; fixed by gating on the
already-documented `asserted_aliases` distinction; pinned twice over
(`conditional_alias_tests`, plus the BMC pipeline tests, one of which
asserts the two-array shape never answers a false clean). Verified:
12,174 workspace tests, Z3 parity 100% (0 decisive mismatches), perf gate
PASS (counters 1.000). The tlaplus-examples BMC corpus moved from
15 clean / 0 violations / 1 unknown to 13 / 1 flagged / 2 — the two
flipped specs were false cleans. Also added: `smtrepro` (solver-level
SMT2 driver), `bmcdump` (per-depth BMC query dumper) and `dumptrans`
examples — the debug tooling this diagnosis needed.

Small follow-ups worth a session, in order of value: TLC-model coverage
for the specs that `EXTENDS TLAPS.tla` (needs a TLAPS.tla source — none
on this machine); the symmetric-decline set on MultiPaxos shrinks if the
evaluator grows bounded `CHOOSE`; a `pcaltrans -reportLabels` equivalent
if anyone wants the auto-label diagnostics.
