# PlusCal translation parity — methodology

## What this measures

`nixie_tla_syntax::pcal` is a PlusCal translator: it turns the
`(* --algorithm … *)` comment a TLA+ module carries into the plain TLA+
definitions that comment specifies. Before it existed, the front end
*accepted* every PlusCal specification and silently ignored the algorithm —
the parity gates ran green over these files because only the surrounding
definitions were ever seen. Nothing was broken; a whole specification layer
was absent.

This suite checks the translator against the normative one:
`tla2tools`' `pcal.trans` (PlusCal 1.12 in the 1.7.4 jar), the translator
SANY itself consults. The oracle is consulted, never linked — the same
relationship `bench/z3_parity` has to Z3. Nothing Nixie ships runs a JVM.

## The four gates

In increasing strength; each one catches what the previous cannot:

| gate | catches |
|---|---|
| **1. TRANSLATE** — our translator must accept exactly the files the oracle accepts (32 in the default corpus; the oracle's own set, minus `.toolbox` duplicates) | a grammar that is a subset of PlusCal's |
| **2. PARSE+LEVELS** — every translated module parses and level-checks in this front end, and SANY resolves it with matching definition levels | output that is not well-formed TLA+ |
| **3. DEFINITIONS** — the names and levels our translation declares equal the oracle's (compared through the parser, not a grep: the oracle lays `LET`-bound names out at column 0, which a line-oriented diff miscounts) | a missing action, an undeclared variable, a mis-levelled definition |
| **4. STATES** — TLC explores a model of the golden translation and of ours, printing every initial state and successor pair; **both** translations' `Init` and `Next` must hold on **both** dumps | a translation that is well-formed and *wrong*: label placement, `UNCHANGED` bookkeeping, self-subscripts, `pc` updates |

Gate 4 is the reason this suite exists. Labels *are* the semantics of a
PlusCal algorithm — a statement cluster between labels is one atomic step —
and every other gate would pass a translator that placed them differently.
The state dump is taken from TLC's `PrintT(<<vars, vars'>>)` inside a probe
module that `EXTENDS` the spec under test, with `INIT`/`NEXT` redirected to
the probe so the pairs come from TLC's own successor generation. Both sides
generate a dump, and `pcalsem` evaluates both translations over both dumps:
agreement in all four directions is parity on the reachable behaviour of
the model.

Current standing (tla2tools 1.7.4, 2026-09-21):

- 32 files translated, oracle agrees on the set;
- parse/level parity clean; SANY accepts 32/32;
- definition parity (names + levels) 32/32;
- state parity 5/5 models — 287,647 agreeing evaluations (DiningPhilosophers
  58, QueensPluscal 2×2 972, 2PCwithBTM 238+248, MultiPaxos 2×1 511,
  DijkstraMutex 2×282 810), 394 symmetric declines (below).

## What a decline means, and the ones that stand

A decline is reported with its reason and never approximated.

**Shared evaluator limits (gate 4's 394 on MultiPaxos).** Both translations
decline with the *same* error on the same state — the golden's `Next`
contains the same `CHOOSE`/`filter` constructs ours does, and `pcalsem`
refuses them identically. A decline that both sides agree on is counted and
reported; a *disagreement* — one translation evaluates where the other does
not, or they evaluate differently — is the failure. The MultiPaxos define
block uses `CHOOSE` (unbounded in the evaluator's view) and LET-bound
higher-order `filter`, which is the standing Snowcat/evaluator boundary.

**Models not runnable in TLC.** Several corpus specs `EXTENDS TLAPS.tla`,
which no library on this machine provides (Simple, SimpleRegular, Bakery,
Lock, Peterson, AddTwo). Others assign constants by *definition replacement*
(`x <- Def`) in their `.cfg`, which binds an operator rather than a value
and cannot be replayed against a state dump. EWD687a uses an unbounded
`CHOOSE` TLC itself refuses. These specs are covered by gates 1–3; their
construct classes are represented in the runnable set.

**BMC on translated specs.** The `nixie-tla` CLI runs on translated modules
unchanged (the output is ordinary TLA+). Smoke results on our translations:

- TeachingConcurrency/Simple (N = 3): `--inv=Inv --length=6` →
  `NoViolationWithin` (exit 0); a deliberately false invariant →
  `Violation` at 0 steps (exit 12), **independently replayed**, ITF trace
  written.
- DiningPhilosophers (NP = 2): `--inv=ExclusiveAccess --length=4` →
  `NoViolationWithin` — the Chandy/Misra mutual-exclusion property holds
  within the bound on the handover's named classic. (An 8-step search for
  a liveness-shaped violation exceeds the smoke timeout; depth 5 stays
  clean.) Note: this spec's `ASSUME NP \in Nat \ {0}` cannot be evaluated
  by the trace replayer (`Nat` is free to it), so a *violation* replay on
  this spec would report `replayed: no` for that reason — the Simple
  replay above is the clean demonstration.

Walls, each checked differentially (the oracle's own translation run
through the same checker):

- **Two function-valued state variables updated in the same step** (the
  standard `x[self] := …` multiprocess shape): the satisfying assignment
  needs set atoms the native set encoding cannot certify, so the verdict is
  an honest `Unknown` — never a false clean. Getting here *found a solver
  soundness bug* (below).

- QueensPluscal: `Next` hits the enumerable-domain wall (a symbolic `todo`
  set with no candidate list) — identical on the oracle's translation.
- DijkstraMutex: fails the typechecker's occurs-check on a recursive
  sort — identical on the oracle's.
- KVsnap: `Init` declines on our translation ("a function where a single
  value is needed"); the oracle's declines at a neighbouring conjunct
  ("a set-valued term with no enumerable members"). Both `Unknown`, no
  verdict claimed; the divergence in *which* conjunct trips first comes
  from rendering shapes (`\cup` vs `\union`, spacing), not semantics.
- An invariant of the shape `pc[0] = "a"` reported no counterexample
  within the bound on **both** translations — a pre-existing encoding
  behaviour of the function-equality shape (see
  `bench/tla_bmc/METHODOLOGY.md` §4), not a translation property.

## What the corpus actually uses

Measured, not estimated: 35 `.tla` files carry algorithm bodies (32 outside
`.toolbox` duplicates; the handover that scoped this work counted 7 — it
searched only for markers on the `(*` line, and missed the multi-line
comment forms, among them Bakery, Boulanger, TLCMC, all of LoopInvariance
and the byzpaxos family). The construct matrix:

- both syntaxes (p- and c-form), `--fair` uniprocess algorithms;
- `fair`/`fair+` processes, process sets and single `= id` processes;
- macros (including macro-callss-macro), `either` (nested), `goto`
  (including `goto Done`), `with` (nested, `=` and `\in`);
- labels inside `if` branches, `\in`-initialized variables, bare variable
  declarations (`defaultInitValue`), label `+`/`-` fairness modifiers;
- `pc` elision (a single `while TRUE` cluster with no labels inside —
  Sailfish, AddTwo), with the `Terminating` disjunct elided with it.

**Declined, not implemented**: `procedure`/`call`/`return` (the stack
machine). Nothing in the corpus uses them; a partial implementation would
be a silent wrong answer, and the parser rejects them with a named error.

## The standing gates, re-run on the landed tree

The two existing parity suites (unchanged by this work) were re-run on the
committed tree, per the handoff's bar that they "stay green":

- `bench/tla_parity` (syntax + levels): 4 422 definitions compared,
  0 level mismatches — PARITY OK;
- `bench/tla_eval` (semantics vs TLC): 362 definitions agreeing with TLC,
  0 mismatches.

The "widen" half of the bar is this suite: those gates never saw the
algorithms (they are comments); gates 2–4 above run the same machinery
over what the translator *generates*.

## How to run

```bash
bench/tla_pcal/run_parity.sh            # all four gates
TLA_PCAL_TLC_SECONDS=600 bench/tla_pcal/run_parity.sh   # bigger models
```

`TLA2TOOLS_JAR` overrides the oracle jar; `CARGO_TARGET_DIR` is honored
(the shared `target/` cannot host a link step when its disk is full).
The oracle rewrites its input in place; it always runs on scratch copies.

## The solver bug the pipeline test found

The first `translate → Bmc::check` test asserted a violation TLC confirms
in four steps on a two-process translation; the checker answered
`NoViolationWithin` — a **false clean**, the catastrophic class. Bisection
(via `bmcdump` printing the per-depth assertion set, cross-checked with
Z3 on the identical formula) traced it to
`nixie-solver`'s upward aliased read-over-write loop, which iterated the
*conditional* alias set: every `pc' = [pc EXCEPT ![self] = …]` inside the
transition relation's disjunction is such an alias, and the unguarded
miss-case lemmas it fabricated killed the satisfiable interleavings.
Fixed by gating that loop on level-0 `asserted_aliases` (the distinction
the collector had already documented); pinned by
`conditional_alias_tests` in `array_axioms.rs`. The corpus effect was
measured: 15 false cleans → 13 clean + 1 flagged (possibly-spurious,
under a dropped ASSUME) violation + 2 honest `Unknown`, over the same 16
checked specs.

## Bugs this suite caught during development

Recorded because each one is a class:

- **process-local variables were not declared** when the algorithm had no
  `define` block (gate 3: `SnapshotIsolation` level Constant vs State);
- **quantifier bound domains were dropped** by the substitution walk —
  `\E x \in S : P` re-rendered with the domain as the body (gate 2: parse
  error);
- **a `with` inside an `either` clause indented left of its binder** —
  column arithmetic that made SANY read the conjunct lists as one
  (gate 2);
- **unary minus rendered as `-.`** — the AST's distinguishing spelling,
  which the lexer does not accept as one token (gate 2).

The remaining known cosmetic difference: our renderer canonicalises
operator spellings (`\union` → `\cup`) and wraps `1..N` with spaces
(`1 .. N`); the oracle preserves source spellings. Parse-equal, and pinned
by every gate.
