# TLA+ front end – design

## Goal

Grow Nixie into a single-repository pipeline **TLA+ → IR → SMT → SAT**, in the shape of
Apalache but without Apalache's architecture. Two targets, in order:

1. **Parity.** Every specification Apalache accepts, Nixie accepts, with the same verdict.
   This is the acceptance bar for the first release: *any valid Apalache input runs.*
2. **Superset.** Beyond parity, principally **temporal logic** — see
   [Long-term: temporal logic](#long-term-temporal-logic). Long term, not milestone 1.

Everything is pure Rust. **No JVM, no `tla2tools.jar`, no FFI** — same rule as the solver
core (`deny.toml`). That decision has one large consequence, stated up front in
[The parser](#1-the-parser-nixie-tla-syntax).

## What we port, and what we deliberately do not

Apalache is Apache-2.0, as is Nixie, so porting is licence-clean with attribution in
`THIRD_PARTY_NOTICES.md`. But "port Apalache" is the wrong instruction, and the distinction
is the whole point of the exercise.

**Port the semantics:**

- the IR (`TlaEx` / `TlaModule`) and the **KerA kernel language** the IR reduces to;
- the Snowcat type system and its inference;
- the preprocessing pipeline: desugaring, inlining, normalisation, constant simplification,
  Keramelizer (reduction to KerA), priming, VC generation;
- the **symbolic-transition split** of `Next` and the assignment problem it solves;
- the analysis passes (skolemization / expansion / free-existential marking);
- counterexample output in ITF.

**Do not port the architecture.** Apalache's design is shaped end to end by Z3 being an
opaque process behind an API boundary: the arena/cell encoding, the `oopsla19` term blast,
the per-transition `push`/`pop` discipline, `--discard-disabled` pruning. Every one of those
is *compensation for not being able to see inside the solver*. Reproducing them in a monorepo
relocates the boundary instead of deleting it — and deleting the boundary is the only thing a
monorepo buys. The recurring theme of
[Cross-layer optimisations](#cross-layer-optimisations) is exactly this: information that is
known exactly at the TLA+ layer, needed at the SAT layer, and destroyed in between.

## Reference material

Read as specification; never linked, never a dependency.

- **Apalache** (Scala, Apache-2.0) — IR, Snowcat, pass pipeline, KerA, both encodings,
  transition splitting, ITF. Not vendored in `../temp`; fetch a read-only checkout when the
  work starts.
- **SANY** (Java, part of `tla2tools`) — the normative TLA+ parser. Its level checker and
  operator table are the ground truth for [the parser](#1-the-parser-nixie-tla-syntax).
- **`tree-sitter-tlaplus`** — the most complete machine-readable TLA+ grammar in existence.
  Treat it the way this repo treats `../temp/z3`: read it to learn the shape, do not link it
  (its generated parser is C).
- ***Specifying Systems*, Lamport** — normative for the operator precedence table, the
  junction-list layout rule, levels, and module instantiation semantics.
- **`nixie-spacer`**, **`nixie-theories/src/set`**, **`nixie-sat/src/symmetry.rs`** — the
  in-repo capabilities the cross-layer work is built on.

## Crate layout

```
nixie-tla-syntax   lexer, layout pre-pass, Pratt expression parser, level checker
nixie-tla          IR + KerA kernel, Snowcat types, preprocessing passes, ITF output
nixie-tla-check    search driver: transitions, BMC, CHC lowering, CEX minimisation
nixie-theories/src/tla_set   TLA+ set/function/record theory plugin (see §3)
```

`nixie-core` stays TLA+-free. The cross-layer items in §4 are changes *inside* existing
crates, driven by hints from `nixie-tla`; they need hint channels, not new crates.

## 1. The parser (`nixie-tla-syntax`)

**This is the critical path, not the SMT encoding.** Apalache does not parse TLA+ — it shells
out to SANY. Removing the JVM means writing the thing Apalache never had to. Scope it
honestly; it is the single largest risk in this plan.

Recommendation: **hand-written recursive descent, Pratt expression parser, layout pre-pass.**
Not a parser generator. Reasons: the layout rule does not fit generators; diagnostic quality
matters for a user-facing tool and `nixie-core` already has `diagnostics.rs` /
`error_recovery.rs` / `interner.rs` to reuse; and incremental reparse later stays open.

### 1.0 Why not a parser generator / LR(1)

Asked directly, and worth recording because the rest of this section rests on it: **TLA+ is
not a good fit for LR(1).** Three problems, increasing in severity.

1. **Junction lists are not context-free** (§1.1), so no LR(1) grammar exists over the raw
   token stream. This one is fixable — the layout pre-pass restores context-freeness — so it
   rules out "LR(1) on raw tokens", not LR(1) in principle.

2. **`[` is overloaded six ways**, and the disambiguating token is arbitrarily far in:
   `[S -> T]`, `[x \in S |-> e]`, `[a : S, b : T]`, `[a |-> 1]`, `[f EXCEPT ![i] = e]`,
   `[A]_v`. Deferring reductions is LR's strength, so left-factoring gets part of the way, but
   `[a, b, c` must stay undecided until `:` / `\in` / `|->` arrives, and that interacts badly
   with the identifier-list productions. Constructible; fragile.

3. **Precedence ranges are the decisive one.** Each operator carries an interval `(lo, hi)`,
   and juxtaposing two operators with *overlapping* intervals is a **static error we want to
   report precisely**, not an ambiguity to resolve silently. Yacc-style `%left` / `%nonassoc`
   assigns one number per token and cannot express an interval, so any LR encoding
   approximates — turning a precise diagnostic ("`\cup` and `\in` have overlapping
   precedence, parenthesise") into a generic parse error.

Two external data points, both worth re-verifying against source when the work starts:

- `tree-sitter-tlaplus` is **GLR**, not LR(1), *and* still needs an external scanner plus
  dynamic-precedence conflict declarations. If LR(1) sufficed, that machinery would not exist.
- SANY is JavaCC-based — LL(k) with syntactic lookahead — and resolves operator precedence in
  a **separate post-parse phase**. That is the same split Pratt parsing gives for free.

A Pratt parser carries `(lo, hi)` in its loop condition and compares intervals directly, which
is exactly what a static precedence table cannot express. Combined with recursive descent it
also yields real error recovery — which matters more here than anywhere in the solver, because
this is the user-facing surface of the entire pipeline.

### 1.1 Junction lists are layout-sensitive (the only non-context-free part)

```tla
Next == \/ /\ a
           /\ b
        \/ c
```

A `/\` or `\/` at column *c* opens a list whose items must align at *c*; any token at a column
≤ *c* terminates it. The indentation column behaves as a bracket.

**Superseded by the implementation — see the correction below.** The original plan was to
handle this the way Haskell does: a token-stream transformer inserting *virtual* open/close
brackets, so that the grammar the parser sees stays plain context-free, on the precedent of
the Haskell 2010 layout algorithm (§10.3) and Python's INDENT/DEDENT insertion.

**That does not work, and `nixie-tla-syntax` does it differently.** A `/\` opens a bulleted
list only where an *expression* is expected; in `x == a /\ b` the identical token is an
ordinary infix operator. A lexical pass cannot separate the two without reconstructing
expression-position — the same problem as regex-versus-division in a JavaScript lexer, and
equally prone to misfiring. The parser already knows, exactly, so layout is decided there:
`/\` in prefix position starts a list, and a column check in the Pratt loop stops an
expression at a token that would close an enclosing one.

The same column mechanism does a second job the original plan did not anticipate: a token at
or left of the column a *unit* started at ends that unit. Without it `A == 1` followed by a
structured `<1>1.` proof step parses as `1 < 1 > 1`, and a `- 5` written at column 1 is
absorbed as a subtraction. Both rules are suspended inside brackets, where a column-1 token
is ordinary continuation.

### 1.2 Operator precedence is a *range*, not a level

TLA+ gives each operator a precedence **interval** (`'` sits at the top, `=>` at the bottom;
*Specifying Systems*' table is normative). Two operators whose intervals overlap may not be
juxtaposed without parentheses — and that is a **static error to report**, not an ambiguity to
resolve. A Pratt parser carrying `(lo, hi)` per operator and rejecting overlap gets this
exactly right and produces a good message.

Note the problem is bounded: TLA+ does **not** admit arbitrary new operator glyphs. A user may
give a definition for a symbol from the fixed table (`x \oplus y == ...`); they cannot invent
one. So the operator table is closed and can be a static table in the lexer.

### 1.3 The rest of the hard list

- **Modules and `INSTANCE`.** `EXTENDS`, `LOCAL`, `I == INSTANCE M WITH a <- e`, parameterised
  instances, and `I!Op(...)` qualification. Substitution must be capture-avoiding and applied
  at use sites. Standard modules (`Naturals`, `Integers`, `Sequences`, `FiniteSets`, `TLC`,
  `Apalache`) ship as built-in module sources.
- **Level checking.** Four levels — constant, state, action, temporal. Primes only at action
  level; `ENABLED`, `UNCHANGED`, `[A]_v`, `<<A>>_v`, `WF_v`/`SF_v` have their own rules. This
  is not optional polish: the symbolic-transition analysis in §2 needs levels, and mislevelled
  input must be **rejected**, never silently accepted (`AGENTS.md`: no silent fallthrough).
- **Higher-order operator parameters.** `Op(f(_), x)` and `LAMBDA`. Apalache supports these
  only where they can be inlined; parity means matching that restriction, and *saying so* when
  it is violated.
- **Comments carry semantics.** `@type:` annotations live inside `\*` comments. The lexer must
  retain comments and attach them to the following definition. Easy to get wrong; costs the
  whole type system if you do.
- **Numerals.** `\b` / `\o` / `\h` binary, octal, hex prefixes.
- **`RECURSIVE`.** Apalache dropped support. Milestone 1 rejects it with a clear message;
  revisit only if parity testing shows real specs need it.

### 1.4 Acceptance test for the parser

Parity is defined by behaviour, not by intent: assemble a corpus from Apalache's own test
suite plus the public TLA+ examples repository, and require that every file Apalache's SANY
front end accepts is accepted here with an isomorphic IR, and every file it rejects is
rejected here. That corpus is also the first differential oracle (§5).

## 2. IR and the KerA kernel (`nixie-tla`)

Two levels, and the second one is what makes the rest tractable:

- **Surface IR** — a faithful tree of what was written, with source spans, for diagnostics and
  round-tripping.
- **KerA kernel** — the minimal core TLA+ reduces to. *Only KerA is ever encoded.* Everything
  downstream (typing, transition analysis, encoding, theory plugin) matches exhaustively on a
  small closed enum, so a new construct **breaks compilation** rather than slipping through a
  `_ =>` arm. This is the same discipline the solver core already runs on, and it is why the
  two-level IR is worth the extra pass rather than a convenience.

**One deliberate divergence from Apalache's Keramelizer.** It expands set operations away:
`A \cup B` becomes a comprehension, `\subseteq` becomes a quantifier. That is right when the
backend is an opaque SMT solver with no set theory — the expansion is the only way to say it.
Nixie has `nixie-theories/src/set`, so `\cup`, `\cap`, `\`, `SUBSET` and `UNION` stay *in* the
kernel, which is what lets the encoder hand them to a set theory instead of blowing them into
quantifiers first (O3). Expanding them here would destroy exactly the structure that
optimisation needs, and it cannot be recovered afterwards. `\subseteq` is the one exception: it
is a quantifier in every encoding, so nothing is lost.

Pass pipeline, mirroring Apalache's: configuration (`Init`/`Next`/`Inv` from the `.cfg`) →
desugaring → inlining (operators, `LET`-`IN`, `LAMBDA`) → Snowcat typing → normalisation and
constant simplification → Keramelizer → priming → VC generation → transition split and
assignment solving → analysis (skolemization / expansion / free-existential) → encode.

**Status: the kernel and the lowering pass are landed** in `nixie-tla`. Measured over the
corpora, 4 349 of 4 637 expression-level definitions lower (93.8%); a further 694 definitions
are *spec structure* — `Spec == Init /\ [][Next]_vars`, fairness, `ENABLED`, temporal operators
— which are correctly rejected because they are not kernel expressions at all. Snowcat typing
and the rest of the pass pipeline are still open.

**`INSTANCE` is resolved.** `I == INSTANCE M WITH v <- w` looks through `M` under that
substitution, including unnamed instances, member arguments, and members that reach other
members of the same module. The visibility rule is the load-bearing part: a module reached
*only* through `INSTANCE` must not contribute to the flat name space, because its definitions
mean something only under the substitution — resolving one directly would silently use the
unsubstituted body and read the wrong module's variables. Only the root and its transitive
`EXTENDS` closure are visible.

The remaining ~1.3% is exponential inlining. Inlining re-lowers a body at each use, so
`F(x) == G(x) + G(x)` over `G(x) == H(x) + H(x)` doubles per level. Memoising on the identity
of already-lowered arguments collapses the common case, but misses when two structurally equal
arguments are lowered separately. Hash-consing the kernel closes it properly; until then a work
budget keeps the failure to a prompt diagnostic.

**The parser recognises TLA+; it does not enforce the fragment.** Milestone 1 originally
rejected `RECURSIVE` and structured proofs at parse time. Running the corpora showed that
conflates two jobs: 33 files use `RECURSIVE` and 47 carry TLAPS proofs, and all of them are
valid TLA+. What the *encoder* can handle is a question for the lowering pass, which knows
what the encoder is; rejecting in the parser also blocks the long-term superset goal. So the
parser now accepts both and records them in the surface IR, and the fragment check moves
here.

The analysis passes deserve a note. In Apalache they are *IR rewrites*, because a hint has no
other way to reach Z3. Here they are **hints handed to the solver**: skolemization marking
becomes a call into `nixie-solver/src/skolemization.rs`, expansion marking becomes an
instruction to the set theory in §3. Same analysis, no rewrite, no lost structure.

## 3. Sets as a theory, not a term blast

Apalache's `oopsla19` encoding turns every set into an arena of cells plus O(n²) Boolean
membership variables *before* the solver sees anything; `CHOOSE` becomes a linear `ITE` chain
over every cell. The solver then spends its time rediscovering structure the front end already
knew exactly.

The transfer to make is the one bit-vectors and arrays already made in this repo: **eager
encoding → lazy theory**. `nixie-theories/src/set/` already has membership, cardinality,
subset and powerset propagators, and `docs/TUTORIAL_CUSTOM_THEORY.md` documents the plug-in
path into Nelson-Oppen.

- Membership becomes a watched propagator instead of 10⁵ Boolean variables.
- `CHOOSE` / `CherryPick` becomes a backtrackable **theory decision** with a real explanation —
  pick-on-demand driven by the SAT trail, i.e. ordinary model-based theory combination.
- Functions and records get the same treatment rather than being flattened to arrays first.

Soundness bar is the repo's usual one: an unjustified propagation yields `Unknown`, never a
verdict; every piece of theory state rolls back in lockstep on `pop`.

## 4. Cross-layer optimisations

Ranked by expected payoff. Each names the information, where it is known, and where it is
needed — the rest of the framing is in §0.

### O1. Symmetry — known exactly at the top, badly rediscovered at the bottom

TLA+ specs are saturated with symmetry over CONSTANT model values (`Perms(Proc)`). TLC
exploits it; Apalache largely declines to. That symmetry is a permutation group over
uninterpreted constants, which after encoding is a permutation group acting on the CNF. A
standalone tool must *rediscover* it by graph automorphism on a CNF the encoding has already
mangled — expensive, and it often fails.

`nixie-sat/src/symmetry.rs` already exposes `SymmetryGroup::add_generator`, `SymmetryBreaker`
and `MatrixSymmetry`, next to the `AutomorphismDetector::detect_symmetries()` path we would be
skipping. The front end hands the generators straight down. Clearest instance of the
principle; do it first.

### O2. Unbounded verification — a new answer class, not a speed-up

Apalache is a *bounded* checker: it cannot prove a safety property for all behaviours. You
hand-write an inductive invariant and check it at `--length=1`.

This repo has `nixie-spacer`: PDR/IC3, CHC, Craig interpolation, k-induction in `bmc.rs`,
`invariant.rs`, `generalize.rs`. Lowering `(Init, Next, Inv)` to a CHC system gives
**automatic inductive invariant inference for TLA+ specs**. For the common case — protocol
specs whose state is records over finite-domain and integer fields after CONSTANT
instantiation — this works with what is already in the crate. The thin part is specs whose
state variables are genuinely higher-order (sets of functions), where Spacer generalisation
over arrays/ADTs is weak. Prior art to mine: **IC3PO** and **mypyvy**, both symmetry-aware
invariant inference over uninterpreted sorts — which composes directly with O1.

### O3. Cross-step lemma replication in the BMC unrolling

Every BMC step encodes the *same* `Next` over renamed variables, so a black-box pipeline hands
the solver k structurally identical copies and it learns the same lemmas k times. In-process
we know the renaming map: a learned clause whose variables lie entirely inside one step's
frame can be replicated to every other step by renaming. Sound, cheap, and impossible
externally because the renaming is invisible there.

Transfer: clause sharing under symmetry (BreakID) crossed with IC3's frame-to-frame clause
pushing. This is a **heuristic** change, so `AGENTS.md` applies in full — it ships with a
matched null (replicate randomly chosen clauses at the same rate and size distribution),
≥10 seeds, tick counters not wall clock, and the reported number is treatment / matched-null.

### O4. One assumption-based solve instead of k enabledness solves

Apalache splits `Next` into symbolic transitions, then feeds each to Z3 *separately* under
`push`/`pop`, pruning with `--discard-disabled` — re-solving the shared subformula once per
transition per step.

In-process: encode all transitions once under selector literals and settle enabledness of all
of them in one solve, via `nixie-sat/src/assumptions.rs`, `backbone.rs`, and projected
enumeration in `allsat.rs`. Further: this problem shape *is* cube-and-conquer — `cube.rs` plus
`kitten.rs` (tick-budgeted sub-solver) give a lookahead splitter, and `clause_exchange.rs`
shares learned clauses across branches. Separate solver contexts cannot.

### O5. Types → intervals → bit-width → CNF encoding, with CEGAR on the width

Snowcat says `Int`, so Z3 gets unbounded `Int` and we are in LIA. But TLA+ specs are almost
always finitely instantiated, so most integers have provable finite ranges. Owning the stack
lets a front-end interval analysis choose a **per-variable BV width**, and then choose the
adder/comparator CNF encoding per operation. If a width proves too narrow the solver says so
and the front end widens — CEGAR on bit-width, reusing the machinery from
`docs/studies/2026-08-bv-mul-cegar.md`.

The cross-domain source is HLS bit-width inference and CBMC-style range analysis, moved to the
front end and wired to the encoder. Apalache structurally cannot do this: the width decision
lives in the encoder with no feedback channel back from the solver.

### O6. Optimal counterexamples via `nixie-opt`

Apalache returns whatever model the solver happened to produce, typically full of junk values.
With MaxSAT/OMT/Pareto in-process we can ask for the *shortest* counterexample, the one
minimising non-default state variables, or a Pareto front over (length, processes involved).
Counterexample delta-debugging expressed as a native optimisation query rather than an
external re-encoding loop.

### O7. Unsat cores → source spans, and invariant vacuity

Assert each TLA+ conjunct under a named assumption literal; `check_with_assumptions` plus
`minimize_unsat_core` then map `unsat` back to source spans at conjunct granularity. This also
buys **vacuity detection**, which Apalache lacks: if the minimised core never touches `Next`,
the invariant is trivially true and the specification is misleading its author.

### O8. Certifying TLAPS backend

`nixie-proof` exports Alethe, LFSC, and Coq/Lean/Isabelle. TLAPS discharges proof obligations
to backends. A monorepo can make Nixie a *proof-producing* TLAPS backend: obligation → SMT →
proof → Isabelle term that TLAPS checks independently. Apalache has nothing here; it is a
checker, not a prover. Given this repo's stance that correctness is existential, that is the
natural market.

### O9. Determinism end to end

`AGENTS.md` forbids wall-clock as a policy input; Apalache drives Z3 on wall-clock timeouts,
so its results are not reproducible under load. In-process, the model-checking search — which
transition to expand, when to abandon a step — runs on Nixie's tick counters, as `kitten`
already demonstrates for sub-solving. Whole-pipeline determinism is worth a great deal for a
verification tool: bug reproduction, CI stability, differential fuzzing.

## Long-term: temporal logic

Deliberately out of milestone 1, recorded so the IR does not foreclose it.

**Step 0 — establish the baseline honestly.** Apalache has *some* temporal-property support
(a bounded loop/lasso tableau encoding, behind a flag). Before scoping "superset", verify
against the current Apalache release exactly which fragment it covers and which fairness
constructs it handles. Do not design against memory of it.

**Step 1 — parity.** Match that bounded encoding: liveness-to-safety over a bounded unrolling
with an explicit loop-back selector (Biere/Artho/Schuppan L2S, the standard hardware
model-checking construction). `WF_v` / `SF_v` become fairness constraints on the lasso.

**Step 2 — superset, and the reason it is worth doing.** Bounded L2S proves nothing when no
lasso is found. The interesting target is **unbounded liveness**: well-founded ranking
arguments discharged through `nixie-spacer` (termination as a CHC problem, in the shape of
T2 / Ultimate / CPAchecker's ranking synthesis), with fairness as Streett/Büchi acceptance.
That is a capability neither Apalache nor TLC has, and it is reachable precisely because the
CHC engine is in the same process. It also inherits O1 directly — liveness proofs over
symmetric protocols are where symmetry pays most.

Constraint on milestone 1: keep levels and fairness constructs in the surface IR even though
milestone 1 rejects them, so the parser never has to be revisited for this.

## 5. Verification bar

A wrong `sat`/`unsat` is catastrophic here for exactly the reasons `AGENTS.md` gives, and a
model checker multiplies the blast radius. Three oracles, all cheap:

1. **Parser differential** — every file in the Apalache test suite and the public TLA+ examples
   corpus: accepted/rejected must agree with SANY, IR must be isomorphic.

   **Status: closed.** `bench/tla_parity/` runs SANY as an oracle over the sibling corpora
   (907 `.tla` files) and compares both directions. SANY is consulted, never linked — the same
   relationship `bench/z3_parity` has with Z3, and `deny.toml` still bans FFI.

   ```
   syntax:  903 both accept | 0 SANY-accepts-we-reject | 2 we-accept-SANY-rejects
   levels:  5 067 definitions compared over 684 files | 0 mismatches
              574 skipped as untrusted | 1 known SANY defect excluded
   ```

   The syntax gate is **one-sided** on purpose: every file SANY parses must parse here, but
   parsing more is allowed, because the target is a superset. The two extras are `\mod` as a
   definable operator — accepted with its own identity rather than aliased to `%`, so that
   `u \mod v == u` cannot silently redefine `%`.

   Level comparison covers only definitions whose level was actually *established*; a guess
   held against SANY measures the missing module resolution, not the level walk. The skipped
   count is reported every run and rising means coverage regressed.

   **Validate the oracle before believing it.** Three of the findings were defects in the
   comparison rather than in the parser: SANY extracts the standard modules into the JVM temp
   directory, so parallel runs sharing `/tmp` corrupt each other; SANY's multi-line per-file
   output interleaves when parallel processes share a pipe, which manufactured ~120 phantom
   level mismatches; and SANY itself reports `x * x` as *constant* for a state-level `x`,
   while every neighbouring operator is right. `METHODOLOGY.md` records all three.

   Every construct beyond the basics was found by this corpus, not by reading the grammar:
   junction-list-versus-infix, the `[`/`{` classifiers, labels (`P0 :: e`), subexpression
   references (`A!1`, `A!:`, `R!+(a, b)`, `Op1(2)!(3)!2!1`), operator-symbol declarations
   (`_++_`, `-._`), operators passed as values (`TestOpArg( - )`), `ASSUME`/`PROVE` sequents
   with `NEW`, structured proofs, nested modules, prose before the header and after the
   footer, digit-leading identifiers, and subscript-underscore adjacency. Reading the
   specification would not have produced that list.
2. **TLC differential** — TLC is explicit-state and exhaustive on finite models. On small
   instances it is a complete oracle for the symbolic checker, exactly the relationship
   `run_parity.sh` has with Z3. This is the soundness canary for the new layer and should be a
   gate, not an afterthought.
3. **Apalache differential** — same spec, same bound, same verdict; disagreements are bugs in
   one of the two and worth chasing either way.

Plus the standing gates: `cargo build --all-features`, `cargo nextest run --workspace
--all-features`, `clippy -D warnings`, `fmt --check`, `cargo doc -D warnings`, and
`./bench/z3_parity/run_parity.sh` for anything that touches the solver core.

## 6. Milestones

| # | Deliverable | Gate |
|---|---|---|
| 1 | `nixie-tla-syntax`: lexer, layout, Pratt parser *(landed, 905/907)*; level checker *(landed, under-reporting)* | Parser differential vs SANY on the corpus |
| 2 | Surface IR + KerA *(landed)* + lowering *(landed, 93.8%)* + `INSTANCE` *(landed)*; Snowcat typing, pass pipeline *(open)* | IR isomorphism on the same corpus |
| 3 | Naive encoding onto existing theories, matching Apalache's `arrays` encoding | Apalache + TLC differential agree on verdicts |
| 4 | O1 symmetry generators handed to `nixie-sat` | Matched-null discipline, ≥10 seeds |
| 5 | O2 CHC lowering to `nixie-spacer` | New answers on specs Apalache cannot decide |
| 6 | O3 set/function theory plugin | Verdict-preserving; encoding-size and conflict-count deltas |
| 7+ | O4–O9, then temporal | Per-item, as above |

Milestone 3 before anything clever is load-bearing: the naive encoding is what gives us an
oracle to test the clever ones against.

## 7. Open questions

- **Parser effort — answered.** `nixie-tla-syntax` accepts **905 of 907** files (99.8%) across
  the two external corpora (see below). The two rejections are invalid TLA+ that SANY rejects
  too. The grammar work is done; what is *not* done is level checking.
- **The operator precedence table is transcribed, not verified.** The common operators are
  high-confidence and pinned by a test; the exotic ones (`\wr`, `\sqcap`, `##`, `$$`, `??`)
  are not. Two errors were found this way — `\X` marked non-associative (rejecting the legal
  ternary product `A \X B \X C`), and `!!`, `:=`, `::=`, `\mod`, `\exists`, `\forall`
  missing altogether. Check the whole table against SANY before declaring the differential
  suite green.
- **Level checking is implemented, and deliberately under-reports.** `nixie-tla-syntax::level`
  computes constant/state/action/temporal levels and reports violations — but only those that
  do **not** depend on a name it could not resolve. Two things it cannot yet see would
  otherwise make it reject correct specifications: `EXTENDS` is not resolved, and operator
  levels use the max rule rather than full TLA+ *argument level constraints* (which is what
  catches `Op(x')` for an `Op` that primes its parameter). Every level therefore carries an
  "unresolved" taint that suppresses reporting.

  The direction is deliberate: it misses real violations and never rejects valid input, which
  is right for a front end whose rejections are user-facing. Levels now agree with SANY on all
  **4 541** definitions the parity suite can compare (§5).

  `LevelReport.definitions` carries the taint, and `trusted_level_of` returns `None` rather
  than a plausible default, so a downstream pass cannot mistake a guess for a fact.

  **Argument level constraints are implemented.** An operator's level is not a maximum over
  its arguments: `B(d) == ENABLED d` is a state predicate however high `d` goes, and
  `SVGElemToString(elem) == TRUE` *ignores* its parameter entirely. Each parameter now carries
  an exact level function on the four-element chain, obtained by evaluating the body once per
  level; built-in operators passed as values (`BoxTest([])`) carry theirs too. Both cases came
  from the parity run — the second was SANY disagreeing and being *right*.

  **`EXTENDS` is resolved** (`module::Loader`), so imported levels are exact — `EXTENDS`
  performs no substitution. `INSTANCE` is not: `I == INSTANCE N WITH v <- e` substitutes, and
  a substitution can lower a level, so instance members stay untrusted until the lowering pass
  can apply the substitution properly.

  Trusted coverage over the corpora went 76.8% → 89.6% of definitions.

  A downstream pass must still not treat "no level errors" as "level-correct".
- How much of Snowcat's inference is needed when `@type:` annotations are present? Parity says
  all of it; a staged path may accept annotated specs first.
- Does `nixie-spacer`'s generalisation hold up over the array/ADT state encodings O2 needs, or
  does O2 need a state abstraction first? Unknown until measured.
- Apalache's current temporal fragment — see Step 0 above.
