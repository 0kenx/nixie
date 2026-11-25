# Issue #29 — Temporal properties: the lasso encoding (step-0 study + landing)

Sources read before designing, as the issue directs:
`tla-pp/.../temporal/LoopEncoder.scala`, `.../TableauEncoder.scala`,
`passes/.../pp/TemporalPassImpl.scala`, `docs/src/adr/017pdr-temporal.md`,
and the 26 `--temporal` cells of `test/tla/cli-integration-tests.md`
(`:1575-1670`).

## The fragment Apalache supports

* **Tableau operators**: `[]`, `<>`, and every **propositional** connective
  between them (`~`, `/\`, `\/`, `=>`, `<=>`, `IF/THEN/ELSE`, with state
  predicates as leaves). `~>` is removed by the Desugarer into
  `[](F => <> G)` before the tableau sees it.
* **Explicitly not supported** (`TableauEncoder` throws): `WF_e(A)`,
  `SF_e(A)`, `\EE`, `\AA`, guarantees (`-+->`). There is **no fairness
  handling**; a fairness construct is an error, never a dropped conjunct.
* An `--inv` naming a temporal-level formula is **exit 255**.
* `NoLoopsNoProblems.FalseLiveness == <>(x > 52) => [](y > 100)` — an
  implication whose **sides** are temporal — is a cell, so `=>` is
  propositional at the temporal level, as above.

The 26 cells collapse to: `Liveness` passes (OK), `FalseLiveness` fails
(exit 12) — or both pass when the system has no loop at all.

## Length semantics

`LoopEncoder.addLoopLogic` turns `(Init, Next)` into a **lasso**:

* a Boolean `__InLoop`, false initially, **monotone** (`InLoop => InLoop'`)
  and Boolean-typed;
* one `__saved_v` per state variable, frozen at loop entry:
  `__saved_v' = IF InLoop' = InLoop THEN __saved_v ELSE v`;
* `__LoopOK == InLoop /\ \A v : v = __saved_v`.

`InLoop` becomes true on the step **into** the loop's first repeated
state, so the loop body is the suffix from the state where `InLoop` first
holds to the state where `LoopOK` holds (where the variables equal their
saved copies). The loop therefore has **≥ 1 state**; `LongLoops` pins
that the loop can be longer than one state and `LongPrefix` that the
prefix can be nonempty. The checked property is the **invariant**
`__LoopOK => __<prop>_init`, i.e. "no lasso of length ≤ k on which the
negation of the property is accepted".

## The tableau (Biere–Artho–Schuppan, as `TableauEncoder` writes it)

Per temporal **node** `N` of the property's syntax tree:

| piece | role |
|---|---|
| `__temporal_N` | the node's truth value **at the current state of the unrolled path** |
| `__temporal_N_unroll` | its value assuming the path continues around the loop |
| `__temporal_N_unroll_prev` | the same, one step back — the lookback the loop close needs |

Init: `unroll = prev = TRUE` for `[]`, `FALSE` for `<>`. Step:

```
node        <=> outer(arg, node')                       -- plain LTL unrolling
unroll      <=> outer(prev, inner(InLoop', arg))        -- loop-aware value
prev'       = unroll
```

with `outer = /\`, `inner = \/`, `innerInLoop = ~InLoop'` for `[]` and
`outer = \/`, `inner = /\`, `innerInLoop = InLoop'` for `<>`. Note the
prime on `InLoop` in the unroll equations ("argue about `InLoop'`, not
`InLoop`": `InLoop` is true from the first state *after* the loop's
start, so the unroll variables start accumulating one state early — sound
because `unroll` only has to be right at the close).

Propositional nodes get `__temporal_N <=> op(args)` in both `Init` and
`Next`. At the close (`LoopOK`): `unroll => node` for `[]`, `node =>
unroll` for `<>`, and `prev = unroll` (the last state's `unroll` is not
checked by `Next`, which can only speak about the current state).

The property becomes `__LoopOK => __<prop>_init` where `__<prop>_init` is
the root node variable captured in `Init` and `UNCHANGED` thereafter.

## Nixie's realisation

Apalache rewrites the **module** (new `VARIABLE`s, new `Init`/`Next`,
a new invariant) and runs its ordinary checker. Nixie's lowerer refuses
temporal operators at the kernel door — by design, "spec structure, not a
kernel expression" — and that stays. The seam chosen here:

* `nixie_tla::Lowerer::lower_temporal(&Expr)` walks the **syntax** of the
  temporal formula; every **state-level leaf** is lowered by the ordinary
  `lower` (full inlining, instance substitution, typing), and the
  temporal structure comes back as a `Temporal` tree
  (`Node / Always / Eventually / Not / And / Or / Implies / Equiv / Ite`).
  Leaves are checked to be state-level; a prime, a fairness construct, a
  temporal quantifier, `-+->` or `\cdot` is **refused by name**.
* `nixie_tla_check::temporal` turns that tree into the lasso + tableau as
  **kernel terms over synthetic state variables** (`__InLoop`,
  `__saved_<v>`, `__temporal_<i>[_unroll[_prev]]`, `__<prop>_init`), and
  hands `Bmc` the rewritten `Init`/`Next` and the state invariant. The
  rest of the pipeline — sort inference, frames, encoding, replay, ITF —
  runs unchanged. `__LoopOK` is a `Kera` term referenced from the
  invariant (no definition-unit rewriting needed).

### Where this differs from Apalache, and why

* The tableau variables are **per property node**, as in Apalache, but
  named by index (`__temporal_0`, …) in post-order — Apalache uses a
  generator plus the printed node; an index is deterministic and
  collision-free, which the reproducibility of a corpus measurement
  needs.
* The `__saved_` copies cover **every** state variable of the spec plus
  every tableau node variable (Apalache: ditto, via `createAllVarCopiesInLoop`
  applied to the extended variable list).
* Fairness: refused by name, exactly as Apalache refuses it (with a
  clearer message). Never dropped — a dropped fairness conjunct invents
  counterexamples.

## Soundness hazards, as the issue lists them

* **A lasso must replay.** The counterexample is an ordinary trace of the
  *rewritten* spec; the evaluator replays `Init`/`Next` step by step on
  it. The loop-closing equality is **in the invariant** the solver had to
  satisfy (`__LoopOK`), and the replay re-evaluates `__LoopOK` on the last
  state independently — so a lasso whose close does not hold is rejected
  before it is ever printed. The ITF trace carries the `loop` field
  (ADR-015) with the loop-start index read off `__InLoop`.
* **"No lasso within k" is not a proof.** The outcome is
  `NoViolationWithin(k)` on the rewritten spec, printed as *"no lasso of
  k steps or fewer violates `P`"* — never "property holds".
* **Unhandled constructs decline.** See above.

## Landing: what was built, what the cells say, and the three solver findings

**Built** (`nixie-tla-check/src/temporal.rs`, `Lowerer::lower_temporal`,
`Bmc::prepare_temporal`, `--temporal=NAME`, `--max-conflicts=N`):

* the lasso + tableau exactly as `LoopEncoder`/`TableauEncoder` write it,
  on kernel terms; the rewritten `Init`/`Next` and the state invariant
  `__LoopOK => __<prop>_init` flow through the ordinary pipeline;
* the ITF `loop` field (ADR-015), read off `__InLoop`; the tableau's
  bookkeeping hidden from `vars`, `__InLoop` kept;
* `--inv=<temporal>` → **255** (the integration corpus's cell), and
  `--temporal` + `--inv` refused;
* the outcomes worded as what they are: *"no lasso of k step(s) or fewer
  violates P; this is a bound, not a proof"*, and `NoError (no violating
  lasso within the bound)`;
* `NIXIE_TLA_DUMP_QUERY=<dir>`: each depth's query as a standalone
  `.smt2` — the instrument that found everything below.

**Three encoding bugs caught by the cells before landing**, each worth
recording because each made a *wrong "holds"*:

1. the `unroll` recurrence was primed (`unroll'`); Apalache's is on the
   **current** state reading only `InLoop'`. Primed, the accumulation
   shifts one state and the close's `unroll => node` is vacuous on every
   box — `[](x = 9)` on a two-cycle "held".
2. the `unroll`/`_prev` auxiliaries had frozen copies. Apalache freezes
   **only the node variable**; freezing the lookback too makes `prev@close`
   disagree with the recurrence's own `prev' = unroll` on every lasso
   longer than one state — the lasso never closes, and every box "holds".
3. the auxiliaries were declared as rigid constants, so `__InLoop` could
   never change and no lasso closed at all.

Plus one lowerer gap: `[](…)`'s operand arrives under `ExprKind::Paren`,
which the temporal walk must see through; and a state-level leaf is
scanned for a **prime anywhere below it** (`~(x' = x)`), not just at the top.

**The cells.** Against the honest oracle (`NIXIE_SMT_NO_INPROC=1`, see #44)
at `--length=10`:

| spec | property | Apalache | Nixie |
|---|---|---|---|
| ManyBoxes | Liveness / FalseLiveness | 0 / 12 | **0 / 12** |
| ManyDiamonds | Liveness / FalseLiveness | 0 / 12 | **0 / 12** |
| DiamondBox | Liveness / FalseLiveness | 0 / 12 | **0 / 12** |
| LongPrefix | FalseLiveness | 12 | **12** (replayed lasso) |
| LongLoops | FalseLiveness | 12 | **12** (replayed lasso) |
| LongPrefix | Liveness | 0 | `Unknown` under budget |
| LongLoops, NoLoopsNoProblems | Liveness, FalseLiveness | 0 | timeout |

**8/12 agree; the other 4 are `Unknown`/timeout, never a wrong verdict.**
All four are the `Range == {v \in Int : 0 ≤ v ≤ 50}` family — 51-member
ranges over two or three variables — where the in-process solver is
~200× slower than the CLI on the *same* assertions (dumped and diffed),
and on one query wrong (a `sat` answered `unsat`). That is **#44**, filed
with minimal reproductions; the encoding is verified against the CLI on
every dumped query.

**A pre-existing wall the cells needed, closed here**: `{v \in Int : lo ≤ v
≤ hi}` — a filter over an infinite set with two-sided **ground** bounds —
has exactly `lo..hi` for members. The encoder enumerates that range and
still evaluates the predicate per candidate (`present`); the evaluator
(`Filter` arm) does the same, so a bound read wrongly could only offer a
non-member, never drop one. Without two-sided ground bounds the refusal
stands. One shared definition (`kera::bounded_int_range`).

**Not done, by the issue's own plan**: WF/SF on the loop (step 3) —
Apalache refuses fairness too (`TableauEncoder`: "Handling fairness is not
supported yet!"), so refusing by name is parity; `nixie-spacer` ranking
functions (step 6) — later, Nixie-only.
