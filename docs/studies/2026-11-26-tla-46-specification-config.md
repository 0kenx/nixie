# Issue #46 – `SPECIFICATION Spec` is read as `Init /\ [][Next]_vars`

A TLC configuration names the system in one of two ways, `INIT Init` with
`NEXT Next`, or `SPECIFICATION Spec`. On `main` @ `8f3d9cc6` the second was
refused outright (exit 255: "a temporal behaviour spec; this checker needs
INIT/NEXT"). In the three local corpora, **221 of 385 `.cfg` files** say
`SPECIFICATION`; 184 of them sit beside a module file and were refused at the
configuration stage. The rest of this records what they are now, what was
found on the way, and what is still declined.

## What the two reference tools do

* **TLC** (`tlc2.tool.impl.SpecProcessor.processConfigSpec`) walks the
  conjuncts of the formula. Each constant- or state-level one becomes an
  initial predicate; the single `[A]_v` contributes **`A`, the action inside
  the brackets**, as the next-state predicate; any other temporal conjunct is
  kept for liveness checking; an action-level conjunct is an error
  (`TLC_CANT_HANDLE_CONJUNCT`), as is `[]P` over a state predicate. A bare
  name whose body is temporal is descended into. Fairness in the formula is
  used for liveness properties only: **invariants are checked on the states
  `Init`/`Next` reach, whatever the fairness**.
* **Apalache** (`ConfigurationPassImpl.extractFromSpec`) flattens nested
  conjunctions, requires exactly one `Init` and one `[][Next]_vars`, both
  bare definition names, in either order – and **warns while ignoring**
  fairness ("Fairness constraints are ignored by Apalache: …"). Anything
  else is a configuration error.

## Why `[][Next]_vars` is `Next` for this check

`[Next]_vars` is `Next \/ UNCHANGED vars`. A stuttering step leaves the state
as it was, so the states a behaviour of `Init /\ [][Next]_vars` visits are
the states a behaviour of `Init /\ [][Next]` visits – the same sequence minus
the repeats. A state invariant holds of one iff it holds of the other. So
does the deadlock question as both tools pose it: a state with no
`Next`-successor is reported as a deadlock under `SPECIFICATION Spec` exactly
as under `INIT`/`NEXT` (TLC's well-known behaviour for a spec that permits
stuttering – the fix is `CHECK_DEADLOCK FALSE`, in the file; Apalache's
`--deadlock` default). Checking the two configurations the same way is
parity, not an approximation. The subscript is not consulted.

## The policy on the rest of the formula

The first cut refused everything but the two roles, fairness included, each
clause named and located. The corpus moved that decision: **98 of the 184**
refused configurations carry a fairness conjunct, almost all of them the
per-process idiom

```tla
Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))
```

and both reference tools check their invariants regardless.

* **Fairness is reported, not assumed.** A fairness clause restricts
  behaviours by their infinite tails; it removes no state from any finite
  prefix a bounded check examines, so for an invariant – and for the deadlock
  question – the safety fragment gives the same answer. The CLI says so on
  stderr (`warning: the specification states fairness (…); it is not assumed
  here … no liveness is checked (issue #47)`) and checks the invariants.
  For a **liveness** property it may not assume the clause away: an unfair
  lasso is not a behaviour of the specification, and a lasso search that
  ignored it would report one. `--temporal=P` under a fair specification is
  declined (75), naming the clauses.
* **Any other temporal conjunct is refused by name.** `[]P` excludes states,
  `[]A` excludes steps, `<>P` and `P ~> Q` say things no bounded unrolling
  reproduces: ignoring one changes the question. So is an action-level
  conjunct, a second `[][A]_v` (TLC refuses that too), and a formula with no
  transition or no initial predicate. Each is printed with its text and its
  place in the module.

## Where the roles are read

The formula's names mean what they mean **where the formula is defined**.
`MC.tla` EXTENDS the specification and redefines `Init`; `Spec` in the
extended module still starts at the extended module's `Init`. TLC and
Apalache read the formula in its own module; resolving `Init` at the root
would check the model's `Init` against the specification's `Next`. The
decomposition returns the defining module (`SafetyForm::home`), and the
checker reads `init`/`next` in that module's scope – through the instance
machinery, as an instance with no `WITH`, so the module's own definitions
take precedence over anything the extending module redefines under the same
name. `INIT Init` / `NEXT Next` keep reading the root's override: two
configurations, two specifications, two verdicts (pinned by a test).

The formula is found wherever a bare name resolves: the root, an **unnamed**
instance (`INSTANCE ChangRoberts` – `tlaplus-examples`' own model files),
or a module the root transitively extends (the Toolbox's generated
`spec_146427254083041000 == Spec`). A member of a *named* instance
(`Spec == I!Spec`) is declined by name: the roles behind it would have to
resolve through the same substitution, a path this lookup does not take.

## Three defects found on the way

1. **An action invariant reached through `EXTENDS` or an instance was
   reported `Unknown` on every check.** Its level was read from the root
   module's report, which lists only the root's own definitions, so it came
   back untrusted and was classified a state invariant. A state-invariant
   query asserts no transition into the step it tests; the free next state
   satisfied the negated action; and the replay gate – which refuses to
   confirm a trace that does not replay – turned that into `Unknown`
   (exit 255) for a specification that holds. The level is now read from the
   **defining** module's report, with the lowered term (does it contain `'`?)
   as the fallback.
2. **`\subseteq` minted a fixed binder.** Every expansion used `sub#0`, so a
   formula with two subset relations failed the binder-uniqueness invariant
   and the whole specification was declined ("`Next` could not be lowered:
   the binder `sub#0` occurs more than once") – 23 of the 184 configurations,
   `bosco` and the German protocol among them. The binder now comes from the
   lowerer's own counter.
3. **Roles defined in an extended module did not resolve at all.**
   `--init=Init` with `Init` in a module the root extends was "no
   zero-argument definition named `Init`". `lower_named` now searches the
   `EXTENDS` closure (nearest first) and lowers in the defining module's
   scope; the `.cfg`'s `CONSTANT x = v` and `x <- Def` reach inside it, as
   they do for an instance.

## Corpus A/B

### The configurations (`check --config=<cfg> --length=4 --max-conflicts=20000`)

385 `.cfg` files of `tlaplus-examples`, `apalache/test` and
`communitymodules/tests`; 45 name a module that is not `<cfg>.tla` and are
skipped. Release binaries, `timeout 120`, ten at a time. Baseline:
`precompile/8f3d9cc6…/nixie-tla`. Arm: this commit.

The 184 configurations refused on `main`:

| outcome | count |
|---|---:|
| `NoError` | 20 |
| `ExecutionsTooShort` | 3 |
| `Unknown` (20 000 conflicts exhausted) | 19 |
| timeout (120 s wall) | 17 |
| declined later, exit 75 | 101 |
| does not type check, exit 120 | 20 |
| nothing to check (no invariant, `CHECK_DEADLOCK FALSE`), 255 | 4 |

All 385, before → after: `NoError` 38 → 58, `ExecutionsTooShort` 0 → 3,
`Unknown` 5 → 22, timeout 0 → 19, exit 75 98 → 199, exit 120 12 → 32, exit
255 185 → 5. **Zero verdict regressions**: every cell that had a verdict
keeps it. The two non-`SPECIFICATION` cells that moved went `Unknown` →
timeout, i.e. the same budget-exhausting search under a loaded machine.

What the 101 later declines are (each the corpus's own blocker, now reached
through the configuration): lowering 37 (25 other, 9 inline-depth, 3 step
budget), encoding 47 (15 no candidate list, 10 function-as-value, 9 other, 8
non-literal bound, 5 function set), 15 refused at the formula itself (8
another temporal clause, 6 an inline next-state action
(`[Next \/ Terminate]_v`), 1 naming no definition), 2 elsewhere. The
timeouts are wall-clock, not verdicts.

### The modules (`bmccheck`, `NIXIE_BMC_LIST=1`, depth 4, 20 000 conflicts)

907 modules of `tlaplus-examples` + `apalache/test`, three arms, so that the
library's effect and the harness's are attributed separately: `main`'s binary
(`precompile/8f3d9cc6…`), this commit's library under the **old** harness, and
this commit's library under the harness that now reads `SPECIFICATION`
configurations (and resolves `INVARIANT` names through `EXTENDS`).

| arm | no-violation | violation | deadlock | undecided | blocked | skipped |
|---|---:|---:|---:|---:|---:|---:|
| `main` | 68 | 21 | 5 | 39 | 185 | 589 |
| new library, old harness | 68 | 21 | 5 | 39 | 185 | 589 |
| new library, new harness | **77** | 21 | **7** | **62** | 277 | 463 |

* **Library effect: 0 of 907 modules change class.** The levels-from-`check_spec`
  change, the roles through `EXTENDS` and the `\subseteq` binder move nothing
  on the convention-driven harness; the first row reproduces the standing
  numbers of the #44 landing exactly.
* **Harness effect: 126 modules move, every one out of `skipped`** – 92
  blocked (with the corpus's own reason: 21 lowering, 15 types, 41 encoding,
  14 the formula itself, 1 a configuration replacement), 23 undecided, 9 no-violation, 2 deadlocks (the two
  `MCConsensus` model files, at step 1). No module that had a verdict loses
  or changes it. The 9 new no-violations are the `HourClock`, `Channel`,
  `ABCorrectness`, `TCommit` and `APReplicatedLog` families; the 23 undecided
  are the German protocol, the asynchronous channels, `APtcp`, `APTokenRing`.

## Tests

`nixie-tla-syntax`: 19 (`tests/behavior.rs`) – the canonical form in either
order, through parentheses, bulleted lists and abbreviations; quantified
fairness; every refusal by name; the module the formula lives in (root,
open instance, `EXTENDS`, a named instance declined); the brief renderer.
`nixie-tla`: the `\subseteq` binder. `nixie-tla-check`: 8 CLI cells (the
issue's reproducer, the deadlock question, fairness announced for invariants
and refused for liveness, every other clause declined, `--init`/`--next`
beside a `SPECIFICATION` refused, the model-file shape) and 3 library cells
(`Scope`, roles through `EXTENDS` with the configuration applied, the action
invariant in an extended module).

## Remaining

* A next-state action written inline (`TerminatingSpec == Init /\ [][Next
  \/ Terminate]_v`) and a second state-level conjunct (`PrintT(R) /\ Spec`,
  which TLC conjoins and Apalache refuses): 14 configurations, declined by
  name at this commit. Both became roles in the commit that followed
  (`RoleSource::Expr`; see the census in the landing comment on #46).
* `PROPERTY` in a configuration was, at this commit, still read and not acted
  on – a wrong-verdict-shaped gap (a run that reports `NoError` having checked
  the invariants while a liveness property sat unexamined in the file). Closed
  in the next commit, `2026-11-26-tla-config-property-passes.md`.
* Fairness for liveness is issue #47.
