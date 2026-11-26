# Issue #44 — a wrong `unsat` from an inprocessing round inside a `push` scope

Found by the temporal lasso encoding (#29), which was the first workload
to query one `Solver` incrementally — eight depths under `push`/`pop`,
each with ~1400 scope-owned clauses (the negated invariant's Tseitin
encoding) — with inprocessing on (the shipped default).

## The symptom

`nixie-tla check --temporal=W --length=8` on a bounded counter answered
"no lasso of 8 steps or fewer violates `<>(x = 999)`" where an 8-step
lasso exists and is found by a fresh solver on the **same `TermId`s**
(`NIXIE_TLA_FRESH_PROBE`). Per-depth bisection: no single earlier query
poisons the solver; it takes several, and only `NIXIE_SMT_NO_INPROC=1`
fixes it. The dumped depth-8 query is `sat` in the CLI.

## Where it is not

Each of these was checked, on fresh binaries, and is sound:

* every clause-level mutation of the round (33 on this query): outer
  clause by outer subsumer, each verified by hand (`(110∨19∨113)` ∧
  `(¬19∨110) ⊨ (110∨113)`, …);
* the final clause database (base + scope + 1245 learned): satisfiable,
  per z3;
* the level-0 trail at round time (103 units): consistent with every
  clause, per z3; the three `force_level0` units transitive reduction
  derives are entailed by base + scope originals.

The `unsat` comes from the **theory's final check** — a conflict over 14
level-0 literals after a search of dl=1629 — i.e. the solver's Boolean
database stays satisfiable while its theory-side view of the level-0
assignment does not. That is state the round leaves behind, not a clause.

## A note on bisecting with knobs

Half of the bisect above was first run on **stale binaries**: `nixie-sat`
edits did not always trigger a rebuild (cargo's fingerprint missed them
under the concurrent builds on this machine), so several early
"knob X does not fix it" results were the unchanged build answering. The
results recorded here are from builds verified by `strings` on the binary
for the knob's name, with `touch nixie-sat/src/lib.rs` before each build.
Lesson for the next bisect: verify the knob is **in** the binary before
trusting a negative.

## The mechanism, as far as it was pinned

Inside a `push`, every pass of the round sees a database and a binary
implication graph that mix **permanent** clauses with the scope's own
(the query's encoding), and a level-0 trail that includes the scope's
units. `transred` retired six permanent original binaries through paths
over scope-owned learned binaries (lost for good at the next `pop`);
the subsumption round strengthened permanent clauses; both are
Boolean-sound *as clauses* (the transitive-reduction gate — no
retirement of a permanent clause through a scope-owned edge — and the
subsumption gate — no scope-owned subsumer — together still left the
wrong answer in place). Skipping **either the subsumption or the
vivification pass** alone removes it; skipping transitive reduction does
not; gating the propagation-head rewind after a strengthening does not.
Those two are the passes that shrink clauses in place inside the scope,
and the failure is not in the clauses (the final database is satisfiable)
but in solver state the round leaves behind. The remaining
interaction sits in the SAT–theory bookkeeping (rewatch/`reset_propagation_head`
re-propagation at level 0 inside a scope, failed-literal units the
theory's atom table is told about under the scope's level) and is not
clause-local.

## The fix

`Solver::inprocess_inner` returns early when `assertion_levels.len() > 1`:
**an inprocessing round runs only at base scope.** Every pass assumes the
base formula is fixed — a retirement is justified by clauses that must
stay, a failed literal by the binary graph as it stands, and the
re-propagation afterwards by the level-0 trail being the base trail — and
under a scope none of that holds. This is cadical's own discipline (it
never inprocesses under assumptions) and extends the two gates the
solver already had (`elimination_allowed`, the pure-literal pass), each
of which was found the hard way. Rounds still run between queries; the
fresh-solver paths (the CLI, the corpus harness) are unaffected.

Pinned by `nixie_sat::…::inprocessing_round_is_a_no_op_inside_a_push_scope`
(the round leaves the database untouched in scope) and
`nixie_tla_check::…::a_lasso_is_found_with_inprocessing_on` (the depth-8
lasso, end to end, with inprocessing on).

## The cost, measured

Corpus A/B (905 modules, 20 000-conflict budget): no-violation 70 → 68,
undecided 37 → 39, everything else identical. The two cells are
`test33.tla` (`x \in [1..6 -> 1..7]`, 117 649 functions) and
`Barrier.tla` (`pc = [p \in ProcSet |-> "b0"]`): on these, in-scope
rounds were doing work the base-scope rounds do not recover, and the
search now exhausts the budget — an honest `Unknown` where it was a
`NoViolationWithin`. Both are function-set enumeration shapes for the
solver line to recover; the trade is deliberate: a wrong `unsat` on a
violated liveness property is the one failure the project forbids above
all, and an `Unknown` under budget is the answer the corpus counts as
such.

## What #44 is not

* **"~200× slower than the CLI"** was a measurement artifact: the dumped
  query was the *invariant* query (`unsat`, 0.3 s in the CLI); the slow
  solves were the **deadlock search** and, with deadlocks off, the
  **full-length-behaviour probe** — two `sat` searches the dump never
  contained. The CLI takes the same 41 s on that probe's formula.
  `nixie-tla --temporal` now skips both by default (`--deadlock` turns
  the search back on): a lasso is itself a full-length behaviour, so "no
  lasso of ≤ k steps violates P" already says what the probe would.
* The self-referential `ite` one-liner is `sat` on current main.
* What remains is **performance**, identical in CLI and library: a
  refutation over `ite`-in-`Int` with a 51-way range (`x ∈ {v ∈ Int : 0 ≤
  v ≤ 50}`, `x' = ite(x ≥ 50, x, x+1)`) takes nixie 10/14/24 s at depths
  4/5/6 against z3's < 1 s (`longloops_d7_full_length.smt2`, `d6_j6.smt2`).

## Also fixed here

`skolemize_walk`'s `debug_assert_eq!(values.len(), m)` (from the first #20
piece) compared the pre-children stack length **after** the children had
pushed — an invariant no non-leaf node can satisfy, so every debug build of
a spec with a set-valued variable tripped it. The `Mark` frame was
vestigial (its doc said it inserts into the value stack; it never did).
The exact invariant now lives on `Rebuild`: `values.len() == base + n`,
one value per child. All tla tests pass in debug for the first time.
