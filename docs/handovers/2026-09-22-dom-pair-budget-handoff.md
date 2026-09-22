# Handoff: the `$dom` wall's first slice — pair budget named and lifted, the don't-care-completion follow-up precisely located (2026-09-22, later)

**From:** the session that took item 1 of
`docs/handovers/2026-09-22-array-alias-soundness-handoff.md` — the
`$dom` set-atom wall — through its first slice and into the second.
One commit landed (`345ecfec`), one wall remains, and that wall is now
located to a single function with a written recipe. Read `AGENTS.md`
first; read the array-alias handoff before this one — the two-array
`Unknown` this session started from is that document's item 1.

## What landed (345ecfec)

**The set pair budget is a named cap, default 256.** The `Unknown` on
the standard multiprocess PlusCal shape was *not* conceptual: the
opaque-pair budget (fixed 48; each pair costs a witness element and
`sets × pairs` axioms) tripped the set honesty gate on every depth-4
unrolling, because every function-valued variable contributes one
`$dom` set-equality per step (`UNCHANGED`/`EXCEPT` preserve the
domain, so the translation asserts `x@k$dom = x@k+1$dom` per step per
variable). Two variables × depth 4 ≈ 45 atoms; corpus BMC queries never
reach 48, which is why nothing there had moved (verified identical
before/after: 13 clean / 1 flagged / 2 undecided).

- `set_pair_budget` through `caps::cap`, `caps::report_fired` on
  overflow, one hoisted `max_set_pairs()` both `reduce` and
  `survey_for_model` read — agreement between the two is the reason it
  is one function.
- The pin moved with it, and the pin is the real content (below).

## The finding the fix exposed — the next owner's actual target

With the budget gone, the two-array shape produces **a 4-step
`Violation` whose decoded trace the independent replay rejects**
(`Verification::NotReplayed`). Diagnosis, verified at solver level with
the landed `brancharr` example:

1. Nothing in the query ever **reads** `x[1]` — the translation writes
   it at the symbolic index `self`, and no guard or invariant selects
   `x` at any point. The array theory therefore leaves that point
   unconstrained (arrays are total; equality is extensional; RoW
   lemmas exist only for observed reads).
2. Two branch-update atoms go **simultaneously true through no-op
   writes** (`x@1 = x@2` from the UNCHANGED branch and
   `x@2 = store(x@1, self, v)` from the A branch are consistent when
   the store writes the value already there). The model is a *correct*
   model of the encoded formula.
3. The per-point trace decoder completes don't-care points
   **independently of the taken branch** — each state's array value is
   read back point-by-point from the model, so a point the query never
   constrained gets an arbitrary completion, and the completed trace
   satisfies no disjunct of `Next`.
4. The replay — the evaluator, a separate TLA+ implementation, checking
   `Init`/`Next`/`¬Inv` over the *decoded values* — rejects it. That is
   `bench/tla_bmc/METHODOLOGY.md` §4 (the function domain an SMT array
   does not carry) with a concrete, minimized face, and the replay
   catching it is the system working as designed.

The test pin (`a_two_array_pluscal_spec_never_answers_a_false_clean`)
now asserts the full contract across all three eras of this shape:
false `NoViolationWithin` (the alias bug) → honest `Unknown` (the
budget) → `Violation{step:4}` AND `NotReplayed` (now). Never a bare
clean; never a trusted unverified violation.

### The follow-up recipe (one function, already scoped)

Make the trace decoder complete don't-care points **consistently with
the taken branch**: in `nixie-tla-check/src/trace.rs`'s array arm, when
a domain point has no select the query built, do not mint a fresh
`select(term, idx)` and hope — walk the variable's **model-assigned
store chain** (the `2026-09-14` fix guarantees the assignment exists
for any equality the SAT model committed true, including branch-local
ones — verified in this session with `brancharr`, which was *rewritten*
because its first version passed `TermId`s from the wrong
`TermManager` into `Context::assert` and tested garbage; use
`execute_script` for solver-level probes) and read the point's value
from the chain under the *same* model (the chain's index and value
subterms evaluated through `Model::eval`, exactly as `select_in` in
`solver/types.rs` already does for points the query did read). Success
criterion, already pinned: the two-array test's `NotReplayed` becomes
`Replayed` with no other pin moving; `pcal_check_verified` (added in
`345ecfec`) gives the test both halves. Then DiningPhilosophers
`ExclusiveAccess` at depth ≥4 — the classic the whole arc is named for
— should flip from its 4-step clean to replayed verdicts at deeper
bounds, and `bench/tla_pcal`'s state-parity harness (TLC) confirms any
new verdict is *right*, not just different.

## Verification bar (all green on `345ecfec`)

12,289 workspace tests; Z3 parity 100%, 0 decisive mismatches (z3
4.16.0); perf gate PASS (counters 1.000, wall 0.95, baseline
`28e82c65`); `tla_bmc` corpus identical before/after; clippy
`-D warnings`, fmt, doc clean. Binaries cached at
`precompile/345ecfec/` (`nixie`, `nixie-tla`).

## Where this leaves the map

1. **Don't-care completion in the trace decoder** — the recipe above;
   the one function standing between a rejected and a replayed
   counterexample for every translated multiprocess spec.
2. The `Bag`-sort bridge / lambda-shaped function encoding — unchanged
   from the earlier handoffs; design note first.
3. Delta-propagation proof obligation (study item 85) — waiting.

## Traps (new this session; standing ones still stand)

- **`Context::assert` takes `TermId`s from the Context's own
  `TermManager`.** Passing ids built in a separate manager silently
  asserts unrelated terms — `check: Sat` on garbage, no warning. For
  solver-level probes use `execute_script` with SMT-LIB text (the
  rewritten `brancharr` is the template). Cost me a wrong conclusion
  once; the rewrite found the truth in minutes.
- **/media/data swings to 100% during a workspace test build** (94G of
  target in ~5 min; other agents build concurrently). `rm` of the
  target's `debug/` (or the whole relocated target) recovers it
  instantly; watch `df` between build phases, and never leave a
  relocated target behind.
- `git worktree add` on a branch already checked out fails — use
  `--detach` + rebase, or `-B` in a fresh worktree.
- The main-contention landing recipe from the previous handoff still
  applies; the retry loop landed `345ecfec` on attempt 1 once the
  resident agent's tree went clean.
