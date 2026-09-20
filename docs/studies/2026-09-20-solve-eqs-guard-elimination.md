# The `solve_eqs` pre-pass executed — guard-equality elimination lands; the nec-smt member folds; three soundness bugs found on the way (2026-09-20)

**Date:** 2026-09-20. **Item:** the attribution-arc handover's open
item 3 (time-boxed): *"the `solve_eqs` pre-pass (handed off with
complete diagnosis): the nec-smt member's residual is a
self-referential priority-select; the memo proved the cost is the case
splits, not sharing. Entry points: guard-equality elimination before
the walk, or split ordering."*  This study is the execution record;
where it disagrees with `2026-09-19-smt-perf-gap-attribution.md`'s
diagnosis, this study wins (it has the fold).

## The verdict up front

**The class closes.** `(simplify <goal>)` on
`nec-smt/small/int_from_list/prp-3-21.smt2` (the ninth session's
fuel-exhausting member) now folds to **`false`** — the residual was a
10.5 KB let-shared DAG whose walk burned the whole 200 k-step budget;
the fold is **11 ms** (z3: 50 ms).  The 724 KB original repro
(`large/checkpass/prp-43-49.smt2`) folds to `false` in **33 ms**
(release build; z3's plain `simplify` also folds it to `false`).

Across `nec-smt/small` (37 members): 20 agree with z3's `(apply
simplify)` fold decision, **11 members nixie folds to `false` where
z3's plain simplify leaves a residual — every one verified `unsat` by
z3's own check-sat** (nixie strictly stronger, zero wrong answers), 4
`print_file` members time out in the downstream printer/substitute
frontier (pre-existing: the old binary times out there too), and the
one `sat` member (`config_read_line/prp-1-31.smt2`) correctly leaves a
residual — after the fix below.

## What "the `solve_eqs` family" actually is (the z3 ground truth)

The parameter sweep of the seventh session named three "individually
necessary families" (`:ite_extra_rules`, `:push_ite`, `:solve_eqs`).
On z3 4.16.0 the nec-smt member's fold is decided by exactly ONE
parameter: `:ite_extra_rules false` leaves a 72 KB residual (everything
else, including `elim_ite` and `push_ite_arith`, is immaterial).
`ite_extra_rules` gates z3 `bool_rewriter`'s ite rule set, whose
load-bearing core for this class is `try_ite_value` — **solving the
equality over the ite's conditions instead of case-splitting them**:

* `(= (ite c t e) v)`, `t` a value `≠ v`  → `(and (= e v) ¬c)` — the
  equality moves DOWN the chain one level, the guard comes OUT as a
  literal;
* `t = v` → `(or (= e v) c)`; `e = v` → `(or (= t v) ¬c)`;
* both branches values, both `= v` → `true`; both `≠ v` → `false`
  (and the all-leaves-distinct generalization `simplify_eq_ite`);
* sub-select branches recurse (`(ite c <solve> (= e v))`);
* plus `try_ite_eq` (`(= (ite c t e) x)` with `t=x`, `e≠x` → `c`) and
  the ite×ite four-clause matrix.

The extracted guards then meet the goal's other conjuncts through
ordinary and/or **complement absorption** (`X ∧ ¬X ≡ false` — z3's
`mk_nflat_and_core`), which is why the fold needs no context walk at
all: the self-referential select `(= 5 (ite (= x 5) 3 x))` solves to
`(and (= x 5) ¬(= x 5))` → `false` by pure value reasoning.  The
comparison analogue (`(<= (ite c 4 x) 3)` → `(and ¬c (<= x 3))`, z3
`arith_rewriter::mk_le_ge_eq_core`) is included: the nec-smt goals
carry `(<= select k)` conjuncts.

## What landed

* `TermManager::eq_ite_rules` + `solve_ite_value` (`query/simplify.rs`):
  the full z3 rule set above, as an **explicit worklist** (z3 re-enters
  its rewriter via `BR_REWRITE2`; the worklist is the re-entry without
  native recursion — the 724 KB members nest selects thousands deep).
  Fuel-bounded (100 k steps); on exhaustion the solve degrades to the
  plain (equivalent) equality.  Applied in the bottom-up pass's `Eq`
  arm AND the ctx walk's `Eq` arm (replacing the old push — the push
  case-SPLIT, which the memo had proven was the fuel cost).
* `rewrite_ite`: z3 `mk_ite_core` (base rules + same-condition merges +
  Boolean connections + the `ite_extra_rules` cross-branch merges),
  iterative, in the bottom-up `Ite` arm and the solve's frame assembly.
* `cmp_ite_rule`: the arith comparison distribution (all four
  operators), in the four comparison simplifiers.
* `absorb_literals`: z3 `mk_nflat_and_core`/`mk_nflat_or_core` parity
  (flatten → dedup → complement decides), at the **simplifier layer**
  (see the placement lesson below), wired into `combine_simplified`'s
  And/Or arms, `ctx_and`, the ctx `Or` arm, and the solve worklist's
  frame assembly.
* `mk_eq` (builder): the Boolean-equality section (constant absorption
  `(= true p) → p`, double-not unfold, complement → `false`) —
  z3-parity constant folding, same class as the builder's existing
  value folds.

## The three soundness bugs (in found order)

1. **A pre-existing false-simplify on main — `ctx_and`'s unwind never
   removed fresh context entries.** The unwind loop restored
   overwritten polarities but `.flatten()`-skipped `None` entries —
   fresh entries leaked past the conjunction's end and poisoned every
   later sibling walk in the enclosing scope.  Symptom: `(or (and p q)
   p)` simplified to `true` (main's own binary does this today); the
   `sat` corpus member folded to `false`.  Found by the new
   equivalence fuzzer's first run; fixed by unwinding `(atom,
   Option<bool>)` with `remove` for fresh entries (the Ite arm's split
   always did this correctly — the bug was ctx_and-only).
2. **R6's frame carried the wrong else-side** (`else_side: t` instead
   of `e`): the t-side was solved twice and the else-branch silently
   dropped — `(= 0 (ite c x (ite p 4 -3)))` folded toward `(= 0 x)`,
   wrong whenever the else-path produced `v`.  A transcription typo
   against z3's `(ite cond, mk_eq_plain(t, val), result)`.  Found by
   the fuzzer at 30 k seeds (invisible at 3 k).
3. **`absorb_literals`' decided polarity was inverted** (`Some(conjunction)`
   instead of `Some(!conjunction)`): `(and p ¬p)` folded to `true` —
   the wrong-`sat` class.  Introduced in the harness port of the
   builder version (the builder version had it right); caught by
   re-running the fuzzer after the port.  This is why the fuzzer runs
   after EVERY change, not once.

The fuzzer is landed as `solve_eq_rules_preserve_equivalence`: random
typed QF_LIA terms over `x,y:Int`, `p,q:Bool` (biased to
ite-with-value-branches, the rule surfaces), the full
`simplify`+`ctx_simplify` pipeline, exhaustive evaluation over
`{-1..2}²`×`{T,F}²` — 30 k seeds at depth 5, ~1.3 s.  It found every
bug above within seconds of each being introduced.

## The placement lesson (negative result: do not fold in the builder)

The absorption/dedup first landed in `builder.rs`'s `mk_and`/`mk_or`
(global).  Three solver-path regression tests broke; two were golden
shapes (benign), but **`set9/set16_family_answers_sat` — MBQI
convergence pins — went from `sat`-in-4 ms to `unknown`-at-290 s**:
builder-level folding changed the instantiated-axiom shapes MBQI's
row-closure completion depends on (e.g. `(or (member x s) (member x
s))` now dedups when an instantiation unifies `s1=s2`).  z3's own
absorption lives in the REWRITER (`mk_nflat_and_core`), never in
`ast_manager`'s constructors; the port now matches that placement —
`absorb_literals` is harness-only (bottom-up combine, ctx walk, solve
frames), the builder stays fold-free, and the pins return to
`sat`-in-4 ms.  **Rule: builder-level rewrites perturb the solver's
term shapes; keep rewriting power in the simplifier harness.**  (The
`mk_eq` Bool section stayed in the builder deliberately: value-class
constant folding, measured inert on the pins, and the same class as
the builder's pre-existing `(= "a" "b")` fold that was itself a
soundness fix.)

## Verification (the full bar)

* `cargo nextest run --workspace --all-features`: **12 078 run, 0
  failures** (nixie-core 2 228 incl. the fuzzer + 9 targeted
  regressions; nixie-theories 2 018; nixie-solver 2 707 incl. the
  MBQI pins; sat/cli/nlsat/proof/spacer/opt 3 162; math/wasm/nixie/
  smtcomp 1 259).  One transient link failure under 100 % disk was a
  corrupted artifact (the documented trap) — clean rebuild, all green.
* `cargo clippy --all-features --all-targets -- -D warnings`: clean.
* `cargo fmt --all -- --check`: clean.  `cargo doc --no-deps
  --all-features -D warnings`: clean.  Doctests: green.
* **Z3 parity** (`bench/z3_parity/run_parity.sh`, z3 4.16.0): **177
  benchmarks, 176 agree, 0 wrong-verdict pairs** (the one difference:
  nixie `unsat` where z3 times out — inconclusive, not a
  disagreement).
* **Perf gate** (`bench/perf_gate/run_gate.sh`, BASELINE `86846e39`):
  **PASS — conflicts 1.000, decisions 1.000, wall 0.99** (the only
  solver-path change is `mk_eq`'s Bool section, measured neutral).
* nec-smt classes: small (above); med — no regressions (timeouts where
  the old binary also timed out; `prp-29-29` newly folds); large —
  `checkpass/prp-43-49` folds in 33 ms, the five non-foldable members
  time out in the pre-existing printer/substitute frontier exactly as
  on main (z3's plain simplify leaves residuals on them too — folding
  them is not this item).

## What remains open (the honest boundary)

* The five large non-foldable members hang in `(simplify)`'s
  downstream `substitute`/printer on residuals z3 prints fine — the
  pre-existing let-printer frontier, next entry: memoized
  `substitute` over shared DAGs (the study's printer addendum already
  names the shape).
* The FOLD is simplifier-level: `(check-sat)` does not run
  `TermManager::simplify`/`ctx_simplify` on assertions, so the nec-smt
  unknown/timeouts in the SOLVING table do not move yet.  Wiring the
  simplifier into check-sat preprocessing is a default-path change
  (gate + parity + a matched measurement campaign) — its own session,
  now unlocked by this landing.
