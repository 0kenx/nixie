# Finite sets with cardinality: landing report and the SAT-layer blocker it exposed

**Date:** 2026-09-14
**Scope:** `nixie-solver/src/solver/set_theory/` (new `cardinality.rs`), the
SMT-LIB set surface in `nixie-core`, and the evidence collected while trying to
make `sat` verdicts reach the user.

## What landed

The finite-set reduction now decides the **ground cardinality fragment**: `|s| = n`,
`|s| ≤ n`, inclusion–exclusion (`|a ∪ b| + |a ∩ b| = |a| + |b|`, `|a \ b| + |a ∩ b| = |a|`),
pigeonhole (`|s| ≥ k` with fewer than `k` slots), `s ⊆ t` coupled to sizes
(including "subset with equal cardinality is equality"), `set.choose`,
`set.complement`/`set.universe` over finite element sorts, and finite-universe
bounds (Bool, bit-vectors, floats, finite fields, `RoundingMode`, non-recursive
datatypes). Before this, `set.card` over an *opaque* set raised the honesty gate:
`x ∈ s ∧ |s| = 0` answered `unknown` where the theory says `unsat`.

The encoding is the eager axiomatization of what CVC5's `cardinality_extension.cpp`
maintains lazily and Z3's 2025 `theory_finite_set_size.cpp` enumerates with a
sub-solver: a counting equation per cone set (`|s| = Σ_e ite(e counts, 1, 0) +
slack_s`), inclusion–exclusion identities over *twin* terms (`a ∪ b`'s missing
`a ∩ b` is created), monotonicity of the **slacks** (`slack(a ∩ b) ≤ slack(a)` —
not of the cardinalities, which are already monotone pointwise), subset rules,
non-negativity, and the chain-union universe bound. The mathematical core is the
classical fact that a monotone modular valuation on a distributive lattice is a
measure over the Venn regions; the axioms are exactly its finite characterization.
Every clause is a valid consequence of the theory of finite sets, so the encoding
can never manufacture a wrong `sat`, and the conjunction of any subset of passes'
axioms stays valid — a property that became load-bearing (below).

### Two soundness bugs found and closed while landing it

1. **Slacks must key on the element list.** `reduce` re-runs on every `assert`
   over the whole stack, and the element list grows between passes (new user
   atoms, plus the previous pass's own conjoined axioms). Two counting equations
   over *different* lists sharing one slack variable conjoin into "the newer
   elements contribute nothing": `|s| = 2` asserted before `1 ∈ s` derived a
   false `unsat`. Slack variables are now keyed by `(set, exact element list)`.
2. **The builder needed complement involution.** Without the rewrite `~ ~ s = s`
   (plus `s ∪ ∅ = s`, `s ∩ U = s`, `s \ s = ∅`, `x ∈ {y} ⇔ x = y`, … after Z3's
   `theory_sets_rewriter`), `~ ~ s ≠ s` is satisfiable in the ground encoding
   while the theory refutes it.

## What did not land, and why: the incremental-SAT watch layer

A family of problems — including several whose generated axiom sets are provably
sufficient (verified by hand and against Z3 4.16.0) — answer `unknown` instead of
their verdict, or **panic in debug builds** on a watch-list invariant. All of them
work through the DIMACS path on the identical CNF. This is *not* in the set
layer; it is pre-existing and reproducible before any of the sets commits.

### Reproducers

```smt2
;; d1.smt2 — debug build panics, release build answers `sat` (Z3 4.16.0: sat)
(set-logic ALL)
(declare-const S (Set Int))
(declare-const T (Set Int))
(assert (= (set.card S) 2))
(assert (= (set.card T) 2))
(assert (= (set.card (set.union S T)) 3))
(assert (set.member 1 S))
(check-sat)
```

- Debug build panic: `SAT solver invariant violated (after rephase): clause
  ClauseId(0) treats Lit(25) as a watched literal, but it is not registered in
  the watch list keyed by its negation` (`nixie-sat/src/invariants.rs`,
  `check_binary_registration`).
- `NIXIE_DUMP_CNF=/tmp/d1.cnf` then `nixie /tmp/d1.cnf` (same clauses, DIMACS
  path): **`sat`, no panic**. The corruption is specific to the incremental
  CDCL(T) session.
- Release build (invariants compiled out): `sat`, matching Z3 — so answers stay
  correct where a verdict is reached; the damage is the lost-propagation state
  underneath.
- Set-free shape with the same outcome: any two-opaque-set problem from the
  pre-existing witness machinery (e.g. `(assert (set.member 1 S))
  (assert (set.subset S T))` → `unknown`) fails on `trail_falsifies_live_clause`
  at `search_ext.rs`'s final-check guard. That guard's own comment notes only
  *original* clauses are scanned in scoped sessions — an original clause
  falsified by a complete assignment means propagation lost an original clause
  mid-search.

### Attribution (bisected, 2026-09-14)

| Commit                              | `finite_sets_decision` |
|-------------------------------------|------------------------|
| `0b33dbdf` (base)                   | 37/37 pass             |
| `b05d949e` (sat round-13 flip-bisection) | 37/37 pass         |
| `fc9c979e` (sets surface, this arc) | 37/37 pass             |
| `b110c2b8` (arith wide-value)       | 37/37 pass             |
| **`e987b4b6`** ("docs… CSR's internal order divergence pinned" — **also changes `list_kernel.rs`, `session_kernel.rs`, `sweep.rs`, `watched.rs`**) | **15/37 fail** |

`e987b4b6` reached `main` through merge `d1dc7f0d`. It breaks the 15 set tests
on its own, before any of this arc's uncommitted cardinality work. The failures
are all `unknown`-not-wrong-answer. With the cardinality work in place, 2 of
those 15 pass again and none are added (diffed failure sets, both directions).

The same subsystem is where the round-13 / CSR-watch agent is working
(`[csr-shadow] scan precondition violated … mirror suspended` fires on these
inputs in `-v debug` runs). The evidence above — DIMACS-clean vs
incremental-corrupt on identical clauses, originals losing watches mid-search —
is offered as a shortcut for that arc.

### Consequence for the sets tests

Twelve tests in `nixie-solver/tests/finite_sets_cardinality.rs` carry
`#[ignore = "SAT-layer watch corruption …"]` with a pointer here: their axiom
sets are sufficient (hand-checked + Z3), but the incremental session trips the
watch layer before a verdict. They should be un-ignored the moment the watch
corruption is fixed; they are the regression suite for that fix as much as for
sets.

## What would complete the theory (next steps, in order of value)

1. **Fix the incremental watch layer** (owner: the round-13/CSR arc). Everything
   below is blocked or degraded behind it: multi-set `sat` answers degrade to
   `unknown` via the guards above.
2. **Set model synthesis for `sat`.** With verdicts reachable, `get-value`
   over set variables needs Z3-style `set.unique` construction: each slack
   region contributes `slack` fresh elements, ground memberships come from the
   member atoms' final assignment. Today set-sorted variables print the
   factory default (`Value::Set([])`).
3. **Relations**: `(Set (Tuple …))` with `rel.join` / `rel.transpose` /
   `rel.product`. Tuple sorts can ride the datatype machinery (constructor +
   selectors + `_ tuple_select i`), and CVC5's `theory_sets_rels.cpp` membership
   rules (join skolemizes its existential witness per element) reduce to this
   same eager scheme.
4. **Bags**: `bag.count` gives pointwise max/min/add identities; the same
   cone/slack skeleton carries over with region *multiplicities* instead of
   0/1. The SMT-LIB surface (`bag.union_max`, `difference_subtract`, …) is
   already reserved in the parser's namespace list.
5. **Caps**: the cone (40) and element-list (24) caps gate to `unknown`
   honestly; once the SAT layer is stable they can be re-measured against the
   TLA+ corpus.
