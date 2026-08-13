# Handover: QF_AUFLIA SAT performance — array disjunctions

## Read first

- `AGENTS.md` — the non-negotiable project rules (soundness-first, read Z3/CVC5
  before inventing, no `unwrap`, iterative walks, etc.).
- `docs/ARRAY_THEORY_PLAN.md` and `docs/ARRAY_THEORY_STAGE5.md` — the staged
  design for the incremental array theory (Stages 1–5, of which 1 + the RoW/ext
  propagation halves are implemented).
- `CHANGELOG.md` — recurring soundness-bug patterns.

## The problem

On QF_AUFLIA, the solver is **sound** (0 wrong answers, parity 163/0/5).  But
five `storecomm`/`swap`/`storeinv` "invalid" (SAT) goals take 3–5 s while z3
takes 0.03–0.07 s:

```
3.1 s  storecomm_invalid_t3_np_nf_ni_00060_006     (z3 0.07s)
4.8 s  storecomm_invalid_t3_pp_nf_ai_00030_001      (z3 0.06s)
5.0 s  storecomm_invalid_t1_pp_nf_ai_00030_003      (z3 0.03s)
4.7 s  storecomm_invalid_t1_pp_nf_ai_00030_006      (z3 0.04s)
1.4 s  storeinv_invalid_t3_pp_sf_ai_00002_001       (z3 0.04s)
```

All are SAT (z3 says `sat`).  The 3–5 s is the **CDCL search over the atoms of
the finite-disjunction array lemma** — the SAT solver branches on the
disjuncts, exploring a large space.

## Root cause (profiled, not guessed)

The array-axiom refinement loop (`check_core`, `oxiz-solver/src/solver/mod.rs:1394`)
adds lemmas and re-solves from scratch each round.  Profiling showed:
- the per-round reset is **~1 µs** (negligible);
- the restart is **warm** (`phase` persists across `backtrack_to_root`);
- the **CDCL search itself** is the cost (~1.5 s/round × 2 rounds).

The search is expensive because of the **atoms the lemmas materialise**:
- the **finite-disjunction clause** (`oxiz-solver/src/solver/array_axioms.rs`,
  `finite_disjunction_extensionality`):
  `a = b ∨ ∨_{k∈K}(val_a(k) ≠ val_b(k))` — for a depth-60 store chain, this
  is a ~60-disjunct clause; the SAT solver branches on each disjunct.
- the **eager full-chain read-over-write** (`build_read_over_write`, same file):
  unfolds every store level, creating ~N intermediate `select` atoms per chain
  per round.
- the **read-over-write lemma atoms** (RoW-SAME/DIFFERENT implications).

The theory-side EUF propagation (`TheoryManager::final_check`,
`propagate_array_read_over_write` + `check_array_extensionality`) catches
**deterministic** conflicts inline but cannot help SAT goals (there are no
conflicts to prune — the goal is satisfiable).

## What's already been tried and does NOT help these SAT cases

1. **Incremental refinement rewrite** (avoid the round-based re-solve): profiled
   and proven unnecessary — the reset is ~1 µs and the restart is warm.  The
   cost is the search, not the round machinery.

2. **Skip the fresh-witness extensionality** when a finite-disjunction clause
   fires: breaks `cvc/read8` (whose unsat needs the witness's `select(a,k)`/
   `select(b,k)` terms for cross-congruence with other constraints).

3. **Concrete model certification** (certify SAT by checking array equality at
   store indices): the model evaluator (`eval_in_model`) returns `Undetermined`
   for array-sorted terms — it cannot represent array values concretely.  Both
   genuine SATs (`array_01`) and bogus SATs (`read7`) are `Undetermined`, so the
   gate cannot distinguish them without over-downgrading.

4. **Extending the honesty gate** (`array_atoms_need_theory`) to cover
   disequalities: a per-atom gate cannot catch `array_incompleteness1`-style
   UNSAT that requires *global* extensionality reasoning through multiple
   aliases.

5. **Moving the theory propagation to `on_assignment`** (mid-search, Z3 `assign_eh`):
   requires `&mut TermManager` in `TheoryManager`, which was attempted and
   reverted — it cascades into refactoring ~10 methods that take `manager` as a
   `&TermManager` param, and creates borrow conflicts in `check_core`'s
   refinement branches.

## The lever: reduce the disjunctive search cost

The SAT solver branches on the finite-disjunction clause's disjuncts.  Each
disjunct is `val_a(k) ≠ val_b(k)` — an integer disequality between two free
variables.  For an invalid `storecomm` (chains provably differ), exactly one
disjunct is satisfiable (pick the vars different); the solver must *find* it
among ~60 options.  z3 does this in 0.03 s; oxiz takes 3 s.

### Approach A — SAT-side: branch on the disjunction eagerly

Instead of adding the disjunction as a learned clause and letting CDCL discover
the right disjunct, **case-split** on it: for each store index `k`, create a
SAT assumption `(val_a(k) ≠ val_b(k))` and try.  The first satisfiable one is
the model.  This is O(|K|) tries, each a fast SAT check, vs. one large CDCL
search.

Implementation: in the array refinement loop (`mod.rs:1394`), after
`instantiate_array_axioms` generates the finite-disjunction clause, instead of
adding it as a lemma + re-solving, **try each disjunct as a `check-sat-
assuming`** and return `sat` on the first that succeeds.  If all fail, the goal
is genuinely `unsat` (the arrays are equal).

This mirrors how Z3's `theory_array` handles extensionality: it tries concrete
indices, not a fresh witness.

### Approach B — Theory-side: propagate the disjunction during search

Add an `on_assignment` hook (requires the `&mut manager` change, or pre-create
the disjunct terms at encode) that, when the SAT solver assigns `a ≠ b`, eagerly
probes the store indices: for each `k`, check if `val_a(k) ≠ val_b(k)` is
already decided in EUF/arith.  If one is, propagate it (satisfying the
disjunction).  This prunes the search toward the satisfiable disjunct.

### Approach C — Model-based: detect the SAT model from the first solve

After the first `solve_with_theory` returns `Sat` (candidate model), read the
model's values for the value variables (`e1`, `e2`, …).  If two values the
disjunction needs different are already different in the model, the
disjunction is satisfied — certify `sat` immediately without the lazy
refinement round.  The challenge: `eval_in_model` returns `Undetermined` for
array-equality assertions (it can't evaluate array values), but the **value
variables** (`e1..eN`, Int-sorted) CAN be read from the arithmetic solver
(`arith.value(term)`).  So check: does the candidate model's arithmetic
assignment already make some `val_a(k) ≠ val_b(k)` true?  If yes, `sat`.

## Key files

| file | what |
|---|---|
| `oxiz-solver/src/solver/mod.rs` | `check_core` (the CDCL loop + refinement), `rebase_theory_state`, `Solver` struct |
| `oxiz-solver/src/solver/array_axioms.rs` | `instantiate_array_axioms`, `build_read_over_write`, `build_extensionality_and_congruence`, `finite_disjunction_extensionality`, `direct_store_map` |
| `oxiz-solver/src/solver/check_array.rs` | `check_array_constraints`, `store_chain_disequality_conflict`, `store_chains_concretely_equal`, `reconstruct_store_chain`, `array_atoms_need_theory` |
| `oxiz-solver/src/solver/theory_manager.rs` | `TheoryManager`, `final_check`, `propagate_array_read_over_write`, `check_array_extensionality`, `process_constraint` |
| `oxiz-solver/src/solver/array_theory.rs` | `ArrayTheory` index (maps, parents, row_targets, ext_witnesses) |
| `oxiz-solver/src/solver/encode.rs` | `encode_depth` (Tseitin encoder), `extract_linear_terms` (Mul linearisation), the array-equality + `has_array_ops` flag |
| `oxiz-solver/src/solver/model_eval.rs` | `eval_in_model`, `eval_in_model_outcome`, `model_refutes_assertions` |
| `oxiz-solver/src/solver/trail.rs` | `ContextState`, `TrailOp`, the debug exhaustive-match scope invariant |
| `oxiz-sat/src/solver/search_ext.rs` | `solve_with_theory` (the SAT↔theory interface; `theory_processed` resets to 0 per call) |
| `oxiz-theories/src/euf/solver.rs` | `EufSolver` (`intern`, `merge`, `find`, `are_equal_immutable`, `are_proven_disequal`, `check_conflicts`, `explain_eq`) |
| `oxiz-core/src/ast/manager/builder.rs` | `TermManager` (`mk_select`, `mk_store`, `mk_eq`, `mk_var`, `mk_ite`, …) |

## Build & verify

```bash
# Use the nix toolchain
export PATH=/nix/store/gr0i02za09y1hif1japlzg1qpd5xsg49-rust-default-1.97.1/bin:$PATH
cargo build --release --bin oxiz     # ~1.5 min

# Soundness canary (must stay 163/0/5)
for f in $(find bench/z3_parity/benchmarks -name "*.smt2"|sort); do
  z=$(timeout 10 z3 "$f" 2>/dev/null|tail -1)
  m=$(timeout 10 target/release/oxiz "$f" 2>/dev/null|tail -1)
  [ "$z" = "$m" ] && echo ok || { [ "$z" = unknown ] || [ "$m" = unknown ] || [ -z "$m" ] && echo inc || echo "MIS $f $z/$m"; }
done

# The 6 formerly-unsound cvc cases (must match z3)
for f in read6 read7 fb_var_5_12 fb_var_6_12 fb_var_12_11 fb_var_27_8; do
  p=$(find smt-lib/non-incremental/QF_AUFLIA/cvc -name "$f.smt2"|head -1)
  echo "$(timeout 12 target/release/oxiz "$p" 2>/dev/null|tail -1) vs $(timeout 12 z3 "$p" 2>/dev/null|tail -1)"
done

# The slow SAT cases (the target)
for spec in storecomm_invalid_t3_np_nf_ni_00060_006 storecomm_invalid_t3_pp_nf_ai_00030_001 storecomm_invalid_t1_pp_nf_ai_00030_003; do
  p=$(find smt-lib -name "$spec.cvc.smt2"|head -1)
  time target/release/oxiz "$p" 2>/dev/null|tail -1
done
```

## Z3 reference

- `../temp/z3/src/smt/theory_array_full.{h,cpp}` — the array theory (indexed,
  event-driven, `merge_eh`/`relevant_eh`).  Pay attention to how it handles
  extensionality: it does NOT use a fresh witness variable; it tries concrete
  indices from the store maps (the "diff" is found by comparing the arrays'
  write sets, not by SAT search over a disjunction).
- `../temp/z3/src/smt/theory_array.{h,cpp}` — the base class.
- `../temp/cvc5/src/theory/arrays/` — CVC5's array theory (`array_info`,
  `inference_manager`).

## Constraints

- **Pure Rust** — no `z3`/`cvc5` as dependencies (banned in `deny.toml`).
- **Soundness first** — a timeout or `Unknown` is acceptable; a wrong `sat` or
  `unsat` is a catastrophe.  Every change must pass parity + the 6 cvc cases +
  the 115-case false-SAT set.
- **No `unwrap()`/`expect()`** in production code (`clippy::unwrap_used` is
  `deny`).
- **Iterative walks** for deep input (no unbounded native recursion).
- The lib-test binary has pre-existing compile errors (E0061 in test code);
  use `cargo build` / `cargo check` (non-test), not `cargo test`.
