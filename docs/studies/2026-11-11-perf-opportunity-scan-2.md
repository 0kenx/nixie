# Perf opportunity scan #2 — post-batch landscape at `e86a7162`

## Registered purpose

A second sampling scan after four landed batches (`6abc321a`, `91e9f6fc`,
`b593a1be`, `a76709df`) and the `f5fb11ef` slot landing removed the previous
scan's top items. Two goals: (1) see what is *now* dominant on the previously
hot workloads, and (2) widen coverage to logic families the first scan never
profiled (QF_IDL dense core, QF_ANIA, QF_AUFLIA storecomm, quantified UF/MBQI,
QF_NIA AProVE).

## Method

Same harness and limitations as scan #1 (`docs/studies/2026-11-10-perf-opportunity-scan.md`):
in-process `pprof` ITIMER_PROF sampling at 250 Hz, `mimalloc` global allocator,
`nixie_solver::Context::execute_script` path, one run per instance. Rebuilt at
HEAD `e86a7162` (harness source archived with this scan; adds DIMACS→SMT-LIB2
conversion via `include!` of `nixie-cli/src/dimacs.rs`, edition 2024). Shares
localize cost; they are not speedup estimates.

| profile | instance | logic/path | samples | done |
|---|---|---|---|---|
| ufidl-vlsat | `QF_UFIDL/Bouvier/vlsat3_f77` | EUF+IDL | 8695 | no |
| uf-peq | `QF_UF/PEQ/PEQ014_size9` | pure EUF | 7642 | yes(?) |
| uf-seq | `QF_UF/SEQ/SEQ005_size6` | pure EUF, solved | 869 | yes |
| uflia-wisa | `QF_UFLIA/mathsat/Wisa/xs-10-18-2-2-5-3` | UFLIA simplex | 580 | yes |
| uflia-wisas | `QF_UFLIA/wisas/xs_8_13` | UFLIA simplex | 267 | yes |
| lia-arctic | `QF_LIA/arctic-matrix/constraint-392137` | dense LIA | 8676 | no |
| aufia-sll | `AUFLIA/.../sll_to_dll_rev-2.i_60` | quantified UF+LIA | 8674 | no |
| nia-verymax | `QF_NIA/VeryMax/SAT14/1000` | NIA ground eval | 8457 | no |
| nia-aprove | `QF_NIA/AProVE/aproveSMT806408602391139285` | NIA ground eval | 7162 | yes |
| bv-sage | `QF_BV/Sage2/bench_9557` | BV SAT-core | 8237 | no |
| sat-carry | gate corpus `Carry_Bits_Fast_19` | SAT | 6191 | no* |
| sat-scpc | gate corpus `SCPC-500-13` | SAT | 999 | yes |
| sat-s38584 | `s38584` (satcomp25) | SAT | 754 | yes |
| idl-gryzzles | `QF_IDL/asp/HamiltonianPath/gryzzles.8` | dense DL | 8477 | yes(?) |
| idl-edgematch | `QF_IDL/asp/EdgeMatching/...colours=11` | dense DL | 8589 | no |
| ania-gp7 | `QF_ANIA/GrandProduct/sound/same/7` | arrays+NIA | 8655 | no |
| ania-floppy | `QF_ANIA/.../floppy_..._8` | arrays+IA, SOI | 3584 | yes |
| auflia-store40/50 | `QF_AUFLIA/storecomm/..._00040/00050` | arrays+LIA | 8685/8650 | no |
| ufq-coilist | `UF/Barrett/coinductive_list` | quantified UF (MBQI) | 8643 | no |
| ufq-huffman | `UF/Barrett/huffman` | quantified UF (MBQI) | 8613 | no |
| ufq-rbt | `UF/Barrett/rbt_impl` | quantified UF (MBQI) | 8355 | no |

*carry "no" = hit the 25 s sampling cap in the harness path. `uflia-25959`
was dropped: it now solves in <1 s under default settings (its 4.4 s A/B
figure was a conflict-budget cut, not a full solve).

## Findings, ranked by measured impact × breadth

### 1. EUF `term_to_node` pop uses full-map `retain` — 67.4% of coilist, 36.9% of huffman

`EufSolver::pop` runs `term_to_node.retain(|_, idx| idx < num_nodes)` whenever
the popped scope created any nodes (`nixie-theories/src/euf/solver.rs:1504`).
On MBQI-heavy instances every scope creates nodes, so **every theory backtrack
scans the entire term vocabulary map** — including all base-scope terms — and
rehashes survivors. This is the single largest share of the whole scan.

Fix, exactly equivalent by construction: trail the *insertions*. All three
insert sites (`intern` at :632/:643, `intern_app` at :788) run only on a
`get()` miss, every entry's idx equals `nodes.len()` at creation, nodes are
LIFO-truncated, and base-scope nodes are never truncated — so "removed by
retain" ⇔ "inserted after the push mark". A `term_to_node_trail: Vec<TermId>`
with per-scope limits (mirroring `sig_trail_limits`, and the
`asserted_arith_eq_trail` / `processed_lit_trail` disciplines already in
`TheoryManager::pop_theory_scope`) pops in O(inserted). Guarded by the
incremental-vs-replay differential fuzzers plus a debug oracle comparing
trail-popped vs retain-popped map state.

### 2. `propagate_bounds_in` re-materializes rows and stamps per fixpoint pass — still 79% of vlsat; `row_stamp` 10.8% of arctic

Batch B fused the derivation pass, but `Simplex::propagate_bounds_in`
(`nixie-theories/src/arithmetic/simplex/mod.rs`) still, per call and per
≤16-iteration fixpoint pass: (a) **deep-clones** every narrow row
(`row_lin(v).map(|arc| arc.as_ref().clone())`) purely to release a borrow —
an `Arc` clone suffices; (b) rebuilds `BigLinExpr`s per term per call; (c)
recomputes `row_stamp` over all narrow rows on every pass — this is deferred
item #9, and it survives *because* the stamp-skip needs the stamp first.

The structural fix (Z3 `theory_arith` bound-watch shape): after a bound change
on `v`, only rows in `columns[v]` can derive anything new — nixie now has that
index (and `f5fb11ef` made it O(1) to maintain). Convert the fixpoint into a
worklist seeded from changed vars' columns. Equivalent-work only if the
derivation order and applied-set stay identical (they need not: fixpoint
iterations are order-insensitive in *result*, but the *trail* order of stored
bounds must be preserved or counters drift — treat as heuristic-tier if order
cannot be pinned). The (a) Arc-instead-of-deep-clone sub-item alone is
equivalent-work and mechanical.

### 3. `nl_eval::euclidean` pays full `BigInt` division for small operands — ~14% of verymax, ~10% of aprove

Every integer `div`/`mod` ground evaluation converts to `BigRational`→
`BigInt`, runs bignum `/`, `*`, `-` (`num_bigint div_rem_cow` ≈ 1187/8457
samples on verymax), even when both operands fit `i64`. Add a checked
`i64` fast path (operands integral and in range → checked truncating div/rem +
Euclidean correction → `BigRational::from_integer`) with BigInt fallback.
Exactness preserved by construction (checked ops; fall back on any overflow).

### 4. Dense DL `DenseDlCore::update_cells` — 87.7% of gryzzles (QF_IDL/asp family)

The incremental all-pairs update (Cottoné–Oddoux / Z3 `dense_graph` shape) is
O(n²) per `assert_edge` by algorithm — two full passes over the `dist` matrix
(row `t` for the F-set, then a column-`s` read for the Y-set) plus, per
improved cell, a `HashMap<(u32,u32)>` `occs` lookup in
`propagate_using_cell`. Algorithm already matches the reference; the
opportunities are constants: (a) per-node watcher vectors instead of the
`(y,x)`-keyed hash (one indirection per improved cell → array index);
(b) `dist`/offsets already `i64`; check whether `cap`-strided column reads
can be re-blocked. Z3/CVC5 comparison required before any change (read
`../temp/z3/src/math/simplex/...` + diff_logic dense core).

### 5. MBQI `build_exists_candidate_lists` scans the whole model per variable — 17.8% of rbt

`nixie-solver/src/mbqi/counterexample.rs`: for each existential variable it
iterates **every** entry of `model.assignments` (`manager.get(term)` per
entry) plus linear `cands.contains` — O(vars × assignments) per call, per MBQI
iteration. A per-sort value index built in one pass over the model (preserving
first-encounter order so candidate order — hence trajectories — stay
identical) makes it O(universe). Equivalent-work verifiable by byte-identical
candidate lists on the MBQI tests.

### 6. SOI `optimize_linexpr` / `reduced_obj_coef` — 17.7% self + 21% adjacent on floppy (simplex_opt)

The SOI feasibility driver re-walks the full tableau per objective probe
(`reduced_obj_coef` under `optimize_linexpr`, `tableau_iter` leaf 740
samples). Z3 maintains reduced costs incrementally across pivots (revised
simplex standard step, O(m) per pivot). Requires reading
`../temp/z3/src/math/simplex/simplex.cpp` + the SOI/`opt` integration before
designing; likely a moderate structural item.

### 7. Row interning hash churn — `intern_row_reported`/`cached_row_slack` probing dominates store40/50

store40: `copy_nonoverlapping` 31.2% + `set_ctrl` 20.0% under
`intern_row_reported`/`cached_row_slack` (`LinKey` build + hash per assert);
store50 shows the same as `movemask` 56.9%. The parsed-constraint struct (from
batch B) could carry a precomputed key hash so asserts stop rebuilding keys.
Mechanical equivalent-work candidate, but measure first: probing cost may be
dominated by map *size* on storecomm, not key builds.

### 8. SAT-core items (unchanged verdicts)

- carry: `find_saved_pos_hit` 24% leaf under `list_kernel::scan` —
  watch-position search inside the propagation kernel; that kernel is
  prior-study territory (`list_kernel`/`block_filter`), document only.
- sage: `ClauseArena::get` 23.5% + `forward_subsume_matching` 3.7% — the
  old deferred #8 (gate-subsume batching); end-to-end dilution stands.
- `shrink_block` 12.5% on carry — the reverted batch D was measured neutral;
  no new evidence.

### Non-findings (explicitly cleared)

- `derive_arith_bound_propagations` no longer appears outside vlsat's own
  family, and vlsat's residual is item #2's materialization, not derivation
  logic.
- EUF congruence `propagate` (batch C target) is down to 2.1–5.7% on the
  families that used to be 70%.
- `columns` maintenance (slot landing `f5fb11ef`) does not register as a leaf
  anywhere.
- ania-gp7's dominant cost is congruence/hash churn at modest absolute share
  (5.7%) — post-batch-C steady state, no action.

## Protocol for landing any item above

Unchanged from scan #1: equivalent-work items need the full release bar +
parity + bit-identical counters; structural items need pre-registration under
`docs/BENCHMARKING.md` with ≥10 seeds and matched nulls; percentages are
localization evidence, not effect estimates. Item #1 additionally requires
the trail-vs-retain equivalence argument restated next to the trail
(invariants: miss-guarded inserts, LIFO node truncation, base nodes never
truncated).

## Artifacts

Collapsed stacks, corpus list, and the harness source are under
`precompile/e86a7162…/benchmark/profile-scan-2-2026-11-11/` (harness
rebuilds against the workspace via path deps).
