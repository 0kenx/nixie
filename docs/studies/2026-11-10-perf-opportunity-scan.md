# Performance opportunity scan — 2026-11-10 (HEAD `660166ad`)

## Registered purpose

Identify performance-optimization opportunities with profiling evidence, as the
follow-up to the 0.3.4 cost investigation (whose equivalent-work reductions
landed; the remaining numeric-pin cost there is correctness-tied and out of
scope). This document records **opportunities only**: no change below has been
implemented, benchmarked under the AGENTS.md protocol, or landed. Every item
names the exact hot sites, the measured share, and the classification
(**equivalent-work reduction** = same facts derived, same search trajectory,
gateable by the single-seed perf gate with bit-identical counters; **structural**
= algorithmic change that needs the full heuristic/measurement protocol).

## Method

`perf_event_open` is blocked in this sandbox (`perf record` fails even for
`cycles:u`, `perf_event_paranoid=2` + seccomp), so sampling used an in-process
signal-based profiler instead of kernel events:

- Harness (archived alongside this doc): a standalone crate depending on
  `nixie-solver` (path dep), global `mimalloc` allocator (parity with the CLI
  binary), driving the exact CLI solve path
  (`nixie_solver::Context::execute_script` on the file text; DIMACS files are
  converted to SMT-LIB2 exactly as `nixie_cli::dimacs::DimacsCnf::to_smtlib2`
  does). Sampling via `pprof` 0.15 (`ITIMER_PROF`, 250 Hz CPU-time, all
  threads), full Rust symbolization including inline frames, collapsed-stack
  output.
- Binary: `--profile perf` workspace build of HEAD `660166ad` (release opt
  flags, symbols retained). Harness build mirrors the release profile.
- Targets: 13 single-seed runs chosen for path diversity and adequate duration
  (0.9–14 s), one run each. Samples per run: 235–3471.

| profile | instance | logic/path | samples |
|---|---|---|---|
| ufidl-vlsat | `QF_UFIDL/20210312-Bouvier/vlsat3_f77` | EUF+IDL, timed out at cap | 3397 |
| uf-peq | `QF_UF/PEQ/PEQ014_size9` | pure EUF, timed out at cap | 3448 |
| uf-seq | `QF_UF/SEQ/SEQ005_size6` | pure EUF, solved | 729 |
| uflia-25959 | `QF_UFLIA/20230314-Jaroslav-Bendik-Certora/25959_...` | UFLIA | 759 |
| uflia-wisa | `QF_UFLIA/mathsat/Wisa/xs-10-18-2-2-5-3` | UFLIA simplex | 516 |
| uflia-wisas | `QF_UFLIA/wisas/xs_8_13` | UFLIA simplex | 235 |
| lia-arctic | `QF_LIA/arctic-matrix/constraint-392137` | dense LIA, timed out | 3470 |
| aufia-sll | `AUFLIA/.../sll_to_dll_rev-2.i_60` | quantified UF+LIA, timed out | 3471 |
| nia-verymax | `QF_NIA/20170427-VeryMax/SAT14/4` | NIA ground eval, timed out | 2206 |
| bv-sage | `QF_BV/Sage2/bench_9557` | BV SAT-core heavy, timed out | 2089 |
| sat-carry | gate corpus `Carry_Bits_Fast_19` | SAT, solved | 1477 |
| sat-scpc | gate corpus `SCPC-500-13` | SAT, timed out | 808 |
| sat-s38584 | gate corpus `s38584` | SAT, solved | 626 |

**Limitations, stated up front.** CPU-time sampling, single seed per instance,
retrospectively selected targets: shares below identify where cost lives, they
are not powered speedup claims, and no item below is "authorized" by its
percentage. Timed-out runs profile the search loop of an unfinished solve —
correct for hotspot identification. The harness path omits CLI-only option
plumbing (defaults; no effect on hotpaths examined). The earlier Wisa
`perf`-based sampling record could not attribute callers (leaf-only frames);
this scan's dwarf/inline symbolization does not have that defect.

## Findings, ranked by measured impact

### 1. `TheoryManager::derive_arith_bound_propagations` — ~95% of a QF_UFIDL solve

`nixie-solver/src/solver/theory_manager.rs:2281`, fired from `on_assignment`
after **every** successful arithmetic atom assertion (`theory_manager.rs:4571`
ff., default-on for QF_UFIDL).

- Evidence: ufidl-vlsat — 86.2% of *all* samples have their hot leaves owned by
  this function (89.8% of library-leaf samples), plus 9.2% more in its callee
  `ArithSolver::derive_expr_bound_reasons`. Leaf mix: `hashbrown` get 69.8%,
  `FilterMap::next` 13.4%, `Vec::extend` 2.9%, mimalloc ~10%.
- Shape: each call (a) rescans the **entire** `var_to_constraint` map, probing
  `var_to_parsed_arith` (second FxHashMap) per entry, (b) re-probes
  `var_to_parsed_arith.get(&var)` a **second** time in the candidate loop for
  `.terms`, (c) optionally runs `tighten_tableau_bounds()` to fixpoint, and
  (d) runs `derive_expr_bound_reasons` per candidate. Cost per assertion is
  O(total atoms) hash probes; on vlsat3_f77 (0.5 MB of atoms) that is the whole
  runtime.
- Opportunities, all **equivalent-work** (identical propagation sets, same call
  sites):
  1. Maintain an incremental candidate index (`Vec<Var>` of non-EQ parsed-arith
     atoms, appended at assert time) instead of the full-map rescan+intersect;
     removes both hash probes of loop (a).
  2. Carry the parsed terms (or an arena index) in the candidate tuple —
     removes the redundant lookup in (b).
  3. Add a conservative dirty epoch: skip the whole derivation when no bound /
     assignment changed since the last call (bounds state is what the
     derivation reads). Must be invalidated by every `set_lower/upper_value`,
     assignment, pop and tighten — and verified by bit-identical SAT counters.
- Expected magnitude: dominant on the DL family; neutral elsewhere (gated by
  `is_dl_family`).

### 2. EUF congruence `propagate` — 70% self on pure-EUF

`nixie-theories/src/euf/solver/congruence.rs:307`, per use-list entry:
`args_copy` SmallVec allocated per entry (line 543), `canon_buf.clone()` to
build the `sig_table` key on fingerprint hit (line 566) and again inside
`update_sig_entry` on miss (line 596), plus double-map lookup
(`fingerprint_table` → `sig_table`).

- Evidence: uf-peq — `propagate` self 70.2%; separate inlined leaves: SmallVec
  `from_iter` 5.6%, `copy` 3.3%, mimalloc dealloc 2.4%, `is_bucket_full` 2.3%,
  SmallVec `spilled` 2.1%.
- Opportunities (**equivalent-work**): reuse one raw-args buffer per merge event
  (the `canon_buf` pattern already adopted there — extend it to `args_copy`);
  eliminate key clones via interned signatures (store the canonical args in the
  node at publish time; compare nodes directly on fingerprint hit instead of
  constructing/hashing a `(u32, SmallVec)` key).
- Secondary in the same file: `self.expl_cache.clear()` on **every** merge
  (line ~352) makes the explanation cache permanently cold on merge-heavy
  workloads and pays O(cache) per merge (congruence.rs:350). An epoch-stamped cache (recompute only
  when the proof forest grew since the entry was made) preserves the "no stale
  longer-than-necessary explanations" intent. Feeds finding 5.

### 3. Simplex column maintenance — 39.6% of a dense QF_LIA solve

`nixie-theories/src/arithmetic/simplex/mod.rs:1717` `column_drop_known`:
`col.iter().position(|&r| r == row)` — linear scan per drop; each pivot drops
per dependent row, so dense columns cost O(len) × O(dependents) per pivot.

- Evidence: lia-arctic — the closure leaf is 39.6% of the entire profile under
  `Simplex::pivot ← make_feasible ← check`. Integer normalization adds
  ~11% (`gcd_i128` 2.8%, `i128::overflowing_mul` 6.2%, `__udivti3` 1.5%,
  `lcm_i128` 0.6%), and `TableRow::term_vars` materializes a fresh SmallVec per
  pivot/bound-pass (45.0% of library-leaf samples on this instance; one call
  site even does `row.term_vars().contains(t)` — mod.rs:4830).
- Reference (read before implementing): Z3 `src/math/lp/static_matrix.h` keeps
  **bidirectional row↔column back-pointers** (`row_cell::m_offset` into the
  column strip, `remove_element` swaps + fixes one offset) — O(1) removal.
- Opportunities: (a) **equivalent-work**: replace `term_vars()` materialization
  with direct term iteration and a `row_has_var` helper (mod.rs:4818–4830);
  (b) **structural**: back-pointer column entries (Z3-style) or epoch-lazy
  columns — changes internal data layout, not search decisions; gate with the
  seeded perf protocol because per-pivot costs shift (trajectory-identical is
  not guaranteed if iteration order changes anywhere — keep swap_remove order
  or prove order-independence).

### 4. `Simplex::find_violating` clones every violated bound — 13.9% of AUFLIA

`nixie-theories/src/arithmetic/simplex/mod.rs:3925`: `Some(lo.clone())` /
`Some(hi.clone())` clone the full `BoundType` (rational, wide-capable) for every
violating row *before* the smallest-var selection decides to keep it; also
allocates `row_term_signs` SmallVec per call (mod.rs:3965).

- Evidence: aufia-sll — `BoundType::clone` leaf 13.9% owned 100% by
  `find_violating ← make_feasible ← check`; uflia-wisa — `Option::as_ref` 6.8%
  in the same function.
- Opportunity (**equivalent-work**, small and safe): track the winner as
  `(VarId, which: Lo|Hi)` and clone exactly once at return; iterate row term
  signs without materializing when only signs are consumed.

### 5. EUF explanation search `try_explain_equality` — 10.5% of AUFLIA

`nixie-theories/src/euf/solver/explain.rs` — path search in the proof forest.

- Evidence: aufia-sll 10.5% leaf; hot on uf-peq (via `try_explain_diseq`) and
  uflia-wisa/wisas as well.
- Coupled to finding 2's `expl_cache.clear()`-per-merge: on merge-heavy runs
  the cache never serves. Opportunity (**equivalent-work**): epoch-stamped
  cache entries (invalidate on proof-forest growth) instead of full clear; the
  cache's answers stay sound-but-possibly-longer until invalidated — same
  contract as today, minus the cold cache and the O(cache) clear per merge.

### 6. `nl_eval::Interpretation` uses SipHash maps — ~11% hashing + ~6% bignum churn on QF_NIA

`nixie-theories/src/nl_eval.rs:90`: `numeric: HashMap<TermId, BigRational>`
(default RandomState = SipHash), while the rest of the solver uses FxHashMap.

- Evidence: nia-verymax — SipHash leaves (`make_hash` 3.0%, `finish` 3.1%,
  `u8to64_le` 2.5%, `d_rounds` 2.5%, `wrapping_add` 2.5%) ≈ 11%; `pin_int`
  (BigInt→BigRational insert) owns 57.5% of library-leaf samples; bigint
  division/drop ≈ 6.4%.
- Opportunity (**equivalent-work**): FxHashMap for `numeric`/`truths`/`cells`
  (TermId keys hash identically-fine with Fx); consider a narrow-int fast path
  in `pin_int`/reads that avoids BigInt boxing when values fit i64 (the
  `BigRational` small-value path, not a truncation — wide values keep exact
  bignums).

### 7. SAT conflict-analysis allocation churn — 12.8% lib on gate corpus

`nixie-sat/src/solver/conflict.rs:2032` `shrink_block` allocates two fresh
`SmallVec<[Var; 32]>` (`shrinkable`, `walk_marked`) **per block per conflict**;
`shrink_and_minimize_clause` also materializes via `SmallVec::from_iter`.

- Evidence: sat-carry — 12.8% of total samples are SmallVec leaves owned by
  `shrink_block ← shrink_and_minimize_clause` (55.9% of library-leaf samples);
  sat-scpc shows `shrink_block` 4.8% self.
- Opportunity (**equivalent-work**): hoist the two buffers into `Solver` state
  (the `propagation_buf` pattern used in EUF), clearing per block. Check
  whether `shrinkable` can be replaced entirely by the `MF_SHRINKABLE` marks +
  block range iteration (the vector is only a list of the block's vars — it is
  already iterated by index elsewhere).

### 8. SAT-core gate inprocessing on BV encodings — `ClauseArena::get` 33.5%

`nixie-sat/src/memory.rs:570` `get` (per-fetch header validation + Option
wrapping) driven by `gate_subsume::forward_subsume_matching` (7.5% self) and
`congruence::augment_big_with_gate_congruence` inside
`equiv::substitute_equivalent_literals_round`.

- Evidence: bv-sage — `ClauseArena::get` leaf 33.5%, gate-congruence +
  forward-subsume own ~39.8%/24.8% of library-leaf samples respectively.
- Opportunity (**structural**): batch clause views across the matching inner
  loop (fetch once per clause per round instead of per candidate pair), and/or
  cache the header-validated view for the duration of a matching round
  (`ClauseRef` stability discipline required). Needs the seeded protocol —
  this is inprocessing cost, not per-conflict, but identical work in a
  different order can shift tie-breaks.

### 9. `Simplex::row_stamp` recompute — 10.5% of UFLIA/Wisa

`nixie-theories/src/arithmetic/simplex/mod.rs:5794`: per basic per
`propagate_bounds_in` pass, re-sums `bound_ver` over the row's vars to build
the derivation-stamp key.

- Evidence: uflia-wisa — `row_stamp` owns the `wrapping_add` leaf (10.5%).
- Opportunity (**structural**): maintain incremental `sum_ver` per row, updated
  when `bound_ver` entries change (the affected rows are exactly the changed
  var's column — see finding 3's column index). Same stamps ⇒ same cached
  derivations ⇒ same trajectory, but proving bit-identical stamps under
  incremental maintenance requires care (associativity of wrapping add is
  exact, so the sum is order-independent — good).

### 10. Encoding-side repeated term scans on UFLIA (secondary)

uflia-25959 (encoding-visible share ~30% of samples in library leaves) spreads
across `mark_array_ops`, `collect_polarities`, `expand_lets`,
`subtree_exceeds_encode_depth`, `ctx_simplify`, `TermManager::intern` builders.
No single site dominates; a shared "one walk collects everything" pass would be
the shape, but that is a larger refactor with modest projected gain. Recorded
for completeness, not recommended first.

## What is deliberately NOT on the list

- `propagation_value` (40% leaf on sat-scpc) and `propagate_session_inner`
  (6.7–10.5% on SAT instances): expected CDCL propagation cost, in an already
  tuned kernel (list_kernel/block_filter studies in `docs/studies/`).
- The numeric-interface pin cost from the 0.3.4 investigation: correctness-tied,
  explicitly not blanket-approved, and owned by that document's protocol.
- VSIDS heap ops (`sift_up`/`sift_down` 2–7.7% on SAT): known, small, and
  touched by prior studies.

## Protocol for landing any item above

1. Equivalent-work items: full release verification bar + Z3 4.16.0 parity +
   single-seed perf gate demanding **bit-identical** counters (any drift
   reclassifies the change as heuristic). Add a regression pinning the touched
   invariant (e.g. derivation content equality, explanation validity).
2. Structural items: pre-register under `docs/BENCHMARKING.md`, ≥10 seeds,
   matched null where the mechanism could be inert, complete-work counters,
   fresh-seed replay.
3. No item is authorized by this scan alone; percentages are localization
   evidence, not effect estimates.

## Artifacts

Collapsed stacks, analysis scripts, and the harness source are under
`precompile/660166ad494aaed22979ed73d36ff33a13a669f/benchmark/profile-scan-2026-11-10/`
(harness rebuilds against the workspace via path deps; `pprof` 0.15, 250 Hz).
Reproduce a table with `python3 analyze.py <file>.collapsed` /
`python3 owners.py <file>.collapsed`.
