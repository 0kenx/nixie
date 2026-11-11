# Perf-opportunity implementation batches — 2026-11-10/11 (follow-up to the opportunity scan)

## Registered task

Baseline the HEAD `660166ad` binary, then implement each opportunity from
[`2026-11-10-perf-opportunity-scan.md`](2026-11-10-perf-opportunity-scan.md),
benchmark, and keep or revert. Landing bar per AGENTS.md (build, nextest,
clippy, fmt, doc, Z3 4.16.0 parity, perf gate) for every kept batch;
counters must stay **bit-identical** (equivalent-work class) — any drift
reclassifies the change as heuristic.

## Method notes (what the baseline taught)

- **Wall-clock harness v1 was wrong**: parallel batches shared the pinned
  CPU and inflated times ~2×, manufacturing a phantom 2.4× win (sll
  "7.66s→3.2s" was 3.15s all along, serialized). All decisions below use
  the serialized v2 harness (one run at a time, CPU 18, min-of-reps,
  `STATS=1` counters). Harness + raw TSVs archived under
  `precompile/a76709df196e7a8c0dc29cb103b71341e74e5126/benchmark/perf-batches-2026-11-10/`.
- Budget metrics must reach the phase the optimization targets: the sll
  conflict-budget (4k) never reaches the later phase where the scan's
  13.9% `BoundType::clone` lived; CPU-time sampling (pprof harness,
  immune to contention) verified work reductions in those phases.
- The single most consequential phenomenon: **per-crate codegen layout
  lottery**. Any edit to a crate's hot unit reshuffles unrelated
  instances ±6–15% at identical counters and strictly-less work (CPU
  shares verified equal-or-lower). Verified directly: identical-source
  rebuilds are bit-stable; the baseline binary was reproducible (8.6s);
  five variants of one change all landed in the same 9.4–10.4s band on
  arctic while helping everything else. Portfolio geomean + CPU-share
  evidence is the only honest arbiter here.
- nia-100 is natively bimodal (0.11s/1.1s clusters at identical counters)
  — excluded from geomeans.

## Batches

### LANDED — A: simplex `find_violating` deferred clone + term-list probes (`6abc321a`)

Clone the winning `Bound` once at return instead of per violating row;
`terms_len`/`any_var` answer the two list-materializing probes without
building lists. CPU share of `find_violating` on sll's late phase:
14.3% → 12.9%. Wall: sll/wisa/wisas 0.95–0.96; arctic +6–10% (layout;
counters identical, CPU equal-or-lower). Gate 1.000.

### LANDED — B: DL bound-propagator fused single pass (`91e9f6fc`)

The headline win of the scan: `derive_arith_bound_propagations` scanned
`var_to_constraint` + probed `var_to_parsed_arith` per entry + collected
an intermediate Vec, per arith assertion, then re-probed per candidate.
Now one probe-free pass over `var_to_parsed_arith` with an
`eq_placeholder` flag set at the `TermKind::Eq` encode site. **vlsat3_f77:
14.42s → 9.01s (0.62×)** at identical counters (decision budget 3000).
Non-DL instances pay only layout (arctic 1.15, 25959 1.12 — the
propagator never runs there). An intermediate variant (iterate
`var_to_constraint`, one probe) measured 11.7s — the flag variant is
strictly better and chosen.

### LANDED — C: EUF congruence buffer reuse + signature match without key builds (`b593a1be`)

Per-merge-event `args_buf` (the `canon_buf` pattern extended to raw
args) and — replacing the per-hit `canon_buf.clone()` + `sig_table`
probe — an exact scan of the small fingerprint bucket against each
node's current `node_sig_key`. Content-identical matching; `sig_table`
and its pop trail untouched. vs B: sll 0.95, bv-sage 0.92, arctic 0.93,
25959 0.93. uf-peq improves vs the args-only build (12.34→12.05s) but
retains +13% vs baseline (cross-crate layout; strictly less work per
entry at identical counters).

### LANDED — E: nl_eval FxHashMap (`a76709df`)

SipHash → FxHash for `Interpretation`'s maps and the eval memo maps
(lookup-only semantics; the entries() iterators are documented
unspecified-order with no callers). SipHash-touching CPU on nia-4:
22.0% → 3.6%. **nia-4 (VeryMax/SAT14/4) end-to-end: 14.2s → 8.9s
(0.63×; 16.6s→9.0s in the pre-batch environment), same verdict.**

### REVERTED — D: SAT `shrink_block` buffer hoist

Implemented exactly as designed (two `SmallVec<[Var;32]>` per block per
conflict → solver-state buffers). Counters identical, but SAT targets
were dead neutral (carry 4.34→4.36: blocks rarely exceed the inline
capacity of 32, so the "allocations" never left the stack) and the
portfolio paid 1.02 via layout. Honest keep/revert verdict: **revert**
(`git checkout`, no landing).

### REVERTED — #5: EUF `expl_cache` epoch invalidation

Implemented (epoch-stamped LRU entries, five clear-sites → epoch bumps,
observable behaviour provably identical). Measured **exactly 1.000**
geomean: the LRU-1024 clear was effectively free in practice. No
demonstrated benefit → reverted to keep the diff minimal (same
discipline as D).

### DEFERRED (with evidence, not attempted-blind) — #3b, #8, #9

- **#3b simplex column O(1) maintenance** (Z3 `static_matrix`
  back-pointers): the real fix for arctic's 39.6% `column_drop_known`
  scan. Nixie's immutable `Arc` rows cannot host Z3's in-row offsets; a
  side-table slot index breaks on `substitute_row_fast`'s row rebuilds,
  and hash-set columns change iteration order (heuristic reclassification).
  Needs its own registered design; arctic's residual +8% vs baseline is
  documented layout sensitivity, not search cost (counters identical).
- **#8 gate-subsume arena fetches**: the canonical sets are already
  materialized (`sets` map) — the arena `get` is one-per-clause per
  round, diluted end-to-end (bv-sage budget 0.99–1.00). No contained
  fix with demonstrable end-to-end win; D's precedent says neutral
  SAT-side changes get reverted anyway.
- **#9 incremental `row_stamp` sum**: 10.5% CPU share inside
  `propagate_bounds_in` on wisa, but wisa already sits at 0.95
  cumulative and the change touches the layout-fragile simplex crate
  for an unclear end-to-end margin.

## Cumulative outcome (final binary `a76709df` vs baseline `660166ad`)

Serialized, fixed CPU, min-of-reps, identical counters on every instance:

| instance | base | final | ratio |
|---|---:|---:|---:|
| ufidl-vlsat (K=3000 dec) | 14.42 | 9.01 | **0.62** |
| nia-4 (end-to-end) | 14.22 | 8.92 | **0.63** |
| uflia-wisas | 1.09 | 1.03 | 0.95 |
| uflia-wisa | 2.43 | 2.31 | 0.95 |
| aufia-sll (K=4000 conf) | 3.13 | 2.96 | 0.94 |
| sat-s38584 | 2.08 | 2.06 | 0.99 |
| bv-sage (K=8000 conf) | 12.12 | 12.06 | 0.99 |
| uf-seq | 3.62 | 3.61 | 1.00 |
| sat-carry | 4.34 | 4.34 | 1.00 |
| sat-scpc | 8.98 | 9.53 | 1.06 |
| uflia-25959 | 3.96 | 4.13 | 1.04 |
| lia-arctic (K=600k dec) | 8.49 | 9.11 | 1.07 |
| uf-peq (K=10k conf) | 10.70 | 11.80 | 1.10 |

Geomean (12 timed instances) ≈ **0.969**, with two family-level wins
(QF_UFIDL −38%, NIA model-search −37%) and layout-lottery taxes of
+4–10% on three instances whose counters and CPU shares are identical
or better. Every landed batch passed the full bar (nextest 12,797,
clippy, fmt, doc, parity 171/0/6 = the tracked record, perf gate
1.000/1.000). Binaries cached under `precompile/<sha>/` for
`6abc321a`, `91e9f6fc`, `b593a1be`, `a76709df`.

## Process findings worth keeping

1. **One failed measurement is not a verdict**: vlsat's first "win"
   (contended harness) and sll's "2.4×" were artifacts; arctic's
   "regression" survived five bisections before revealing itself as
   binary layout, not code. Bisect, serialize, CPU-sample, and check
   identical-source rebuilds before believing any number.
2. **Combos matter in both directions**: A1's rewrite *destroyed* the
   probes' win when combined (6.3s vs 3.2s on the contended harness);
   C's two pieces only made sense together; D looked fine until the
   portfolio view. Always measure the batch, not just the piece.
3. The repo's deterministic-counter discipline is what made all of this
   decidable: every keep/revert call above rests on bit-identical
   trajectories, so wall differences could be attributed to real work
   or layout — never to search reshuffling.
