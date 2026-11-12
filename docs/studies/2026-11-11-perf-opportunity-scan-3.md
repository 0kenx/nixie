# Perf opportunity scan #3 — FF theory, SAT front-end, and post-batch residuals at `896cddd8`

## Registered purpose

Third sampling scan after the scan #2 implementation round (F: EUF pop
trail, G: Arc row sharing, H: `nl_eval` fast paths; I reverted).  Goals:
(1) profile theory families never covered before — finite fields (the
`bench/ff` bn254 chains), the SAT front-end on large CNFs (satcomp mains),
transcendentals, strings/FP/datatypes/LRA; (2) re-read the residuals on
the campaign's standing instances after the landed batches.

## Method

Same harness and limitations as scans #1/#2 (in-process `pprof`, 250 Hz,
`execute_script` path, one run each, shares localize cost).  Rebuilt at
HEAD `896cddd8`.  Corpus: 17 workloads (3 FF chains, 7 residuals, 5
satcomp-2025 mains, storecomm, dense DL).

**Coverage negative results, stated up front:** the in-repo corpora for
strings (`bench/native_sequences`), FP/datatypes/arrays/LRA/NIRA
(`bench/z3_parity/benchmarks/qf_{fp,dt,a,lra}`, `bench/extended_theories`)
and transcendentals (`bench/trans`, 25 files) all solve in <1.5 s under
default settings — no measurable perf surface exists for those theories
in this repo's corpora.  FF chains are the exception (3.7–11.5 s).

| profile | instance | samples | done |
|---|---|---|---|
| ff-1024/512/256 | `bench/ff/bn254_chain_planted_{1024x1536,512x768,256x384}` | 3257/1964/771 | yes |
| arctic-1M | `QF_LIA/arctic-matrix/constraint-392137`, 35 s default-mode | 8657 | no |
| ufidl-vlsat | `vlsat3_f77` | 8723 | no |
| bv-sage | `Sage2/bench_9557` | 8300 | no |
| ufq-coilist/rbt/huffman | Barrett quantified UF | 8538/8305/8549 | no |
| aufia-sll, auflia-store40 | as before | 8683/8688 | no |
| idl-gryzzles | `asp/HamiltonianPath/gryzzles.8` | 7002 | yes |
| sat-14norm | satcomp25 `14.normalised` (CNF) | 5377 | no |
| sat-break12/ws500 | satcomp25 mains (CNF) | 8594/8669 | no |
| sat-ila96 | `bv_ILA_Piccolo_JALR` (CNF, solved 9.4 s) | 3055 | yes |
| sat-frb35 | `frb35-17-5_ext` (CNF, solved 5.5 s) | 1269 | yes |

## Findings, ranked

### 1. FF theory polynomial layer — the whole FF family's cost

- **ff-1024 (11.5 s): `ff_theory::linear_core` ~40%** — `MPoly::clone`
  materialization (`to_vec_in::ConvertVec` 30.5% + slice index 14.9% +
  `HashMap::clone` 3.5% + `Monomial::div` 3.1% + `BTreeMap` node pushes).
  Clone sites: `ff_theory.rs:378` (replay→atoms), `:458` (`uni.clone()`),
  plus coefficient clones in `linear_core`.
- **ff-256: `Monomial::grevlex_cmp` 35.8% + `PartialOrd::lt` 29.6%** —
  monomial ordering comparisons during poly inserts/sorts.
- **ff-512: `FieldCtx::mul_raw` 36.5% self** — the bn254 field multiply
  itself; if it is a per-limb portable loop, a 4-limb Montgomery CIOS
  carry chain (pure Rust, `u128` carries) is the standard 2–4× shape.
  Read `nixie-math/src/ff/field.rs` before designing.

These three are one work item (the FF chain path), with (a) clone
elimination likely equivalent-work, (b) ordering-compare and (c) mul_raw
needing their own designs.

### 2. SAT front-end on large CNFs — parse+intern is ~50% of sat-14norm

- **`SortManager::resolve_alias` SipHash 7.1%** — the SortManager's maps
  still hash with std `RandomState` while the rest of the codebase uses
  FxHash (`hash_term_key` already does).  Lookup-only usage ⇒ an
  FxHash swap is an equivalent-work candidate (verify no iteration-order
  dependence first).
- **Hashcons probe loads full Terms: `intern`'s find-closure 19.4% self**
  under `mk_or`/`build_variadic` — every bucket candidate pays a full
  `Term` arena load just to compare `(sort, kind)`.  Storing the 64-bit
  key hash beside each `TermId` in the `HashTable` bucket and comparing
  hashes first removes most candidate loads (equivalent-work: identity
  unchanged, only probe cost drops).
- Parser pipeline (`parse_term`/`close_op`/`build_variadic`) ≈ 15% —
  document-only unless the above two land and it still dominates.

### 3. `extract_binary_resolvents` — 21.9% of sage (SAT inprocessing)

`nixie-sat/src/solver/congruence.rs:606` snapshots every irredundant
ternary clause and re-derives binary resolvents per inprocessing round —
O(DB) per round regardless of what changed.  The CaDiCaL/Kissat shape
marks processed clauses and revisits only dirty ones.  Structural item:
read `../temp/kissat` + `../temp/cadical` inprocessing first,
pre-register under `docs/BENCHMARKING.md` (it can shift trajectories).

### 4. MBQI candidate lists — refined root cause for the reverted batch I

On rbt, `build_exists_candidate_lists` is 14.6% self + 17.8%
hash-probing leaves: the per-entry cost is the *hash probe* (term lookup
to read `.sort`), not the map iteration.  A `Vec<SortId>` side-table
indexed by `TermId` (sorts are immutable per term) would remove the Term
loads without batch I's bucket machinery.  Still gated on the
measurement dead-end documented in scan #2: rbt-class MBQI phases are
unreachable at fixed conflict/decision budgets, so an MBQI-iteration
budget must exist before any A/B can authorize the change.

### 5. arctic-1M residual — diffuse, algorithm-adjacent

`pivot` inline comparisons (`NonNull::eq` 15.5% + slice iter 11.4%) and
`DeltaRational::cmp` 7.9% are the simplex bound machinery itself;
`lhs_is_integral` re-walks rows on asserts.  No single lever ≥10%
remains — the slot/G landings removed the structural ones.  Document;
revisit only with a pre-registered structural idea.

### 6. EUF `use_list_push` — 30% of huffman

Congruence use-list appends (2581-sample `ptr::write` stack) — the
append-only use-list churn of the congruence closure itself (Z3 has the
same shape).  Document-only unless a Z3 read shows a cheaper
registration discipline.

### 7. SAT kernel micro (equivalent-work candidates)

- `mut_trace::cwrite_target` OnceLock read per watch-list scan = 7.2% on
  ila96 — cache the probe in `Solver` at init (the per-scan hoist
  already exists; the per-scan `OnceLock::get` is what remains).
- `shrink_block` 7.4% (break12), `subsume_round_impl` 7.0% (frb35),
  VSIDS `sift_down` 4.7–5.7% — known, prior-study territory.
- `big_span_start`/BIG span lookups 7.5% on ila96 — binary-clause
  propagation kernel; the list_kernel studies covered the long-clause
  side; the BIG side is the analogue candidate (structural, own study).

### 8. Standing confirmations

- vlsat: `derive_arith_bound_propagations` **77% self** — the #2
  columns-seeded bound-watch worklist remains the only lever (structural,
  trajectory-risk: fixpoint stored-bound order must stay pinned or the
  change reclassifies as heuristic).
- gryzzles: `update_cells` 85.6% (via inlined `Vec::push_mut`) — dense
  DL item #4 unchanged.
- store40: `is_full` 33.7% + `find_or_find_insert` 20.8% — item #7
  (intern key churn) unchanged.
- coilist is now fully diffuse (max share 7.5%) — batch F removed the
  giant; no further lever.

## Implementation outcomes (same-day follow-up session)

Items #2 (both), #7, #1a, #1c were taken through the gated protocol:
three landed, one fixup, one reverted with evidence.  All kept batches
are equivalent-work: bit-identical counters and verdicts across the A/B
portfolio, parity 171/0/6, perf gate 1.000/1.000.

| batch | commit | change | measured (vs parent) |
|---|---|---|---|
| J+K (#2) | `adfab1e2` | FxHash string interner (`Rodeo` alias + Debug-friendly newtype) + hash-reject hashcons probe (parallel `hashes: Vec<u64>` side array; GC's `table.retain` leaves it consistent) | **14.normalised 0.76×** (the profiled front-end unit), bv_ILA_Piccolo 0.80×, Carry 0.89×, 25959 0.90×, SCPC 0.92×, coilist 0.92×; geomean 0.947 |
| M (#1a) | `c7e5206a` + `9f8cd15a` | ff `linear_core` takes the pivot row instead of cloning it per eliminated row | ff-1024 0.97×, ff-512 0.98× — strictly less work, kept; residual is the certificate bookkeeping itself (snapshot clones + N×G identity polys), structural follow-up documented |
| L (#7) | `63bed214` | `ScanProbes` solver field snapshots the `NIXIE_CWRITE`/AVX2 gates; per-scan `OnceLock` reads gone | ila96 (profiled) 0.96×, sage 0.97×, coilist 0.97×; arctic 1.08×/peq 1.06× layout wobble; geomean 0.997 |
| N (#1c) | reverted | stack-backed CIOS accumulator (n ≤ 8) | FF targets UNMOVED (the loop arithmetic is the cost, not the per-call vec allocation) while the nixie-math rebuild wobbled unrelated instances to 1.23× at identical counters — negative result recorded in `field.rs` |

Campaign cumulative vs the original `660166ad` baseline (old set):
vlsat 0.62×, sll 0.95×, wisa 0.93×, wisas 0.95×, 25959 0.97×, arctic
1.00×, geomean 0.963; peq 1.20×/seq 1.07× are the standing layout
drift (identical counters, documented since the first batches).

Second follow-up session (2026-11-12), continuing the standing items:

- **vlsat derive rescan** (`62323220`): the fused pass rescanned every
  `var_to_parsed_arith` entry per call — 75.6% of a 25 s vlsat3_f77
  profile (the `assigned_pol_of` frames).  An ever-undecided atom
  worklist (built once per manager — the borrowed map is frozen for its
  lifetime; entries borrowed so the loop needs no lookups; compacted per
  call since `assigned_pol_of` is ever-set semantics) preserves the
  exact iteration order and skip conditions.  vlsat 0.95×/0.93×
  (A/B budget / deeper K=6000–10000), counters identical.  The 75%
  converts only partially: most of it is the cache walk over a
  mostly-undecided map, which the worklist shares — the rest needs the
  bound-watch redesign (derive only atoms whose variables' bounds
  changed), still deferred as trajectory-risk.
- **`iter_views`** (`3fa55066`): single-pass live-clause scan replacing
  the double view construction in whole-DB passes; first user
  `extract_binary_resolvents` (21.9% of sage).  Batch A/B read sage
  1.05×/arctic 1.11× at identical counters; interleaved re-measurement
  contradicted both (sage 0.97×, arctic 1.00×) — kept on mechanism +
  interleaved evidence.  Lesson repeated: batch-level cells wobble ±10%
  at identical counters; interleave before believing a regression the
  mechanism cannot explain.

Process note recorded after M: a clippy gate piped through `tail`
masked one failure (`needless_range_loop`, fixed in `9f8cd15a`); all
later gates test clippy's own exit status.

## Protocol

Unchanged: equivalent-work items → full bar + parity + bit-identical
counters; structural items → pre-registration, ≥10 seeds, matched nulls.

## Artifacts

Collapsed stacks + corpus under
`precompile/896cddd8…/benchmark/profile-scan-3-2026-11-11/`; harness
rebuilds from the scan #2 archive against the workspace.
