# The parse-pipeline follow-up: profile-driven wins, priced ablations, and the fused blockwise tokenizer (2026-09-21, third pass)

The SIMD tokenizer (`8d34ea72`) took the load class to −29 %.  "Below
expectations" was right: a symbolized profile of the 531 MB anatomy
(`--profile perf`, `strip=none` — the release profile strips symbols;
`--config 'profile.release.strip="none"'` does NOT relink, and
`RUSTFLAGS -C strip=none` is overridden by the profile) showed the
remaining load-path budget:

| symbol | share |
|---|---|
| `FlatCnf::scan_sized` (the scalar driver between kernels) | **36.9 %** |
| `skip_ws_avx2` + `scan_digits_avx2` (per-token kernel calls) | 20.6 % |
| `drop_in_place<Solver>` (per-file teardown!) | **7.45 %** |
| `BinaryImplicationGraph::ensure_codes` (per-binary BIG growth) | 5.34 % |
| memmove / memset (alloc churn + var-array zeroing) | 15.5 % |
| resize cluster (CHB/LRB/VSIDS/Trail at `new_vars_bulk`) | ~9 % |

## What landed

1. **The fused blockwise tokenizer** (`scan_tokens_fused`): one load +
   two masks per 32 *bytes*; tokens walked with `tzcnt` arithmetic
   inside the block (start from the non-ws mask, run from the inverted
   digit mask), `parse_lit` and the clause/var bookkeeping unchanged.
   The scalar driver stays the reference semantics and owns every
   non-fast path: `c`/`p` lines, tokens touching a block edge, the
   <32-byte tail, and all errors — each fused stop returns to it and
   the loop re-enters fused mode (progress guaranteed per stop).
   Two real bugs shipped in drafts and were caught by the differential
   harness *before any measurement*: (a) the digit mask stayed
   block-relative while positions went frame-relative — every token
   after the first in a block read wrong bits (randomized iter 2);
   (b) the final block can end exactly at `n` and the driver then read
   `raw[n]` — the loop-head re-check is the exit.
2. **`mem::forget(sat)`** after the DIMACS fast-path solve: the drop is
   millions of small deallocations (15.8M watch-list `Vec`s alone) with
   every consumer of the solver already served (stats absorbed); the OS
   reclaims.  Multi-file batches pay one solver-footprint per file —
   the documented trade.
3. **The deferred-BIG pair wired into the DIMACS load**
   (`begin_deferred_big`): built and validated in the CSR campaign, but
   the producer side was never called anywhere.  Bit-identical,
   measured instruction-neutral; kept for its structural win (exact-size
   BIG, no per-literal doubling churn — the campaign's original
   motivation).
4. `scan_sized` (file-length hint for the whole-file buffer).

## What was tried and REFUSED (priced ablations, do not retry blind)

- **`lits` exact upper bound (`len/2 + 1`)**: **+3.2 % instructions on
  the load cells.**  mimalloc's large-allocation path costs more than
  the doubling regrows it saves — the "GB-scale memmove" theory was
  wrong for this allocator (large reallocs are remap-cheap).  Reverted
  to `len/8`.
- **Vec-world counting-sort watch materialization** (extending the
  CSR-B deferred build to `Vec<Vec<Watcher>>`): **+5.4 % on 6s299b685,
  +5.0 % on 6s163**, search cells flat.  15.8M exact allocations cost
  more than push-grown doubling lists under mimalloc.  Deleted; joins
  the CSR campaign's verdict that the Vec world's allocator handles its
  own churn.

## The measurements (paired instruction corpus, 12 cells)

| cell | SIMD-only (8d34ea72) | this pass | cumulative |
|---|---|---|---|
| 6s299b685 (531 MB) | 0.7049 | **0.839** | **0.592 (−41 %)** |
| 6s163 | 0.7236 | **0.825** | **0.597 (−40 %)** |
| GP_105 | 0.8804 | 0.983 | 0.866 |
| search cells | 1.000-1.002 | 0.997-0.999 | — |

(Each pass's ratio is against its own immediate predecessor; the
cumulative column chains them.)  Conflicts bit-identical everywhere;
verdicts paired.  The hwmcc anatomy's parse+load side (kissat 0.85 s vs
our 9.5 s at campaign start) is now a fraction of its former self.

## Traps

- **`--config` profile overrides dirty every dependent crate** — a
  full rebuild hits whatever in-flight breakage other agents have in
  the shared tree; profile in a worktree.
- **`#[cfg(feature = "std")]` is a no-op in nixie-cli** (no such
  feature) — a debug print guarded by it silently compiles out.
- Rust's `Debug` for slices **truncates long arrays** — a
  counterexample extracted from a panic message is a prefix, not the
  input; replay the generator from the seed instead.
- The differential harness paid for itself twice more: both fused-pass
  bugs were caught pre-measurement, one of them (the frame mismatch) by
  randomized iteration 2 of 3000.

## Addendum — the lazy BIG `extra` and the `parse_lit` fast path (same day)

The post-landing profile (symbolized) put two more items on top:
`ensure_codes` at 7.4 % (its `extra.resize(2·V, Vec::new())` zeroing
380 MB of empty `Vec` headers on the 7.9M-var anatomy — lists that
stay empty outside search-time appends) and `parse_lit` at 16.6 % of
the whole run (per-byte iterator/bounds overhead in the digit loop).

- **Lazy `extra`**: the overflow lists grow on first append
  (`extra_push` extends to the touched index); every reader goes
  through `extra_list(code)` (a short `extra` reads as all-empty).
  `span_end`/`live` still resize eagerly (every code's span must stay
  addressable).  Three direct-index readers outside mod.rs needed the
  accessor (`session_kernel`, `equiv` ×2 — the 24-test breakage when
  one was missed was the tell).
- **`parse_lit` fast path**: runs of ≤8 digits with 8 readable bytes
  parse from one `u64` load with a register-only accumulate (≤8 digits
  cannot overflow; the freeze logic stays for longer runs); the range
  decision hoisted into a shared `finish_lit`.

Paired corpus vs `ac7f5404`: 6s299b685 **0.892**, 6s163 **0.890**,
GP_105 0.973, search cells flat, conflicts bit-identical, geomean
**0.979**.  **Cumulative vs the pre-SIMD baseline: −47 % whole-run
instructions on the hwmcc anatomy** (24.85G → 13.11G), −47 % on 6s163.

Wall on the anatomy (loaded box, cold-cache first run excluded):
~11 s → ~8-9 s vs kissat's 1.0 s — the remaining gap is the solving
machinery (the instance decides UNSAT with 0 conflicts — preprocessing
work, not parse).

## Addendum 2 — the block-edge inline completion measured NEGATIVE (do not retry this shape)

The post-`bf938922` profile still showed the block-edge token round
trips (`scan_digits_avx2` 7.6 % + much of the driver's 8.8 % — every
32-byte boundary bails one token to the scalar driver, which re-enters
the per-token kernels; ~16.6 M round trips on the anatomy).  Completing
edge tokens *inline* in the fused loop (a `complete_digit_run` byte
walk across the boundary + a shared `emit_lit`, resuming the block
loop at the token's end) was tried in three forms:

| form | 6s299b685 instructions |
|---|---|
| landed baseline (`bf938922`) | 13.11 G |
| shared `emit_lit` helper (also hot path) | **18.67 G (+42 %)** |
| `#[inline(always)]` helper | **15.89 G (+21 %)** |
| straight-line hot path + helper only on edge | **15.45 G (+18 %)** |

The hot path refusing the helper explains form 1-2 (the `?`-carried
`String` error paths outline the body); but form 3 — with the hot path
byte-identical to the landed code — still costs +18 %: **carrying the
completion logic inside the block loop itself disrupts its register
allocation**; the cold-`return`-to-driver shape of the landed code is
what keeps the loop tight.  The round trips are cheaper than the
in-loop alternative.  Reverted; the scan's landed shape is the end
state of this arc.

## Where the parse pipeline stands (arc close)

Cumulative vs the pre-SIMD baseline on the hwmcc anatomy:
**24.85 G → 13.11 G whole-run instructions (−47 %)**; 6s163 −47 %,
GP_105 −13 %.  The remaining load-path budget (post-`bf938922`
profile): the fused scan 42.9 % (≈5.6 G — parse proper), memmove
12.4 % (watch-list push growth — the counting-sort materialization was
measured +5.4 % and refused), memset 9.4 % (`new_vars_bulk`'s ~20
V-scaled arrays + the 380 MB watch-outer headers — the latter is the
Vec-world architecture the CSR campaign priced), the scalar driver
8.8 % + boundary round trips 7.6 % (priced above), resize cluster ~9 %
(heuristic bookkeeping arrays, semantically necessary zero-fill).
Wall on the loaded box: ~8–9 s vs kissat's 1.0 s — most of the
remaining gap is the *solving* machinery (the anatomy decides UNSAT
with 0 conflicts; the fold/BVE preprocessing dominates what's left
after parse).  The next parse-side lever would be architectural (the
watch-list world), already priced and refused by its corpus ledger.
