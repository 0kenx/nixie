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
