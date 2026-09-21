# The SIMD DIMACS tokenizer + the load-time watch-scan skip (2026-09-21)

Item 1 of `docs/handovers/2026-09-21-sat-next-three.md`, landed as one
slice.  Both changes are **bit-identical by construction** (same literal
stream, same watch pairs) and priced with the paired instruction corpus
(trap 23's tool, now committed as `bench/perf_gate/paired_instructions.sh`).

## The motivation (measured, standing)

- `FlatCnf::scan` was the **top profile symbol in every profile of the
  CSR arc** — 12.7 % of `14.normalised`'s whole run, ~21 % on
  load-dominated classes; the hwmcc anatomy had kissat 0.85 s vs our
  9.5 s on a 544 MB file, most of it parse.
- The 0-conflict families (GP, the normalised class) are essentially
  parse+load+propagate.
- The change is **world-agnostic**: both watch worlds (Vec default,
  `NIXIE_CSR_B=1`) pay the parser equally.

## Change 1 — the tokenizer (`nixie-cli/src/dimacs.rs`)

The scan kept its exact driver semantics (line/comment path, token
grammar, every error message byte-identical); two hot inner operations
were replaced and the integer assembly made direct:

1. **Whitespace skip / digit-run scan as AVX2 boundary kernels**
   (`skip_ws_avx2` / `scan_digits_avx2`): 32-byte blockwise
   classification — whitespace via five `cmpeq`s `or`-reduced (the exact
   `is_ascii_whitespace` set: space, `\t`, `\n`, `\x0C`, `\r` — *not*
   `\x0B`), digits via the `sub/min_epu8/cmpeq` trick — then one
   `movemask` + `tzcnt` to the boundary.  A 32-lane movemask covers a
   full `i32`, so `!m` + `trailing_zeros` is exact (the classic 128-bit
   version corrupts the high bits — this is an AVX2-only shape).
   Trailing partial blocks fall back to the scalar reference kernels.
   No gathers anywhere (trap 19); the kernels touch only the raw byte
   buffer (no struct-layout questions).
2. **Direct integer assembly** (`parse_lit`): the per-token
   `from_utf8` + `str::parse::<i32>` round trip replaced by accumulate-
   multiply over the ASCII bytes with a **freeze sentinel**: once the
   running magnitude exceeds `214_748_364`, one more digit proves the
   magnitude exceeds `2_147_483_649` — beyond every `i32` literal bound —
   so the accumulator clamps to `3_000_000_000` and the token is
   rejected at the end.  Unclamped accumulators are exact up to
   `214_748_364 * 10 + 9`, which covers every valid magnitude including
   `-2147483648`; arbitrarily long leading-zero runs stay safe in `u64`.
3. **Runtime gate**: AVX2 detected once (`OnceLock`), `NIXIE_NO_SIMD=1`
   opts out — the same pattern as `nixie-sat`'s list-kernel gate.  The
   kernels are `#[target_feature(enable = "avx2")]` under
   `#[cfg(target_arch = "x86_64")]`; `scan_body(raw, simd = true)` is a
   documented caller contract.

### The differential harness (written first, and it earned its keep)

`scan_tests` pins the two equivalence claims separately:

- `parse_lit_matches_str_parse` — boundary magnitudes around
  `i32::MAX`/`i32::MIN`/the freeze point, with arbitrary leading zeros,
  against `str::parse` itself.  **This test caught a real bug before it
  shipped**: the first freeze threshold was `200_000_000`, which
  rejected valid 10-digit literals whose 9-digit *prefix* crosses 2e8
  (`2147483646` → `None`).  The property test found it on the first
  run; the correct threshold is `214_748_364`.
- `scan_paths_agree_*` — the SIMD path vs the scalar reference on
  deterministic cases (well-formed, every malformed path, comments, the
  `'c'`-swallows-the-line quirk, invalid UTF-8, i32 overflow,
  `i32::MIN`), 32-byte block-boundary pokes (tokens at every offset
  near edges, whitespace/digit runs crossing edges, exact-multiple
  buffers, all-digit and all-whitespace final blocks, digit runs ending
  at EOF), and 3000 seeded-random cases (structured CNF, byte soup,
  hostile alphabet, headerless) comparing full `Ok`/`Err` results
  *including the exact error message*.

## Change 2 — the load-time watch-scan skip (`nixie-sat/src/solver/mod.rs`)

`add_clause`'s two-argmax watch-pair selection runs two O(n) scans with
a `watch_rank` call per literal (~5.2 % of run on the same classes).
With an **empty trail every literal ranks `(1, u32::MAX)`**
(`watch_rank`'s undefined case), the strict `>` tie-break then keeps
`best = 0` / `second = 1`, and both swaps are self-swaps — the scans
are **provably identity maps**.  The skip: `if
self.trail.num_assigned() != 0 { ...scans... }`.  Placement notes:

- `pre_check_effective_unit` runs before the selection and may only
  *shrink* the trail (`backtrack_to_root`); its `ForceUnitAtLevelZero`
  assignment happens *after* the selection, so the emptiness test sees
  the exact trail the scans would have.
- The `learn.rs` selection sites are search-time (trail non-empty);
  they are untouched.

## The measurements

Perf gate (trajectory-identity canary): **1.000 / 1.000 PASS** after
each change separately and combined; nixie-sat suite 1083/1083.

Paired instruction corpus (12 cells, `perf stat cpu_core/instructions/u`,
candidate vs the pinned `86846e39` baseline, verdicts+conflicts paired
bit-identical on every cell):

| cell | ratio (combined) |
|------|------|
| hwmcc xits-iso-6s299b685 (544 MB) | **0.7049** |
| hwmcc xits-iso-6s163 | **0.7236** |
| GP_105_308_40 | **0.8804** |
| 6s299b685_Iter22 | 0.9769 |
| circuit_48in64out_800gates | 0.9975 |
| Carry_Bits_Fast_19 | 0.9990 |
| s38584 | 0.9995 |
| SCPC-500-13 | 0.9998 |
| x9-07092 / b21 / frb35 / WS_500 | 1.0000-1.0001 |
| **geomean** | **0.9333** |

Parser alone was 0.9364 (the search cells carried +0.05-0.5 % dispatch
overhead); the watch-scan skip paid that back and added on the load
cells.  The motivating class beats the handover's projection: **-29.5 %
whole-run instructions on the 544 MB hwmcc anatomy instance**, against
a projected 10-15 %.

## Traps / notes for the next session

- **Trap 24 (candidate): property-test the fast path against the
  reference before measuring it.**  The freeze-threshold bug
  (`200_000_000` → `214748364`) would have produced wrong-error (not
  wrong-answer) behaviour on 10-digit literals — invisible to the
  trajectory gate, caught in seconds by the `str::parse` oracle.
- `__m256i` does not implement `BitOr` on stable — use
  `_mm256_or_si256` explicitly.
- The `lits` reserve heuristic (`raw.len() / 8`) under-reserves ~4× for
  typical CNF (one literal per ~2 bytes); on the 544 MB file that is
  two GB-scale regrows inside the parse.  Untouched here (allocation
  shape out of slice scope); if a future profile shows `realloc`
  dominating, size it from `len/2` — but re-price with the paired
  corpus, memory is not free on this box.
- The paired-instruction tool is now committed:
  `bench/perf_gate/paired_instructions.sh <candidate> [baseline]` —
  the pairing check (verdict+conflicts identical) is a hard failure
  unless `EXPECT_TRAJECTORY_SHIFT=1`.
