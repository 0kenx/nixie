# Handover — parser + watch-skip landed and priced; the fold-flip refused by its powered experiment; next: gate-based subsumption (2026-09-21, second session)

Continuation of `2026-09-21-sat-next-three.md`.  Items 1 and 1.5 are
landed and priced; item 2 is landed as pinned machinery with a refused
flip and a recorded landscape shift; item 3 remains the open lever and
its brief is sharpened below.  READ AGENTS.md FIRST (the git and
verification rules are non-negotiable; the `-rn` rg flag is the
replace-with-"n" flag — it mangles output, use `-n`).

## Landed this session

- `8d34ea72` **perf(sat): the SIMD DIMACS tokenizer + the load-time
  watch-scan skip.**  FlatCnf::scan: AVX2 boundary kernels + direct
  integer assembly (freeze-sentinel exactness, pinned against
  `str::parse` — the oracle caught a real threshold bug pre-landing);
  add_clause skips its two argmax watch scans when the trail is empty
  (all ranks tie `(1, u32::MAX)`, strict `>` keeps indices 0/1 —
  identity maps).  Gate 1.000; **paired instruction corpus geomean
  0.9333** (6s299b685 −29.5 %, 6s163 −27.6 %, GP_105 −11.5 %, search
  cells flat).  Study: `docs/studies/2026-09-21-simd-dimacs-parser.md`.
  Binary cached `precompile/8d34ea72/`; BASELINE re-pinned (`0a2d4ba6`).
- **feat(sat): the BVE-after-fold skip policy** (this session's second
  landing, sha in git log): `NIXIE_FOLD_BVE_SKIP=1` (threshold
  `NIXIE_FOLD_BVE_SKIP_PCT`, default 25 %) consumes phase-1's trigger
  without running it — advancing `elim_phases`, clearing marks, syncing
  `last_elim_fixed`/`lim_elim` (a completed zero-yield phase's
  bookkeeping; a bare `return false` would re-fire every conflict).
  Default off = gate-proven bit-identical.  Study:
  `docs/studies/2026-09-21-bve-after-fold-policy.md`.

## The two verdicts that reshape the next session

1. **The SSR-study landscape moved.**  On today's tree bv_ILA's default
   arm is 16,023 conflicts (was 302,978); the armed fold stack is a 2×
   win there (8,098); BVE-after-fold no longer re-entangles (BVE-off is
   now WORSE: 10,357).  Two intervening arcs moved both arms ~19×/44×.
2. **The fold-stack default flip is REFUSED** by the powered experiment
   (10 seeds × 12 cells, zero verdict mismatches): geomean ≈ 1.11×
   conflicts, regressions WS 2.01× / x9 1.77× / Carry 1.59× against
   wins frb 0.49× / circuit 0.96× / 6s299b685_Iter22 0.94×.  The knobs
   stay opt-in for the gate-dense family.

## Item 3 — GATE-BASED SUBSUMPTION (the open lever; sharpened)

From `docs/studies/2026-09-18-ite-gate-congruence.md` §"next slices":
kissat's `forward_subsume_matching_clauses` over repr-canonicalized
literals subsumed **108,484 clauses = 44 % of tried** on bv_ILA before
search.  This session's refused-flip verdict makes item 3 MORE
valuable, not less:

- It is the mechanism that would push the fold's retirement ratio past
  the `NIXIE_FOLD_BVE_SKIP` threshold (44 % ≫ 25 %) — the skip policy
  landed this session is the standing guard for exactly that
  composition; re-power fold+skip the moment subsumption lands.
- Port target FIRST per AGENTS.md: kissat `src/subsume.c` /
  `forward_subsume_matching_clauses` in `../temp/kissat`.  Our
  extraction lives in `nixie-sat/src/solver/congruence.rs`; the
  repr-canonicalization (union-find-root-keyed literals) already
  exists from the fold's class materialization.
- Bar: heuristic class (trajectories change) — verdict-agreement corpus
  + the powered experiment (the `/tmp/fold_ab.sh` pattern, committed in
  the study) + Z3 parity.  The paired instruction corpus
  (`bench/perf_gate/paired_instructions.sh`, committed `8d34ea72`)
  prices any cost claim.

## Standing traps (new this session)

- **Lucky pre-solving answers toy fixtures before the pre-search ELS
  block** — unit tests driving the arm need `enable_lucky: false`; the
  SSR tests' own fold assertions pass through the MID-SEARCH one-shot
  (`learn.rs` ~2162), not the pre-search block.  See the study.
- **Re-measure the premise before powering the experiment** — the
  item-2 specc'd for a tree that no longer exists.
- **Trap 24 (from item 1):** property-test the fast path against its
  reference BEFORE measuring (the freeze-threshold bug was invisible to
  the trajectory gate, trivially caught by the `str::parse` oracle).
- `__m256i` has no `BitOr` on stable — `_mm256_or_si256`.
- Disk: `/media/data` swung to 100 % twice; the shared `target/` was
  deleted once mid-session (by an agent reclaiming space).  Build with
  `CARGO_TARGET_DIR` elsewhere when tight; precompile binaries survive
  (they are in the repo tree, not `target/`).

## Where everything lives

- `docs/studies/2026-09-21-simd-dimacs-parser.md` — item 1's record
  (kernels, the parse_lit bug, the paired-corpus table).
- `docs/studies/2026-09-21-bve-after-fold-policy.md` — item 2's record
  (the landscape shift, the refused flip, the trigger-consumption
  semantics, the lucky-pre-solve trap).
- `bench/perf_gate/paired_instructions.sh` — trap 23's tool, committed.
- `/tmp/fold_ab.sh` pattern (in the study) — the powered A/B harness.
- `precompile/8d34ea72/nixie` — the current pinned baseline binary.

## First moves

1. AGENTS.md again; confirm tree health (`bash bench/perf_gate/run_gate.sh`
   → 1.000/1.000; the workspace suite's one known-red is the foreign
   in-flight `encode.rs` test — check `git status` for other agents'
   dirty files before blaming the tree).
2. Item 3: read kissat's `subsume.c` first, then `congruence.rs`'s
   extraction; land behind `NIXIE_GATE_SUBSUME=1` (default off), pin
   with differential unit tests, then the powered experiment — and
   re-power fold+skip on the same corpus (the composition thesis).
