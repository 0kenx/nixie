# Handover — the SAT load-wall campaign closed; next: parser, then armed congruence, then gate-based subsumption (2026-09-21)

You are continuing the SAT-side work on the nixie repo
(`/media/data/proj/nixie`, multi-agent shared tree — **READ AGENTS.md
FIRST**; its git/verification rules are non-negotiable).  Everything in
this handoff is landed on `main`, verified, and binary-cached.

## Where main stands (arc close, 2026-09-20/21)

- `d2025ba0` HEAD at write time (other agents' graph-constraints arc
  closed on top of our landings).
- **The CSR-watches campaign is CLOSED with a full honest record**
  (`docs/studies/2026-09-20-csr-slice6-load-path.md`, seven addenda —
  the flip's corpus ledger killed it; see "the verdict" below).
- Tree health at handoff: perf gate **1.000/1.000 PASS**, nixie-sat
  suite 1116/1116, workspace 12,079/12,080 (the 1 timeout is the known
  load-flaky `scope_rebase_tests` MBQI test — passes isolated), Z3
  parity not re-run post-revert (nothing SMT-side changed; the last run
  on this machinery was 176/0/1).
- `bench/perf_gate/BASELINE` pinned `8d386c8c`, binary cached at
  `precompile/8d386c8c/nixie`.
- **Disk discipline**: `/media/data` swings to 100% (the shared
  `target/` is ~107 GB; other agents build concurrently).  Build with
  `CARGO_TARGET_DIR` on `/` when `/media/data` is tight; watch for
  ENOSPC truncating `.d` files — it looks like a compile error and
  isn't (cost us one suite run this arc).

## The verdict that shapes everything below

The slack-CSR flip (CSR as default watch representation) was landed,
then **reverted on a corpus-wide paired ledger: geomean 1.16×
instructions** (search-heavy cells +15-32%; the motivating load-heavy
instances were its *best* case at +3-6%; memory a wash; the surgery
payback measured negative).  Default = legacy `Vec` world;
`NIXIE_CSR_B=1` opts into the slack-CSR (bit-identical, all driver
optimizations intact).  The surgery/index machinery (752 lines) was
deleted.  **Trap 23** (recorded): the perf gate's wall band and its
trajectory-identity counters are BOTH blind to a uniform +16%
instruction cost — **the paired instruction-count corpus
(`perf stat -e cpu_core/instructions/u`, default vs predecessor, every
cell) is the required check for any change that claims cost-neutrality.
Run it on the standing corpus, not the motivating class.**

---

# Item 1 — THE PARSER (the next session; the load wall's residue)

This is where the original campaign's remaining payoff lives, it is
**world-agnostic (a pure win — both watch worlds pay it equally)**, and
it is the shape of SIMD that actually pays: a flat byte buffer.

## The measured motivation

- `FlatCnf::scan` is **12.7% of 14.normalised's entire run** and ~21%
  on load-dominated classes — the **top symbol in every profile this
  arc took**, in both worlds.
- The hwmcc anatomy (open item 5 of the congruence-arc handover):
  **kissat 0.85 s vs our 9.5 s** on the 544 MB file.
- The 0-conflict families (GP_190, the normalised class) are now
  essentially parse+load+propagate — parse is the single biggest lever.

## The code (read these first)

- `nixie-cli/src/dimacs.rs`: `FlatCnf::scan` (~line 824+) — one
  whole-file `read_to_end`, then a **byte-at-a-time loop**: per token it
  does `is_ascii_whitespace` classification, a digit-run scan, a
  `str::from_utf8` over the token, and `str::parse::<i32>`.  The `%`
  header and `c` comments take a slow line path (fine — they're rare).
- The CLI consumer: `nixie-cli/src/processor.rs` ~line 700 — walks the
  flat `lits` stream, per clause builds a `Vec<Lit>` (reused buffer,
  already optimized), calls `add_clause`.
- The deferred-load pair (`begin_deferred_watches` /
  `finish_deferred_watches`) is already on this path — the counting-sort
  materialization happens after the loop (B-gated; harmless in the Vec
  world as a no-op).

## The design (SIMD tokenizer; the classic shape)

1. **Blockwise tokenization over `raw`**: process 32 bytes at a time;
   classify each byte (whitespace / `-+` / digit / other) into a mask
   via `_mm256_cmpeq` families (AVX2 present on this box, no AVX-512 —
   check `rg avx /proc/cpuinfo` on any new hardware).  The token
   boundaries fall out of the masks; only boundary positions need
   scalar work.
2. **Bulk integer assembly**: a DIMACS literal is ≤ 9 digits — parse
   the digit run with at most two `u64` multiplies (or a small
   lookup-free loop); the per-token `from_utf8`+`str::parse` is pure
   overhead (digits are always valid UTF-8/ASCII — validate by mask,
   not by `from_utf8`).
3. **Slow paths stay slow**: the `p cnf` header line, `c` comments, and
   error reporting (report the byte offset, keep the messages
   byte-identical to today's where feasible).
4. **Bit-identity is FREE here**: the output is the same `(num_vars,
   lits)` flat stream — conflicts must be identical at every step.  The
   verification is the perf gate (1.000 counters) plus the paired
   instruction corpus for the *cost* claim.
5. **The `scan_clause_for_attach` bonus** (~5.2% of the run on the same
   classes): `add_clause`'s watch-pair selection runs two argmax scans
   over the clause literals even when the trail is empty (all
   `watch_rank`s tie → the result is provably `(lits[0], lits[1])`, no
   swaps).  An "any literal assigned?" pre-check (or a solver-level
   assigned-counter check) skips both scans at load time — bit-identical
   by the tie-break argument (`>` is strict, first index wins).  Read
   `nixie-sat/src/solver/mod.rs` ~line 4055-4085 (the selection) and
   3580 (`scan_clause_for_attach`) before touching it.

## Traps for this session (from this arc, apply directly)

- **std::arch gather addresses through typed pointers** (trap 19) — a
  byte-indexed gather does not exist; misuse reads wild addresses as a
  sys-time fault storm.  The tokenizer wants `cmpeq`/`movemask`, not
  gathers.
- **`#[repr(C)]` is load-bearing** on any struct whose fields SIMD
  touches (`Watcher` carries the comment; the tokenizer touches only
  the raw byte buffer, so no struct questions here).
- **Validate with a differential unit test on the tokenizer** against
  the scalar scanner over randomized inputs INCLUDING malformed ones
  (the parse-error paths must stay reachable and equivalent).
- Wall-clock is void under load (trap 16); instructions are the
  currency; the paired-corpus rule (trap 23) gates the landing.

## Expected outcome (from the profile shares)

Parse is ~13-21% of these runs; a 5-10× tokenizer takes that to 2-4% —
a **10-15% whole-run instruction win on the load class**, both worlds,
zero trajectory risk.  That is larger than the entire CSR delta this
arc chased.

---

# Item 2 — THE ARMED-CONGRUENCE DEFAULT FLIP (search-quality lever)

`docs/studies/2026-09-18-ssr-binaries.md` §4-5 is the complete brief;
the short version:

## The measured state

- With `NIXIE_SSR_BIN=1 NIXIE_ELS_PRESEARCH=1`, **our congruence fold
  produces a residual kissat solves in 9,430 conflicts — identical to
  kissat's own full pipeline (9,465).  The preprocessing collapse is at
  PARITY.**  The remaining gap is pure search quality on the same
  formula.
- bv_ILA armed: 354,947 conflicts vs 302,978 default — **net-negative
  today** because the conflict-scheduled BVE runs right after the fold
  and re-entangles it (355K with BVE vs 155-172K with
  `NIXIE_SAT_BVE=0`; the 36M-resolution phase-1 elim is the destroyer;
  kissat's eliminate barely fires there because `substitute` already
  did the work).

## The slice

The **BVE-after-fold policy**: skip or budget the elimination when the
pre-search fold actually collapsed the formula (the
`eliminating_presearch` fixpoint result is the natural gate — e.g.
"if the fold removed ≥ X% of clauses, skip phase-1 BVE / cap its
resolution budget").  Risk: the BVE-averse families from the fold
study.  Then:

1. Fix the policy (gated, default-off).
2. **Powered experiment** per `docs/BENCHMARKING.md`:
   `GATE_SEEDS=10`, 10 seeds × the 30-instance standing corpus, 60 s
   cap, cells recorded via `benchstore.py` under
   `precompile/<sha>/benchmark/`.
3. If the powered verdict is green (no family regresses beyond the
   band), flip the default; the env knobs die.

The residual-dump tooling for A/B on identical formulas
(`NIXIE_DUMP_ELIM_ENTRY`) already exists and is the cleanest probe
surface in the repo — every search-quality knob can be tested on the
frozen 366K-clause residual without preprocessing interactions.

---

# Item 3 — GATE-BASED SUBSUMPTION (the structural gap to kissat)

From `docs/studies/2026-09-18-ite-gate-congruence.md` §"next slices":

- kissat's `forward_subsume_matching_clauses` over
  repr-canonicalized literals **subsumed 108,484 clauses = 44% of tried
  on bv_ILA** before search starts; we extract the gates but don't
  subsume through them.
- Directly shrinks the 36M-resolution BVE phase on this family (the
  same phase item 2 has to budget around — items 2 and 3 compound).
- Port target: read kissat's `src/subsume.c` /
  `forward_subsume_matching_clauses` (in `../temp/kissat`) FIRST per
  AGENTS.md; our extraction lives in
  `nixie-sat/src/solver/congruence.rs` with the repr-canonicalization
  already in place (the fold's class materialization keys literals by
  union-find root — the canonical literals exist).
- Gates: trajectory-identity is NOT available (it changes which
  clauses survive — heuristic class); the bar is the standard screen
  (verdict agreement corpus-wide + the powered experiment + Z3 parity
  for the SMT surface).

---

## Where everything lives

- `docs/studies/2026-09-20-csr-slice6-load-path.md` — the CSR campaign's
  complete record (seven addenda; the flip's ledger, the SIMD
  findings/traps 19-21, the surgery verdict, the revert + deletion).
- `docs/studies/2026-09-18-ssr-binaries.md` — item 2's measured arms.
- `docs/studies/2026-09-18-ite-gate-congruence.md` — item 3's numbers.
- `docs/handovers/2026-09-19-sat-congruence-arc.md` — the congruence
  arc's full context (items 2-5 there = items 2-3 here).
- `bench/perf_gate/` — the gate + corpus; the paired-instruction-count
  pattern (trap 23's tool) is one `perf stat` invocation per arm.
- `precompile/8d386c8c/nixie` — the current pinned baseline binary.

## First moves

1. Read AGENTS.md (again — the stash trap bit once this arc; per-file
   staging from a worktree is the rule).
2. Re-run the gate to confirm tree health (`bash
   bench/perf_gate/run_gate.sh` — expect 1.000/1.000).
3. Start item 1 (the parser): read `FlatCnf::scan`, write the
   differential tokenizer test FIRST, then the SIMD path behind a
   runtime knob (`NIXIE_NO_SIMD=1` exists as the opt-out pattern), then
   measure with the paired instruction corpus.
