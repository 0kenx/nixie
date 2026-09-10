# Handover: QF_BV gap vs z3 — Tier A landed (elim-uncnstr, cohencu), Tier B next

Written 2026-09-10 (evening), superseding the Tier-A prompt in
`2026-09-10-qf-bv-gap-tier-a.md`. Everything below is measured and banked.

## Where the campaign stands

509-file stratified `QF_BV` sample, 25 s cap, z3 4.16.0 (banked column):

| state | solved of 509 |
|---|---|
| pre-campaign baseline (u64-wrap fix landed) | 266 |
| after Tier A | 276 |
| **after the depth-guard frontier fix (a1a08ec0)** | **283** |
| z3 | 281 |

The depth-guard fix (see the commit) made the assert-time depth guard
measure the *recursion frontier* instead of total structure — deep
bit-vector operation chains and BV-sorted ite chains are iterative
territory — converting 7 sample files (+10 more outside it, all
header-correct) from instant spurious `Unknown`.  Nixie now solves
three sample files z3 4.16.0 times out on (smulov3bw0512/0768,
float/square.3.0.i).

Zero verdict disagreements vs z3 at every step. The remaining net gap of
~5 files is a set of *load-flaky boundary files* (see below) plus the
Tier-B search-class losses.

## What landed (all on main, batteries green)

1. **`elim-uncnstr` port** (256bb0e6) — `bv_elim_uncnstr.rs`, z3's
   operator rules over exactly-once variables, gated take-over routing
   (rewrite must shrink the goal ≤75 %), assert-time circuit deferral for
   wide div/mul with candidate variables, model completion + definition
   reconstruction, `eval_bv_value` model second-chance, BV `distinct`
   evaluation. **brummayerbiere4/unconstrained01–10: 0/10 → 10/10**
   (~0.06 s each).
2. **Ring solve-eqs stage-4 un-gating (literal-only)** (ed50002) — the
   historical gate rested on a false premise (the ring pass has been
   odd-pivot/unit-only since birth; the recorded false-sat was the
   *linearity* bug). Literal ring rewrites are now asserted alongside;
   non-literal ones stay off (three boundary regressions measured).
   **cohencu.c_2/3/4 solved** (+ s3_srvr UA2019, uclid catchconv-1568
   as side effects).
3. **Parser ill-typed-term rejection** (3016567) — `ite` with a
   non-Bool condition and `=`/`distinct`/chainables between different
   sorts are now parse errors, as in z3; `Int`/`Real` stay one
   compatibility class (numeral polymorphism + nixie's `to_real`
   embedding). Two in-repo test scripts turned out ill-typed and were
   corrected (see the commit; the float64 one's old `sat` verdict was an
   artifact of the very leniency this removes). Verdict-neutral on the
   509-file corpus (0 parse rejections).

Binaries: `precompile/7ba2f401/nixie` (HEAD; md5 c832538c…),
`precompile/b4968556/nixie`, `precompile/256bb0e6/nixie`. Cells:
`precompile/*/benchmark/bv_gap/final_rescreen.jsonl` — the recorded
7ba2f401 run is the load-settled one (load ≈ 8): **276/509**, 0 verdict
changes vs the baseline, 0 z3 disagreements. An earlier run under load
36–43 read 267 with the identical binary — pure contention; always
check `uptime` before believing a re-screen. Re-screen runner:
`precompile/ac13904/benchmark/bv_gap/rescreen.py` (509 files, max 4
concurrent, cores pinned).

## The screened-out item (do not re-try unchanged)

Tier A item 2 (structural concat/extract rewriting for bitrev1024,
bench_4443, calypto 14/19, BuchwaldFried, maxandminor016) was
implemented, measured, and **reverted**: zero per-cell differences in a
matched-null A/B (`NIXIE_BV_STRUCT_RW` on/off, same binary), and a
deterministic **false `unsat`** on `RWS/Example_1` (reduced to a
49-assert prefix; only six width-126 `bvlshr`-by-1/2/3 rewrites fire)
that survived term-level brute-force equivalence tests at widths ≤ 63.
Full findings + revival path in
`docs/studies/2026-09-10-bv-structural-rewriting-screen.md`. The
revival path starts with root-causing that width-126 interaction (prime
suspect: the bit-blaster's concat/extract encoders, or a >64-bit-width
assumption in a rule interaction) and moves to n-ary concat piece lists
— the binary-spine seam splits are what keep bitrev0512+ from closing.

## Tier B triage (2026-09-10 night session)

The near-misses (solved 30-47 s against the 25 s cap: `maxandminor016`
30 s, `bv-term-small-rw_1300` 34 s, `ex7_prime` 41 s — unified path
fastest on all three) need ~2x search speed, not routing.  BuchwaldFried
needs z3's propagate-values/solve-eqs rewrite chain (the screened-out
structural family).  `smulov1bw12` is resolution-hard for our CNF (kissat
needs 31 s; z3's own encoding+inprocessing wins 40x) — an encoding-level
problem.  **Routing is ruled out as a lever**: the wide-`bvmul` flag that
should divert mul-heavy goals to the eager CEGAR dispatch has been dead
since stage 4 (its only setter cannot fire on well-typed input), and
reviving it measured −6 files (see
`docs/studies/2026-09-10-wide-mul-routing-flag.md`).  The remaining
Sydr/s3_clnt/spear cluster needs the CEGAR refinement tiers or the
unified path's word-level reasoning improved *in place*.

## Tier B (the original framing)

Search-class losses where z3 needs 1–24 s: `Sydr/master/cjpeg`
predicates (5 — bvmul CEGAR territory), `bmc-bv-svcomp14/s3_clnt*` (4),
`spear/samba` (2 + more near-misses), `Sydr symbolic_memory`, Wolf
zipcpu, brummayerbiere2 smulov/umulov wide-mul overflow, nlz 256-bit
variants. These need measured work on the CEGAR lemma tiers or the
search — read `docs/BENCHMARKING.md` first; every claim needs the
matched-null discipline (a bare before/after is not evidence on this
box, which regularly runs at load 30+).

## Operational cautions (still true)

- Never trust a verdict without the binary's md5 in the same shell block;
  never source benchmark binaries from a shared `target/`.
- This box is *shared and often loaded*: boundary-file flips (the five
  known ones: `countbitsrotate128`, `log-slicing/bvsub_10979`,
  `pspace/power2sum.6296`, `mcm/54`, `RWS/Example_19` — z3 says unknown
  on 4 of 5) are load noise, not regressions; always run a serial paired
  control before believing a flip.
- Worktrees need the corpus symlinks (`smt-lib`, `satcomp2024/25`,
  `satlib`); delete them when done.

## Addendum (2026-09-11): option 1 resolved — no AIG pass to wire; constants re-opacified at op boundaries

The option-1 premise ("check whether an AIG simplification pass exists but
isn't wired") is answered: `bv/aig.rs`, `aig_builder.rs`, and
`bitblast_advanced.rs` are standalone test-only modules — nothing to wire.
[CORRECTED 2026-09-11 evening: the first write-up here said the blaster
alone closes the goal — that was a probe artifact (the corpus file's
trailing `(exit)` ran before the appended tactic).  The corrected stage
bisect: `then bit-blast sat` **times out**; `then simplify bit-blast sat`
answers unsat in 206 ms — the **term-level simplify before blasting** is
the lever, not the blaster.]  The gap it exploits: folded constants stay constants through the
whole DAG in z3's rewriting layer, while nixie's op results re-opacified
them into pinned fresh variables.

Landed (see `docs/studies/2026-09-11-bv-constflow-results.md`):

- **Op encoders over signals** (default-on): `bv_sub`/`bv_neg` single-pass
  ripple (`a + ~b + 1`, no temp vectors), barrel shifters composed through
  the folding gates (constant shift-amount bits select branches at build
  time), `bv_shl_const` through `wire`.  Measured neutral-to-positive
  (corpus 285 ≥ banked 283 in the null arm; byte-identical time on
  `maxandminor016` vs the previous binary under matched serial runs), zero
  verdict flips across the 509-file A/B, Z3 parity 175/175.
- **Constant-flow result canonicalization** (`NIXIE_BV_CONST_FLOW=1`,
  default off): installs the reserved constant variables as op-result
  bits.  Sound (zero flips), deterministic 1.3–2× wins across the whole
  `bitrev` family (256–4096), but −1 aggregate cell at the 25 s cap
  (`std_bv_formula` 20 s → 33 s, deterministic) — ships off.
- Side unlock: the rewrite makes `RWS/Example_7` solvable (~43 s; previous
  binary > 390 s; z3 times out) — `sat` + full model validated by pinning
  the model back into the formula and re-checking with z3.
- The debug model-validity net gained an undetermined-bit filter (vars
  past the adopted snapshot previously read as `false` and fabricated
  mismatches); its residual false-positive mode on multi-round unified
  solves is documented in the study with the evidence trail.

Next-lever finding for the Tier-B near-misses: the `maxandminor` collapse
needs constants/substitution through the **`ite` selector layer** (boolean
`solve-eqs`-style substitution at the Tseitin boundary), not BV-operand
constants; ELS already folds 45 k literals there without closing the file.

## Addendum (2026-09-11, late): Tier-B triage — the CEGAR framing is the wrong layer for cjpeg

The option-2 framing ("CEGAR refinement tiers improved in place" for the
Sydr/cjpeg × 5 + s3_clnt × 4 cluster) was measured against ground truth:

- **cjpeg: no search happens at all, in either solver's winning path.**
  `NIXIE_BV_CEGAR_TRACE` on the dispatch path prints zero refinement
  rounds — the whole cost is one embedded SAT solve over the blasted
  instance.  z3 (`-v:10`) refutes these files by **post-blast boolean
  substitution**: bit-blast → simplifier → `solve-eqs :num-exprs 1` →
  unsat, no SAT decisions — the *same mechanism as maxandminor*, i.e.
  the shared lever is the Tseitin-boundary substitution layer, not the
  CEGAR loop.  (Divisors are *dynamic* — `concat` of symbolic refs — so
  the newly landed constant-divisor identities do not apply here.)
- **s3_clnt is genuine search for z3** (148 decisions, sat-cleaner
  passes over a 247 k-clause instance): that half of the cluster is an
  encoding/search-quality problem.
- Division abstraction on the dispatch path (`NIXIE_BV_CEGAR_DIV=64`)
  moves nothing on cjpeg (traced: only 8 muls abstracted; divisors
  dynamic) — the per-shape gate experiment is moot for this cluster.

Landed as a side effect (e8c986da): the constant-divisor division
identities (Z3 `bv_rewriter` parity — `udiv/urem` by powers of two →
shift/mask, 0/1-divisor total semantics), applying to 5126 corpus
files; verdict-identical on the 509-file screen.

**Resolved** (update 2026-09-12): the `known_unsound_regressions`
breakage from the watch-cursor series is fixed at HEAD (6/6 pass in the
main tree; d7b5dc34 "do not XOR-rewrite clauses from stale long-watchers"
was the closing fix).  Note for future triage: some of my intermediate
"failures at clean HEAD" observations were a worktree artifact — those
tests read `smt-lib/...` relative paths, so any worktree verification
needs the corpus symlink first (the AGENTS.md rule, now twice bitten).
