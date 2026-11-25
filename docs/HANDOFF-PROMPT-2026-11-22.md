# Handoff prompt – nixie performance campaign (2026-11-22)

You are continuing a long-running performance campaign on **nixie**, a
pure-Rust SMT solver (~440 kloc, 17 crates, repo root
`/media/data/proj/nixie`).  The mission: close benchmark gaps vs **z3**
on SMT-LIB QF_BV, landing measured wins and recording measured
negatives.  **`AGENTS.md` is canonical** – read it first (soundness
rules, verification bar, git discipline, benchmarking protocol).  The
running log with every addendum (28–47) is
`docs/studies/2026-11-15-bv-andfold-soundness-and-termrules.md`; the
previous handoff is `docs/HANDOFF-PROMPT-2026-11-19.md`.

## Where things stand (HEAD `485be906`, tree clean)

The 2026-11-19 handoff's targets #1–#3 are **closed** (hdp assert storm
37.1 %→1.5 % + family census 4→6 cells at the cap; prefetch over-issue;
the 9 singles decomposed).  On top of that, this campaign day landed
**11 more commits** (17 total), all bar-green, zero wrong verdicts:

* `fb545619`/`d444269d` hdp atom sets (sorted SmallVec + manager cache)
* `aa89eb68` prefetch 3→1 per binary assignment (kissat shape)
* `9953e791` bv constant-wrap fast paths (no modulus alloc/division)
* `0b0cd392`/`b90f3807` slack-grown per-var arrays (`new_var`
  21.7 %→14.7 %)
* `350bbe32` regression tests for the identity arguments
* `0515153e` single-pass `iter_views` for the hot inprocessing scans
* `6269fa88` dense-slab substitution memo (SubstCache trait)
* `bca04f4a` domain-bitmap prefilter + `SubstSession` (binder scopes
  must NOT inherit the bitmap – rename entries; capture hazard fixed
  pre-landing)
* `9dc0f84d` **bvmul AC canonicalization** – the first new-family win:
  the wienand-cav2008 commute cluster (5 cells 10 s-TO → 0.02–0.89 s)

Two heuristic "matched-null sessions" were closed **cheaply as
negatives** on deterministic counters (addenda 34–35: reduce arms,
restart-stall) – do not re-run them.  Binaries for every landing are
cached under `precompile/<sha>/`.

## KNOWN BROKEN AT HEAD (not ours): two sets tests

`choose_of_ite_picks_the_taken_branch` and
`rejected_set_synthesis_cannot_publish_identical_choices` fail at HEAD
– **pre-existing**, introduced by the tla merge wave between
`6269fa88` and `69e394e8` (exonerated via throwaway-worktree
reproduction at bare HEAD; window pinned in addendum 45).  The tla
agents own it (a `tla-43` worktree was active).  **Before running any
full-suite bar, check whether these still fail**; until fixed, run the
suite with:

```bash
taskset -c 0-7 cargo nextest run --release --workspace --all-features \
  -E 'not (test(choose_of_ite_picks_the_taken_branch) or test(rejected_set_synthesis_cannot_publish_identical_choices))'
```

## Your entry points, ranked (evidence in addendum 47)

1. **wienand distrib/mult** (6+ gap cells, the natural next slice):
   ring-distributive normalization – expand `x*(y+z)` over the
   AC-canonical mul form just landed.  The commute win is the template:
   term-level collapse at assert time, validated by the term-rules
   discipline (mechanism unit tests + 100-cell z3 re-check + parity).
2. **bitrev** (4 cells): rev∘rev via 10-stage shift-and-mask ladders –
   needs a constant-mask/shift algebra normalizer (distribute shift
   over or/and, mask-mask meet).  z3-shaped rewrite-engine work.
3. **isqrt/icbrt** (5 cells): nonlinear-BV (`y²` range properties) –
   mul-to-algebra bridge (nixie-math grobner exists for QF_NIA) or
   squaring-aware blast sharing.  Largest scope.
4. calypto (3), brummayerbiere2 smulov (2, signed-overflow checks),
   singles – one profiling pass each before scoping.
5. The addendum-39 survey's leftovers: rebuild-skip (gated on the
   parser-normality invariant audit – addendum 43), ternary index
   (ordering hazard: clauses shrink into length 3).

The sweep itself is regenerable: 6-cell prefixes (`sort | head -6`) of
the 51 families not in `20210219-Sydr`/`asp`/`uclid`/`bench_ab`, then
20-cell deepening of gap families, 10 s cap, matched-interleaved vs
z3 4.16.0.  We LEAD z3 on mcm and float – do not regress them.

## Measurement discipline (7 recorded traps – each has an incident)

1. **Matched interleaved A/B only**; alternate arm order (ABBA) – an
   A-then-B sequence under a load ramp biases against B (addendum 31).
2. **Deterministic counters, never wall**, as the primary metric; the
   SMT path is seed-invariant, so single counter runs ARE valid
   trajectory comparisons.  `--stats` writes to **stderr** (so does the
   verdict line – a stdout-only read once called every cell TO).
3. **Reset the verdict on timeout** – a TO'd run leaves the previous
   cell's verdict greppable in a reused output file.
4. **Assert non-empty verdicts before comparing** (caught two panics
   and one crash this campaign); `/usr/bin/time` does not exist on this
   NixOS box (exec-127) – bracket with `date +%s.%N`.
5. **Swap pressure invalidates the load gate**: check `free`/`vmstat`,
   not just `uptime`; si in MB/s steals memory bandwidth even at low
   load average (addendum 34).
6. **Shared affinity mask**: every agent pins `taskset -c 0-7`, so a
   co-tenant benchmark time-shares your cores while the 20-core load
   average hides it.  **Gate: `vmstat`'s runnable count `r` ≤ 9
   sustained**, load ≲ 12, si/so ≈ 0 (addendum 44).  Under continuous
   multi-agent operation this window may not exist – the minigzip
   census and deferred wall A/Bs are **machine-bound, deferred**
   (addendum 46); counters/profiles carried every landing instead.
7. **Stale-link bisect**: rapid `git bisect` checkout switching in one
   worktree produces fingerprint-lie "good" verdicts – a clean build
   per step (fresh worktree or `cargo clean -p`) is mandatory
   (addendum 45).

## Verification bar

Per commit: `cargo fmt --all -- --check`, clippy (`-D warnings`,
doc-warnings fail), targeted tests.  At intervals and before any
heuristic landing:

```bash
taskset -c 0-7 cargo nextest run --release --workspace --all-features   # ~12 900 (+ the sets exclusion while broken)
taskset -c 0-7 ./bench/z3_parity/run_parity.sh                          # 171 Correct / 6 Inconclusive
taskset -c 0-7 bench/perf_gate/run_gate.sh                              # counters ≤1.05, wall ≤1.25
```

Counter-identity on probe cells for pure-perf changes (minigzip 492,
BBB-32, duthen-50 `.steps.10`, hdp 3365, bzip2recover 2763; assert
non-empty verdicts).  **Rewrite/term-rule changes** (the AC class) are
NOT counter-identical: mechanism unit tests + a ~100-cell z3 verdict
re-check on affected families + parity are the bar.  Cache every
landed binary under `precompile/<sha>/`.

## Machine policy

Shared 20-core box, other agents active (tla line, compile storms,
benchmark runs; load has hit 150 with 92 MB/s swap-in).  Builds capped
at 8 jobs via `~/.cargo/config.toml`; **prefix every test/gate/benchmark
with `taskset -c 0-7`**.  Never `git stash`/`restore`; throwaway
worktrees for old revisions (clean them up); LTO test-binary links OOM
under memory pressure – retry after a pause.  Stage only your own
files; other agents land to main continuously (expect rebases of your
in-flight commits; a rebase once mangled a test attribute – clippy
caught it).

## Session-start ritual

```bash
git log --oneline -5 && git status --short        # expect clean at 485be906+
uptime; free -m; vmstat 1 2                       # the r/si gate, not just load
git worktree list                                 # whose worktrees are live
```

Then read the study's latest addenda (44–47) and this file's known-broken
section.  The profiling harness recipe (standalone `Context::
execute_script` bin + pprof at 250 Hz, `RUSTFLAGS="-C force-frame-
pointers=yes"`) is re-derivable from any addendum; scratch it after use.
