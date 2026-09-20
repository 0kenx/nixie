# Handover — nixie SAT-side perf campaign, sessions 2026-09-17 → 09-19 (congruence arc + load throughput + the false-sat root cause)

You are continuing the SAT-core solver-performance campaign on the nixie
repo (`/media/data/proj/nixie`, multi-agent shared tree — **READ
AGENTS.md FIRST**; its git/verification rules are non-negotiable).
Everything in this handoff is landed on `main`, verified, and
binary-cached; nothing is left uncommitted by this arc.

## What was accomplished (11 landings, chronological)

### Gate/counter vs kissat standing at arc start
Session start (2026-09-17 handover): 26/30 solved, wall geomean 1.93× vs
kissat 4.0.4, 0 verdict mismatches. Open item 1 (search quality) named
three diseases: bv_ILA 41.7×, oddball 25.1×, b21 2.37×.

### The congruence arc (the bv_ILA family, 405,848 → 15,144 conflicts)
1. `1fd5b96f` — **ITE gate congruence**: `detect_gates` gained the kissat
   `extract_ite_gates_with_base_clause` shape (4-clause ITE definitions,
   CSR literal index, else-discovery by pair scan). The closure merges on
   canonical presentations: `(c?t:e) ≡ (¬c?e:t)` SWAPS then/else with the
   cond flip (NOT an all-three negation — that is the complement's swap
   form); trivial `c?t:t` folds `o≡t`; four lookup rules so complementary
   pairs collide in both scan orders; class materialization keys each
   literal by its OWN union-find root. Three prototype false-unsats were
   caught by differential fuzz + kissat tiebreak and are pinned by tests.
2. `b47b93ff` — **SSR-binaries cascade + pre-search ELS arm**
   (env-gated, default OFF): `extract_binary_resolvents` (kissat
   `extract_binaries`: ternary×binary SSR adding resolvent binaries) +
   `NIXIE_ELS_PRESEARCH=1` (one bounded ELS fixpoint before the
   conflict-scheduled elimination). Armed on bv_ILA: 7,906 binaries →
   161,708 gates → 79,306 substitutions (kissat: 50,931). **The decisive
   measurement**: kissat solves our armed residual in 9,430 conflicts ≈
   its own pipeline (9,465) — preprocessing parity reached.
3. `ce42f335` — **XOR/XNOR gate congruence** (the 20× follow-up): the XOR
   arm found ZERO gates because it checked input signs only as written —
   one of four presentations (2,534 complete parity sets invisible). The
   closure uses the ITE presentation algebra: `f=a⊕b` presents as
   `(a,b)/(¬a,¬b)`, `¬f` as `(¬a,b)/(a,¬b)`; **signed-inputs-only key**
   (keying all three vars merges a definition's inputs with its outputs;
   parity-folding merges `o` with `¬o` — both false-unsats minimized to
   56 clauses and pinned). Powered 10-seed: geomean 0.825, solved
   239→251, bv_ILA 0.053×, **nla-digbench 0/10→10/10**; 78,164 claimed
   equivalences kissat-verified 0 bogus.
4. `2b0b4d54` — **pre-search factoring ON by default**: kissat's oddball
   profile shows factored=21% vars; `NIXIE_FACTOR=1` was 96× on oddball
   but flipped b21/b22 10/10→0/10 (mid-search rounds introducing nothing,
   60× wall). The split: winners introduce pre-search (oddball 1,398,
   Break_t 144, x9 368), losers introduce ZERO pre-search — so
   `NIXIE_FACTOR_PRE`-only is bit-identical on b21 at every seed.
   Powered: geomean 0.6317, solved 268=268, oddball 0.008×. Mid-search
   rounds stay off (`NIXIE_FACTOR_MID=1` opts in).
5. `dc3c2f34` — **the fold's exact-duplicate retire, SOUND** (see the
   false-sat section below — this was the arc's hardest bug).

### Load throughput (the 0-conflict families' 30-50 s wall)
6. `7788b321` — `new_vars_bulk(n)` (sequential `new_var` measured 2 µs/var
   — ~25 tables resized one variable at a time) + one reused literal
   buffer in the CLI add loop (25 M transients). Bit-identical by
   construction.
7. `1710e125` — header-driven `reserve_clause_slots` +
   `reserve_clause_bytes` (the flat stream's exact literal count sizes the
   arena). `begin/finish_deferred_big` on the fast path measured
   NET-NEGATIVE on hwmcc (9.5→10.6 s over three pairs) and was dropped;
   the DimacsParser path keeps its pair.
8. `c755033f`/`58fb224f`/`d18f63f4` — earlier this window: the
   search-vs-inprocessing propagation split counters and the
   ELS/Tarjan scratch amortization (fold into this arc's toolkit).

### The extension-walk hardening
9. `3274d86e` — bounded 8-pass fixpoint wrapper on `save_model`'s
   extension walk (repeat the backward pass until a pass repairs
   nothing). Bit-identical on healthy trajectories by construction;
   strictly better models on non-oscillating divergence. Landed as
   hardening while the real bug was still being hunted (see below).

## The false-sat that wasn't a walk bug (read this before touching save_model)

The dedup experiment initially flipped four UNSAT families to `sat`. The
full forensic chain — **study:
`docs/studies/2026-09-18-fold-dedup-false-sat.md`, three addenda** — is
the template for verdict-level debugging here:

1. The **consistency instance** (fix every never-eliminated var to the
   search's own model, add every extension entry as a clause, hand to
   kissat) proves verdict-level wrongness when UNSAT: no consistent
   extension exists; the folded formula LOST a constraint.
2. The minimal unsat core (3 entry-clauses + the search's units) names
   the hinge: the resolvent `(¬2990∨¬2382∨¬15955)`.
3. Clause-id lifecycle watchdogs traced it: ADDED by BVE → shrunk (sound)
   → **dedup-retired the ORIGINAL for a LEARNED owner** → the learned
   owner (correctly!) purged at the next elimination
   (`mark_redundant_clauses_with_eliminated_variables_as_garbage` — that
   purge is a soundness requirement) → constraint gone, no obligation →
   folded formula satisfiable → `sat` on UNSAT.
4. Fix: originals retire only for ORIGINAL owners; an original takes
   ownership over from a learned owner. The honest powered re-run:
   **0.9946 geomean, solved 243→250, 0 mismatches** (the parked 0.8066
   was clause-loss inflation). Landed `dc3c2f34` with tests.

The addendum-2 notes on cadical's `extend.cpp` (flip-all-falsified vs
witness-only, the naive port regressing 13,762 clauses) are recorded as
reference-divergence notes — the walk was never the bug.

## Standing at arc close (2026-09-19)

| family | arc start | now |
|---|---|---|
| bv_ILA | 405,848 conflicts / ~52 s | 15,144 / ~6 s (armed: 8,153, below kissat's 9,465) |
| oddball | 25× wall | 0.42× (faster than kissat) |
| nla-digbench | 0/10 solved | 10/10 |
| GP_190 / normalised | 7-9× | 0 conflicts (load wall is the residue) |
| solved-at-cap (10 seeds) | 239 | 250-251 |
| verdict mismatches | 0 throughout | 0 |

vs kissat 4.0.4 on the 30-instance corpus: the remaining wall geomean is
dominated by (a) the load-time sys wall (see below) and (b) parse.

## Verification protocol (use exactly this)

1. **Bit-identity** for semantics-inert changes: gate corpus conflicts
   must be BIT-IDENTICAL (run `bench/perf_gate/run_gate.sh`; ratio
   1.000).
2. `GATE_SEEDS=10` for heuristic landings + the powered experiment
   (10 seeds × 30 instances, `precompile/<sha>/benchmark/*/power.tsv`).
3. `cargo nextest run --workspace --all-features --no-fail-fast`
   (corpus tests in worktrees need the `ln -s` corpus symlinks — the
   `nixie-testcorpus` header's warned failure mode).
4. `cargo clippy --all-features --all-targets -p <your crates> -- -D warnings`
5. `bench/z3_parity/run_parity.sh` (z3 4.16.0; 177/0/1 baseline).
6. Cache the binary (`precompile/<sha>/nixie`) and re-pin
   `bench/perf_gate/BASELINE` deliberately. **Current pin: `1710e125`.**
7. For congruence-class changes: dump the claimed equivalence classes and
   kissat-verify every pair (`F ∧ ¬(a↔b)` must be UNSAT) — the
   78,164-pair/0-bogus audit is the bar.

## Traps (every one bit this arc)

- **Never retire an original for a learned clause** — learned clauses
  are purged at eliminations (correctly); the constraint dies
  obligation-free. This is now pinned by
  `fold_dedup_owner_rule.rs`.
- **Sign presentations**: XOR/ITE congruence has 4 (8) sign
  presentations; a signs-as-written scan finds zero gates and
  parity-folding merges `o` with `¬o`. Test at the presentation level.
- The shared `target/release/nixie` binary is deleted/rebuilt by other
  agents constantly — **always point experiments at `precompile/<sha>`
  binaries**, and re-pin deliberately.
- Perf-harness arm bugs (both arms → same binary) produce perfect-looking
  nonsense; check `$bin` resolution before believing a powered table.
- Long background runs (powered experiments, gates): poll briefly, work
  in parallel — never block on `sleep 3000`.
- Disk on `/media/data` swings to 0 (shared `target/` is the hog); build
  worktrees with `CARGO_TARGET_DIR` on `/`, symlink the corpora.
- `rg -r` is `--replace`, not recursive. Wall-clock is unusable under
  load-20; conflicts are the currency.

## Open items (ranked, measured)

1. **CSR-watches-primary** (the load wall): 18.7 M per-literal
   `Vec<Watcher>` headers ≈ 450 MB + one small allocation per watched
   literal = the dominant remaining sys on the 9.4 M-var class
   (`docs/studies/2026-09-18-bulk-load-throughput.md`). The
   2026-09-13 kickoff doc has the slice plan; slices 1-1.5 (the optional
   mirror) are landed. This is the biggest single remaining wall item
   (hwmcc 22×, normalised 30-50 s load).
2. **The armed-congruence composition** (`NIXIE_SSR_BIN=1
   NIXIE_ELS_PRESEARCH=1`): bv_ILA 8,153 (below kissat) but Carry_Bits
   4.5× — needs the BVE-interaction policy before any default flip; the
   2026-09-18-ssr-binaries study has the measured arms.
3. **Gate-based subsumption** (kissat's `forward_subsume_matching_
   clauses` over repr-canonicalized literals: 65 K clauses on the
   residual, 108 K on the raw file) — the remaining structural gap after
   the fold.
4. Break_12_30's 1.39× factor-schedule cell; n-ary gates (XOR arity ≤4,
   n-ary AND) — lower priority, measured roughly at parity.
5. The mmap parse question (kissat 0.85 s vs our 9.5 s on the 544 MB
   hwmcc anatomy; mostly the same watch-list churn, not read() itself).

## Where everything lives

- `docs/studies/2026-09-18-{ite-gate-congruence, ssr-binaries,
  xor-congruence, factor-presearch, bulk-load-throughput,
  fold-dedup-false-sat}.md` — the six decision records (the last with
  three addenda: mechanism, core, root cause, fix).
- `precompile/<sha>/benchmark/` — powered-experiment result stores
  (ite-power/, xor-power/, factor-pre/, fixed-dedup/).
- `bench/perf_gate/` — the gate + corpus; BASELINE pinned `1710e125`.
- Key code: `nixie-sat/src/solver/congruence.rs` (AND/XOR/ITE gates +
  closure + SSR cascade), `equiv.rs` (the fold + the dedup owner rule),
  `learn.rs` (`save_model`'s fixpoint walk), `factor.rs`
  (`factor_mid_rounds_enabled`), `config_presets.rs` (CaDiCaL =
  CLI default: factoring ON, mid-search OFF).
- Env knobs: `NIXIE_SSR_BIN`, `NIXIE_ELS_PRESEARCH`, `NIXIE_FACTOR`,
  `NIXIE_FACTOR_MID`, `NIXIE_SAT_SEED`, `NIXIE_SAT_BVE/_RESTART/
  _STABLE_POLARITY/_DELETION`, `NIXIE_DUMP_GATE_CLASSES`,
  `NIXIE_WATCH_TRIPLE` (study watchdogs in git history).

First moves: read AGENTS.md, re-run the gate to confirm tree health,
then pick from OPEN ITEMS. The congruence/factor/load arcs are closed;
the CSR-watches migration is the natural next campaign.
