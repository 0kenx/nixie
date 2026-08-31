# Handover: clause-arena layout — header density & slot packing

## Read first

- `AGENTS.md` — the non-negotiables (soundness-first, read kissat/cadical before
  inventing, no `unwrap`, matched-null discipline for heuristic changes).
- `docs/BENCHMARKING.md` — §2 matched nulls, §3 the ±5 % neutrality band, §10
  escalation ladder. This work is **path-preserving** (see below), so its null
  is *trajectory identity*, but the gates still apply.
- `docs/studies/2026-08-watcher-8byte.md` and
  `docs/studies/2026-08-flat-watch-arena.md` — the two experiments that closed
  the *watcher-side* thread and named **this** one as the remaining propagate
  lever.
- `docs/studies/2026-08-30-analyze-quadratics.md` — the session map: loss-file
  classification, everything measured dead en route, and the harness lessons.

## The problem

Propagation is the last big cost-bound bucket on the remaining loss files:
**33–40 % of all instructions** on `circuit_64in64out…` and `frb45-21-2`
(profiled, no-LTO symbols build). Every *other* constant-factor lever in the
BCP loop has been measured dead or landed:

| lever | verdict |
|---|---|
| watcher 12→8 bytes | 1.0068, sub-threshold — reverted |
| flat watch arena (kissat parity) | 0.955–0.965, neutral/negative — reverted |
| clause prefetch (distance 3) | **+8–11 % cycles** on the target class — reverted |
| shrink packed-key retention | 0.994–1.000 — reverted |
| validation elision in `live_lits_hot` | landed (−12–16 % instructions) |
| direct arena addressing (slot in watcher) | landed (one dependent load saved/visit) |

What remains inside the propagate visit is the **clause-arena layout itself**:
the header the scan must load on every non-blocker-hit visit, and the slot
stride that determines how many literals share a cache line.

## Grounded facts about the current layout (verify, don't trust prose)

`oxiz-sat/src/memory.rs`:

```rust
#[repr(C, align(4))]
struct ClauseHeader {
    len: u32,        // genuinely large DIMACS clauses exist
    lbd: u16,        // saturating; consumers threshold at <= 10
    flags_tier: u8,  // 2 flag bits + 2 tier bits
    usage: u8,       // saturating; promotions fire at 3 and 10 uses
    activity: f32,   // ONLY the reduce_clause_database sort key
}
```

- Header = **12 bytes**; `Lit` = 4 bytes; slot stride rounded to 8.
  A 3-literal clause slot is 24 bytes (two per cache line), a 5-literal slot
  32 bytes (half a line). The f32 activity at offset 8 is documented as "what
  lets" these properties hold — that claim is the thing to re-examine.
- Buffer is `Vec<u64>` (8-aligned by construction; an earlier `Vec<u8>`
  buffer with aligned header reads was **unconstructible unsoundness** —
  fixed, do not regress it).
- Lifetime invariants (load-bearing, documented at the top of the file):
  **append-only** slots (a `ClauseRef` never comes to name a different
  clause — stale watchers and trail reasons depend on this) and
  **shrink-in-slot only** (rewrites only ever drop literals; the tail becomes
  dead padding; growing is refused).
- The module doc's "32-byte header" line is **stale** — the struct-level doc
  (12 bytes) is accurate. Fix the stale line while you are in there.

## The kissat reference (ground truth, `../temp/kissat/src/clause.h`)

```c
struct clause {
  unsigned glue : 19;                      // + 8 bool flag bits + used:5
  bool garbage/quotient/reason/redundant/shrunken/subsume/swept/vivify : 1;
  unsigned used : 5;
  unsigned searched;                       // vivify scan cursor
  unsigned size;
  unsigned lits[3];                        // first 3 literals INLINE
};
```

- The whole glue/flags/used state is **one 32-bit word** of bitfields vs our
  8 bytes (`lbd+flags_tier+usage`).
- **No activity in the hot clause** — kissat's reduce is glue/used-based, no
  activity sort; ours is activity-sorted (`reduce_clause_database`).
- Literals overlap the header tail (`lits[3]`) — a size-3 clause is exactly
  `sizeof(clause)` with zero literal bytes beyond it.
- Compare also `../temp/cadical/src/clause.hpp` (header + literals, different
  packing) before choosing a shape.

## Approaches, in attack order (pre-register before running)

**A. Relocate `activity` out of the hot header → 8-byte header.**
The field's only consumer is the `reduce_clause_database` tier sorts
(learned clauses only). Move it to a side table keyed by clause id (or pack
`f16`-style scaled activity — but the side table is the clean cut). Header
becomes `len:u32 + lbd:u16 + flags:u8 + usage:u8` = 8 bytes: a 4-lit slot =
24 bytes, a **6-lit slot = 32 bytes** (vs 5 today) — +20 % literal density
per line on the arena scans, and one fewer word in every header load.
Expected win is honest-uncertain: the watcher-8byte result warns that
density effects here run ~1 %; the difference is that this one moves the
*clause* line, not the watcher line, and non-blocker-hit visits are bounded
by exactly this arena.

**B. Bit-pack the header kissat-style → 8-byte header without moving
activity off-slot is impossible; with A done, pack `lbd`(needs ≤10 +
saturating stats), tier(2b), flags(3b), usage(5b) into `len`'s spare
upper bits or a second u32 alongside it.** Marginal after A; only if A
measures close to the bar.

**C. Kissat `lits[3]` inline overlap.** Only if A+B leave the bar unmet;
touches every literal-array consumer and the shrink-in-slot arithmetic.

## Gates (pre-registered; write them into a study doc BEFORE running)

1. **Trajectory identity** — decisions/propagations/conflicts/restarts/
   learned + verdict bit-identical on the 54-file `/tmp/sc24f` corpus
   (or `bench/` equivalents) at `PRESET=cadical`, default seed. Layout
   changes must not reorder any visit. Divergence = the refactor is
   semantically wrong, fix before measuring.
2. **Instructions-to-verdict geomean ≥ 1.02×** on the both-solve files
   (the watcher-8byte study's harness shape). 1.00–1.05 = *neutral, below
   the bar* — revert and record, per `BENCHMARKING.md` §3's band wording.
   Watch `circuit_64in64out…`, `frb45`, `si2-b03m` (propagate-heavy) and
   `noL-11-14` (analysis-heavy, as the control that should not move).
3. Soundness: full workspace suite + clippy/fmt/doc; differential CNF fuzz
   (the sweep studies' generator script shape is in
   `2026-08-30-analyze-quadratics.md`); z3 parity only if anything reaches
   the default path.

## Hazards (all bit someone this session — do not repeat)

- **Shared `target/`**: another agent's build can leave you testing a stale
  binary. After any edit, force `touch` + rebuild and diff the binary sha
  before trusting a measurement (this exact trap produced a false
  "guards fixed it" conclusion).
- **Hybrid CPU**: `perf stat -e cycles` reads the atom PMU first — always
  use `cpu_core/...` events and pin with `taskset -c`.
- **Orphaned solvers**: `timeout` on a harness that `start_new_session`s
  children orphans them (three incidents, load 75). Kill the process group.
- `perf report`'s flat view lies on the LTO build — use `perf script` stack
  walks or a no-LTO symbols build
  (`CARGO_PROFILE_PERF_LTO=false CARGO_PROFILE_PERF_CODEGEN_UNITS=16`).
- Wall-clock is never the metric; PMU instructions are.

## Key files

| file | what |
|---|---|
| `oxiz-sat/src/memory.rs` | `ClauseArena`, `ClauseHeader`, `ClauseRef`, `alloc`, `live_lits_hot`, `shrink` — the whole layout |
| `oxiz-sat/src/clause.rs` | `ClauseDatabase` over the arena; `bump_activity` / tier sorts (activity's consumers) |
| `oxiz-sat/src/solver/learn.rs` | `reduce_clause_database` (the activity sort), `sweep_root_fixed_clauses` |
| `oxiz-sat/src/solver/propagate.rs` | the BCP scan (the customer) |
| `oxiz-sat/src/invariants.rs` | `check_learned_clause_lbd` (LBD clamping interplay) |

## Build & quick measures

```bash
cargo build --release --example cnf_solve --example stats_solve -p oxiz-sat
# per-visit cost at fixed cap (deterministic, pin one core):
p=$(ls /tmp/sc24f/6f7a0e1c*.cnf)   # circuit_64in64out
taskset -c 4 perf stat -e cpu_core/instructions/ -x, \
  env MAXC=40000 ./target/release/examples/cnf_solve "$p"
# trajectory identity harness shape: diff stats_solve counters old vs new
# binaries at MAXC=60000 across the corpus (see the studies for the script).
```

Precompile binaries exist for every session commit (`precompile/<sha>/`,
each with `cnf_solve` + `stats_solve`) — use them as the pre-change arm;
never rebuild an old revision by hand on the shared tree.

## Constraints

- Pure Rust, no new C/C++ deps (banned in `deny.toml`).
- `#![deny(unsafe_code)]` stands in `oxiz-sat`; `memory.rs` already carries a
  documented module exception — keep any new raw-pointer work inside it and
  argued per-write.
- No `unwrap()`/`expect()` in production paths (clippy `deny`).
- If the win lands: full battery (corpus verdict sweep, fuzz, workspace,
  differential, parity) before the default flip, per the enablement rule in
  `BENCHMARKING.md` §3.
