# Handoff: the finite-graph-constraints arc executed — integrated theory, 1600-instance MonoSAT parity, 5.1×→1.65×, the shared-path fixes banked

**Date:** 2026-09-21.  **Arc:** the full graph-constraints engagement, from the
`SpecialRelationSolver`-is-not-a-theory finding through the integrated propagator, four
perf rounds, and the validation stack (exhaustive oracles, MonoSAT differential,
backtrack-heavy stress, generated-oracle campaign).  **Goal for the next agent:** the
capability is **done and hardened** — nothing is owed.  This handoff exists so the
*several shared-path defects found along the way* are not re-diagnosed, the
*measurement tooling* is reusable, and the *two deliberately-not-taken levers* are
picked up with their context intact.

## Where things stand (all landed on main, `39192c3b` at handoff)

- **The feature**: `nixie_theories::graph` + `Solver::register_graph` — symbolic
  directed graphs over fixed finite vertex universes, Boolean edge terms (fresh vars or
  any non-constant Boolean term), reified `reach`/`acyclic` atoms, MonoSAT's
  monotonic-theory scheme over the explained user-propagator API.  Semantics:
  `reach` requires paths of **length ≥ 1** (zero-length paths do not count;
  `reach(u,u)` ⇔ u lies on a cycle — deliberately *not* MonoSAT's reflexive
  convention; they coincide exactly for `u ≠ v`, which is how the differential
  compares).  Docs: `docs/GRAPH.md`; design + everything else:
  `docs/studies/2026-09-19-graph-constraints-differential.md` and
  `...-graph-perf-vs-monosat.md` (the second is the engineering log; read its
  addenda in order — each one corrected an earlier attribution).
- **Soundness evidence, in decreasing order of strength**:
  exhaustive all-completions oracles (small graphs, every partial state × every
  concrete graph — caught a real false-`unsat` bug class during development);
  **generated-oracle campaign** (200 seeded adversarial event scripts with nested
  rollback — the incremental state machine's risk surface; 200/200 clean);
  **MonoSAT differential 1600/1600** (2–20 vertices, plus the backtrack-heavy
  crafted set: ~25k conflicts, both solvers TMO identically on the over-hard ones);
  Z3 4.16.0 parity clean throughout; exhaustive n≤3 solver-level oracles with
  independent model re-validation.
- **Performance vs MonoSAT** (release, 40-instance corpus, medians of 3):
  **1.65× geomean** (was 5.1× at feature-landing), totals 30.5 s → 3.35 s, worst
  instance 39× → 6.3×.  Under backtracking (crafted 3-SAT-coupled instances)
  Nixie tracks within 1.0–1.4×.  Fixed process overhead: 3.0 ms vs 2.3 ms.
- **The shared-path fixes that benefit every theory** (each landed with
  bit-identical solver counters where applicable): manager undo journals instead of
  per-SAT-level state clones; O(1) watch lookup; O(watches) registration dedup
  (was O(watches²)); FxHash in the propagator-manager maps (was SipHash+RandomState,
  ~12% of a graph solve); `OnceLock`-memoized env gates (`getenv` is a linear scan,
  ~11%); gated set/bag per-assertion re-survey (was **quadratic in assertions for
  every non-set/bag goal** — hits all SMT users); skipped BV unified sweep when no
  BV term exists; `O(terms²)→O(terms)` arith-term collection in the EUF→arith
  propagation (16% of a 4000-term QF_LIA run).
- **The propagator itself** is event-driven incremental with a full-re-read
  fallback: `on_fixed` routes `(term,value)` in O(1); runs apply events to packed
  view bits/edge values/growable adjacency rows and **merge** memoized BFS trees on
  true-edge additions (parents stay real forced edges, so extracted paths remain
  valid justifications); `pop` invalidates and the next run re-reads from the
  manager.  Worst case = the pre-incremental cost; typical case O(1) per event.
  **This is verdict-preserving but NOT counter-identical** (merged trees may pick
  different, equally valid path parents) — that is why the validation stack leans
  on the oracles/differential, not counter diffs.

## Commit map (this arc)

| sha | what |
|---|---|
| `0b1fcb12` | the feature: module, `register_graph`, exhaustive oracles, `docs/GRAPH.md` |
| `1adb9f4f` | per-model atom-name salt, focused empty-cut regression, assumptions/reset/multi-registration lifecycle |
| `1b974b80` | MonoSAT differential campaign (1600/1600) + GNF driver example + rebuild recipe |
| `f7225ba6` | six inert optimizations (journals, watch index, dedup, set/bag + BV gates, view cache) — 5.1×→2.65× |
| `ac873333` | arith-term O(n²)→O(n) (shared) |
| `4723b1c6` | SipHash→Fx + env-gate memoization (shared) — →2.33× |
| `aa8a6cf6` | event-driven incremental propagator — →1.65× |
| `9ff377ff` | generator modes (`--clause-size/--coupling/--unit-prob`) + backtrack-heavy stress |
| `0387eb02`+`39192c3b` | generated-oracle campaign (200 campaigns, nested rollback) + record |

Binaries cached under `precompile/<sha>/` for the perf-relevant commits.

## The two deliberately-not-taken levers (pick up with context)

1. **Incremental *decremental* handling for the possible view.** False-edge
   assignments currently mark it dirty and the next run rebuilds the possible-side
   CSR + backward memos from scratch. True assignments leave it untouched, so only
   backtrack-heavy false-heavy phases pay. Nothing in any current profile says it is
   due; if a workload appears, Ramalingam–Reps decremental reachability is the
   reference (`../temp/monosat/src/monosat/dgl/RamalReps*.h`).  **Warning from this
   arc's history:** the negative-reachability *cut* must be taken over the
   **backward** closure of the target with every false in-edge participating — a
   forward-closure cut emits empty (unconditional) justifications that become
   permanent unit clauses and later produce **false `unsat`** (the bug class the
   exhaustive oracle caught; regression test:
   `self_pair_negative_propagation_pins_the_cut_edges`).
2. **Theory-directed decisions** (MonoSAT's `-decide-theories`) and any propagator
   change that alters *which* consequences fire: these change search trajectories —
   matched-null discipline (`docs/BENCHMARKING.md` §2) applies, not the inert-landing
   shortcut used here.

## Reusable measurement tooling (not in-tree — recipes in the studies)

- **MonoSAT rebuild** (read-only source, out-of-tree, ~3 min):
  `cmake ../temp/monosat -DCMAKE_BUILD_TYPE=Release -DGPL=OFF -DCMAKE_POLICY_VERSION_MINIMUM=3.5 -DCMAKE_CXX_FLAGS="-DNDEBUG -I<gmpxx dir>"`,
  `make -j8`, then link `monosat` manually with `-lz -lgmpxx -lgmp` **dynamically**
  (the CMake link line hardcodes `-Wl,-Bstatic`, which this nix environment lacks).
- **LD_PRELOAD allocation attribution** (~zero overhead): bucketed malloc/realloc
  counters + caller-slot sampling + a sentinel allocation to bound the profiled
  phase.  This is what decomposed the "~40% allocator/libc" perf blob into SipHash
  + getenv — perf alone could not (all sites inline into `finish_grow`, and the
  symbolized build is required: `--config` with `profile.release.strip="none"` +
  `RUSTFLAGS=-g`; the default release strips everything and perf shows garbage
  addresses, and *symbolizing one build's addresses against another's symbols
  produces confident nonsense* — always rebuild the interposer target with the
  exact binary under test).
- **GNF driver**: `cargo run -p nixie-solver --example graph_gnf -- file.gnf`;
  `STATS=1` prints deterministic counters (the bit-identity tool — requires
  identical feature sets between the compared builds), `TIMING=1` prints phase
  breakdown.  Campaign: `bench/graph_differential/run_differential.sh`
  (`VERTICES=…`, `MONOSAT=…`, `NIXIE_GNF=…` env).

## Trap list (bit this arc; each cost real time)

1. **Counter bit-identity is only comparable across identical feature sets** —
   `--all-features` vs default produce different propagator behavior (property
   tests change schedules); always diff `STATS=1` lines from same-flag builds.
2. **A failing test at shared-tree HEAD is not yours until proven**: this arc saw
   three separate windows where another agent's in-flight edit broke the shared
   tree (`LiaBranchRequest` impls, simplex mid-edit).  The protocol that worked:
   worktree at HEAD → apply only your diff → compare failure *sets* (not counts)
   with and without it → say so in the landing message.  `git worktree` + copy the
   diff; never stash/restore the shared checkout.
3. **Load flakiness is routine here** (load average 35 observed): the
   `scope_rebase_tests` and `pete_5s` tests time out under `-j 10–12` and pass at
   `-j 4`/isolated.  Re-run before believing; and your own multi-second CPU test
   (the generated oracle at 18 s did this) can push a *neighbor* timing test over
   — trim it.
4. **The shared disk fills from parallel agents' builds**; `/var/tmp` scratch on
   the root FS is the escape hatch, but orphaned test binaries in
   `target/debug/deps` (same name, different hashes) are ~0.5 GB each and safe to
   dedupe by keeping the newest hash.  Rustc also leaves `no/` temp dirs in the
   repo root on ENOSPC crashes — delete them, they are debris.
5. **`perf` on this hybrid machine**: default sampling records ~10 atom-core
   samples and looks plausible — pass `-e cycles:u` explicitly, or you profile
   noise.

## Owner notes

- The **`bench/perf_gate/BASELINE` pin** was re-pinned twice by other agents during
  this arc (correctly — SAT-core landings moved counters 1.013); graph landings are
  exactly neutral on the gate corpus (module inert unless registered) — keep it
  that way: any graph-module change that touches shared solving paths must re-run
  the gate and attribute the delta (build HEAD-without-diff if the pin is stale;
  the 1.013-attribution trick is in the `f7225ba6` study addendum).
- **`docs/GRAPH.md`** is the user-facing contract (semantics, naming salts,
  lifecycle, limits, the network-policy example, the perf numbers).  If the perf
  numbers move again, update the limits section — they are dated and sourced to
  the studies.
- The **`SpecialRelationSolver`** remains standalone bookkeeping (no solving path
  consults it); the module doc in `graph/mod.rs` states this so nobody
  re-conflates them.
