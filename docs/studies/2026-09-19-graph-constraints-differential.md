# Study: integrated finite-graph constraints — differential parity vs MonoSAT and scale probes

**Date:** 2026-09-19
**Landed in:** `0b1fcb12` (module), `1adb9f4f` (fixes + lifecycle), this commit (campaign)
**Verdict:** **PASS** — 1 600/1 600 random instances agree with the MonoSAT
reference implementation (no disagreement, no skip); scale guidance in
`docs/GRAPH.md` validated as conservative (random instances to n = 100 /
6 224 edges solve sub-second in a *debug* build).

## What was checked

The integrated graph constraint capability (`nixie_theories::graph`,
`Solver::register_graph`) implements MonoSAT's monotonic-theory scheme
adapted to Nixie's explained user-propagator API. The propagator-level
exhaustive oracles (all partial states of small case graphs × all concrete
completions) and the solver-level exhaustive small-graph oracles shipped
with the module. This campaign adds the strongest external check: **verdict
parity against MonoSAT itself** on random instances.

## The one deliberate semantics split

MonoSAT's `reach(a,b)` counts the zero-length path (reflexive: `dist[source]
= 0`, so `reach(a,a)` is trivially true — verified in
`ReachDetector.cpp`/`Dijkstra.h`). Nixie's `reach` requires length ≥ 1, so
`reach(a,a)` means "a lies on a directed cycle". For `a ≠ b` the two
conventions **coincide exactly**, so the campaign restricts reach atoms to
distinct endpoints; the GNF driver (`nixie-solver/examples/graph_gnf.rs`)
rejects self-pair reach instances loudly (exit 2) instead of comparing
mismatched semantics.

## Campaign

- Generator: `bench/graph_differential/gen_instance.py` — 1–2 digraphs,
  random edges incl. self-loops, up to `--reach-max` reach atoms on random
  distinct pairs, an optional `acyclic` atom (probability 0.6), and random
  unit + two-literal clauses over the theory variables (polarity mix), so
  the corpus spans both verdicts.
- Driver: `bench/graph_differential/run_differential.sh` — both solvers see
  the same file; a verdict mismatch, a Nixie `Unknown`, or a driver-side
  parse rejection is a loud failure (instance preserved under `failures/`).

| Batch | Instances | Vertices/graph | Agree | Disagree | Skipped | sat / unsat |
|---|---|---|---|---|---|---|
| mixed seeds | 1 000 | 2–8 (random) | 1 000 | 0 | 0 | 532 / 468 |
| `VERTICES=12` | 400 | 12 | 400 | 0 | 0 | 214 / 186 |
| `VERTICES=20` | 200 | 20 | 200 | 0 | 0 | 114 / 86 |
| **total** | **1 600** | — | **1 600** | **0** | **0** | 860 / 740 |

## Scale probes (single-solve wall time, debug build — indicative only)

The module docs state the stateless-recompute design "targets tens of
vertices and hundreds of edges". Probes with `--reach-max 8`:

| n | edges | Nixie (debug) | MonoSAT (release) | verdicts |
|---|---|---|---|---|
| 25 | 140 | 0.007 s | 0.007 s | sat/sat |
| 50 | 1 467 | 0.063 s | 0.011 s | unsat/unsat |
| 100 | 6 224 | 0.282 s | 0.011 s | unsat/unsat |

Atom-count stress at n = 50 (`--reach-max` 4/12/24, 153 edges): 0.010 /
0.009 / 0.013 s — all agree with MonoSAT. The per-event `O(V·E)`
recomputation is not the bottleneck at these sizes; the gap to MonoSAT at
n = 100 (≈25×) is the documented upgrade path (incremental reachability,
min-cut explanations, theory-directed decisions). Wall times are
single-run, load-sharing machine — recorded as scale evidence only, not as
a policy metric (see `docs/BENCHMARKING.md`).

## Defects found by the shipped oracles during development (recap)

1. **Empty-cut false-unsat class.** A forward-closure cut for the self-pair
   case emitted `Consequence(¬reach(u,u), [])` — an unconditional
   justification that becomes a permanent unit clause and would refute any
   later branch re-enabling the cut edges. Caught by the all-completions
   oracle on a parallel-edges case; fixed by MonoSAT's backward-closure cut
   (every false in-edge of the backward-reachable set participates, making
   each learned clause valid over arbitrary graphs). Focused regression:
   `self_pair_negative_propagation_pins_the_cut_edges` +
   solver-level companion.
2. **Name-interning atom sharing.** Two `GraphModel`s over one term manager
   minted identical atom names, silently binding both graphs to one
   constraint set (caught by the reset-re-registration lifecycle test);
   fixed with per-model name salts.

## Rebuilding MonoSAT for the campaign (read-only source, out-of-tree build)

```bash
mkdir /tmp/monosat-build && cd /tmp/monosat-build
GMP=$(dirname $(find /nix/store -maxdepth 3 -name gmpxx.h | head -1))
GMPLIB=$(dirname $(find /nix/store -maxdepth 4 -name libgmpxx.so | head -1))
ZLIB=$(dirname $(find /nix/store -maxdepth 4 -name libz.so | head -1))
cmake ../temp/monosat -DCMAKE_BUILD_TYPE=Release -DGPL=OFF \
  -DCMAKE_POLICY_VERSION_MINIMUM=3.5 -DCMAKE_CXX_FLAGS="-DNDEBUG -I$GMP"
make -j12 libmonosat_static
g++ -DNDEBUG -DNO_GMP -std=c++11 -O3 \
  CMakeFiles/monosat_static.dir/src/monosat/Main.cc.o -o monosat \
  -L$GMPLIB -L$ZLIB -Wl,-rpath,$GMPLIB -Wl,-rpath,$ZLIB \
  libmonosat.a -lz -lgmpxx -lgmp
```

(The CMake link rule hardcodes static `-Wl,-Bstatic` for zlib/gmp, which
this nix environment lacks; linking the CLI binary dynamically is the only
change. `run_differential.sh` takes the binary path via `MONOSAT=...`.)
The build tree is ephemeral scratch and intentionally not preserved.
