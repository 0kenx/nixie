# Bulk-load throughput: the 0-conflict families pay 30-50 s of load-time sys (2026-09-18)

The fresh standing table after the congruence/factor landings showed the
remaining wall gaps concentrated in families that now solve at **zero
conflicts** but take 9–50 s: `14.normalised` 42–50 s (kissat 4.3 s),
`GP_190` 25 s, `GP_105` 9.4 s, `hwmcc-6s299` 22× (parse-anatomy, known).
Time-splitting `14.normalised` (9.4M vars / 25.2M clauses / 505 MB):

| phase | wall |
|---|---|
| `FlatCnf::scan` (read + scan + flat build) | ~2–5 s |
| `for _ in 0..num_vars { new_var() }` | **18.6 s** |
| 25.2M × `add_clause` | ~17.8 s |
| search (lucky answers sat) | ~0 s |

and the run's split is **6–7 s user / 28–42 s sys** — an allocation-churn
fault storm, not compute (kissat: 3.5 s user / 0.95 s sys; it pre-sizes
from the header).

## Landed: `new_vars_bulk` + the reused literal buffer

- `Solver::new_vars_bulk(n)`: one resize per per-var/per-literal table to
  the final size (the same fills `new_var` writes), then the same
  `vsids`/`chb` insertions in the same order (all-equal activities make
  each O(1)).  Sequential `new_var` measured 2 µs/var — ~25 tables
  resized one variable at a time, amortized-doubling reallocs and their
  page-fault traffic dominating huge-formula load.  The CLI fast path now
  calls the bulk form.
- The CLI add loop allocated a fresh `Vec<Lit>` per clause (25M transient
  allocations); it now reuses one buffer.

Both are strictly-less-work and **bit-identical by construction**
(verified: conflicts/decisions/propagations identical on the gate-corpus
spot set; the perf gate reads counters 1.000 vs the `2b0b4d54` pin).
Measured effect on `14.normalised` under heavy external load: user
7.7 → 5.6 s, wall consistently 10–15 s below the old binary across
interleaved runs (the box's contention inflated both arms' sys to
40–60 s during measurement — the deltas are directional, not final).

## Named next slices (the remaining ~35 s of sys on this class)

1. **The 18.7M per-literal `Vec<Watcher>` headers** (`WatchLists.watches:
   Vec<Vec<Watcher>>`): ~450 MB of headers plus one small allocation per
   watched literal — the dominant remaining churn.  The CSR-watches arc
   (`2026-09-13-csr-watches-kickoff.md`, slices 1–5, currently an
   optional mirror) is the structural answer; promoting it to the primary
   on the bulk-load path (the CLI knows the whole literal stream upfront)
   is the natural slice 6.
2. **The clause-arena doubling** (~600 MB grown by doubling ≈ 1.2 GB
   moved): a header-driven reserve for the original-clause count.
3. `begin_deferred_big`/`finish_deferred_big` around the CLI bulk load
   (the `DimacsParser::parse_reader` path already does this; the fast
   path does not — it only covers binary/BIG edges, but those are 78 %
   of the hwmcc anatomy).
