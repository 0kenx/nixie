# The arithmetic hot path after the landings: slice-6 candidates, a dense basic list, and what the text profile got wrong (2026-11-24)

Third equivalent-work round of the session, on the arithmetic final-check path
that the first two rounds left dominant on every UFLIA/AUFLIA/UFIDL probe
cell. Everything here is **trajectory-identical** (conflicts / decisions /
propagations / theory_props equal on all 17 probe cells) and lands with the
standard bar. Paired instruction counts vs `03832ace`:

| cell | before this round | after | instructions |
|---|---|---|---:|
| QF_UFIDL vlsat3_f30 (budget 3 000) | 7.98 G | 4.00 G | **0.502** |
| QF_UFLIA wisas xs_8_13 | 14.46 G | 13.85 G | 0.958 |
| QF_UFLIA Wisa xs-10-18-2-2-5-3 | 25.20 G | 24.08 G | 0.956 |
| QF_UFLIA wisas xs_10_20 | 81.82 G | 78.15 G | 0.955 |
| QF_AUFLIA dlx-pc (budget 2 000) | 23.53 G | 22.80 G | 0.969 |
| QF_ANIA avg20 | 10.13 G | 10.01 G | 0.988 |
| the other 11 cells | — | — | 0.998–1.005 |
| geomean (17 cells) | | | **0.9499** |

Cumulative over the session's three rounds vs the start `61fbec68`: wisa
xs-10-18 0.884, wisas xs_8_13 0.878, wisas xs_10_20 0.906, vlsat3_f30 0.459,
dlx-pc 0.418, avg20 0.976; geomean over the 17 cells ≈ **0.89**.
## Method: a text profile, and why the earlier numbers were misread

`perf record` does not work in this sandbox (`perf stat` does), so the
profile came from the CLI's `pprof-signal` guard — extended here with
`NIXIE_PPROF_TEXT=<path>` (`nixie-cli`): the sampled stacks as collapsed text,
leaf-first, every frame — inlined ones included — suffixed `@file:line`.
`llvm-cxxfilt` demangles the Rust v0 names; the analysis scripts lived in the
session scratch (`collapsed.py`, `stacks.py`). This is the first profile in
the repo with *inline-accurate* attribution on the SMT path, and it matters:

* The symbol-level view put 15 % of a wisa run in
  `DeltaRational::from_rational` — a two-field constructor. The inline view
  showed those PCs were the inlined body of `derive_basic_bound`'s
  accumulation, i.e. rational arithmetic, not the constructor.
* The inline view then put **20 % of wisa in `Arc::drop`** inside
  `propagate_bounds_in`'s row scan and **10 % of xs_10_20 in
  `TableRow::clone`** inside the pivot. Both are refcount operations; the
  first removal (borrowed row views) measured 1.7 % on wisa but 45 % on
  UFIDL; the second (sharing instead of cloning the leaving/dependent rows)
  measured **nothing** (0.9551 vs 0.9554 on xs_10_20). Lock-prefixed
  instructions sample early and often; **the instruction counter decides,
  the profile only nominates.**

## What changed

### 1. `propagate_bounds_in` visits candidates, not the tableau

The slice-6 bound pass runs inside `tighten_tableau_bounds`' fixpoint (up to
16 passes per arithmetic check) and each pass scanned every tableau row,
paying per visit an `Arc<LinExpr>` clone/drop, the `row_stamp` input sum and
a `derive_stamp` hash probe even when the row's inputs had not changed.

A row's derivations read exactly: its content (`rows_ver`), the crossing
epoch (`cross_ver`), the bound versions of its basic and of every row
variable, and `int_vars.len()`. So a pass can derive something new only if a
global input changed since the previous pass — every row is then a candidate
— or one of those bound versions bumped. Every bump already flows through
`note_bound_change` or the pop-restore loop; both now call
`s6_mark_rows_of(var)`, which marks `var`'s own row (when basic) and the rows
of the basics in its column (`columns`, the exact index of narrow rows
referencing `var`). The pass visits the marked rows in `tableau` order,
so the store sequence — and with it the application order of stored bounds —
is the historical one.

With the candidate set exact, the per-row stamp machinery was dead weight:
`row_stamp`, the `derive_stamp` map (made dense for one build, then deleted)
and the wide loop's never-compared stamp are gone. The wide loop still visits
every wide row (no marks for it) — unchanged behaviour.

`slice6_consider` takes the pass's two mutable destinations (the store queue
and the pending crossing) as parameters, so every derivation runs behind
`&self` row views (`row_lin_view`); `Int`-form candidate rows are
materialized in place first, exactly where the historical `row_lin` did.

### 2. `find_violating` scans a dense basic list

The selection is the smallest violating basic id — it needs the key set of
`tableau`, not its buckets. `basic_list` / `basic_pos` keep that key set as a
compact list (O(1) membership, swap-removal) at the eight `tableau`
membership sites, and `find_violating` iterates it. **The first cut was
wrong**: a single-line `grep 'tableau\.insert('` finds five of the eight —
rustfmt had split three calls across lines (`self.tableau\n .insert(`) — and
the A/B harness answered `sat → unknown` on five cells. The debug-build
oracle (`basic_list.len() == tableau.len()`) found the next drift: the test
scaffolding writes `tableau` directly. The list now self-heals — a length
mismatch rebuilds it from the key set — so correctness never rests on the
incremental maintenance, and the arithmetic tests (262, debug) run against
the same code path as production.

### 3. The pivot shares rows instead of cloning them

`self.tableau.get(&x).cloned()` at the two pivot fetches deep-copied every
non-`Int` row's `LinExpr` to pattern-match the variant; both now borrow and
clone only the `Arc` they need. Strictly less work; no measurable cell moved
(it is kept for that reason and because the borrow is the plainer code).

## Bar (this tree)

`cargo fmt --all -- --check`; `cargo clippy --release --all-features
--all-targets -p nixie-theories -p nixie-solver -- -D warnings` clean;
`cargo test -p nixie-theories --lib -- arithmetic` (debug assertions, with
the `basic_list` oracle) **262 passed**; `cargo nextest run --release` for
the two crates; `cargo nextest run --release` for the two crates **5 291 passed** (the two
documented pre-existing HEAD failures excluded); `bench/z3_parity/
run_parity.sh` **171 Correct / 0 Wrong / 6 Inconclusive** (z3 4.16.0);
`bench/perf_gate/run_gate.sh` **PASS** 1.000 / 1.000 (pure-SAT corpus:
unaffected, run for the record); `smt_probe_ab.sh` counters identical on
all 17 cells, instructions 0.9499. Binary cached under `precompile/<sha>/`.

## Traps recorded

* **A grep for mutation sites is not a list of mutation sites.** Three of
  seven `tableau` writes were split across lines. Multi-line-aware search
  (`re.finditer(r'tableau\s*\n\s*\.(insert|remove|…)\(')`) plus a debug
  oracle on the invariant plus the counter-identity A/B is the net that
  catches this class; all three were needed here.
* **Make derived indices self-healing, not just maintained.** A rebuild on
  length mismatch costs nothing when the maintenance is right and makes a
  missed site a performance bug instead of a wrong verdict.
* `cargo test -p nixie-theories --lib` (dev profile) works again for the
  arithmetic module; `debug_assert` oracles are affordable there (36 s for
  the module).
* The perf-profile binary (`--profile perf`, symbols) differs from release
  in inlining; profile *shares* are hints, instruction counts are evidence.
