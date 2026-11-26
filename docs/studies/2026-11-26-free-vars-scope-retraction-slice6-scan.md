# Free-variable collection, batched retraction, and the slice-6 scan – three cost slices (2026-11-26)

Three slices off the opportunity list of 2026-11-26, on base `8f3d9cc6`
(the session opened on `d52242fe`; `main` moved under it twice – to
`8f3d9cc6` with `90298f37`, the inprocessing scope fix, and on to
`47b5c438` with the tla line – neither touching the files below or, for
the second, a crate the `nixie` binary compiles).  One is an output-identical win on a traversal that the
standing corpus does not run; one is a trajectory-identical retraction on
the SAT side whose two quadratic terms each cost up to tens of
milliseconds on shapes the in-repo TLA queries produce; one is a scan skip
in the simplex that the new census shows paying on one standing cell in
25.  None is a benchmark win on the standing probe; each is reported for
what it is.

## Method

Cost is paired instruction counts (`perf stat -x, -e cpu_core/instructions/u`
on the P-cores, cores 0–7 of this box), interleaved, candidate against the
base built the same way.  The box ran at load 11–92 throughout (other
agents' builds and test runs), so wall is quoted only for the component
tables, as the median of interleaved runs, and never as a gate.  Three
probes drove the components, all from temporary files (the method of each
is in its section):

* a `nixie-core` example that parses a corpus file and times
  `TermManager::free_vars` on its assertions, carrying a copy of the
  pre-change traversal for an in-process interleaved A/B;
* a `nixie-sat` example that builds a scope (`push`, clauses, optionally a
  bounded search) and times the one `pop` / `forget_learned_since`, with a
  `-setup` twin that stops before the retraction so that a whole-process
  instruction count subtracts to the retraction alone;
* a `nixie-theories` example that builds a narrow tableau and runs the
  slice-6 pass after its inputs have settled.

Instruction counts repeat to ~1e-7 here, so the component numbers below
are exact for the binaries that produced them; they are one machine's.

## Slice 1 – free variables: a membership index past the measured crossover

`TermManager::free_vars` kept its answer in first-occurrence order and
asked the output vector whether a variable was already in it
(`vars.contains(&id)`) at every free occurrence: n²/2 comparisons for n
distinct variables.  One SchurNumbers assertion (QF_BV/asp) has 24,306;
the traversal compared 295 million times, 77 ms.

Indexing every occurrence was the first candidate and it is not the change
that landed.  Measured in-process against the pre-change traversal
(interleaved, 8 occurrences per variable), the index is the SLOWER of the
two up to about a hundred variables – a contiguous `u32` compare
vectorises, a hash insert does not – and by 18–30 % on this box's E-cores:

| distinct variables | 2 | 4 | 8 | 16 | 32 | 64 | 96 | 128 | 256 | 512 | 1,024 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| index / scan, P-cores | 1.04 | 1.03 | 1.02 | 1.00 | 1.02 | 1.00 | 1.01 | 0.97 | 0.74 | 0.51 | 0.33 |
| index / scan, E-cores | 1.06 | 1.24 | 1.30 | 1.27 | 1.25 | 1.18 | 1.02 | 0.97 | 0.78 | 0.54 | 0.36 |

Most traversals in a solve are small – the MBQI grounding guard and
`is_ground` ask about single terms – so the landed query
(`ast/manager/query.rs`) scans below
`FREE_VARS_INDEX_MIN = 128` and indexes above it, migrating the scan's
output into the index once.  An occurrence is recorded only once it is
known to be free: a `Var` node has one `TermId` wherever it occurs, and a
shadowed occurrence recorded as seen would hide a later free one (the
regression test `a_shadowed_occurrence_visited_first_does_not_hide_the_later_free_one`
fails against that ordering; it pins both halves of the membership test).

Both arms of the final code, against the base library built the same way
(`8f3d9cc6`'s `query.rs`):

| parsed corpus file (one assertion) | free vars | instructions per traversal | wall, interleaved (P-cores, load 20–90) | ordered output |
|---|---:|---:|---:|---|
| QF_BV/asp/SchurNumbers/15.1.schur.lp.smt2 | 24,306 | 1,551.0 M → **40.3 M** (0.026) | 76.0–76.9 ms → 3.0–4.1 ms | identical (hash of the id sequence) |
| QF_BV/asp/SchurNumbers/20.18.schur.lp.smt2 | 24,281 | – | 73.9–74.7 ms → 3.0–3.9 ms | identical |
| bofill-scheduling ex10000_2600_100 | 780 | 3.463 M → **2.074 M** (0.599) | 0.18–0.38 ms → 0.11–0.20 ms | identical |
| QF_AUFLIA/storecomm 00050_001 | 51 | 67,815 → 67,973 (1.0023) | – | identical |
| QF_UFLIA/wisas/xs_8_13 | 13 | 120,525 → 120,595 (1.0006) | – | identical |
| AUFLIA/Rodin smt3330… (quantified) | 3 | 2,929,559 → 2,933,653 (1.0014) | – | identical |

Instruction counts are whole-process over N traversals (parse amortized:
40 of the SchurNumbers file, 20,000 of the others), the mean of three
interleaved pairs; a second run of the three small files, and of a ground
one and a 2-variable one, at 30,000 traversals read 0.9966–0.9994.  Below
the crossover the change is inside ±0.35 %.

## Slice 2 – `pop` and `forget_learned_since`: per list, and the registry once

`Solver::pop` retracted a scope's clauses one at a time: per clause, a
purge of its two implication-graph edges (`purge_binary_edges`: a scan of
the trigger's list to the edge, then a move of the rest), its DRAT
deletion, its removal – and a `learned_clause_ids.retain` over the whole
registry.  Two quadratic terms:

* **shared triggers.**  A list holding d of the scope's edges is rescanned
  d times, each scan to its edge: with ids ascending in a list, the i-th
  removal walks i edges.  16,000 binary clauses under one trigger: 28.1 ms
  to pop; the same 16,000 over disjoint triggers: 0.18 ms.
* **the registry.**  k retracted ids × L registered learned clauses
  compares, whether or not the retracted clause is learned.  A real scope –
  8,000 shared binaries, 68,000 asserted 3-clauses and 4,245 clauses a
  bounded search learned – popped in 86–97 ms, of which the registry was
  340 million compares.

`Solver::retract_clauses` (`solver/incremental.rs`) does one pass over the
batch and removes the edges per LIST: a list holding two or more of the
batch's edges is compacted once, order-preserving
(`BinaryImplicationGraph::remove_marked_edges`, sharing `sift_span` /
`sift_extra` with the factor pass's `compact_dead`); every other list keeps
the per-edge removal, which is the cheaper constant there.  Which lists
those are is found without a second walk: an edge within
`RETRACT_PER_EDGE_MAX_LEN` (8) of the front of a short list goes as it is
met; a long list's entry is collected, and its LAST entry – the first one
reached in a backwards walk – says whether the batch holds one edge there
(the per-edge removal, by the unbounded scan) or several (the compaction).
A short list only shrinks and a long one is only shortened in the
backwards walk, so no list takes both paths.  The registry is filtered
against the batch's marks once.

Two attempts are recorded because their measurements are the reason the
landed shape is what it is:

* **Compacting every touched list** made the disjoint shape 1.31–1.58×
  slower: a one-edge list costs the old removal ~13 ns and the batch's
  bookkeeping more than that.
* **Bounding the per-edge scan instead of the list length** reintroduced a
  quadratic: once the first eight edges of a 16,000-entry list went
  per-edge, the next eight were shallow too, and every removal moved the
  rest of the list (101 M instructions against the base's 900 M).

Per-retraction instruction counts, base against candidate, each the mean
of two interleaved pairs (the `-setup` twin subtracts everything else):

| retraction | base | candidate | ratio |
|---|---:|---:|---:|
| pop: 16,000 binaries under one trigger | 899.9 M | **5.20 M** | 0.006 |
| pop: 76,000 asserted + 4,245 learned (a bounded search in the scope) | 2,627.5 M | **15.8 M** | 0.006 |
| `forget_learned_since`: 4,245 learned, short lists (the FP probe shape) | 0.707 M | 0.743 M | 1.051 |
| pop: 16,000 binaries, disjoint one-edge lists | 3.968 M | 4.623 M | 1.165 |
| pop: 2,000 binaries, disjoint | 0.480 M | 0.562 M | 1.170 |
| pop: 200 binaries, disjoint | 50.9 k | 58.8 k | 1.155 |

Wall for the two first rows: 28.1 → 0.17 ms and 97 → 0.74 ms.  The
remaining cost on the shapes where the old code was already fast is the
batch's bookkeeping – one mark, one flag and one push per edge: +43
instructions per binary clause on one-edge lists (0.1 ms per 16,000), +9
per learned clause on the FP shape; a scope of one clause on a 64-edge
list pops in 40 ns against 28.

**Where it runs.**  Every SAT-level `pop` – an SMT-LIB `(pop)`, each
`nixie-tla-check` query (the lasso encoding of #29 asserts ~1,400
scope-owned clauses per query, plus what the query's search learns) – and
the FP solver's `forget_learned_since` per probe.  The standing cells are
non-incremental; the probe shows the change's cost there as neutral (see
Bar).

**Equivalence** is held by `solver/retract_tests.rs`, whose oracle is the
retired per-clause sequence: two solvers are built to the same state (six
40-edge lists under one trigger with 30 scope clauses each, twelve 12-edge
lists with one, eight 5-edge lists shared by three, random binaries and
longer clauses, a pigeonhole core, a 400-conflict search in the scope, a
graph rebuild with the scope open so that the batch's edges sit in the
primary spans as well as the overflow lists, a learned clause retired
before the pop); on one, every binary of the batch is purged by the
unbounded `purge_binary_edges` before the retraction; on the other the
retraction runs alone.  The two must agree on every implication list edge
for edge and in order, on the learned registry, on the live-clause set, on
the DRAT proof byte for byte, and on the whole search that follows; the
same for `forget_learned_since` with learned binaries on long lists (made
by `learn_clause` itself).  Checked by mutation: skipping the compaction,
leaving the marks unset, leaving the primary span alone, and leaving the
overflow list alone each fail at least two of the five tests.

## Slice 3 – slice 6: the narrow scan runs only when a row is marked

`Simplex::propagate_bounds_in` skips the derivation of an unmarked row but
walked the whole `tableau` to find the marked ones.  A flag
(`s6_any_marked`) is raised by the one marking site (`s6_mark_rows_of`)
when it marks a row and cleared by every pass; with the global inputs
unchanged (`rows_ver`, `cross_ver`, the integer set) and the flag clear,
no row of the tableau is marked and the scan is skipped.  The invariant the
skip rests on – after a pass no tableau row stays marked, and a row cannot
gain or lose tableau membership without a `rows_ver` bump, which makes the
next pass visit everything – is asserted under `debug_assertions` at every
skip, so the whole test suite checks it.  The wide-row loop and the
pending-crossing handling run on every pass as before.

| tableau rows | idle pass, base | idle pass, candidate |
|---:|---:|---:|
| 1,000 | 20,063 instructions (0.76 µs) | 166 (0.017 µs) |
| 4,000 | 79,748 instructions (3.4 µs) | 166 |
| 16,000 | 318,500 instructions (14.9 µs) | 166 |

**The census.**  `S6_SCAN_TRACE` (re-exported through `nixie-solver`;
`; stats s6: passes= scans= rows_skipped=` on `--stats` / `STATS=1`) and
`Simplex::s6_scan_census` count the passes, the ones that walked, and the
rows the skipped walks would have visited.  Over the 25 standing probe
cells, 76,443 passes, 2,428 skipped (3.2 %), 2,673,111 rows not walked –
all of it on one cell:

| cell | passes | scans | rows skipped |
|---|---:|---:|---:|
| QF_UFIDL/vlsat3_f30 (conflict limit 3,000) | 17,937 | 15,509 | 2,673,111 |
| the other 16 cells whose arithmetic runs the pass | 58,506 | 58,506 | 0 |

Every pass on the other cells arrives with a row marked or a global input
changed: the fixpoint loop ends on the pass that stores nothing, and the
next final-check round pivots first (`rows_ver`), which makes its first
pass `all`.  On the probe the slice is
therefore 1.26 % of one cell's instructions (vlsat3_f30: 4,038.9 M →
3,987.9 M) and nothing elsewhere – inside the neutrality band, and
reported as the structural change it is: a settled tableau now costs a
pass nothing, for the callers that re-tighten without a pivot in between.

Tests (`simplex/tests.rs`, `s6_scan_tests`): the census of a 1,000-row
tableau through convergence, 1,000 idle passes, a bound write, a scoped
write and its pop, and two resets (each event's scan count exact); and a
wide basic over a settled tableau whose crossing with a later bound is
still found on a pass whose narrow scan was skipped.  Ignoring the flag in
either direction fails both.

## Bar

Run on the final tree (`47b5c438` plus these changes; `47b5c438` differs
from `8f3d9cc6` in the tla line and `bench/` only, none of it in a crate
the `nixie` binary or the tested crates compile), the candidate built with
the standing recipe.

* `cargo fmt --all -- --check`; `cargo clippy --all-features --all-targets
  -- -D warnings`; `cargo doc --no-deps --all-features` (warnings are
  errors through `rustdocflags`): clean.
* `cargo nextest run -p nixie-core -p nixie-sat -p nixie-theories -p
  nixie-solver -p nixie-cli --all-features` (dev profile, E-cores, load
  70–117): **9,034 run, 9,016 passed, 14 skipped**, 13 failed, 5 timed
  out – every non-pass accounted for, none from this change:
  * 11 `SIGABRT` stack overflows: the documented 128 KiB-stack canaries
    (`*_small_stack`, `check_array/eval_*`, `format_sort_name`) over code
    byte-identical to `main`.
  * 2: `choose_of_ite_picks_the_taken_branch` and
    `rejected_set_synthesis_cannot_publish_identical_choices` (the
    documented sets pair).
  * 5 slow-timeout terminations: `pete_5s_family_instance_is_unsat`,
    `odd_width_identity_pairs_hold`, `memory_alias_shape_converges`,
    `memory_alias_shape_with_guard_clauses_both_polarities`,
    `order_network_random_differential`.
  * **In the release profile all 18 pass** on this tree (their binaries
    built with `cargo test --release --no-run --lib --test <name>` and run
    from `target/release/deps/`: the canaries and the sets pair in 0.5 s;
    the five slow ones in 95, 39, 20, 76 and 37 s), and so do the new
    tests' homes – `retract_tests` 5/5, `s6_scan_tests` 2/2, the
    free-variable tests.
* `bench/z3_parity/run_parity.sh`: **171 Correct / 0 Wrong / 6
  Inconclusive** (z3 4.16.0) – the standing result.
* `bench/perf_gate/run_gate.sh` vs the pinned baseline: **PASS**, conflicts
  1.000 / decisions 1.000 / wall 0.98 (n = 9).
* `bench/perf_gate/paired_instructions.sh`: vs `precompile/8f3d9cc6/nixie`
  (the base): geomean **1.0000** over 12 cells (0.9998–1.0003), conflicts
  identical; vs the pinned `28e82c65`: 0.9934 (0.9769–1.0025) – the
  landings between the two bases, none of them this one.
* `bench/perf_gate/smt_probe_ab.sh` vs `precompile/8f3d9cc6/nixie`:
  verdicts and counters identical on every cell; 25 cells geomean
  **0.9996**; `vlsat3_f30` **0.9874** (slice 3's cell: 50.9 M instructions
  of 4,039 M), the other 24 within 0.9979–1.0015.
* The dev-profile run above predates the last edit to `query.rs` (the
  return to two references, trap below); that file's own tests were re-run
  after it in both profiles, and clippy, doc and every gate ran on the
  final tree.

## Traps recorded

* **`main` moved under the session, twice.**  `90298f37` and its merge
  `8f3d9cc6` landed in this checkout at 11:04 and four tla-line commits
  (`87e871a0` … `47b5c438`) between 14:51 and 17:02, each time with these
  edits uncommitted in the tree; `git status` and the diff stat were
  re-read before every build, and the base for every "HEAD" probe after
  11:04 is `8f3d9cc6` (`git diff 8f3d9cc6 47b5c438` over the CLI's crates
  is empty).  Another agent commits in this checkout; a commit here has to
  name its paths.
* **`target/release` and `precompile/28e82c65` were gone mid-session.**
  Between 09:00 and 15:00 the release profile directory shrank from ~54 GB
  to 0.7 GB without a `cargo clean` from this session (the volume's free
  space rose 30 → 59 GB), and the pinned gate baseline
  `precompile/28e82c65/nixie` disappeared with it.  The baseline was
  rebuilt from its commit in a throwaway worktree with the standing
  recipe; `precompile/8f3d9cc6/nixie` (the new base) was created the same
  way.
* **The gate binaries are the plain workspace build.**  The ~17 MB
  binaries under `precompile/` are what `cargo build --release` (no
  flags, the command `run_parity.sh` runs) produces: feature unification
  with `bench/profile` puts the `profiling` feature into every library.
  `cargo build --release -p nixie-cli` is a 7 MB binary and
  `--all-features` one of 17.7 MB with `pprof-signal` on (inert unless
  `NIXIE_PPROF` is set); neither is the standing recipe, and a paired
  instruction count against the standing binaries is only meaningful
  between builds of the same one.  Check `stat -c %s` against
  `precompile/<sha>/nixie` before believing an A/B.
* **The first "idle" pass is not idle.**  The probe's timed loop began
  right after the pass that stored the bounds; its first iteration reads
  the marks those stores left and scans and derives every row (5 ms at
  16,000 rows), which read as the cost of an idle pass until instruction
  counts with 3 and 1,003 passes subtracted to 166.  Time passes 3 onward.
* **A bounded scan is not a bounded list.**  Gating the per-edge removal on
  where the edge sits (slice 2, second attempt) let a long list feed one
  shallow edge after another down the per-edge path, each removal moving
  the rest of the list.  The gate has to be the list's length.
* **One `&mut` struct for two was not free.**  The first version of slice 1
  passed the output vector and its index to the step function as two
  `&mut` references; a clippy-driven tidy-up bundled them into one `&mut`
  struct with a `note_free` method and the small traversals read
  1.008–1.021 against the base – logic identical, `#[inline]` on the method
  no help.  Two non-aliasing references it stayed (`#[allow(
  clippy::too_many_arguments)]`, as `query/substitute.rs` does three times),
  and every "neutral" number above was re-measured on that build.
* **A stale scratch copy silenced the tests.**  A copy of `solver/mod.rs`
  saved for a library swap predates the test module; restoring from it
  dropped `mod retract_tests;` and the next two mutation checks ran zero
  tests (`Summary: 0 passed … skipped`) while printing `RESTORED_OK`.
  Read the test count on every nextest line; a mutant that changes
  nothing is either equivalent or not compiled.
