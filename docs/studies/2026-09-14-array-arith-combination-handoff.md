# Handoff: the array/arithmetic combination arc

Written 2026-09-14 at the end of the session that opened and closed it. Read
this before touching `purify_numeric_uf_args`, `interface_const_pins`, or the
trichotomy machinery in `encode.rs`.

## What this arc was

A TLA+ specification from Apalache's own test suite (`Rec3.tla`) was reported
as violated when it has no counterexample. Chasing it found **two distinct
wrong `sat`s** in the array/arithmetic combination, neither of which had
anything to do with TLA+ — both are reachable from four or five lines of
SMT-LIB.

The entry point was the trace replay in `nixie-tla-check`: it decodes a
reported counterexample and re-checks it with `nixie-tla`'s evaluator, and
surfaced both as *decoded but did not replay* rather than counting them as
violations. That gate paid for itself three times in one session.

## What landed on `main`

| commit | what |
|---|---|
| `9195a7a7` | **Wrong `sat` #1.** A lemma-minted numeric equality atom with no trichotomy clause. |
| `112731aa` | the reproducer's module doc, which still called itself a known failure |
| `bb71b91f` | cost re-measured on settled load: 5.5x on `pete_5s`, not the 10x first reported |
| `8512a2f8` | **Wrong `sat` #2** — see the warning below; this commit's *subject* is about the QF_FF arc and says nothing about it. |

Studies: `2026-09-14-array-index-equality-from-arithmetic.md` (#1, closed) and
`2026-09-14-array-index-entailed-equal-to-a-constant.md` (#2, closed).

### The two defects, in one paragraph each

**#1 — no trichotomy on a lemma-minted equality.** `(a = b) | (a < b) |
(a > b)` is the only channel by which a numeric disequality reaches the
tableau: `process_constraint`'s negative-`Eq` branch tells EUF and the BV
solver and stops, and must, because the simplex has no `!=`.
`ensure_numeric_equality_splits` builds that clause by walking
`self.assertions` — so an atom a *lemma* mints (a read-over-write index guard,
an arrangement care-split) is invisible to it. Fix: the encoder queues every
numeric `Eq` atom it mints while `solving`, and `encode_depth` drains at
`depth == 0`. `refine_arrangement_splits` had the same hole in a non-array
path; the same fix closes it.

**#2 — a constant array index is not an interface term.**
`nelson_oppen_combine`'s arithmetic-to-EUF probe pairs terms that are both EUF
application arguments *and* arithmetic interface terms. In
`select(A, 0) = 0, select(A, 1) = 1, n0 = 0, n = n0 + 1, select(A, n) = 5`
the constant `1` is the former but not the latter, so `(n, 1)` was never
proposed, the entailed `n = 1` never derived, and the congruence
`select(A, n) = select(A, 1)` never fired. No store is involved, so nothing
mints an index atom and fix #1 cannot reach it. Fix: `purify_numeric_uf_args`
gets a `Select`/`Store` arm that **pins** a constant numeric index (it already
pinned constant `Apply` arguments — the `pr30#3` class — and walked past
arrays). Pinned, not purified: the array theory matches indices by `TermId`,
so a proxy would change which writes a read is judged to alias.

## NOT landed — pick this up first

`b177fab5` in the worktree **`/tmp/wt-selidx`** (detached, rebased onto
`8512a2f8`):

> `refactor(solver): name the constant-pin map for what it now holds`
> `quant_uf_const_pins` -> `interface_const_pins`,
> `pin_quantified_uf_const_arg` -> `pin_interface_const`, six files.

Why it exists: the `quant_` meant *quantified* (the map was populated only for
functions in `quantifier_uf_funcs`). Fix #2 gave it a second population that
has nothing to do with quantifiers, so the name described half of it. It also
moves a `trail.rs` comment that sat on the pin map but described
`numarg_proxies`, and drops a dead `continue`.

**Do not rename it to `qf_*`.** `QF_*` is the SMT-LIB *logic-name* pattern and
appears in this repo only as string literals in `logic_contract.rs`; reading
`quant_` as quantifier-free inverts the meaning.

To land: `git -C /tmp/wt-selidx log -1`, confirm it still rebases onto `main`,
then ff-merge. Delete the worktree afterwards (`git worktree remove`); its
target dir was already cleaned.

## Verification status — read this carefully

The **full change** (fix #2 + rename, on base `bb71b91f`) is green:

* `cargo nextest run --workspace --all-features` — **11 672 / 11 672 pass**
* `./bench/z3_parity/run_parity.sh`, z3 **4.16.0** — 177 benchmarks,
  **100.0 % parity, 0 mismatches**, recorded verdicts unchanged
* `cargo fmt` clean, `cargo doc` clean; clippy adds nothing beyond the four
  findings already on `main` in `nixie-solver` (`clone_on_copy` x2 at
  `encode.rs:332,360`; `doc_lazy_continuation` x2 at `encode.rs:955`) and the
  three `unused_mut` in `nixie-theories/src/arithmetic/simplex/mod.rs:3041,
  3258,3267`. **`main` does not currently pass `cargo clippy -D warnings`**,
  and has not for this whole session — it is not from this arc.

After rebasing onto `8512a2f8`: **11 670 passed, 0 FAIL, 5 timed out**. The
five are the known-slow set (`scope_rebase_tests` x4,
`bv_odd_width_blast_differential::odd_width_identity_pairs_hold`). Re-run in
isolation, four passed; `odd_width_identity_pairs_hold` still hit the 180 s
nextest cap, having passed at 135 s / 143 s / 153 s in three earlier runs.

**Outstanding, and the first thing to do after landing:** re-run that one test
on an idle machine. It is pure BV and the change only touches Int/Real-sorted
constants, so a real interaction would be surprising — but it is not confirmed
and should not be written up as if it were.

## The corpus check — NOT done

Before fix #2, the 905-module corpus stood at (`run_fix.txt` in the session
scratchpad):

```
prepared 228, checked at depth 4: 90
  no violation within the bound : 66
  violations found              : 21
    of which replayed end to end     : 19
    of which decoded but not replayed:  2
```

The two non-replays are `Rec3.tla` (`Next` from state 0 is FALSE — fix #2) and
one `ASSUME` that exceeds the 4096-element set limit (not a wrong answer).
**Expect 1, not 2, after fix #2** — `Rec3.tla` alone now reports *no
counterexample of 3 step(s) or fewer*. The re-run was started and killed by
machine memory pressure; it has not been measured.

Do measure it. This exact check is what caught a **false attribution** in
study #1, which originally claimed `Rec3.tla` was one of the two specs that
defect explained. It was not — it was defect #2 — and only the corpus re-run
revealed it. That correction is recorded in both studies.

Runner: `bash <scratchpad>/corpus.sh > out.txt` after
`cargo build --release -p nixie-tla-check --example bmccheck`. ~9 min idle.

## Open work, ranked

1. **The corpus re-run and the one BV test** (above). Cheap, and closes this arc.
2. **`pete_5s` costs 5.5x** from fix #1 (3.16/3.16/3.35 s -> 17.61/17.63/18.29 s,
   n=3 each, settled load). Not volume — 101 trichotomy clauses over the whole
   run — but **202 unguided `lt`/`gt` atoms**, the free-comparator thrash the
   injective-map A-family suppression exists for.
   `add_arith_trichotomy_clause` already pins a deterministic acyclic
   orientation, but only under `has_array_ops && plain_vars`. Extending that to
   lemma-minted pairs is a **heuristic** change: matched null, >=10 seeds, per
   `docs/BENCHMARKING.md`. Do not bundle it with a soundness fix.
3. **The set theory is the real next TLA+ slice**, not the `..` bounds. I
   ranked `..` second on a count of 22 blocked specs and that ranking was
   wrong: **17 of the 22 have no `.cfg` at all**, so their CONSTANTS are
   genuinely unpinned and refusing is *correct*. The remaining shapes
   (`1..natMin(primer, template)`, `0..(nSntE + nByz)`, `1..x'`) are
   variable-bounded ranges — the same capability the set theory needs, not an
   independent slice.
   Set-shaped causes dominate the blocked list: **47 + 11 + 10 + 4 = 72 specs**.
4. **Wiring `nixie-theories/src/set/` in is not a shortcut.** Surveyed: 8 366
   lines, but `SetExpr::Singleton(u32)` (elements are opaque `u32`, not
   `TermId` — TLA+ sets hold ints, strings, tuples, records, functions),
   `Comprehension { var, formula: Box<SetExpr> }` cannot hold a predicate,
   `can_handle` returns `true` for every term, `id()` returns
   `TheoryId::Bool`, `get_model` returns empty, and `Theory::check` maps a
   conflict to `TR::Unsat(vec![])` — **an empty conflict clause**. It is a
   propagator, not a decision procedure, and nothing in `nixie-solver`
   constructs it. The live path is `nixie-solver/src/solver/set_theory.rs`
   (689 lines, sound reduction, `set.card` honestly excluded). The missing
   capability there is **comprehension** — and `nixie-tla-check`'s
   `SetEncoding::Native` doc already says so.
5. `tla-connect`'s interactive JSON-RPC workflow — still unsupported.

## Traps this session actually hit

* **The machine is the main hazard, not the code.** Three separate "failures"
  were infrastructure: 3 test timeouts (my private target dir filled `/` at
  114 GB), a linker `Bus error (core dumped)` (`/media/data` at 0 bytes), and
  **12 `nixie-tla-check::sequences` FAILs at 0.003 s each** (another agent
  rebuilt the shared `target/` mid-run — all 18 passed in a clean tree at the
  identical commit, and the next invocation died with `can't find crate for
  nixie_theories`). None were real. Do not write any of these up as results.
* **Size a private target dir.** Full workspace `--all-features --all-targets`
  debug is **~130 GB**. With
  `CARGO_PROFILE_DEV_DEBUG=line-tables-only CARGO_INCREMENTAL=0` it is
  **~31 GB**, with `opt-level` and `debug-assertions` untouched so every test
  outcome is identical. Reclaim with `cargo clean --profile dev`.
* **Uncommitted work in the shared checkout gets committed by someone else.**
  Fix #2, its three regressions and both studies were swept into `8512a2f8`,
  an unrelated docs commit, while still being verified. Snapshot into your own
  worktree the moment an edit is complete. If it happens to you: rebase onto
  their commit, never revert or rewrite it, and say in your own message which
  commit carried the rest.
* **Load, not regression.** Timeouts clustered on the same five tests at load
  average 32-48 on a 20-core box. Check `uptime` before believing a timing
  result.
