# Handoff: the PlusCal arc's closing session — a solver soundness bug the pipeline test caught, the `$dom` wall named (2026-09-22)

**From:** the session that closed out `2026-09-21-pluscal-landed.md`'s
verification bar and then followed the thread it pulled. The headline is
not PlusCal — the translator was done — it is a **false-`unsat` class in
`nixie-solver`'s array theory** that the new translate→BMC pipeline test
caught, complete with a measured corpus impact (two false cleans on the
BMC corpus) and a fix verified to the full solver-change bar. Read
`AGENTS.md` first; read `2026-09-21-pluscal-landed.md` for the translator
itself. **Next owner's entry point: the `$dom` set-atom wall, item 1
below, with a concrete first-session recipe.**

## What landed (aa9e9d1b, plus the closing-numbers follow-up f3fb692b-equivalent)

A record-keeping note first: **`main` was rebuilt by another agent** after
my PlusCal landings — those commits exist on main as rewritten copies
(`1cccf71b` → `bcf430d9` etc.). Any worktree or branch still holding the
old lineage has silently diverged; check
`git merge-base --is-ancestor main <ref>` before rebasing anything old.
This cost an hour of rebase confusion mid-session.

### The bug

`array_axioms.rs`'s **upward aliased read-over-write** loop iterated
`collected.aliases` — which deliberately includes **conditional** aliases
(a `var = store(...)` equality inside an `or`/`ite`/`=>`, recorded there
for the *guarded* lemma families) — and asserted the aliased-form lemmas
with **no antecedent**:

```
i ≠ j  ⇒  select(var, j) = select(base, j)
```

Those are theorems only for **level-0** `var = store(...)` conjuncts —
exactly the distinction `ArrayStructure::asserted_aliases` exists to
carry and documents ("a conditional alias … would fabricate lemmas").
The loop never consulted it. For a conditional alias the miss-case is
simply false whenever a different disjunct ran; with literal indices the
antecedent folds away and a **bare `select(x1,2) = select(x2,2)` lands in
the core as a fact**, killing satisfiable branch combinations: false
`unsat`.

Why nothing caught it before PlusCal: it needs a disjunction of
store-updates on **two or more array variables with select-guards** —
i.e. exactly the shape every multiprocess PlusCal translation produces
(`Next == \E self \in S : P(self)` with `pc' = [pc EXCEPT ![self] = …]`
inside). Hand-written SMT2 in the corpus never had the shape.

### The method (worth reusing — this is the session's transferable skill)

1. **Suspect the translation, prove otherwise.** The pipeline test said
   `NoViolationWithin` for a property TLC refutes in four steps. TLC on
   the same translated module confirmed the violation is real → the
   checker, not the translator, was wrong.
2. **Bisect at the TLA level** (M1–M17, N1–N5): which constructs make it
   appear/vanish. Found the trigger: ≥2 function variables, both
   store-updated under the same `\E self`.
3. **Dump the exact assertion set** (`bmcdump` example, landed) and hand
   the identical formula to **Z3**: z3 `sat`, nixie `unsat` → the terms
   are fine, the solver is wrong, and the smallest divergent script is
   588 bytes.
4. **Validity-check every lemma the run asserts** against Z3 (universal
   quantification over minted witness constants): the invalid ones
   separated from the Skolem-legitimate witnesses immediately. The
   invalid family was all miss-cases of one shape.
5. Fix, pin (test must fail `unsat`-vs-`sat` pre-fix — verify by
   reverting the gate alone), re-run the corpus differential.

Step 3's dump→Z3 cross-check is the general recipe for any future
"nixie says X, is the input or the solver wrong" question; `smtrepro`
(landed) runs any SMT2 script through `nixie_solver::Context` for
exactly this.

### The measured impact

`bench/tla_bmc` corpus harness, tlaplus-examples, same 16 checked specs,
before → after: **15 clean / 0 violations / 1 unknown → 13 clean / 1
flagged violation (under a dropped ASSUME, un-replayed) / 2 unknown.**
The two flipped specs were false cleans. Recorded in
`bench/tla_pcal/METHODOLOGY.md`'s new section.

### The verification bar (all green)

- 12,215+ workspace tests (2 `scope_rebase` timeouts under parallel load
  were **disk pressure**, see traps — both pass standalone pre- and
  post-fix at 229s/261s);
- Z3 parity 100%, 0 decisive mismatches (z3 4.16.0);
- perf gate PASS (conflicts/decisions 1.000, wall 0.87–0.91);
- clippy/fmt/doc clean.

Pins: `conditional_alias_tests` in `array_axioms.rs` (the two-array
588-byte repro + the isolated miss-case shape) and four
`nixie-tla-check` pipeline tests in `tests/bmc.rs` — including
`a_two_array_pluscal_spec_never_answers_a_false_clean`, which asserts
the honest `Unknown` so a regression to the false clean fails loudly.

Debug tooling landed: `smtrepro` (solver-level SMT2 driver),
`bmcdump` (per-depth BMC assertion-set dumper), `dumptrans` (translate
one PlusCal file), and an env-gated `NIXIE_ARRAY_LEMMA_LOG=1` print on
the lemma-assert path. Binaries cached at `precompile/aa9e9d1b/`.

## Also closed from the previous handoff's bar

- The two standing parity gates re-run green on the committed tree:
  `bench/tla_parity` 4 422 definitions / 0 mismatches; `bench/tla_eval`
  362 agreeing / 0 mismatches.
- BMC smoke on the named targets: DiningPhilosophers NP=2 gives a real
  `NoViolationWithin` on `ExclusiveAccess` at depth 4; QueensPluscal
  (enumerable-domain wall) and KVsnap (Init-encoding decline) verified
  **identical on the oracle's translation** — pre-existing walls, not
  translation defects. Queens/KVsnap/DP walls all documented in the
  METHODOLOGY.
- `run_parity.sh` now exits 2 with a usage line on an empty corpus (it
  ran vacuously from relocated worktrees before).

## The TLA+ open map (ranked)

### 1. The `$dom` set-atom wall — the named next step

With the false-unsat fixed, the standard multiprocess shape
(`x[self] := …`, ≥2 function-valued variables updated in one step)
answers **honest `Unknown`**: the satisfying assignment needs set atoms
the native set encoding cannot certify (`set_terms_unconstrained` —
`NIXIE_DEBUG_QROUNDS=1` prints the exact downgrade reason). Every
function-sorted state variable gets a `$dom` companion; `UNCHANGED` and
`EXCEPT` translate into `$dom` **chain equalities**
(`x@k$dom = x@k+1$dom`), and those set-sorted atoms trip the gate
because native sets aren't wired into Nelson-Oppen.

**First-session recipe:**
1. `bmcdump` the two-array pipeline test at depth 4; confirm the gate
   fires on `$dom`-sorted atoms specifically (not the ground `1..N`
   domain terms, which have candidate lists).
2. Classify `$dom` atoms: **chain equalities** (EUF decides them — they
   should never reach the set theory), **ground terms with candidates**
   (the arena/finiteset path), **genuinely symbolic** (keep the honest
   decline).
3. Success criterion, already pinned: `a_two_array_pluscal_spec…`
   becomes `Violation { step: 4 }`; the false-clean pin stays sat-or-
   better; TLC state parity (`bench/tla_pcal`, the `pcalsem` harness)
   confirms verdicts are right, not just different.
4. Re-run the solver-change bar (Z3 parity + perf gate) — this touches
   the combination layer.

The larger route (wire native finite sets into Nelson-Oppen) is the same
design that unblocks item 2.

### 2. The `Bag`-sort bridge / lambda-shaped function encoding

Unchanged from `2026-09-21-pluscal-landed.md`: symbolic-domain bag
updates and `DOMAIN` quantifiers; the workload now exists (35 PlusCal
files). Design note first.

### 3. Delta-propagation proof obligation (study item 85) — waiting, not urgent.

## Traps (new this session; the standing ones still stand)

- **Root filesystem `/` swings to 100 %.** This bit three ways: silent
  **truncation of files being written** (lost `pcalsem.rs` and
  `run_parity.sh` mid-edit to 0 bytes — always write via temp file +
  `mv` when `/` is over ~95 %), **nextest timeouts from IO pressure**
  (the `scope_rebase` "regression" was disk, not code — rerun standalone
  before believing a timeout), and build-link failures. Countermeasure:
  `df -h /` before writes and test runs; `CARGO_TARGET_DIR` on
  `/media/data` when `/` is full (it had 107–172 G free all session).
  The big root consumers (`~/.cache/uv` 26 G, `sccache` 7.5 G) are
  other agents'.
- **`main` is heavily contended.** Four+ agents landed 10+ commits
  during this session; `git push . HEAD:main` is refused whenever the
  shared checkout (on `main`) is dirty — which is nearly always. What
  worked: own worktree → rebase → retry push in a loop catching the
  clean window right after another agent's commit lands; `git merge
  --ff-only` from the shared checkout as the last resort (only after
  confirming no file overlap with the resident's dirty set). Never
  force; never rewrite.
- **`main` can be rebuilt under you** (see the record-keeping note).
  Worktrees/branches holding the old lineage diverge silently.
- `/tmp`'s `d15*`/`dd_*.smt2` files and the `/tmp/nixie-*` worktrees
  belong to the active agents — leave them.
- The two-array PlusCal `Unknown` is **expected and pinned**; don't
  "fix" it away without the item-1 work.
