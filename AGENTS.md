# OxiZ – Agent Guide

> Instructions for any AI coding agent working in this repository. **Read this before editing.**
> This file is canonical; `CLAUDE.md` imports it.

## What this codebase is

OxiZ is a **pure-Rust SMT solver** – a clean-room reimplementation of Z3's CDCL(T)
architecture: SAT core, theory solvers (EUF, LRA, LIA, BV, arrays, strings, floats,
datatypes), quantifiers (E-matching, MBQI, QE), NLSAT/CAD, Spacer/PDR (CHC), proof
generation (DRAT, Alethe, LFSC, Coq/Lean/Isabelle exports), and optimization (MaxSAT/OMT).
See `README.md`, `docs/ARCHITECTURE.md`, and `CONTRIBUTING.md`.

It is ~440k lines across 17 crates, with advanced mathematics (CAD, resultants,
virtual substitution, Cooper, simplex, IEEE-754, polynomial GCD/resultant) and deeply
nested logic (recursive term/proof/model walks, hash-consed DAGs, CDCL search trees,
theory-combination glue).

**Correctness is existential, not a nice-to-have.** Downstream users run OxiZ to *prove*
things – formal verification, security analysis, compiler correctness, SMT-based model
checking. A single wrong `sat` or `unsat` can ship a bug, bless an unsafe system, or
"prove" a false theorem. A timeout or `Unknown` is acceptable; a wrong answer is a
catastrophe. Every rule below follows from that.

## Core operating principles (non-negotiable)

1. **This is highly complex, safety-critical software with advanced math and deeply
   nested logic.** Treat every change as if a verification pipeline depends on it being
   right. It often does.

2. **When debugging, dig very deep – and keep digging.** Apply a fix *while verifying
   soundness at every layer*, even when there is no immediate visible benefit, and even
   at the cost of a small performance regression. Keep digging and stacking fixes –
   sometimes **10 layers deep** – until the bug is actually resolved at its root, not
   papered over. The first plausible-looking cause is almost always a symptom, not the
   cause. Follow the causal chain all the way to the bottom before you stop.

3. **Always apply the most rigorous and correct fix, regardless of effort or cost.**
   Trying to simplify, shortcut, or "good-enough" a fix here **will always bite back** –
   usually as a latent soundness bug discovered months later in someone else's proof.
   Prefer the principled rewrite over the clever patch. Prefer the exhaustive `match`
   over the `unwrap()`. Prefer the explicit heap-stack walk over the recursive one.
   Prefer the real decision procedure over the heuristic that happens to pass the test.

   4. **When in doubt about how something should behave, read the reference implementations
   first**, before writing or guessing:
   - **Z3** source: [`../temp/z3`](../temp/z3) (C++; mostly under `src/`)
   - **CVC5** source: [`../temp/cvc5`](../temp/cvc5) (C++; under `src/`)
   - **CaDiCaL** source: [`../temp/cadical`](../temp/cadical) (C++; under `src/`;
     C++ binary at `../temp/cadical/build/cadical`)

   These are the ground truth for theory decision procedures, SAT/NLSAT, CAD, proof
   rules, quantifier handling, and theory combination. CaDiCaL is the ground truth
   for the SAT core (CDCL search, restarts, VMTF/VSIDS, inprocessing, LRAT). Before
   reinventing a procedure, find it in Z3, CVC5, and/or CaDiCaL, understand *why*
   it is shaped that way, and match their semantics. Do not invent new ones.

   **Read-only reference.** Do **not** add `z3`, `z3-sys`, `cvc5`, or `cadical` as
   dependencies – they are **banned** in `deny.toml` (this project is strictly pure
   Rust, no FFI, no C/C++). You consult their source as a specification; you never
   link it. `Pure Rust is a fundamental requirement` (`README.md`).

## Soundness rules specific to OxiZ

These are the recurring bug classes this codebase has actually bled from. Internalize
them; every one of them has caused a real soundness bug here.

- **No silent fallthrough.** An unmatched enum variant, an out-of-range index, a missing
  theory case, an unhandled AST node – these must raise an **error or return `Unknown`**.
  Never a default value, never a silently-dropped clause, never a fabricated answer. The
  0.3.1 soundness sweep found 40+ instances of "unhandled input silently dropped or
  defaulted instead of raising an error"; that pattern is the enemy. Prefer exhaustive
  `match` so a new variant *breaks compilation* rather than slipping through `_ =>`.

- **No fabrication.** An unjustified conflict clause yields `Unknown`, never `Unsat`. A
  model you cannot concretely verify yields `Unknown`, never `Sat`. When you cannot prove
  a step, say so honestly. Stale models / unsat-cores / proofs must be invalidated on
  `push`/`pop`/`assert` so a stale answer is never handed back.

- **Deep input must not overflow the stack.** Convert every recursive term / formula /
  proof / model / substitution walk into an **explicit heap stack**
  (`while let Some(frame) = stack.pop()` with resume state carried inside the frame enum,
  e.g. `Expand(T)` / `Combine(T, n)`). Do not write new unbounded native recursion over
  user-controlled DAGs. See the pattern note in `CONTRIBUTING.md` → *Error Handling*.

- **No `unwrap()`/`expect()` in production code.** `clippy::unwrap_used` is `deny` in
  every member crate. A peek-then-pop `expect("just matched above")` is **not** an exempt
  "truly impossible case" – it is exactly the shape this rule exists to forbid, because
  every future refactor done the same way reproduces the unsoundness. Make the impossible
  state unrepresentable instead.

- **Wide bit-vectors and bignums are exact.** `>64`-bit BV constants, `BigUint` /
  `BigRational` paths, resultants, GCDs – never truncate to `u64`/`f64` for convenience.
  Truncation has already produced both false `sat` and false `unsat` in this codebase.

- **State must be scope-consistent across `push`/`pop`/`assert`.** Theory solvers,
  Tseitin memos, MBQI search state, `term_to_var` maps – anything that can leak across a
  scope boundary *has* leaked here. On `pop`, roll every table back in lockstep; do not
  wholesale-clear a memo and re-encode on the next check.

- **Math must be real, not stubbed.** Primitive PRS polynomial GCD, exact resultants,
  real Ferrante-Rackoff / Loos-Weispfenning virtual substitution, IEEE-754-correct
  `fp.rem` and single-rounded FMA – these replaced earlier stubs. A "TODO: implement
  properly" that returns a plausible default is a soundness bug waiting to fire. If you
  encounter one, implement it properly (principle 3) or make it return `Unknown`.

## Git: never stash or restore

Multiple agents work in this repo **in parallel**. **Never** `git stash`,
`git stash pop`/`apply`, `git restore`, `git checkout --`, or any other command
that discards or overlays uncommitted work in the shared working tree — you will
wipe another agent's in-flight changes. If you need a clean tree, create a
**git worktree** (`git worktree add …`) and work there.

## Git: land every finished step on `main`

After each **meaningful** completed step or experiment, **commit to `main`**.
Do not leave finished work sitting only in a worktree, a feature branch, or
uncommitted files. A meaningful step is a finished bug fix, a landed feature
slice, a measured experiment with a verdict, or a recorded negative result —
not a half-written function or a mid-debug scratchpad.

- **Positive / productive step:** commit the code (and tests) to `main`.
- **Negative experiment:** do **not** discard the finding. Write it up (verdict,
  what was tried, why it failed, what not to retry) under `docs/studies/` and
  commit that documentation to `main`. A negative result that exists only in
  chat is wasted work the next agent will repeat.
- Stage **only your own files**. Never commit another agent's in-flight edits.
  Inspect `git status` / `git diff` before every commit.
- If the primary checkout is dirty with someone else's work, commit from **your
  worktree** and fast-forward `main` (`git push . HEAD:main` when `main` is a
  strict ancestor; otherwise merge `--ff-only` into `main` from a clean
  checkout). Never force-push, never rewrite `main`, never stash to make the
  land possible.
- Do not skip the verification bar in *How to verify your work* just to land
  faster. A commit of a known-broken tree is not a finished step.

## Git: clean up after yourself

When a step is landed (or abandoned), **delete every worktree, branch, and
artifact you created** that is not currently in use by another agent:

- `git worktree list` / `git branch` — remove *your* unused worktrees
  (`git worktree remove …`) and *your* unused branches. Leave anything another
  agent still has checked out or that still has uncommitted work.
- Scratch files, temp corpora, one-off scripts, profile dumps, and similar
  artifacts you created outside the commit: delete them. Do not leave `/tmp`
  trees, extra worktrees, or local branches as implicit documentation —
  if it mattered, it is on `main`.
- When unsure whether another agent is using it, **leave it**. Cleanup is
  mandatory for *your idle* leftovers, not a license to garbage-collect the
  shared tree.

## Git: older binaries for testing

If you need an **older revision's binary** (baseline, bisect, A/B, parity):

1. Check it out in a **throwaway worktree** (never `git checkout` / `restore`
   on a shared tree).
2. Build the binary, **copy only that binary** to a stable path
   (e.g. `/tmp/oxiz-<sha>` or a local `bench/bin/` you will delete later).
3. **Immediately** delete the worktree, its `target/` dir, and any other
   source/build artifacts. Do not keep the old checkout around "in case".
4. Keep **only the binary** for as long as the comparison needs it; delete
   that too when the experiment is done (or it was already committed as
   part of a recorded study).

## How to verify your work

Before declaring a fix done, all of the following must be clean:

```bash
cargo build --all-features
cargo nextest run --workspace --all-features   # the full suite (~9.7k tests) + doc tests
cargo clippy --all-features --all-targets -- -D warnings
cargo fmt --all -- --check
cargo doc --no-deps --all-features -- -D warnings
```

For anything touching solving, theories, proofs, quantifiers, or NLSAT, **also re-run the
Z3 differential parity suite** – it is the soundness canary (a real `z3 4.15.4` binary; an
honest comparator that never counts `Unknown` as a match):

```bash
./bench/z3_parity/run_parity.sh          # see bench/z3_parity/METHODOLOGY.md
```

A bug fix ships with a test that reproduces the bug – ideally the exact input that *would
have* returned the wrong answer. Add it next to the code it protects.

## Heuristic changes: every comparison ships with a matched null

This applies to any change that alters the *path* the search takes without altering the answer –
branching, phase/polarity, restarts, rephasing, clause deletion, inprocessing schedules,
stabilization, and every learned or auto-tuned variant. (Not soundness: a wrong answer is a bug
at n=1, no statistics required.)

**CDCL is chaotic.** Perturb it anywhere and the trajectory diverges, so what you measure is
always `the idea's merit + trajectory reshuffling`. The second term is not small – measured on
this repo's benchmarks, changing *only the RNG seed* moves aggregate cost **7.31×**, while the
effects being hunted are 1.1–2.5×. A real improvement and a coincidence look identical.

So a before/after number is not evidence. **Report `treatment / matched-null`, not
`treatment / baseline`.** A matched null does the same physical thing as your change, with the
same magnitude, timing, code path and number of choices – differing *only* in the semantic
content you claim is doing the work (e.g. for a learned model: permute its weights). If that
ratio is ≤ 1 you have nothing, however good the raw number looked.

Also non-negotiable here:

- **Never use wall-clock as the primary metric, or as any policy input** – it is contaminated by
  other load and makes the solver nondeterministic, breaking `run_parity.sh`, bug reproduction
  and differential fuzzing. Use tick counters, and verify the counter covers *all* the work your
  change affects.
- **≥10 seeds per cell**, baseline reported as a distribution. A deterministic policy compared
  against a stochastic baseline at one seed is a rigged comparison – and a learned policy in
  greedy mode is deterministic.
- **Replay any hindsight-selected configuration at a fresh seed.** In the study below, 80% of a
  2.56× rollout gain evaporated on reseeding.

Read [`docs/BENCHMARKING.md`](docs/BENCHMARKING.md) before running the experiment – it has the
construction recipes, the power table (a 5% effect needs ~1 800 unpaired runs), the failure
modes, and a checklist. The worked case study in `docs/studies/` shows these controls killing
two confident, entirely real, entirely meaningless measurements.

## When you get stuck

1. Read the corresponding Z3/CVC5/CaDiCaL code ([`../temp/z3`](../temp/z3),
   [`../temp/cvc5`](../temp/cvc5), [`../temp/cadical`](../temp/cadical)) – the
   procedure is almost certainly documented there.
2. Read `docs/ARCHITECTURE.md`, `docs/PITFALLS.md`, `docs/THEORY_GUIDE.md`, and the
   relevant crate's `README.md` / `TODO.md`. For measuring a heuristic change, read
   `docs/BENCHMARKING.md`; for past experiments and their verdicts, `docs/studies/`.
3. Check `CHANGELOG.md` – many "new" bugs are recurrences of fixed ones; the changelog
   names the recurring patterns by name.
4. If a fix feels too easy, it is. Go back to principle 2 and keep digging.

## Quick map

- Workspace root: `Cargo.toml` (17 member crates). `oxiz-py` is excluded from the default
  build (needs maturin).
- Crates: `oxiz-core` (AST/sorts/parser/tactics) → `oxiz-math` → `oxiz-sat` /
  `oxiz-nlsat` → `oxiz-proof` / `oxiz-theories` → `oxiz-solver` (CDCL(T)) →
  `oxiz-spacer` / `oxiz-opt` → `oxiz-cli` / `oxiz-wasm` / `oxiz-py` / `oxiz-smtcomp` /
  `oxiz-ml`. Meta-crate: `oxiz`.
- Rust edition 2024, MSRV 1.88 (pervasive let-chains). Do not lower either casually.
- Reference solvers (read-only spec): [`../temp/z3`](../temp/z3),
  [`../temp/cvc5`](../temp/cvc5), [`../temp/cadical`](../temp/cadical)
  (C++ SAT core; binary `../temp/cadical/build/cadical`).

### Benchmarks live in-repo – search them, not the disk

Benchmark corpora referenced in parity runs, regressions, and issue reports are checked
in under the repo root. Look for files here first (e.g. via `rg --files <dir> | rg <name>`
or `fd <name> <dir>`); do **not** `find /` over the whole disk:

- `bench/` – `z3_parity` (Z3 differential parity suite + `run_parity.sh`), `differential`,
  `extended_theories`, `regression`, `suite`, `profile`, `qf_ania_ce`.
- `smt-lib/` – SMT-LIB corpus tarballs (`QF_BV`, `QF_LIA`, `QF_NIA`, `QF_UF`, …) and
  `non-incremental/` extracts. Files like `459.smt2`, `1527.smt2`, `1659.smt2` come
  from these.
- `satcomp2024/`, `satcomp2025/` – SAT Competition inputs (`bench/`, `main_easy_mid/`).
- `satlib/` – SATLIB instances (`RND3SAT`).
