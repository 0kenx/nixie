# Z3 Parity Test Methodology

## Overview

This test suite validates OxiZ's correctness by comparing its results against Z3, the de facto standard SMT solver. The goal is to ensure OxiZ produces the same satisfiability decisions as Z3 on a representative set of benchmarks.

## Test Structure

### Benchmark Categories

- **QF_LIA** (16 benchmarks): Quantifier-Free Linear Integer Arithmetic
- **QF_LRA** (16 benchmarks): Quantifier-Free Linear Real Arithmetic
- **QF_BV** (15 benchmarks): Quantifier-Free Bit-Vectors
- **QF_S** (10 benchmarks): Quantifier-Free Strings
- **QF_FP** (10 benchmarks): Quantifier-Free Floating Point
- **QF_DT** (10 benchmarks): Quantifier-Free Datatypes
- **QF_A** (10 benchmarks): Quantifier-Free Arrays

**Total:** 87 benchmarks

### Benchmark Selection Criteria

Each benchmark was selected to:

1. **Cover diverse constraint patterns** - Not just simple satisfiability checks
2. **Mix of SAT/UNSAT/UNKNOWN** - Approximately 40% SAT, 40% UNSAT, 20% UNKNOWN
3. **Varied complexity** - Easy, medium, and hard instances
4. **Execute within timeout** - Both solvers should complete within 60 seconds
5. **Test edge cases** - Boundary conditions, special values, tricky patterns

### Benchmark Sources

Benchmarks are derived from:

- SMT-LIB benchmark repository
- Z3 test suite
- Manually crafted instances targeting specific features
- Real-world verification problems (simplified)

## Running Tests

### Prerequisites

1. **Install Z3**:
   ```bash
   # macOS
   brew install z3

   # Linux
   sudo apt-get install z3

   # Or download from: https://github.com/Z3Prover/z3/releases
   ```

2. **Build OxiZ**:
   ```bash
   cd "$(git rev-parse --show-toplevel)"
   cargo build --release
   ```

### Execute Parity Tests

```bash
cd bench/z3_parity
cargo run --release
```

This will:
1. Discover all `.smt2` files in `benchmarks/`
2. Run each benchmark on both Z3 and OxiZ (in parallel)
3. Compare results
4. Generate a summary report
5. Save detailed results to `results.json`

### Interpreting Results

#### Match Status

- **Correct**: Both solvers agree (SAT/SAT, UNSAT/UNSAT, UNKNOWN/UNKNOWN)
- **Wrong**: Disagreement on SAT/UNSAT (critical bug!)
- **Timeout**: One or both solvers exceeded 60s timeout
- **Error**: Parse error or execution failure

**Note:** If one solver returns UNKNOWN and the other returns SAT or UNSAT, this is considered **Correct** (UNKNOWN is a valid response).

#### Pass Criteria

For **v0.1.3 release**, the following accuracy is required:

- **QF_LIA**: 100% correct (0 wrong)
- **QF_LRA**: 100% correct (0 wrong)
- **QF_BV**: 100% correct (0 wrong)
- **QF_S**: ≥ 80% correct (exploratory)
- **QF_FP**: ≥ 80% correct (exploratory)
- **QF_DT**: ≥ 70% correct (work in progress)
- **QF_A**: ≥ 90% correct (mature theory)

**Overall**: ≥ 95% correct across all logics

## Limitations

### What This Tests

✅ **Correctness of satisfiability decisions**
✅ **Logic-specific feature coverage**
✅ **Regression prevention**
✅ **Relative performance (execution time)**

### What This Does NOT Test

❌ **Model quality** - We don't validate model values, only SAT/UNSAT
❌ **Proof generation** - OxiZ doesn't generate proofs yet
❌ **Incremental solving** - Benchmarks are one-shot
❌ **Quantifiers** - Limited to quantifier-free logics
❌ **Performance limits** - All benchmarks finish in < 60s

## Differential Testing

In addition to the curated `.smt2` corpus above, this crate ships a
**generator-based differential-testing harness** that produces small,
random, well-typed SMT-LIB2 scripts and checks that OxiZ's sat/unsat
verdict agrees with Z3's. Unlike the curated corpus, this harness is not
limited to a fixed, hand-written set of benchmarks: every run explores a
fresh (but fully reproducible) slice of each logic's formula space.

### Components

- **Generator** (`src/generator.rs`): a dependency-free, seeded PRNG
  (SplitMix64) drives recursive term/formula builders for `QF_LIA`,
  `QF_LRA`, `QF_BV`, and `QF_UF`. `generate_script(logic, seed)` is a pure
  function of its two arguments — no wall-clock time or OS entropy is ever
  consulted, so any failing case is trivially reproducible from its
  `(logic, seed)` pair alone. Arithmetic terms are kept linear (constant
  \* subterm only, never variable \* variable) so `QF_LIA`/`QF_LRA` scripts
  never drift into `QF_NIA`/`QF_NRA`.
- **Runner** (`src/difftest.rs`): `run_case`/`run_cases` generate a script,
  write it to a scratch file, execute it through both `oxiz_runner::run_oxiz`
  (library call, in-process with a timeout) and `z3_runner::run_z3` (the
  `z3` binary discovered on `PATH`), and reuse `comparator::compare_results`
  — the same comparison logic the curated benchmark suite uses — to
  classify the outcome. `Unknown` on either side is `Inconclusive` (skipped,
  no parity claim), a definite `Sat`/`Unsat` disagreement is `Wrong` (a real
  bug), and `summarize()` buckets a batch of outcomes accordingly.
- **Repro capture**: any `Wrong` outcome has its exact reproducing script
  written under `std::env::temp_dir()/oxiz_difftest_repro/<logic>_<seed>_<ts>.smt2`
  via `difftest::save_repro`, and the path is included in the panic
  message.

### Running it

Two `cargo test` entry points under `tests/`:

1. **Always-on smoke test** (`tests/difftest_smoke.rs`) — a fixed seed,
   ~25 generated cases per logic (100 total). Runs as part of a plain
   `cargo test` in this crate with **no extra flags**. Like the existing
   `z3_runner` tests, it self-skips (prints a message, does not fail) when
   no `z3` binary is found on `PATH`, so CI without Z3 is never affected.
   Whenever Z3 *is* present, this is a real regression check: an OxiZ
   change that flips a sat/unsat verdict on any of the 100 fixed cases
   fails the test.
2. **Full sweep, opt-in** (`tests/difftest_full.rs`) — gated behind an
   environment variable so it never runs by accident:

   ```bash
   OXIZ_DIFFTEST=1 cargo test --test difftest_full -- --nocapture
   ```

   Tunable via:
   - `OXIZ_DIFFTEST_CASES` (default `200`) — cases generated per logic.
   - `OXIZ_DIFFTEST_SEED` (default `42`) — base PRNG seed (each logic
     derives its own seed from this so the four sweeps don't replay
     correlated streams).

   Also self-skips when no `z3` binary is present, or when
   `OXIZ_DIFFTEST` is unset/not `1`.

### Scope and honesty notes

- This harness targets **sat/unsat verdict parity only** (same contract as
  the curated benchmark suite above) — it does not validate model values or
  proofs.
- A `Wrong` verdict is the only thing that fails a differential test;
  `Unknown`/`Timeout`/solver `Error` on either side is reported but treated
  as inconclusive, never as a pass *or* a hard failure, so the harness can
  never be gamed by a solver that just gives up.
- There is intentionally no new CI workflow wired to this harness (Z3 is an
  external binary dependency this project does not control, and the
  project's CI-workflow policy restricts which `.github/workflows/*.yml`
  files may be added). Run it manually, or in any environment that happens
  to already have `z3` on `PATH`.

## Adding New Benchmarks

To add a new benchmark:

1. Create a `.smt2` file in the appropriate logic directory
2. Include a comment at the top documenting:
   - What feature/pattern it tests
   - Expected result (sat/unsat/unknown)
   - Source (if adapted from elsewhere)

Example:
```smt2
; Test: Branch and bound with negative coefficients
; Expected: unsat
; Source: Adapted from SMT-LIB QF_LIA/20230215-Barrett

(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

(assert (= (+ (* -2 x) (* 3 y)) 7))
(assert (>= x 0))
(assert (<= x 5))
(assert (>= y 0))
(assert (<= y 2))

(check-sat)
```

3. Run the parity suite to validate
4. Commit both the benchmark and updated `results.json`

## Troubleshooting

### "Z3 not found"

Ensure Z3 is installed and in your PATH:
```bash
which z3  # Should print /usr/local/bin/z3 or similar
z3 --version  # Should print version info
```

### All OxiZ tests showing "Error"

Check that OxiZ builds successfully:
```bash
cd ../../oxiz
cargo test
```

### Timeout issues

If benchmarks are timing out, increase the timeout in `z3_runner.rs` and `oxiz_runner.rs`:
```rust
const Z3_TIMEOUT_SECS: u64 = 120;  // Increase from 60
```

## Maintenance

This test suite should be run:

- **Before every release** - Blocking requirement
- **Weekly (CI)** - Automated regression testing
- **After major changes** - Especially to core theories
- **When adding new features** - Ensure no regressions

## Future Enhancements

- [ ] Model validation (check SAT models satisfy constraints)
- [ ] UNSAT core comparison
- [ ] Incremental solving tests (push/pop)
- [ ] Performance benchmarking (not just correctness)
- [ ] Fuzz-generated benchmarks
- [ ] Quantified formula tests (once implemented)
