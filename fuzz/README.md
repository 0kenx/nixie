# OxiZ Fuzzing

This directory contains fuzz tests for the OxiZ SMT solver using [cargo-fuzz](https://rust-fuzz.github.io/book/cargo-fuzz.html) and libFuzzer.

## Installation

Install cargo-fuzz (requires nightly Rust):

```bash
cargo install cargo-fuzz
```

## Fuzz Targets

### fuzz_smtlib_parser

Fuzzes the SMT-LIB2 parser with arbitrary byte sequences (interpreted as UTF-8 text) to find crashes or panics during parsing.

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_smtlib_parser
```

### fuzz_parse_and_solve

Fuzzes the parser-to-solver end-to-end path: arbitrary bytes are interpreted as an SMT-LIB2 script and fed through `parse_script` and then the solver, applying the same soundness oracles as `fuzz_solver` (every assertion must evaluate to `true` under a `Sat` model; `check()` must be idempotent).

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_parse_and_solve
```

### fuzz_term_builder

Fuzzes term construction with random operations (boolean, integer, real, array, string, bitvector) to ensure the TermManager handles all cases correctly.

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_term_builder
```

### fuzz_solver

Fuzzes the solver with structured random SMT commands to test solver behavior under various constraint combinations. Includes soundness oracles: every `Sat` result's model is checked against the assertions that produced it, and `check()` is required to be idempotent.

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_solver
```

### fuzz_quantifiers

Fuzzes quantifier instantiation (`forall`/`exists` over 1-3 `Int` variables, with a handful of representative bodies) to find crashes or hangs in quantifier handling. Runs with a short internal timeout since quantifier reasoning can be expensive.

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_quantifiers
```

### fuzz_tactics

Fuzzes tactic application (`Simplify`, `Propagate`, `SolveEqs`, `Eliminate`, `Split`, `CtxSimplify`) over small randomly-shaped goals to ensure tactics never crash or panic on arbitrary input.

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_tactics
```

### fuzz_theory_arithmetic

Fuzzes the arithmetic theory with random `Int` constraints (add/sub/mul/div/mod/neg combined with each comparison operator) to find crashes in arithmetic constraint handling.

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_theory_arithmetic
```

### fuzz_theory_array

Fuzzes the array theory (`select`/`store`/extensionality) over a small set of `Array Int Int` variables.

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_theory_array
```

### fuzz_theory_bitvector

Fuzzes the bitvector theory (bitwise, arithmetic, and shift operations) across the four common bitwidths (8/16/32/64).

```bash
cd /path/to/oxiz/fuzz
cargo +nightly fuzz run fuzz_theory_bitvector
```

## Common Options

### Run with a time limit

```bash
cargo +nightly fuzz run fuzz_smtlib_parser -- -max_total_time=3600
```

### Run with a specific number of iterations

```bash
cargo +nightly fuzz run fuzz_smtlib_parser -- -runs=100000
```

### Run with multiple jobs

```bash
cargo +nightly fuzz run fuzz_smtlib_parser -- -jobs=4 -workers=4
```

### Use a specific seed corpus

```bash
cargo +nightly fuzz run fuzz_smtlib_parser corpus/fuzz_smtlib_parser
```

### Limit memory usage

```bash
cargo +nightly fuzz run fuzz_smtlib_parser -- -rss_limit_mb=2048
```

## Coverage Reporting

Generate coverage reports to see which code paths have been exercised:

```bash
# Run fuzzing with coverage instrumentation
cargo +nightly fuzz coverage fuzz_smtlib_parser

# Generate HTML report (requires llvm-cov)
cargo +nightly fuzz coverage fuzz_smtlib_parser --lcov > coverage.lcov

# Or use grcov for HTML reports
grcov coverage.lcov -t html -o coverage_report/
```

## Reproducing Crashes

When a crash is found, a file will be saved in `artifacts/fuzz_TARGET/`:

```bash
# Reproduce the crash
cargo +nightly fuzz run fuzz_smtlib_parser artifacts/fuzz_smtlib_parser/crash-XXXXX

# Minimize the crash input
cargo +nightly fuzz tmin fuzz_smtlib_parser artifacts/fuzz_smtlib_parser/crash-XXXXX
```

## Directory Structure

```
fuzz/
  Cargo.toml           # Fuzz package configuration
  README.md            # This file
  fuzz_targets/        # Fuzz target source files (9 targets, see above)
  corpus/              # Seed corpus, one subdirectory per target (see below)
  artifacts/           # Crash artifacts, created on demand
```

## Seed Corpus

Every target under `fuzz_targets/` has a starting corpus under
`corpus/<target_name>/` so fuzzing does not have to rediscover basic
structure from a cold start:

- **`fuzz_smtlib_parser`** and **`fuzz_parse_and_solve`** consume raw
  SMT-LIB2 text, so their seeds are small `.smt2` files covering a spread of
  the grammar (arithmetic, bitvectors/arrays, quantifiers/`let`/`:named`,
  datatypes/strings, reals/floating-point, `push`/`pop`/`reset`) plus one
  deliberately near-valid/malformed script to exercise the parser's error
  paths.
- The other six targets (`fuzz_quantifiers`, `fuzz_solver`, `fuzz_tactics`,
  `fuzz_term_builder`, `fuzz_theory_arithmetic`, `fuzz_theory_array`,
  `fuzz_theory_bitvector`) consume raw bytes through `arbitrary`'s
  `Unstructured` decoder to build structured commands directly (there is no
  SMT-LIB2 text involved), so their seeds are a handful of small binary
  files with varied, deterministic byte patterns (all-zero, all-`0xFF`, an
  incrementing byte sequence, and a fixed pseudo-random pattern) at a length
  long enough to drive several generated commands per run. Precisely which
  command each byte decodes to is an implementation detail of the
  `arbitrary` crate's derive macro, so these seeds are deliberately generic
  rather than hand-encoded to hit one specific command sequence.

> **Note:** the repository root `.gitignore` excludes `fuzz/corpus/`
> entirely, so this seed corpus lives only in a local checkout unless that
> rule is relaxed (e.g. to allow committing curated `seed*` files while
> still ignoring corpus growth from actual fuzzing runs). Regenerate it
> locally if it is ever missing; none of the fuzz targets require it to run
> (an empty corpus just means libFuzzer starts from nothing, as before).

## Tips

1. **Run fuzzing overnight**: Fuzzing benefits from long run times. Consider running overnight or for several hours.

2. **Monitor with AFL-style stats**: Use `-print_final_stats=1` to see coverage statistics.

3. **Address sanitizers**: cargo-fuzz automatically enables AddressSanitizer. For other sanitizers:
   ```bash
   RUSTFLAGS="-Zsanitizer=memory" cargo +nightly fuzz run fuzz_smtlib_parser
   ```

4. **Debug crashes**: To get better stack traces:
   ```bash
   RUST_BACKTRACE=1 cargo +nightly fuzz run fuzz_smtlib_parser artifacts/crash-XXXXX
   ```
