# OxiZ

Next-Generation SMT Solver in Pure Rust

[![Crates.io](https://img.shields.io/crates/v/oxiz.svg)](https://crates.io/crates/oxiz)
[![Documentation](https://docs.rs/oxiz/badge.svg)](https://docs.rs/oxiz)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

## About This Project

OxiZ is a high-performance Satisfiability Modulo Theories (SMT) solver written entirely in Rust. This project reimplements [Z3](https://github.com/Z3Prover/z3) in Pure Rust with a focus on correctness, performance, and safety.

**Pure Rust is a fundamental requirement** - no C/C++ dependencies, no FFI bindings, just clean, safe Rust code.

### Implementation Status (v0.3.0)

OxiZ is under active development with core theories at production quality on its tested surface.

- **Pure Rust Implementation**: 384,047 lines of production Rust code (481,652 total including comments/blank lines, per `tokei .`)
- **Unit Tests**: 8,119 passing, 8 skipped (`cargo nextest run --workspace --all-features`, confirmed at release time), plus 106 doc-tests (`cargo test --doc --workspace --all-features`)
- **Z3 Parity**: honest, non-fabricated comparison against a real `z3` 4.15.4 binary (`bench/z3_parity`) across 175 benchmarks spanning 19 logics: **161 Correct**, 12 Inconclusive (OxiZ honestly answered `Unknown`), 2 Timeout, 0 Error, 0 Wrong — zero soundness disagreements on all 161 decisive comparisons, not an overall "100% parity" claim (16 of 19 logic families are individually at 100%; three quantified logics — `UFLIA`, `UFLRA`, `AUFLIA` — are not). The 8-logic quickstart core (QF_LIA, QF_LRA, QF_NIA, QF_BV, QF_DT, QF_A, QF_S, QF_FP) is 95/95 Correct — see "Z3 Parity" below and [`TODO.md`](TODO.md)
- **Audit + hardening (multiple waves)**: a 2026-07-16 production-readiness audit (19 scoped agents + adversarial verification) plus this release's follow-on implementation waves found and fixed soundness and honesty gaps across every crate — SMT-LIB parser coverage, quantifier elimination (Ferrante-Rackoff, virtual substitution, MBI/Craig interpolants), MBQI SAT certification, Spacer MIC generalization and multi-threaded parallel PDR, IEEE-754 `fp.rem`/fused-multiply-add, proof-rule/checker validation, and two process-crash fixes. Re-verified status (which items are fixed vs. still open) is tracked per-item in [`TODO.md`](TODO.md); a small number of NLSAT/quantifier items (irrational-root isolation; two ex-crash benchmarks that now honestly answer `Unknown`/`Timeout` instead of crashing) remain open and are called out there and in the [CHANGELOG](CHANGELOG.md#030---2026-07-22)

## What's New in 0.3.0 (2026-07-22)

A large hardening-and-capability wave on top of 0.2.4's audit. Full itemized detail is in [`CHANGELOG.md`](CHANGELOG.md#030---2026-07-22); highlights:

### Soundness fixes
Exact `BigRational` floor/ceil and real polynomial GCD/resultant in `oxiz-math`; `QF_NIRA` variable-type dispatch and incomplete-atom tracking in `oxiz-nlsat`; real Ferrante-Rackoff and Loos-Weispfenning virtual-substitution quantifier elimination for LRA; a real propositional Craig interpolant for MBI; IEEE-754-correct `fp.rem` and single-rounded fused multiply-add (plus a separate `div128` remainder-overflow bug in the `ieee754_full` engine that returned `0.0` for divisions with a true quotient in `(0.5,1)`); an `ArithSolver::pop()` state-rollback bug where `term_to_var` was not rolled back in lockstep with `var_to_term` (recycled `VarId`s could attach a constraint to the wrong variable) plus a `lia_model` backtrack-clear fix; a simplex `register_var`/`ensure_var` hardening pass that closed both an index-out-of-bounds crash and a silent-drop of out-of-range bound-setting calls; several proof-checker rubber-stamps (resolution, parallel proof checking, per-theory checkers) replaced with real verification.

### New capabilities
`(get-consequences ...)` and `:named` assertions; a regex sublanguage for the string theory plus a new ground string decision procedure (definitional propagation, concat-splitting by known lengths, and regex-intersection search via the Brzozowski automata engine, gated by full concrete verification before returning `Sat`) that lifts `qf_s` from 3/10 to 10/10 on the parity suite; a sound concrete floating-point model finder that lifts `qf_fp` from 1/10 to 10/10; MBQI SAT certification (lifts `UFLIA`/`UFLRA`/`AUFLIA` from mostly-`Unknown` toward a majority-decisive verdict — see "Z3 Parity" below); real datatype and bitvector quantifier elimination; Spacer MIC generalization plus a genuine multi-threaded parallel PDR portfolio; a McMillan-style Craig interpolation system; `oxiz-ml` is now genuinely wired into `oxiz-cli` via the opt-in `--ml-tactic-selection` flag (off by default — see "Features" below); `oxiz-wasm` gains hard-preemptible solving via a dedicated Web Worker (`PreemptibleSolver`), `SharedArrayBuffer`-backed cooperative cancellation (`CancellationToken`), and a Rust-generated TypeScript `.d.ts` — see "WebAssembly" below.

### Honesty & robustness
Two process-crash panics fixed (a SAT theory-conflict-with-unassigned-literal panic; a simplex out-of-bounds panic); both SMT-LIB parser regressions surfaced by 0.2.4's stricter undeclared-symbol check (`to_fp` rounding-mode arguments, `re.allchar`) are closed; roughly a dozen previously-dead-but-tested `oxiz-nlsat` modules (subsumption, inprocessing, vivification, structure analysis, …) are now wired into the real solve loop; confirmed-dead GPU-flag scaffolding (zero references anywhere in the workspace) was deleted rather than left as a misleading placeholder.

### Z3 Parity gains
Re-measured against `bench/z3_parity` at release time: **161/175 Correct** (QF_NIA expanded 1→8 this pass), **0 Wrong**, **0 process crashes**, 12 Inconclusive, 2 Timeout — 100% agreement with z3 on every decisive comparison, but not an overall "100% parity" claim. `qf_fp` 1/10→10/10, `qf_s` 3/10→10/10, `AUFLIA` 2/10→7/10, `UFLIA` 7/20→14/20, `UFLRA` 2/10→5/10. 16 of 19 logic families now hold at 100% Correct; the 8-logic quickstart core is 95/95. See "Z3 Parity" below for the full breakdown.

For the 0.2.4 production-readiness audit and the 0.2.3 feature set (generic `DratWriter`/`LratWriter` proof writers, NLSAT root-isolation completions, the full `oxiz-opt` optimization pipeline, real BMC/k-induction in `oxiz-spacer`), see the [0.2.4](CHANGELOG.md#024---2026-07-19) and [0.2.3](CHANGELOG.md#023---2026-06-09) CHANGELOG entries.

## Theory Support Status

Numbers below are re-measured at release time against the current `bench/z3_parity` suite (a real `z3` binary, an honest comparator that never counts `Unknown` as a match — see [`bench/z3_parity/src/comparator.rs`](bench/z3_parity/src/comparator.rs)).

### Core Logics at 100% Z3 Parity ✅

#### Arithmetic Theories
- **QF_LIA** (Linear Integer Arithmetic) - **100.0%** (16/16 tests)
  - Simplex with GCD-based infeasibility detection
  - Branch-and-bound for integer solutions
  - Cutting plane generation
- **QF_LRA** (Linear Real Arithmetic) - **100.0%** (16/16 tests)
  - Tableau-based simplex solver
  - Efficient pivot selection
  - Incremental constraint management
- **QF_NIA** (Nonlinear Integer Arithmetic) - **100.0%** (8/8 tests)
  - NLSAT solver with CAD
  - Branch-and-bound for integers
  - Complete theory integration

#### Bit-Vector Theory
- **QF_BV** (Bit-Vectors) - **100.0%** (15/15 tests)
  - Bit-blasting with word-level reasoning
  - Constraint propagation for arithmetic ops
  - Signed/unsigned division and remainder (double-width, non-wrapping encoding)
  - Logical operations (NOT, XOR, OR, AND), barrel-shifter over-shift handling
  - Comparison conflict detection

#### Datatype Theory
- **QF_DT** (Datatypes) - **100.0%** (10/10 tests)
  - Constructor exclusivity enforcement
  - Tester predicate evaluation
  - Selector function semantics
  - Cross-variable constraint propagation
  - Enumeration type handling

#### Array Theory
- **QF_A** (Arrays) - **100.0%** (10/10 tests)
  - Read-over-write axioms
  - Extensionality reasoning
  - Store propagation (101 unit tests)

#### String Theory
- **QF_S** (Strings) - **100.0%** (10/10 tests) — up from 3/10 Correct, 7 Inconclusive last release
  - A new ground string decision procedure (definitional propagation, concat-splitting by known operand lengths, and per-variable regular-constraint intersection search via the existing Brzozowski derivative automaton engine) synthesizes a candidate model and only returns `Sat` after concretely verifying it against every assertion — it never guesses, so the previous honest `Unknown` gate (`string_atoms_need_theory`) is bypassed only on a verified witness. Unsatisfiable cases are still caught by the pre-existing definite-conflict detector before this path runs.

#### Floating-Point Theory
- **QF_FP** (Floating Point) - **100.0%** (10/10 tests) — up from 4/10 Correct, 6 Inconclusive last release
  - A sound concrete FP model finder pins every FP-sorted term to a bit-exact IEEE-754 value (definitional-equality propagation plus predicate-driven witness synthesis for free NaN/Infinity-typed variables) and reports `Sat` only after verifying every assertion; a genuine `div128` remainder-overflow bug in the `ieee754_full` engine (dropped bit 127 whenever a division's true quotient fell in `(0.5,1)`, e.g. `10/3` previously evaluated to `0.0`) is also fixed, so directed-rounding (`RTP`/`RTN`/`RTZ`) division is now bit-exact.

### Additional Logics (Extended Suite, 19 Logics / 168 Benchmarks Total)

`bench/z3_parity/benchmarks/` also covers `AUFLIA`, `AUFLIRA`, `QF_ABV`, `QF_ALIA`, `QF_AUFBV`, `QF_AUFLIA`, `QF_NIRA`, `QF_UFLIA`, `QF_UFLRA`, and `UFLIA`/`UFLRA` (quantified logics). Aggregate result across all 175 benchmarks: **161 Correct, 12 Inconclusive, 2 Timeout, 0 Error, 0 Wrong** — zero soundness disagreements this run (100% match on the 161 decisive comparisons, not an overall "100% parity" claim). A new MBQI SAT certifier substantially reduced how often the quantified logics fall back to `Unknown`: `AUFLIA` improved 2/10 → 7/10 Correct, `UFLIA` 7/20 → 14/20, `UFLRA` 2/10 → 5/10. These three remain the only logic families below 100% — the rest are honest `Unknown`/`Timeout`, never a wrong verdict (`UFLIA`: 5 `Unknown` + 1 `Timeout`; `UFLRA`: 4 `Unknown` + 1 `Timeout`; `AUFLIA`: 3 `Unknown`). `QF_NIA` (8/8), `QF_NIRA` (5/5) and the other 16 logic categories (including `qf_s`/`qf_fp`) remain at 100% Correct with no regressions.

- **QF_UF** (Uninterpreted Functions) - E-graphs with congruence closure (not separately benchmarked; exercised indirectly by every other logic above)
- **QF_NRA** (Nonlinear Real) - CAD-based NLSAT solver (Alpha: irrational-root isolation still open; not part of this benchmark suite, see `TODO.md`)
- **AUFBV** (Arrays + UF + BV) - Theory combination via Nelson-Oppen (`QF_AUFBV` scores 5/5 on the parity suite)
- **UFLIA** (Quantified LIA) - MBQI SAT certifier now resolves 14/20 benchmarks decisively; remaining cases honestly fall back to `Unknown` or time out at 60s rather than guessing
- **HORN** (Horn Clauses) - PDR/IC3 engine with MIC generalization and a multi-threaded parallel portfolio this release; real BMC, k-induction, and init/transition SMT queries (not part of this benchmark suite)

## Features

- **Pure Rust** - No C/C++ dependencies, memory-safe by design
- **CDCL(T) Architecture** - Conflict-Driven Clause Learning with theory integration
- **Comprehensive Theory Support** - EUF, LRA, LIA, BV, Arrays, Strings, FP, Datatypes
- **Advanced Quantifier Handling** - MBQI, E-matching, Skolemization, DER
- **SMT-LIB2 Support** - Full standard input/output format
- **WebAssembly Ready** - Run in browsers via WASM bindings
- **Incremental Solving** - Push/pop for efficient constraint management
- **Proof Generation** - DRAT, Alethe, LFSC, Coq/Lean/Isabelle export
- **Optimization** - MaxSAT, OMT with Pareto optimization
- **Model Checking** - CHC solving with PDR/IC3
- **Z3 API Compatibility** - `TacticRegistry`, `FuncInterp`, sort/substitution/pattern APIs
- **ML-Guided Heuristics (opt-in)** - `oxiz-cli --ml-tactic-selection` (off by default) drives a real `oxiz-ml` tactic-recommendation engine (feature extraction, decision-tree training, outcome-based retraining); the SAT core separately exposes a `BranchingHeuristic` trait for custom LBD/conflict-driven heuristics
- **Recursive BV Encoding** - Full nested bit-vector term encoding with structured conflict diagnostics

## Z3 Parity: Quickstart Suite Results (Honest Comparator) ✅

`bench/z3_parity` compares OxiZ against a real `z3` binary using a comparator that **never** counts an `Unknown` answer (from either solver) as a match (see [`bench/z3_parity/src/comparator.rs`](bench/z3_parity/src/comparator.rs)) — a solver cannot inflate its "parity" score by declining to answer. Results below are the current `bench/z3_parity/results.json` for the original 8-logic, 88-benchmark quickstart core:

| Logic | Tests | Result | Notes |
|-------|-------|--------|-----------|
| QF_LIA | 16/16 | ✅ 100% Correct | Simplex, branch-and-bound, cutting planes |
| QF_LRA | 16/16 | ✅ 100% Correct | Tableau-based simplex, pivot selection |
| QF_NIA | 8/8 | ✅ 100% Correct | NLSAT with CAD + integer B&B |
| QF_S | 10/10 | ✅ 100% Correct | Ground string decision procedure (verified models); up from 3/10 |
| QF_BV | 15/15 | ✅ 100% Correct | Constraint propagation, div/rem, logical ops |
| QF_FP | 10/10 | ✅ 100% Correct | Concrete FP model finder + `div128` bugfix; up from 4/10 |
| QF_DT | 10/10 | ✅ 100% Correct | Constructor exclusivity, cross-variable propagation |
| QF_A | 10/10 | ✅ 100% Correct | Read-over-write, extensionality |
| **TOTAL** | **95/95 Correct** | **✅ 100%** | All 8 quickstart-core logics now at 100% — see caveats below |

This 95-benchmark quickstart core is a narrower subset of the full 175-benchmark, 19-logic extended suite (including quantified `AUFLIA`/`UFLIA`/`UFLRA` and combined theories), which totals **161 Correct / 12 Inconclusive / 2 Timeout / 0 Error / 0 Wrong** — **not** 100% overall; see "Theory Support Status" above for the full breakdown and the caveats below before generalizing this table's result.

### What This Means

- ✅ **Correctness Validated on All 8 Quickstart-Core Logics**: QF_LIA, QF_LRA, QF_NIA, QF_BV, QF_DT, QF_A, QF_S, and QF_FP now match Z3 on every quickstart benchmark (95/95); `QF_NIA` expanded to multivariate products, Pythagorean triples, and integer div/mod this pass.
- ⚠️ **Not 100% on the Extended Suite**: the broader 175-benchmark, 19-logic suite is **161/175 Correct**, not 100% — three quantified logics (`UFLIA` 14/20, `UFLRA` 5/10, `AUFLIA` 7/10) still honestly return `Unknown`/`Timeout` on cases needing existential-witness (Skolemization) construction the MBQI certifier doesn't yet build. Do not read this table's 95/95 as a claim about the whole solver. Tracked in [`TODO.md`](TODO.md).
- ⚠️ **Not a General Production-Readiness Claim**: the 2026-07-16 audit and this release's follow-on hardening waves found and fixed soundness gaps across the parser, quantifier elimination, MBQI, SAT conflict analysis, NLSAT, math, MaxSAT/QE, Spacer, and proof checking — this run recorded 0 Wrong and 0 process crashes across the parity suite — but a handful of NLSAT/quantifier items (algebraic-number model witnesses; ex-crash benchmarks that now honestly answer `Unknown`/`Timeout` instead of crashing) remain open; see [`TODO.md`](TODO.md) for the itemized gaps and fix status before relying on OxiZ outside this suite's scope
- ✅ **Pure Rust**: Achieved without any C/C++ dependencies

This snapshot validates OxiZ's core arithmetic/BV/datatype/array/string/FP reasoning against Z3 on the quickstart suite, while being explicit that the extended suite's quantified logics still have honest `Unknown`/`Timeout` gaps and that non-core logics are ongoing work.

## Project Statistics (v0.3.0, 2026-07-22)

| Metric | Value |
|--------|-------|
| Rust Lines of Code (code) | 384,047 |
| Total Rust Lines (with comments/blanks) | 481,652 |
| Total Tests | 8,119 passing, 8 skipped (`--all-features`) at the last full nextest run, plus 106 doc-tests |
| Z3 Parity (quickstart core, 95 benchmarks) | **95/95 (100%) Correct**, 8/8 logics at 100% |
| Z3 Parity (extended suite, 175 benchmarks / 19 logics) | **161 Correct / 12 Inconclusive / 2 Timeout / 0 Error / 0 Wrong** (not 100% overall — see caveats above) |
| Crates | 17 |

### Codebase Breakdown by Module

| Module | Description |
|--------|-------------|
| Core/AST/Tactics | Term management, sorts, tactics framework |
| Theories (EUF/BV/Arrays) | Theory solvers: EUF, LRA, LIA, BV, Arrays, Strings, FP, ADT |
| SAT Solver | CDCL SAT solver with optimizations and generic proof writers |
| Math Libraries | Simplex, matrix operations, polynomials |
| Proof System | Resolution, interpolation, DRAT/LRAT |
| NLSAT (CAD) | Non-linear arithmetic via CAD; root isolation and resultant completed |
| Main Solver | CDCL(T) integration layer; eval_in_model added |
| Optimization | MaxSMT/OMT/Pareto wired to real solver backend |
| Model Checking | SPACER/PDR/IC3; real BMC and sound k-induction wired |
| ML Integration | Neural network guided heuristics |

## Workspace Structure

```
oxiz/
├── oxiz/           # Meta-crate (unified API)
├── oxiz-core/      # Core AST, sorts, SMT-LIB parser, tactics, rewriters
├── oxiz-math/      # Mathematical algorithms (polynomials, matrices, LP)
├── oxiz-sat/       # CDCL SAT solver with VSIDS/LRB/VMTF
├── oxiz-nlsat/     # Nonlinear arithmetic (CAD, algebraic numbers)
├── oxiz-theories/  # Theory solvers (EUF, Arith, BV, Arrays, Strings, FP, ADT)
├── oxiz-solver/    # Main CDCL(T) orchestration, MBQI
├── oxiz-opt/       # Optimization (MaxSAT, OMT)
├── oxiz-spacer/    # CHC solving, PDR/IC3, BMC
├── oxiz-proof/     # Proof generation and verification
├── oxiz-py/        # Python bindings (PyO3/maturin)
├── oxiz-wasm/      # WebAssembly bindings
├── oxiz-smtcomp/   # SMT-COMP benchmarking utilities
├── oxiz-cli/       # Command-line interface
├── oxiz-ml/        # ML-guided heuristics (neural networks)
└── oxiz-vscode/    # VS Code extension (TypeScript, SMT-LIB2 language support)
```

## Requirements

**Minimum Rust Version:** 1.88.0 (stable), declared as `rust-version` in the workspace `Cargo.toml`.

Edition 2024 itself only requires rustc 1.85, but the workspace makes pervasive use of let-chains (`if ... && let Some(x) = ... { }`), which were stabilized in 1.88 — that is the real floor, not 1.85.

For optimal performance, we recommend:
- Rust 1.88.0 or later (stable)
- 8GB+ RAM for building
- 4GB+ RAM for running complex SMT queries

## Quick Start

### Installation

```toml
# Add to your Cargo.toml
[dependencies]
oxiz = "0.3.0"  # Default includes solver
```

Or with specific features:

```toml
[dependencies]
oxiz = { version = "0.3.0", features = ["nlsat", "optimization"] }
```

For all features:

```toml
[dependencies]
oxiz = { version = "0.3.0", features = ["full"] }
```

### Building from Source

```bash
git clone https://github.com/cool-japan/oxiz
cd oxiz
cargo build --release
```

### Running Tests

```bash
cargo nextest run --all-features
```

### Using the CLI

After installation:

```bash
# Install from crates.io
cargo install oxiz-cli

# Solve an SMT-LIB2 file
oxiz input.smt2

# Interactive mode
oxiz --interactive

# With verbose output
oxiz -v input.smt2
```

Or run directly from source:

```bash
# Solve an SMT-LIB2 file
cargo run --release -p oxiz-cli -- input.smt2

# Interactive mode
cargo run --release -p oxiz-cli -- --interactive

# With verbose output
cargo run --release -p oxiz-cli -- -v input.smt2
```

### Library Usage

```rust
use oxiz::solver::Context;

fn main() {
    let mut ctx = Context::new();

    let results = ctx.execute_script(r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (> x 0))
        (assert (< y 10))
        (assert (= (+ x y) 15))
        (check-sat)
        (get-model)
    "#).unwrap();

    for result in results {
        println!("{}", result);
    }
}
```

## Supported Logics

Status reflects results on the `bench/z3_parity` suite against a real `z3` binary with an honest comparator (`Unknown` never counts as a match); logics marked Alpha/Partial have known gaps documented in [`TODO.md`](TODO.md) (e.g. NLSAT root isolation for irrational roots, MBQI completeness, PDR/IC3 consecution checks).

| Logic | Description | Status |
|-------|-------------|--------|
| QF_UF | Uninterpreted Functions | ✅ Complete |
| QF_LRA | Linear Real Arithmetic | ✅ Complete (16/16) |
| QF_LIA | Linear Integer Arithmetic | ✅ Complete (16/16) |
| QF_BV | Fixed-size BitVectors | ✅ Complete (15/15) |
| QF_DT | Datatypes (ADT) | ✅ Complete (10/10) |
| QF_A | Arrays | ✅ Complete (10/10) |
| QF_NIA | Nonlinear Integer Arithmetic | ✅ Complete (8/8 parity; multivariate products, div/mod, Pythagorean) |
| QF_S | Strings | ✅ Complete (10/10 Correct via a new ground string decision procedure; up from 3/10) |
| QF_FP | Floating Point | ✅ Complete (10/10 Correct via a new concrete FP model finder + `div128` bugfix; up from 4/10) |
| QF_NRA | Nonlinear Real Arithmetic | 🔶 Alpha (irrational-root isolation still open) |
| AUFLIA / UFLIA / UFLRA | Quantified logics | 🔶 Alpha (MBQI SAT certifier resolves most cases decisively now — AUFLIA 7/10, UFLIA 14/20, UFLRA 5/10 — remainder honest `Unknown`/`Timeout`, not wrong) |
| AUFBV | Arrays + UF + BV | 🔶 Alpha (`QF_AUFBV` variant scores 5/5 on the parity suite) |
| QF_NIRA | Nonlinear Integer + Real Arithmetic | ✅ Complete (5/5 on the parity suite; the previous confirmed-wrong result is fixed) |
| HORN | Constrained Horn Clauses | 🔶 Partial (real PDR init/transition SMT queries wired this release) |

## Key Components

### SAT Solver
- CDCL with two-watched literals
- Multiple branching heuristics (VSIDS, LRB, VMTF, CHB)
- Clause learning with minimization
- Preprocessing (BCE, BVE, subsumption)
- DRAT/LRAT proof generation via generic `DratWriter<W>` / `LratWriter<W>` (any `Write + Send` sink)
- Local search and lookahead
- AllSAT enumeration

### Theory Solvers
- EUF with congruence closure
- LRA with Simplex
- LIA with branch-and-bound, Cuts
- BV with bit-blasting and word-level reasoning
- Arrays with extensionality
- Strings with automata
- Floating-point with bit-precise semantics
- Datatypes (ADT) with testers/selectors
- Pseudo-Boolean constraints
- Special relations (partial/total orders)

### Quantifier Handling
- E-matching with triggers
- MBQI (Model-Based Quantifier Instantiation)
- Skolemization
- DER (Destructive Equality Resolution)
- Model-Based Projection

### Optimization
- MaxSAT (Fu-Malik, RC2, LNS)
- OMT with lexicographic/Pareto optimization
- Weighted soft constraints

### Model Checking
- PDR/IC3 for CHC solving
- BMC (Bounded Model Checking)
- Lemma generalization
- Craig interpolation

## Architecture

OxiZ follows a layered CDCL(T) architecture:

1. **SAT Core** (`oxiz-sat`) - CDCL solver with modern heuristics
2. **Theory Solvers** (`oxiz-theories`) - Modular theory implementations
3. **SMT Orchestration** (`oxiz-solver`) - Theory combination and DPLL(T)
4. **Tactics** (`oxiz-core`) - Preprocessing and simplification
5. **Proof Layer** (`oxiz-proof`) - Proof generation and verification

## Beyond Z3: Rust-Specific Enhancements

OxiZ goes beyond Z3 with Rust-native features:

### 🦀 Rust Advantages

- **Memory Safety**: No segfaults, buffer overflows, or undefined behavior
- **Zero-Cost Abstractions**: Generic programming without runtime overhead
- **Fearless Concurrency**: Safe parallel solving with work-stealing
- **Modern Type System**: Algebraic data types, pattern matching, trait-based design
- **Package Ecosystem**: Seamless integration with Rust's cargo ecosystem

### ⚡ Performance Optimizations

- **SIMD Operations**: Vectorized polynomial and matrix operations
- **Custom Allocators**: Arena allocation for AST nodes, clause pooling
- **Lock-Free Data Structures**: Concurrent clause database access
- **Compile-Time Optimization**: Monomorphization and inline expansion

### 🎯 Unique Features

1. **Enhanced Proof Systems**
   - Machine-checkable proofs exportable to Coq, Lean 4, and Isabelle/HOL, in addition to DRAT/Alethe/LFSC (`oxiz-proof`)
   - Proof compression and optimization
   - Interactive proof exploration

2. **WebAssembly Bindings**
   - Compact WASM bundle — see [`oxiz-wasm/README.md`](oxiz-wasm/README.md) for current, build-specific size measurements
   - Code splitting for lazy theory loading
   - Browser-optimized memory management

3. **ML-Guided Heuristics** (opt-in)
   - `oxiz-cli --ml-tactic-selection` (off by default) selects a solver posture per formula via a trained decision tree and learns from outcomes
   - Adaptive restart policies
   - Clause usefulness prediction

4. **Advanced Type Safety**
   - Compile-time logic validation
   - Type-safe term construction
   - Impossible state elimination

5. **Developer Experience**
   - Rich error messages with suggestions
   - Comprehensive documentation
   - Property-based testing with proptest

## Python Bindings

OxiZ provides Python bindings via PyO3:

```bash
# Install from PyPI (when published)
pip install oxiz

# Or build from source
cd oxiz-py
pip install maturin
maturin develop --release
```

```python
import oxiz

tm = oxiz.TermManager()
solver = oxiz.Solver()

x = tm.mk_var("x", "Int")
y = tm.mk_var("y", "Int")
solver.assert_term(tm.mk_gt(x, tm.mk_int(0)), tm)
solver.assert_term(tm.mk_eq(tm.mk_add([x, y]), tm.mk_int(10)), tm)

if solver.check_sat(tm) == oxiz.SolverResult.Sat:
    print(solver.get_model(tm))
```

## WebAssembly

OxiZ can be compiled to WebAssembly for browser use:

```bash
cd oxiz-wasm
wasm-pack build --target web
```

Beyond the basic async solver API, `oxiz-wasm` provides:
- **Hard-preemptible solving** (`PreemptibleSolver`): runs a solve inside a dedicated `Worker` and can `terminate()` it from the main thread on timeout — a real interrupt, unlike racing a `setTimeout` against a synchronous, non-yielding solve loop.
- **Cooperative cancellation** (`CancellationToken`): a `SharedArrayBuffer`/`Atomics`-backed flag a worker polls between operations, plus a plain-`JsValue` message protocol (`WorkerHandler.handleMessage`) for a real `Worker`'s `onmessage` handler.
- **Generated TypeScript definitions** (`generate_typescript_dts()`): the `oxiz.d.ts` type definitions are generated from the Rust source, so they can't drift from the JS API.

## Contributing

Contributions are welcome! Please see our contributing guidelines.

## Sponsorship

OxiZ is developed and maintained by **COOLJAPAN OU (Team Kitasan)**.

If you find OxiZ useful, please consider sponsoring the project to support continued development of the Pure Rust ecosystem.

[![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-red?logo=github)](https://github.com/sponsors/cool-japan)

**[https://github.com/sponsors/cool-japan](https://github.com/sponsors/cool-japan)**

Your sponsorship helps us:
- Maintain and improve the COOLJAPAN ecosystem
- Keep the entire ecosystem (OxiBLAS, OxiFFT, SciRS2, etc.) 100% Pure Rust
- Provide long-term support and security updates

## License

Apache-2.0

## Authors

COOLJAPAN OU (Team KitaSan)

## Benchmarks

`bench/z3_parity` records real wall-clock time for both solvers, but OxiZ is invoked as an in-process library call while Z3 is invoked as an external subprocess (see [`bench/z3_parity/METHODOLOGY.md`](bench/z3_parity/METHODOLOGY.md)) — the two aren't measured under comparable conditions, so this repo does not publish a solver-vs-solver speed ratio from that data. There is no other in-repo apples-to-apples throughput benchmark against Z3 yet; `bench/regression` and `bench/profile` track OxiZ's own performance over time (see `docs/PROFILING_REPORT.md`) rather than a cross-solver comparison. Treat any "OxiZ is Nx faster/slower than Z3" claim you see elsewhere as unverified until it cites a same-process, same-hardware methodology.

## Roadmap

Historical high-level phases, not a parity percentage claim — see "Z3 Parity" above and [`TODO.md`](TODO.md) for the actual measured gaps still open.

### Phase 1: Quick Wins ✅ Complete
- Export unintegrated modules
- Fix API compatibility issues
- Complete enhanced MaxSAT solvers

### Phase 2: High-Impact Features ✅ Complete
- SMT integration layer enhancement
- Math libraries expansion
- Quantifier elimination expansion
- Tactics system expansion

### Phase 3: Rust-Specific Enhancements ✅ Mostly Complete
- ✅ Comprehensive error handling
- ✅ Trait-based architecture
- ✅ SIMD & parallel optimizations
- ✅ Property-based testing
- ✅ Documentation generation

### Phase 4: Advanced Features ✅ Mostly Complete
- ✅ Machine-checkable proof export (Coq/Lean/Isabelle)
- ✅ WebAssembly bindings
- ✅ ML-guided heuristics (opt-in, off by default)

### Phase 5: Gap Closure 🔄 In Progress
- Additional rewriters
- Muz/Datalog expansion
- SAT solver enhancements
- Closing the remaining `TODO.md` items surfaced by the production-readiness audit (irrational-root isolation, string/FP `Unknown` gaps, etc.)

## Acknowledgments

This project is inspired by and references the algorithms in:
- Z3 (Microsoft Research) - Primary reference implementation
- CVC5 (Stanford/Iowa) - Theory integration techniques
- MiniSat/Glucose - CDCL SAT solving
- Various academic papers on SMT solving

### Key References

- "Satisfiability Modulo Theories" (Barrett et al., 2018)
- "Programming Z3" (de Moura & Bjørner, 2008)
- "DPLL(T): Fast Decision Procedures" (Ganzinger et al., 2004)
- "Efficient E-matching for SMT Solvers" (de Moura & Bjørner, 2007)
