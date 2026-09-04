# Nixie

A pure-Rust SMT solver. No C/C++, no FFI.

Nixie is a detached fork of [OxiZ](https://github.com/cool-japan/oxiz),
rebranded and developed independently.

## Build

```sh
cargo build --release                          # solver binary: target/release/nixie
cargo nextest run --workspace --all-features   # test suite
```

Rust 1.88+, edition 2024. `nixie-py` (Python bindings) is excluded from the
default workspace build.

## Crates

| Crate | Role |
|---|---|
| `nixie-core` | AST, sorts, SMT-LIB parser, tactics |
| `nixie-math` | exact arithmetic, polynomials, algebraic numbers |
| `nixie-sat` | CDCL SAT core |
| `nixie-nlsat` | NLSAT / CAD solver |
| `nixie-proof` | proof logging and checking (DRAT, LRAT, …) |
| `nixie-theories` | EUF, arithmetic, BV, arrays, strings, floats, datatypes |
| `nixie-solver` | CDCL(T) combination |
| `nixie-spacer` | CHC solving / PDR model checking |
| `nixie-opt` | MaxSAT / optimization |
| `nixie-cli` | command-line interface |
| `nixie-wasm` | WebAssembly build |
| `nixie-smtcomp` | SMT-COMP entry tooling |
| `nixie-ml` | learned heuristics |
| `nixie-time` | timing abstractions |
| `nixie` | meta-crate |

Deeper docs: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md),
[`docs/BENCHMARKING.md`](docs/BENCHMARKING.md). Differential parity against a
real Z3 binary: [`bench/z3_parity`](bench/z3_parity).

## References

- [OxiZ](https://github.com/cool-japan/oxiz) — upstream this fork detached
  from
- [Z3](https://github.com/Z3Prover/z3) — CDCL(T) architecture, theory
  solvers, quantifiers, NLSAT, Spacer, proofs
- [CaDiCaL](https://github.com/arminbiere/cadical),
  [Kissat](https://github.com/arminbiere/kissat) — SAT core

These projects are used as specifications and as sources of ported code; no
third-party binaries or libraries are linked.

## License

[Apache-2.0](LICENSE). Portions derive from OxiZ (Apache-2.0) and from
CaDiCaL and Kissat (MIT); their copyright notices are retained in
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md). Those licenses are
compatible with this project's Apache-2.0 terms.
