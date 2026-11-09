# Literal representation obligations

This standalone package migrates the nine upstream harnesses, nine contracted
wrappers and their nine proof harnesses over the real `nixie-sat::{Lit, Var,
LBool}` API. The wrappers specify literal packing, sign/negation, raw-code
round trips, DIMACS conversion and three-valued Boolean negation. The unbounded
index and insufficient DIMACS-precondition specimens intentionally expose
invalid inputs; they are not claims that those APIs accept every integer.

Run the ordinary concrete boundary tests without a formal toolchain:

```sh
cargo test --release --manifest-path nixie-sat/formal/Cargo.toml
cargo clippy --release --manifest-path nixie-sat/formal/Cargo.toml --all-targets -- -D warnings
```

The contract attributes are inactive in this plain build. Passing these tests
checks the concrete inputs in them; it is not a symbolic proof of the contracts.
Unlike upstream's debug-only checks, Nixie's literal bounds are asserted in every
build profile, and the concrete tests check those release assertions.

## Formal and randomized runtime builds

The upstream `oxiformal` dependency was an unpublished local checkout. It is not
vendored or replaced with a mock. Supply its real crate directory explicitly:

```sh
python3 nixie-sat/formal/prepare.py \
  --oxiformal /path/to/cargo-formal/crates/oxiformal \
  --output /tmp/nixie-literal-formal
cd /tmp/nixie-literal-formal
cargo build --release
RUSTFLAGS='--cfg oxiformal_runtime_checks' cargo test --release
cargo formal check
cargo formal replay --all --solver z3
```

Use the compiler/toolchain required by that verifier checkout. The preparation
script refuses an existing destination and points at this repository's actual
SAT crate. It does not run a verifier or certify the supplied tool. Setting
`formal`/`oxiformal_runtime_checks` directly on the plain package without preparing
the dependency is unsupported and fails to resolve the external macros.
Randomized runtime tests provide sampled execution evidence, not proof; the
single-draw contract specimen remains ignored as upstream documents.

No formal or randomized-verifier result for Nixie is claimed here: the external
toolchain was unavailable during migration. The conservative `self-host` metadata
is retained because the verifier and target share solver ancestry. Proofs checked
only by related components do not provide independent corroboration. Record the
actual tool versions and use external replay (the migration environment provides
Z3 4.16.0) before making a verification claim.

## Provenance

The source is adapted from [OxiZ 0.3.4's formal package](https://github.com/cool-japan/oxiz/tree/41439c5194ebbb80649505a1116ef4ea2716dd0b/oxiz-sat/formal).
`UPSTREAM_EXPECTED.toml` preserves its historical measurements under the original
names and versions. It is deliberately not named `EXPECTED.toml`: those verdicts
were measured on a different target/toolchain and are not Nixie expectations or
results. Nixie's stronger unconditional bounds can change the generated proof
obligations. Generate and review new evidence with the actual verifier instead
of copying the historical verdicts.
