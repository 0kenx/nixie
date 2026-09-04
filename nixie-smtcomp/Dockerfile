# syntax=docker/dockerfile:1.7
# Multi-stage build for nixie-smtcomp runner (smtcomp2026 binary).
#
# Build (from the repo root):
#   docker build -f nixie-smtcomp/Dockerfile -t nixie-smtcomp:latest .
#
# Run a single SMT-LIB2 file (the binary takes an optional FILE argument
# or reads from stdin). Exit codes: 0=sat, 10=unsat, 20=unknown/error.
#   docker run --rm -v "$PWD/bench:/bench:ro" \
#     nixie-smtcomp:latest /bench/problem.smt2
#
# Or pipe via stdin:
#   cat problem.smt2 | docker run --rm -i nixie-smtcomp:latest
#
# Print version:
#   docker run --rm nixie-smtcomp:latest --version
#
# Pin the Rust toolchain via build arg (default: current stable that
# supports edition 2024). Override with:
#   docker build --build-arg RUST_VERSION=1.89 -f nixie-smtcomp/Dockerfile -t nixie-smtcomp:latest .

ARG RUST_VERSION=1.85

FROM rust:${RUST_VERSION}-slim-bookworm AS builder

WORKDIR /workspace

# Pure-Rust build: no native linker deps beyond the default toolchain.
# ca-certificates is kept because `cargo` must reach crates.io over
# HTTPS to resolve and fetch every dependency: this repo ships no
# committed lockfile, so resolution happens here at build time.
RUN apt-get update && \
    apt-get install -y --no-install-recommends ca-certificates && \
    rm -rf /var/lib/apt/lists/*

# Copy the workspace manifests and sources. Every workspace member's
# Cargo.toml must be present for cargo to resolve the workspace even
# when building a single package.
#
# Cargo.lock is deliberately NOT copied: it is git-ignored as of 0.3.1,
# so dependencies are resolved fresh at build time. A caller who wants a
# byte-reproducible build should bind-mount or COPY their own lockfile
# and add `--locked` to the cargo build below.
COPY Cargo.toml ./
COPY nixie ./nixie
COPY nixie-core ./nixie-core
COPY nixie-math ./nixie-math
COPY nixie-sat ./nixie-sat
COPY nixie-nlsat ./nixie-nlsat
COPY nixie-theories ./nixie-theories
COPY nixie-solver ./nixie-solver
COPY nixie-opt ./nixie-opt
COPY nixie-spacer ./nixie-spacer
COPY nixie-proof ./nixie-proof
COPY nixie-wasm ./nixie-wasm
COPY nixie-cli ./nixie-cli
COPY nixie-smtcomp ./nixie-smtcomp
COPY nixie-ml ./nixie-ml
COPY bench ./bench

# Build the release binary with the workspace release profile
# (opt-level=z, lto, panic=abort, strip=symbols).
RUN cargo build --release --package nixie-smtcomp --bin smtcomp2026

# ---- Runtime ----
FROM debian:bookworm-slim AS runtime

RUN apt-get update && \
    apt-get install -y --no-install-recommends ca-certificates && \
    rm -rf /var/lib/apt/lists/*

COPY --from=builder /workspace/target/release/smtcomp2026 /usr/local/bin/smtcomp2026
COPY nixie-smtcomp/docker/entrypoint.sh /usr/local/bin/entrypoint.sh
RUN chmod +x /usr/local/bin/entrypoint.sh /usr/local/bin/smtcomp2026

# Non-root user for safety.
RUN useradd --system --no-create-home --shell /usr/sbin/nologin nixie
USER nixie

WORKDIR /workspace
VOLUME ["/bench", "/results"]

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
CMD ["--help"]
