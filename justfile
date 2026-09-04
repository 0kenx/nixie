default:
    @just --list

_fuzz_dir := "fuzz"
_fuzz_targets := "fuzz_smtlib_parser fuzz_term_builder fuzz_solver fuzz_theory_arithmetic fuzz_theory_bitvector fuzz_theory_array fuzz_quantifiers fuzz_tactics fuzz_parse_and_solve"

# ======== Build ========

build:
    cargo build --all-features

build-release:
    cargo build --release --all-features

watch:
    cargo watch -x 'build --all-features'

# ======== Test ========

test:
    cargo nextest run --workspace --all-features

test-doc:
    cargo test --doc --workspace --all-features

test-all:
    just test
    just test-doc

# ======== Lint / Format / Audit ========

lint:
    cargo clippy --all-features --all-targets -- -D warnings
    cargo deny check bans

fmt:
    #!/usr/bin/env bash
    set -euo pipefail
    RUSTC_WRAPPER= cargo fmt --all
    just emrep
    just comment-clean

fmt-check:
    cargo fmt --all -- --check

emrep:
    #!/usr/bin/env bash
    set -euo pipefail
    git ls-files -z | while IFS= read -r -d '' path; do
        case "$path" in
            *.c|*.cpp|*.h|*.hpp|*.py|*.js|*.ts|*.rs|*.sh|*.yml|*.yaml|*.json|*.toml|*.txt|*.md)
                perl -0pi -e 's/\xE2\x80\x94/\xE2\x80\x93/g' "$path"
                ;;
        esac
    done

comment-clean:
    #!/usr/bin/env bash
    set -euo pipefail
    mapfile -d '' -t files < <(
        git ls-files -z -- '*.rs' \
            | xargs -0 -r rg -l -0 '^\s*//\s*(?:=+\s*$|[-=─]{2,}.*[-=─]{2,}\s*$)' -- || true
    )
    ((${#files[@]})) && perl -0pi -e 's{^(\s*// )=+\h*\n\1([^\n]+?)\h*\n\1=+\h*$}{$1."======== ".$2." ========"}gme; s{^(\s*// )[-=─]{2,}\h*(.*?)\h*[-=─]{2,}\h*$}{$1."======== ".$2." ========"}gme' "${files[@]}"

audit:
    cargo deny check

# ======== Docs / Verify ========

doc:
    cargo doc --no-deps --all-features

verify:
    cargo build --all-features
    cargo clippy --all-features --all-targets -- -D warnings
    cargo fmt --all -- --check
    cargo doc --no-deps --all-features

verify-full:
    just verify
    just test-all

# ======== Fuzz ========

fuzz-run target duration="60":
    #!/usr/bin/env bash
    set -euo pipefail
    if [[ -n "${NIXIE_FUZZ_TOOLCHAIN_BIN:-}" ]]; then
      export PATH="${NIXIE_FUZZ_TOOLCHAIN_BIN}:$PATH"
    fi
    if ! rustc -Z help >/dev/null 2>&1; then
      echo "cargo-fuzz requires a nightly rustc; enter the Nix dev shell or set NIXIE_FUZZ_TOOLCHAIN_BIN to a nightly toolchain bin directory." >&2
      exit 1
    fi
    corpus_dir="{{_fuzz_dir}}/corpus/{{target}}"
    mkdir -p "$corpus_dir"
    cargo fuzz run --fuzz-dir {{_fuzz_dir}} {{target}} "$corpus_dir" -- -timeout=5 -max_total_time={{duration}}

fuzz-smoke:
    #!/usr/bin/env bash
    set -euo pipefail
    for t in {{_fuzz_targets}}; do just fuzz-run "$t" 15; done

fuzz-nightly:
    #!/usr/bin/env bash
    set -euo pipefail
    for t in {{_fuzz_targets}}; do just fuzz-run "$t" 300; done

fuzz-list:
    @echo "Available fuzz targets: {{_fuzz_targets}}"

# ======== Perf ========

flamegraph *args="":
    ./scripts/flamegraph.sh {{args}}

perf-check *args="":
    ./scripts/perf_check.sh {{args}}

perf-vs-z3 *args="":
    ./scripts/perf_vs_z3.sh {{args}}

# ======== Parity / Bindings / CLI ========

# Honest Z3 differential suite. Needs z3 4.15.4 on PATH. See bench/z3_parity/METHODOLOGY.md.
parity:
    ./bench/z3_parity/run_parity.sh

wasm profile="minimal":
    ./scripts/wasm_build.sh {{profile}}

py *args="--release":
    ./scripts/build_python.sh {{args}}

cli *args="":
    cargo run --release -p nixie-cli -- {{args}}

clean:
    cargo clean
    rm -rf result
