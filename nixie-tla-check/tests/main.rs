//! Every integration test of this crate, linked as ONE test binary.
//!
//! Each `tests/*.rs` file used to be its own crate, and each crate is a
//! separate link of the whole dependency stack (~0.5 GB of debug binary
//! apiece). Folding them into modules here links once per crate instead.
//! The files themselves are unchanged: a `#[path]`-loaded module owns its
//! directory, so their own `mod common;` / `#[path = ...]` lines and their
//! `#![cfg(...)]` gates keep working. nextest still runs every test in its
//! own process; only the binary is shared. Test names gain the file stem as a
//! prefix (`foo.rs`'s `bar` is now `foo::bar`), so run one file with
//! `cargo nextest run -p nixie-tla-check -E 'test(/^foo::/)'` or
//! `cargo test -p nixie-tla-check --test integration foo::`.
//!
//! `autotests = false` in Cargo.toml means a new `tests/*.rs` file is NOT
//! picked up by itself: add it below (or as a standalone `[[test]]` in
//! Cargo.toml if it installs a `#[global_allocator]` or mutates the process
//! environment). `every_test_file_is_registered` fails until you do.

#[path = "annotations.rs"]
mod annotations;
#[path = "apalache_stdlib.rs"]
mod apalache_stdlib;
#[path = "arena.rs"]
mod arena;
#[path = "assumptions.rs"]
mod assumptions;
#[path = "bags.rs"]
mod bags;
#[path = "bmc.rs"]
mod bmc;
#[path = "choose.rs"]
mod choose;
#[path = "cli.rs"]
mod cli;
#[path = "comprehensions.rs"]
mod comprehensions;
#[path = "config_driven.rs"]
mod config_driven;
#[path = "deadlock.rs"]
mod deadlock;
#[path = "encode.rs"]
mod encode;
#[path = "fairness.rs"]
mod fairness;
#[path = "folds.rs"]
mod folds;
#[path = "frames.rs"]
mod frames;
#[path = "functions.rs"]
mod functions;
#[path = "ground_bounds.rs"]
mod ground_bounds;
#[path = "itf_output.rs"]
mod itf_output;
#[path = "ranges.rs"]
mod ranges;
#[path = "recursive_functions.rs"]
mod recursive_functions;
#[path = "sequences.rs"]
mod sequences;
#[path = "skolem.rs"]
mod skolem;
#[path = "structs.rs"]
mod structs;
#[path = "temporal_props.rs"]
mod temporal_props;
#[path = "tlc_operators.rs"]
mod tlc_operators;
#[path = "traces.rs"]
mod traces;
#[path = "variants.rs"]
mod variants;

/// A `tests/*.rs` file that is neither a module here nor a `[[test]]` target
/// in Cargo.toml would silently never compile or run (`autotests = false`).
#[test]
fn every_test_file_is_registered() {
    let here = include_str!("main.rs");
    let manifest = include_str!("../Cargo.toml");
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut missing = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("tests/ is readable") {
        let path = entry.expect("tests/ entry is readable").path();
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !name.ends_with(".rs") || name == "main.rs" {
            continue;
        }
        let as_module = format!("#[path = \"{name}\"]");
        let as_target = format!("path = \"tests/{name}\"");
        if !here.contains(&as_module) && !manifest.contains(&as_target) {
            missing.push(name.to_string());
        }
    }
    missing.sort();
    assert!(
        missing.is_empty(),
        "tests/{{{}}} not registered: add `#[path = \"<file>\"] mod <stem>;` to \
         tests/main.rs, or a `[[test]]` to Cargo.toml",
        missing.join(",")
    );
}
