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
//! `cargo nextest run -p nixie-math -E 'test(/^foo::/)'` or
//! `cargo test -p nixie-math --test integration foo::`.
//!
//! `autotests = false` in Cargo.toml means a new `tests/*.rs` file is NOT
//! picked up by itself: add it below (or as a standalone `[[test]]` in
//! Cargo.toml if it installs a `#[global_allocator]` or mutates the process
//! environment). `every_test_file_is_registered` fails until you do.

#[path = "audit_math_misc.rs"]
mod audit_math_misc;
#[path = "audit_math_poly.rs"]
mod audit_math_poly;
#[path = "audit_qe_math_follow.rs"]
mod audit_qe_math_follow;
#[path = "audit_resultant_algebraic.rs"]
mod audit_resultant_algebraic;
#[path = "audit_sweep_core_math.rs"]
mod audit_sweep_core_math;
#[path = "edge_cases.rs"]
mod edge_cases;
#[path = "ff_f4_properties.rs"]
mod ff_f4_properties;
#[path = "ff_gb_scale_regression.rs"]
mod ff_gb_scale_regression;
#[path = "ff_gb_seed_dedup_regression.rs"]
mod ff_gb_seed_dedup_regression;
#[path = "ff_gb_traced_untraced_identity.rs"]
mod ff_gb_traced_untraced_identity;
#[path = "grobner_rational_soundness.rs"]
mod grobner_rational_soundness;
#[path = "monomial_order_regressions.rs"]
mod monomial_order_regressions;
#[path = "property_based.rs"]
mod property_based;
#[path = "property_based_extended.rs"]
mod property_based_extended;

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
