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
//! `cargo nextest run -p nixie-theories -E 'test(/^foo::/)'` or
//! `cargo test -p nixie-theories --test integration foo::`.
//!
//! `autotests = false` in Cargo.toml means a new `tests/*.rs` file is NOT
//! picked up by itself: add it below (or as a standalone `[[test]]` in
//! Cargo.toml if it installs a `#[global_allocator]` or mutates the process
//! environment). `every_test_file_is_registered` fails until you do.

#[path = "ania_nested.rs"]
mod ania_nested;
#[path = "arith_pop_state_rollback.rs"]
mod arith_pop_state_rollback;
#[path = "array_integration.rs"]
mod array_integration;
#[path = "audit_theories_arith_p2.rs"]
mod audit_theories_arith_p2;
#[path = "audit_theories_bv.rs"]
mod audit_theories_bv;
#[path = "audit_theories_euf.rs"]
mod audit_theories_euf;
#[path = "audit_theories_fp_p3.rs"]
mod audit_theories_fp_p3;
#[path = "audit_theory_soundness.rs"]
mod audit_theory_soundness;
#[path = "bv_budget.rs"]
mod bv_budget;
#[path = "bv_conflict_detection.rs"]
mod bv_conflict_detection;
#[path = "bv_div_test.rs"]
mod bv_div_test;
#[path = "bv_fixes_verification.rs"]
mod bv_fixes_verification;
#[path = "bv_mul_test.rs"]
mod bv_mul_test;
#[path = "bv_root_scoped_definitions.rs"]
mod bv_root_scoped_definitions;
#[path = "bv_selector_fragment_and_pins.rs"]
mod bv_selector_fragment_and_pins;
#[path = "bv_soundness.rs"]
mod bv_soundness;
#[path = "bv_wide_scope_and_model.rs"]
mod bv_wide_scope_and_model;
#[path = "c4_theories_deep_recursion.rs"]
mod c4_theories_deep_recursion;
#[path = "c4_theories_regex_and_aig.rs"]
mod c4_theories_regex_and_aig;
#[path = "combination_presolve_singleton.rs"]
mod combination_presolve_singleton;
#[path = "cp_domain_certificates.rs"]
mod cp_domain_certificates;
#[path = "cp_table_certificates.rs"]
mod cp_table_certificates;
#[path = "datatype_integration.rs"]
mod datatype_integration;
#[path = "ff_binary_oracle.rs"]
mod ff_binary_oracle;
#[path = "ff_linear_point.rs"]
mod ff_linear_point;
#[path = "ff_oracle.rs"]
mod ff_oracle;
#[path = "ff_planted_fuzz.rs"]
mod ff_planted_fuzz;
#[path = "ff_window_split.rs"]
mod ff_window_split;
#[path = "fp_comprehensive.rs"]
mod fp_comprehensive;
#[path = "fp_integration.rs"]
mod fp_integration;
#[path = "lia_gcd_test.rs"]
mod lia_gcd_test;
#[path = "lia_heuristics_integration.rs"]
mod lia_heuristics_integration;
#[path = "lra_regression_issue6.rs"]
mod lra_regression_issue6;
#[path = "mixed_integer_mode.rs"]
mod mixed_integer_mode;
#[path = "nia_verymax_flip_regression.rs"]
mod nia_verymax_flip_regression;
#[path = "nlsat_mixed_sort.rs"]
mod nlsat_mixed_sort;
#[path = "pr27_nia_divmod.rs"]
mod pr27_nia_divmod;
#[path = "regex_membership_solving.rs"]
mod regex_membership_solving;
#[path = "simplex_stale_var_registration.rs"]
mod simplex_stale_var_registration;
#[path = "string_integration.rs"]
mod string_integration;
#[path = "test_adder_extra.rs"]
mod test_adder_extra;
#[path = "test_adder_only.rs"]
mod test_adder_only;
#[path = "test_adder_ult.rs"]
mod test_adder_ult;
#[path = "test_bv10.rs"]
mod test_bv10;
#[path = "test_dump_encoding.rs"]
mod test_dump_encoding;
#[path = "test_minimal_add_ult.rs"]
mod test_minimal_add_ult;
#[path = "test_mul_add_ult.rs"]
mod test_mul_add_ult;
#[path = "test_sat_verify.rs"]
mod test_sat_verify;
#[path = "test_trace_bits.rs"]
mod test_trace_bits;
#[path = "test_ult_unknowns.rs"]
mod test_ult_unknowns;
#[path = "theory_completeness.rs"]
mod theory_completeness;

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
