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
//! `cargo nextest run -p nixie-core -E 'test(/^foo::/)'` or
//! `cargo test -p nixie-core --test integration foo::`.
//!
//! `autotests = false` in Cargo.toml means a new `tests/*.rs` file is NOT
//! picked up by itself: add it below (or as a standalone `[[test]]` in
//! Cargo.toml if it installs a `#[global_allocator]` or mutates the process
//! environment). `every_test_file_is_registered` fails until you do.

#[path = "aggressive_simplify_rules.rs"]
mod aggressive_simplify_rules;
#[path = "audit_core_p3.rs"]
mod audit_core_p3;
#[path = "audit_core_simp.rs"]
mod audit_core_simp;
#[path = "audit_core_subst.rs"]
mod audit_core_subst;
#[path = "audit_div_semantics.rs"]
mod audit_div_semantics;
#[path = "audit_ff_surface.rs"]
mod audit_ff_surface;
#[path = "audit_normal_forms.rs"]
mod audit_normal_forms;
#[path = "audit_parser_cmds.rs"]
mod audit_parser_cmds;
#[path = "audit_parser_fp_bv_ext.rs"]
mod audit_parser_fp_bv_ext;
#[path = "audit_parser_sort_cycles.rs"]
mod audit_parser_sort_cycles;
#[path = "audit_parser_terms.rs"]
mod audit_parser_terms;
#[path = "audit_printer_proof.rs"]
mod audit_printer_proof;
#[path = "audit_qe_arith.rs"]
mod audit_qe_arith;
#[path = "audit_sweep_core_math.rs"]
mod audit_sweep_core_math;
#[path = "audit_tactic_misc.rs"]
mod audit_tactic_misc;
#[path = "audit_tactic_quant.rs"]
mod audit_tactic_quant;
#[path = "audit_tactic_wave2.rs"]
mod audit_tactic_wave2;
#[path = "binary_field.rs"]
mod binary_field;
#[path = "c3_core_parser_model.rs"]
mod c3_core_parser_model;
#[path = "define_fun_expand.rs"]
mod define_fun_expand;
#[path = "get_consequences_parse.rs"]
mod get_consequences_parse;
#[path = "native_sequences.rs"]
mod native_sequences;
#[path = "nested_boolean_operands.rs"]
mod nested_boolean_operands;
#[path = "parse_script_lexer_errors.rs"]
mod parse_script_lexer_errors;
#[path = "pr27_define_fun_params.rs"]
mod pr27_define_fun_params;
#[path = "property_based.rs"]
mod property_based;
#[path = "qe_elimination_equiv.rs"]
mod qe_elimination_equiv;
#[path = "qe_lra_elimination.rs"]
mod qe_lra_elimination;
#[path = "qe_virtual_substitution.rs"]
mod qe_virtual_substitution;
#[path = "regex_sublanguage.rs"]
mod regex_sublanguage;
#[path = "theories_nelson_oppen.rs"]
mod theories_nelson_oppen;
#[path = "upstream034_model_interfaces.rs"]
mod upstream034_model_interfaces;

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
