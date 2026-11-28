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
//! `cargo nextest run -p nixie-solver -E 'test(/^foo::/)'` or
//! `cargo test -p nixie-solver --test integration foo::`.
//!
//! `autotests = false` in Cargo.toml means a new `tests/*.rs` file is NOT
//! picked up by itself: add it below (or as a standalone `[[test]]` in
//! Cargo.toml if it installs a `#[global_allocator]` or mutates the process
//! environment). `every_test_file_is_registered` fails until you do.

#[path = "arith_diseq_soundness.rs"]
mod arith_diseq_soundness;
#[path = "arith_wide_literal_regressions.rs"]
mod arith_wide_literal_regressions;
#[path = "arrangement_round_regressions.rs"]
mod arrangement_round_regressions;
#[path = "array_arith_combination.rs"]
mod array_arith_combination;
#[path = "array_axiom_instantiation.rs"]
mod array_axiom_instantiation;
#[path = "array_index_entailed_equal.rs"]
mod array_index_entailed_equal;
#[path = "array_model_chain_walk.rs"]
mod array_model_chain_walk;
#[path = "array_store_extensionality.rs"]
mod array_store_extensionality;
#[path = "audit_model_default_depth.rs"]
mod audit_model_default_depth;
#[path = "audit_solver_cmd_wiring.rs"]
mod audit_solver_cmd_wiring;
#[path = "audit_solver_core_p2.rs"]
mod audit_solver_core_p2;
#[path = "audit_solver_fp_string.rs"]
mod audit_solver_fp_string;
#[path = "audit_solver_p3b.rs"]
mod audit_solver_p3b;
#[path = "audit_solver_p3c.rs"]
mod audit_solver_p3c;
#[path = "audit_sweep_solver.rs"]
mod audit_sweep_solver;
#[path = "big_int_const_abstraction.rs"]
mod big_int_const_abstraction;
#[path = "budget_bitblast.rs"]
mod budget_bitblast;
#[path = "bv_dispatch_folding_regressions.rs"]
mod bv_dispatch_folding_regressions;
#[path = "bv_dispatch_memo_isolation.rs"]
mod bv_dispatch_memo_isolation;
#[path = "bv_divisor_identities.rs"]
mod bv_divisor_identities;
#[path = "bv_eager_fragment_regressions.rs"]
mod bv_eager_fragment_regressions;
#[path = "bv_elim_uncnstr_regressions.rs"]
mod bv_elim_uncnstr_regressions;
#[path = "bv_euf_combination.rs"]
mod bv_euf_combination;
#[path = "bv_mul_hoist_regressions.rs"]
mod bv_mul_hoist_regressions;
#[path = "bv_odd_width_blast_differential.rs"]
mod bv_odd_width_blast_differential;
#[path = "bv_ring_elim_regressions.rs"]
mod bv_ring_elim_regressions;
#[path = "bv_shift_wiring.rs"]
mod bv_shift_wiring;
#[path = "bv_soundness_integration.rs"]
mod bv_soundness_integration;
#[path = "bv_unified_regressions.rs"]
mod bv_unified_regressions;
#[path = "bv_wide_soundness.rs"]
mod bv_wide_soundness;
#[path = "certified_uf_sat.rs"]
mod certified_uf_sat;
#[path = "combined_theories_integration.rs"]
mod combined_theories_integration;
#[path = "const_array_and_rmw_regressions.rs"]
mod const_array_and_rmw_regressions;
#[path = "cp_complete_proof.rs"]
mod cp_complete_proof;
#[path = "cp_domain_certificates.rs"]
mod cp_domain_certificates;
#[path = "cp_global_constraints.rs"]
mod cp_global_constraints;
#[path = "cp_optional_scheduling.rs"]
mod cp_optional_scheduling;
#[path = "cp_oracle.rs"]
mod cp_oracle;
#[path = "cp_table_certificates.rs"]
mod cp_table_certificates;
#[path = "define_fun_alias_regressions.rs"]
mod define_fun_alias_regressions;
#[path = "distinct_encoding.rs"]
mod distinct_encoding;
#[path = "ff_binary_extension.rs"]
mod ff_binary_extension;
#[path = "ff_solver_regression.rs"]
mod ff_solver_regression;
#[path = "ff_ufff_oracle.rs"]
mod ff_ufff_oracle;
#[path = "ff_ufff_regression.rs"]
mod ff_ufff_regression;
#[path = "finite_bags_core.rs"]
mod finite_bags_core;
#[path = "finite_range_expansion.rs"]
mod finite_range_expansion;
#[path = "finite_sets_cardinality.rs"]
mod finite_sets_cardinality;
#[path = "finite_sets_decision.rs"]
mod finite_sets_decision;
#[path = "finite_sets_model.rs"]
mod finite_sets_model;
#[path = "finite_sets_relations.rs"]
mod finite_sets_relations;
#[path = "finite_sets_sort_and_terms.rs"]
mod finite_sets_sort_and_terms;
#[path = "fp_const_folding.rs"]
mod fp_const_folding;
#[path = "fp_format_aliases.rs"]
mod fp_format_aliases;
#[path = "fp_hybrid.rs"]
mod fp_hybrid;
#[path = "fsm_constraints.rs"]
mod fsm_constraints;
#[path = "fsm_script_lifecycle.rs"]
mod fsm_script_lifecycle;
#[path = "func_interp_euf.rs"]
mod func_interp_euf;
#[path = "get_consequences_e2e.rs"]
mod get_consequences_e2e;
#[path = "get_value_batch_rows.rs"]
mod get_value_batch_rows;
#[path = "graph_constraints.rs"]
mod graph_constraints;
#[path = "guarded_quantifier_instantiation.rs"]
mod guarded_quantifier_instantiation;
#[path = "heap_separation.rs"]
mod heap_separation;
#[path = "injective_repair.rs"]
mod injective_repair;
#[path = "int_case_split_determinism_regressions.rs"]
mod int_case_split_determinism_regressions;
#[path = "issue40_model_blocking.rs"]
mod issue40_model_blocking;
#[path = "lia_integration.rs"]
mod lia_integration;
#[path = "lia_quantifier_witnesses.rs"]
mod lia_quantifier_witnesses;
#[path = "logic_contract_acceptance.rs"]
mod logic_contract_acceptance;
#[path = "mbqi_exhaustion_soundness.rs"]
mod mbqi_exhaustion_soundness;
#[path = "mbqi_sat_certification.rs"]
mod mbqi_sat_certification;
#[path = "mbqi_tests.rs"]
mod mbqi_tests;
#[path = "model_output_and_options.rs"]
mod model_output_and_options;
#[path = "model_render_shared_walks.rs"]
mod model_render_shared_walks;
#[path = "model_rows_without_array_rendering.rs"]
mod model_rows_without_array_rendering;
#[path = "model_soundness_regressions.rs"]
mod model_soundness_regressions;
#[path = "native_sequences.rs"]
mod native_sequences;
#[path = "negated_quantifier_soundness.rs"]
mod negated_quantifier_soundness;
#[path = "nia_disjunctive_dispatch.rs"]
mod nia_disjunctive_dispatch;
#[path = "nl_definition_bool_model.rs"]
mod nl_definition_bool_model;
#[path = "nlsat_feature_gate.rs"]
mod nlsat_feature_gate;
#[path = "nlsat_integration.rs"]
mod nlsat_integration;
#[path = "nra_algebraic_model.rs"]
mod nra_algebraic_model;
#[path = "optimization_arith_regressions.rs"]
mod optimization_arith_regressions;
#[path = "overflow_predicates.rs"]
mod overflow_predicates;
#[path = "pr27_divmod_semantics.rs"]
mod pr27_divmod_semantics;
#[path = "pr28_pr29_soundness.rs"]
mod pr28_pr29_soundness;
#[path = "pr30_soundness.rs"]
mod pr30_soundness;
#[path = "pr31_nonlinear_search.rs"]
mod pr31_nonlinear_search;
#[path = "pr32_pr33_soundness.rs"]
mod pr32_pr33_soundness;
#[path = "proof_roundtrip.rs"]
mod proof_roundtrip;
#[path = "property_based.rs"]
mod property_based;
#[path = "push_sat_pop_leak.rs"]
mod push_sat_pop_leak;
#[path = "qf_ania_ce.rs"]
mod qf_ania_ce;
#[path = "qf_fp_concrete_model.rs"]
mod qf_fp_concrete_model;
#[path = "qf_nia_relaxation.rs"]
mod qf_nia_relaxation;
#[path = "qf_s_ground_string.rs"]
mod qf_s_ground_string;
#[path = "qf_uf_bcp_fixpoint_regression.rs"]
mod qf_uf_bcp_fixpoint_regression;
#[path = "qf_uf_euf_propagate.rs"]
mod qf_uf_euf_propagate;
#[path = "qfidl_dl_regressions.rs"]
mod qfidl_dl_regressions;
#[path = "real_division_dispatch.rs"]
mod real_division_dispatch;
#[path = "recfun_e2e.rs"]
mod recfun_e2e;
#[path = "repro_disjunctive_lia.rs"]
mod repro_disjunctive_lia;
#[path = "rounding_mode_first_class.rs"]
mod rounding_mode_first_class;
#[path = "s10_dead_modules.rs"]
mod s10_dead_modules;
#[path = "scaled_row_canonicalization.rs"]
mod scaled_row_canonicalization;
#[path = "scope_leak_hazard.rs"]
mod scope_leak_hazard;
#[path = "scope_rebase_adversarial.rs"]
mod scope_rebase_adversarial;
#[path = "set_tuple_reconstruction.rs"]
mod set_tuple_reconstruction;
#[path = "shrink_tautology_regression.rs"]
mod shrink_tautology_regression;
#[path = "solver_final_regression.rs"]
mod solver_final_regression;
#[path = "state_hygiene_audit.rs"]
mod state_hygiene_audit;
#[path = "trans_delta_icp.rs"]
mod trans_delta_icp;
#[path = "uflia_quantified_sat.rs"]
mod uflia_quantified_sat;
#[path = "uflra_quantified_sat.rs"]
mod uflra_quantified_sat;
#[path = "uflra_quantifier_regressions.rs"]
mod uflra_quantifier_regressions;
#[path = "upstream034_array_completion.rs"]
mod upstream034_array_completion;
#[path = "upstream034_array_ite.rs"]
mod upstream034_array_ite;
#[path = "upstream034_arrays_and_symbols.rs"]
mod upstream034_arrays_and_symbols;
#[path = "upstream034_budget_transitions.rs"]
mod upstream034_budget_transitions;
#[path = "upstream034_bv_bridge.rs"]
mod upstream034_bv_bridge;
#[path = "upstream034_bv_scopes.rs"]
mod upstream034_bv_scopes;
#[path = "upstream034_datatype_builders.rs"]
mod upstream034_datatype_builders;
#[path = "upstream034_datatype_separation.rs"]
mod upstream034_datatype_separation;
#[path = "upstream034_datatypes.rs"]
mod upstream034_datatypes;
#[path = "upstream034_finite_array_domains.rs"]
mod upstream034_finite_array_domains;
#[path = "upstream034_function_models.rs"]
mod upstream034_function_models;
#[path = "upstream034_generated_model_values.rs"]
mod upstream034_generated_model_values;
#[path = "upstream034_guard_points.rs"]
mod upstream034_guard_points;
#[path = "upstream034_model_interfaces.rs"]
mod upstream034_model_interfaces;
#[path = "upstream034_model_publication.rs"]
mod upstream034_model_publication;
#[path = "upstream034_names_and_statistics.rs"]
mod upstream034_names_and_statistics;
#[path = "upstream034_nested_interfaces.rs"]
mod upstream034_nested_interfaces;
#[path = "upstream034_quantifier_positions.rs"]
mod upstream034_quantifier_positions;
#[path = "upstream034_quantifiers.rs"]
mod upstream034_quantifiers;
#[path = "upstream034_refinement.rs"]
mod upstream034_refinement;
#[path = "z3_compat_arena.rs"]
mod z3_compat_arena;
#[path = "z3_compat_extensions.rs"]
mod z3_compat_extensions;
#[path = "z3_compat_extensions2.rs"]
mod z3_compat_extensions2;
#[path = "z3_compat_extensions3.rs"]
mod z3_compat_extensions3;

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
