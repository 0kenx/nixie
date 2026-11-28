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
//! `cargo nextest run -p nixie-sat -E 'test(/^foo::/)'` or
//! `cargo test -p nixie-sat --test integration foo::`.
//!
//! `autotests = false` in Cargo.toml means a new `tests/*.rs` file is NOT
//! picked up by itself: add it below (or as a standalone `[[test]]` in
//! Cargo.toml if it installs a `#[global_allocator]` or mutates the process
//! environment). `every_test_file_is_registered` fails until you do.

#[path = "allocation_reduction.rs"]
mod allocation_reduction;
#[path = "arena_compaction.rs"]
mod arena_compaction;
#[path = "assertion_scope_contradictions.rs"]
mod assertion_scope_contradictions;
#[path = "assumption_retention.rs"]
mod assumption_retention;
#[path = "asymmetric_branching_strengthen.rs"]
mod asymmetric_branching_strengthen;
#[path = "audit_sat_core.rs"]
mod audit_sat_core;
#[path = "audit_sat_p2.rs"]
mod audit_sat_p2;
#[path = "audit_sat_p3.rs"]
mod audit_sat_p3;
#[path = "budget_deadline.rs"]
mod budget_deadline;
#[path = "cdclt_propagation_fixpoint_soundness.rs"]
mod cdclt_propagation_fixpoint_soundness;
#[path = "chrono_backtracking_soundness.rs"]
mod chrono_backtracking_soundness;
#[path = "chrono_trail_level_filter_regression.rs"]
mod chrono_trail_level_filter_regression;
#[path = "elimination_model_reconstruction.rs"]
mod elimination_model_reconstruction;
#[path = "elimination_soundness_regressions.rs"]
mod elimination_soundness_regressions;
#[path = "els_value_filter_soundness.rs"]
mod els_value_filter_soundness;
#[path = "fold_dedup_owner_rule.rs"]
mod fold_dedup_owner_rule;
#[path = "fs_watch_position_soundness.rs"]
mod fs_watch_position_soundness;
#[path = "incremental_probe_soundness.rs"]
mod incremental_probe_soundness;
#[path = "inprocess_drat_deletion.rs"]
mod inprocess_drat_deletion;
#[path = "ite_gate_congruence_regressions.rs"]
mod ite_gate_congruence_regressions;
#[path = "lrat_e2e.rs"]
mod lrat_e2e;
#[path = "mid_factor_soundness.rs"]
mod mid_factor_soundness;
#[path = "minimizer_chrono_soundness.rs"]
mod minimizer_chrono_soundness;
#[path = "no_fake_gpu_backend.rs"]
mod no_fake_gpu_backend;
#[path = "otfs_tightness_regression.rs"]
mod otfs_tightness_regression;
#[path = "pr26_gatekeeper_regressions.rs"]
mod pr26_gatekeeper_regressions;
#[path = "pr26_inprocessing_regressions.rs"]
mod pr26_inprocessing_regressions;
#[path = "pr26_lrat_proof_regressions.rs"]
mod pr26_lrat_proof_regressions;
#[path = "pr26_search_core_regressions.rs"]
mod pr26_search_core_regressions;
#[path = "preprocessor_slot_bound_regression.rs"]
mod preprocessor_slot_bound_regression;
#[path = "probe_hbr_promotion_soundness.rs"]
mod probe_hbr_promotion_soundness;
#[path = "profiling_pass.rs"]
mod profiling_pass;
#[path = "property_based.rs"]
mod property_based;
#[path = "random_seed_enforcement.rs"]
mod random_seed_enforcement;
#[path = "rng_seed_reproducibility.rs"]
mod rng_seed_reproducibility;
#[path = "root_clause.rs"]
mod root_clause;
#[path = "sat_final_regressions.rs"]
mod sat_final_regressions;
#[path = "sbva_soundness.rs"]
mod sbva_soundness;
#[path = "shrink_inprocessing_regression.rs"]
mod shrink_inprocessing_regression;
#[path = "shrink_trail_index_regression.rs"]
mod shrink_trail_index_regression;
#[path = "test_add_after_solve.rs"]
mod test_add_after_solve;
#[path = "test_allsat_debug.rs"]
mod test_allsat_debug;
#[path = "test_clause_add.rs"]
mod test_clause_add;
#[path = "test_clause_violation.rs"]
mod test_clause_violation;
#[path = "test_clear_learned.rs"]
mod test_clear_learned;
#[path = "test_debug_learned.rs"]
mod test_debug_learned;
#[path = "test_debug_trail.rs"]
mod test_debug_trail;
#[path = "test_detailed_trace.rs"]
mod test_detailed_trace;
#[path = "test_incremental_build.rs"]
mod test_incremental_build;
#[path = "test_learned_conflict.rs"]
mod test_learned_conflict;
#[path = "test_learned_detail.rs"]
mod test_learned_detail;
#[path = "test_lucky.rs"]
mod test_lucky;
#[path = "test_propagation.rs"]
mod test_propagation;
#[path = "test_propagation_debug.rs"]
mod test_propagation_debug;
#[path = "test_trace_bug.rs"]
mod test_trace_bug;
#[path = "test_trace_decisions.rs"]
mod test_trace_decisions;
#[path = "test_trace_incremental.rs"]
mod test_trace_incremental;
#[path = "test_trace_xor_detailed.rs"]
mod test_trace_xor_detailed;
#[path = "test_trail_state.rs"]
mod test_trail_state;
#[path = "test_unit_debug.rs"]
mod test_unit_debug;
#[path = "test_unsat_debug.rs"]
mod test_unsat_debug;
#[path = "test_var_count.rs"]
mod test_var_count;
#[path = "test_watch_corruption.rs"]
mod test_watch_corruption;
#[path = "test_watch_state.rs"]
mod test_watch_state;
#[path = "test_xor_bug.rs"]
mod test_xor_bug;
#[path = "test_xor_debug2.rs"]
mod test_xor_debug2;
#[path = "test_xor_verify.rs"]
mod test_xor_verify;
#[path = "theory_stale_conflict_regression.rs"]
mod theory_stale_conflict_regression;
#[path = "theory_trail_suffix_delivery_regression.rs"]
mod theory_trail_suffix_delivery_regression;
#[path = "theory_unit_propagation_regression.rs"]
mod theory_unit_propagation_regression;
#[path = "threading_model.rs"]
mod threading_model;
#[path = "watch_position_soundness.rs"]
mod watch_position_soundness;
#[path = "xor_gate_congruence_regressions.rs"]
mod xor_gate_congruence_regressions;

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
