//! Unit and regression tests for Craig interpolation.

use super::parsing::find_resolution_pivot;
use super::*;
use crate::premise::{PremiseId, PremiseTracker};
use crate::proof::{Proof, ProofNodeId};
use num_rational::BigRational;
use rustc_hash::FxHashSet;

#[test]
fn test_interpolant_term_creation() {
    let t = InterpolantTerm::true_val();
    assert!(t.is_true());

    let f = InterpolantTerm::false_val();
    assert!(f.is_false());

    let x = InterpolantTerm::var("x");
    assert!(!x.is_true());
    assert!(!x.is_false());
}

#[test]
fn test_interpolant_term_and() {
    let t = InterpolantTerm::true_val();
    let x = InterpolantTerm::var("x");
    let y = InterpolantTerm::var("y");

    // true ∧ x = x
    let and1 = InterpolantTerm::and(vec![t.clone(), x.clone()]);
    assert_eq!(and1, x);

    // false ∧ x = false
    let f = InterpolantTerm::false_val();
    let and2 = InterpolantTerm::and(vec![f.clone(), x.clone()]);
    assert!(and2.is_false());

    // x ∧ y
    let and3 = InterpolantTerm::and(vec![x.clone(), y.clone()]);
    match and3 {
        InterpolantTerm::And(args) => assert_eq!(args.len(), 2),
        _ => panic!("Expected And"),
    }
}

#[test]
fn test_interpolant_term_or() {
    let t = InterpolantTerm::true_val();
    let f = InterpolantTerm::false_val();
    let x = InterpolantTerm::var("x");

    // false ∨ x = x
    let or1 = InterpolantTerm::or(vec![f.clone(), x.clone()]);
    assert_eq!(or1, x);

    // true ∨ x = true
    let or2 = InterpolantTerm::or(vec![t.clone(), x.clone()]);
    assert!(or2.is_true());
}

#[test]
fn test_interpolant_term_not() {
    let t = InterpolantTerm::true_val();
    let f = InterpolantTerm::false_val();
    let x = InterpolantTerm::var("x");

    // ¬true = false
    let not_t = InterpolantTerm::not(t);
    assert!(not_t.is_false());

    // ¬false = true
    let not_f = InterpolantTerm::not(f);
    assert!(not_f.is_true());

    // ¬¬x = x
    let not_x = InterpolantTerm::not(x.clone());
    let not_not_x = InterpolantTerm::not(not_x);
    assert_eq!(not_not_x, x);
}

#[test]
fn test_interpolant_term_implies() {
    let t = InterpolantTerm::true_val();
    let f = InterpolantTerm::false_val();
    let x = InterpolantTerm::var("x");

    // false → x = true
    let imp1 = InterpolantTerm::implies(f.clone(), x.clone());
    assert!(imp1.is_true());

    // true → x = x
    let imp2 = InterpolantTerm::implies(t.clone(), x.clone());
    assert_eq!(imp2, x);

    // x → true = true
    let imp3 = InterpolantTerm::implies(x.clone(), t);
    assert!(imp3.is_true());
}

#[test]
fn test_interpolant_term_display() {
    let x = InterpolantTerm::var("x");
    let y = InterpolantTerm::var("y");
    let and = InterpolantTerm::and(vec![x.clone(), y.clone()]);

    assert_eq!(format!("{}", and), "(and x y)");

    let or = InterpolantTerm::or(vec![x, y]);
    assert_eq!(format!("{}", or), "(or x y)");
}

#[test]
fn test_symbol_collection() {
    let x = InterpolantTerm::var("x");
    let y = InterpolantTerm::var("y");
    let and = InterpolantTerm::and(vec![x, y]);

    let mut symbols = FxHashSet::default();
    and.collect_symbols(&mut symbols);

    assert_eq!(symbols.len(), 2);
    assert!(symbols.contains(&Symbol::var("x")));
    assert!(symbols.contains(&Symbol::var("y")));
}

#[test]
fn test_interpolant_simplify() {
    let x = InterpolantTerm::var("x");
    let t = InterpolantTerm::true_val();

    let term = InterpolantTerm::and(vec![t, x.clone()]);
    let simplified = term.simplify();
    assert_eq!(simplified, x);
}

#[test]
fn test_partition_creation() {
    let partition = InterpolantPartition::new(
        vec![PremiseId(0), PremiseId(1)],
        vec![PremiseId(2), PremiseId(3)],
    );

    assert!(partition.is_a_premise(PremiseId(0)));
    assert!(partition.is_a_premise(PremiseId(1)));
    assert!(!partition.is_a_premise(PremiseId(2)));

    assert!(partition.is_b_premise(PremiseId(2)));
    assert!(partition.is_b_premise(PremiseId(3)));
    assert!(!partition.is_b_premise(PremiseId(0)));
}

#[test]
fn test_interpolation_config_default() {
    let config = InterpolationConfig::default();

    assert_eq!(config.algorithm, InterpolationAlgorithm::Pudlak);
    assert!(config.use_theory_interpolants);
    assert!(config.simplify_interpolants);
    assert!(config.enable_caching);
}

#[test]
fn test_interpolation_stats_default() {
    let stats = InterpolationStats::default();

    assert_eq!(stats.nodes_processed, 0);
    assert_eq!(stats.a_nodes, 0);
    assert_eq!(stats.b_nodes, 0);
    assert_eq!(stats.ab_nodes, 0);
}

#[test]
fn test_lia_interpolator() {
    let interp = LiaInterpolator;

    assert_eq!(interp.name(), "LIA");
    assert!(interp.can_handle(&["x + y <= 10"]));
    assert!(!interp.can_handle(&["p and q"]));
}

#[test]
fn test_lia_interpolator_projects_to_shared_vocabulary() {
    let interp = LiaInterpolator;
    let mut shared = FxHashSet::default();
    shared.insert(Symbol::var("x"));

    let a_literals = vec![InterpolantTerm::var("x"), InterpolantTerm::var("a_local")];
    let b_literals = vec![InterpolantTerm::var("x")];

    let result = interp
        .interpolate(&a_literals, &b_literals, &shared)
        .expect("interpolate should produce a value");

    // Must not mention the non-shared symbol `a_local`.
    let mut symbols = FxHashSet::default();
    result.collect_symbols(&mut symbols);
    assert!(!symbols.contains(&Symbol::var("a_local")));
    assert!(symbols.contains(&Symbol::var("x")));
}

#[test]
fn test_euf_interpolator() {
    let interp = EufInterpolator;

    assert_eq!(interp.name(), "EUF");
    assert!(interp.can_handle(&["f(x) = y"]));
    assert!(interp.can_handle(&["x = y"]));
}

#[test]
fn test_array_interpolator() {
    let interp = ArrayInterpolator;

    assert_eq!(interp.name(), "Array");
    assert!(interp.can_handle(&["select(a, i)"]));
    assert!(interp.can_handle(&["store(a, i, v)"]));
}

#[test]
fn test_tree_node() {
    let node = TreeNode {
        id: 0,
        formula: InterpolantTerm::var("x"),
        children: vec![1, 2],
        parent: None,
    };

    assert_eq!(node.id, 0);
    assert_eq!(node.children.len(), 2);
    assert!(node.parent.is_none());
}

#[test]
fn test_sequence_interpolator_too_few() {
    let seq = SequenceInterpolator::default();
    let result = seq.interpolate_sequence(&[]);

    assert!(matches!(result, Err(InterpolationError::TooFewFormulas)));
}

#[test]
fn test_interpolation_error_display() {
    let err = InterpolationError::NoRoot;
    assert_eq!(format!("{}", err), "Proof has no root");

    let err2 = InterpolationError::NodeNotFound(ProofNodeId(5));
    assert!(format!("{}", err2).contains("not found"));
}

#[test]
fn test_color_display() {
    assert_eq!(format!("{}", InterpolantColor::A), "A");
    assert_eq!(format!("{}", InterpolantColor::B), "B");
    assert_eq!(format!("{}", InterpolantColor::AB), "AB");
}

#[test]
fn test_mcmillan_basic() {
    let config = InterpolationConfig {
        algorithm: InterpolationAlgorithm::McMillan,
        ..Default::default()
    };
    let partition = InterpolantPartition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
    let mut interpolator = CraigInterpolator::new(config, partition, PremiseTracker::new());
    interpolator.global_symbols.insert(Symbol::var("p"));

    // A-axiom "p" with p shared: interpolant is `p` itself, not the
    // trivial constant `true` the unfixed implementation produced.
    let a_interp = interpolator
        .compute_axiom_interpolant(ProofNodeId(0), InterpolantColor::A, "p")
        .expect("axiom interpolant should succeed");
    assert_eq!(a_interp, InterpolantTerm::var("p"));

    let b_interp = interpolator
        .compute_axiom_interpolant(ProofNodeId(1), InterpolantColor::B, "q")
        .expect("axiom interpolant should succeed");
    assert!(b_interp.is_true());
}

#[test]
fn test_pudlak_basic() {
    let config = InterpolationConfig {
        algorithm: InterpolationAlgorithm::Pudlak,
        ..Default::default()
    };
    let partition = InterpolantPartition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
    let mut interpolator = CraigInterpolator::new(config, partition, PremiseTracker::new());
    interpolator.global_symbols.insert(Symbol::var("p"));

    let a_interp = interpolator
        .compute_axiom_interpolant(ProofNodeId(0), InterpolantColor::A, "p")
        .expect("axiom interpolant should succeed");
    assert_eq!(a_interp, InterpolantTerm::var("p"));
}

#[test]
fn test_huang_basic() {
    let config = InterpolationConfig {
        algorithm: InterpolationAlgorithm::Huang,
        ..Default::default()
    };
    let partition = InterpolantPartition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
    let mut interpolator = CraigInterpolator::new(config, partition, PremiseTracker::new());
    interpolator.global_symbols.insert(Symbol::var("p"));

    // Huang's dual base cases: A-axiom -> false, B-axiom -> negated
    // shared literals.
    let a_interp = interpolator
        .compute_axiom_interpolant(ProofNodeId(0), InterpolantColor::A, "p")
        .expect("axiom interpolant should succeed");
    assert!(a_interp.is_false());

    let b_interp = interpolator
        .compute_axiom_interpolant(ProofNodeId(1), InterpolantColor::B, "p")
        .expect("axiom interpolant should succeed");
    assert_eq!(b_interp, InterpolantTerm::not(InterpolantTerm::var("p")));
}

#[test]
fn test_mixed_axiom_is_rejected_not_fabricated() {
    let config = InterpolationConfig::default();
    let partition = InterpolantPartition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
    let interpolator = CraigInterpolator::new(config, partition, PremiseTracker::new());

    let result = interpolator.compute_axiom_interpolant(ProofNodeId(0), InterpolantColor::AB, "p");
    assert!(matches!(result, Err(InterpolationError::MixedAxiom(_))));
}

#[test]
fn test_tree_interpolator_empty() {
    let tree_interp = TreeInterpolator::default();
    let result = tree_interp.interpolate_tree(&[]);

    assert!(result.is_ok());
    let interps = result.expect("Should succeed");
    assert!(interps.is_empty());
}

#[test]
fn test_tree_interpolator_single_leaf() {
    let tree_interp = TreeInterpolator::default();
    let nodes = vec![TreeNode {
        id: 0,
        formula: InterpolantTerm::var("x"),
        children: vec![],
        parent: None,
    }];

    let result = tree_interp.interpolate_tree(&nodes);
    assert!(result.is_ok());

    let interps = result.expect("Should succeed");
    assert_eq!(interps.len(), 1);
    assert!(interps.contains_key(&0));
}

#[test]
fn test_nested_and_or() {
    let x = InterpolantTerm::var("x");
    let y = InterpolantTerm::var("y");
    let z = InterpolantTerm::var("z");

    // (x ∧ y) ∧ z should flatten to x ∧ y ∧ z
    let inner = InterpolantTerm::and(vec![x.clone(), y.clone()]);
    let outer = InterpolantTerm::and(vec![inner, z.clone()]);

    match outer {
        InterpolantTerm::And(args) => assert_eq!(args.len(), 3),
        _ => panic!("Expected flattened And"),
    }
}

#[test]
fn test_num_term() {
    use num_bigint::BigInt;

    let one = InterpolantTerm::Num(BigRational::from_integer(BigInt::from(1)));
    let two = InterpolantTerm::Num(BigRational::from_integer(BigInt::from(2)));

    let add = InterpolantTerm::Add(vec![one.clone(), two.clone()]);
    assert_eq!(format!("{}", add), "(+ 1 2)");

    let mul = InterpolantTerm::Mul(vec![one, two]);
    assert_eq!(format!("{}", mul), "(* 1 2)");
}

#[test]
fn test_select_store_display() {
    let a = InterpolantTerm::var("a");
    let i = InterpolantTerm::var("i");
    let v = InterpolantTerm::var("v");

    let select = InterpolantTerm::Select(Box::new(a.clone()), Box::new(i.clone()));
    assert_eq!(format!("{}", select), "(select a i)");

    let store = InterpolantTerm::Store(Box::new(a), Box::new(i), Box::new(v));
    assert_eq!(format!("{}", store), "(store a i v)");
}

#[test]
fn test_shared_symbols() {
    let mut partition = InterpolantPartition::new(vec![PremiseId(0)], vec![PremiseId(1)]);

    let x = Symbol::var("x");
    let y = Symbol::var("y");

    partition.set_shared_symbols(vec![x.clone()]);

    assert!(partition.is_shared(&x));
    assert!(!partition.is_shared(&y));
    assert!(partition.shared_symbols().contains(&x));
}

#[test]
fn test_interpolation_algorithms() {
    // Test all three algorithms are distinct
    assert_ne!(
        InterpolationAlgorithm::McMillan,
        InterpolationAlgorithm::Pudlak
    );
    assert_ne!(
        InterpolationAlgorithm::Pudlak,
        InterpolationAlgorithm::Huang
    );
    assert_ne!(
        InterpolationAlgorithm::McMillan,
        InterpolationAlgorithm::Huang
    );
}

#[test]
fn test_mcmillan_inference_global_pivot_uses_and() {
    let config = InterpolationConfig {
        algorithm: InterpolationAlgorithm::McMillan,
        ..Default::default()
    };
    let partition = InterpolantPartition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
    let mut interpolator = CraigInterpolator::new(config, partition, PremiseTracker::new());
    interpolator.global_symbols.insert(Symbol::var("p"));

    let x = InterpolantTerm::var("x");
    let y = InterpolantTerm::var("y");
    let premises = vec![x, y];
    let conclusions = vec!["p", "(not p)"];

    let result = interpolator.mcmillan_interpolant(
        "resolution",
        &premises,
        &conclusions,
        InterpolantColor::AB,
    );

    // `p` is a global (shared) pivot -> McMillan combines with AND.
    match result {
        InterpolantTerm::And(args) => assert_eq!(args.len(), 2),
        _ => panic!("Expected And for a global pivot, got {result:?}"),
    }
}

#[test]
fn test_mcmillan_inference_a_local_pivot_uses_or() {
    let config = InterpolationConfig {
        algorithm: InterpolationAlgorithm::McMillan,
        ..Default::default()
    };
    // `q` is never declared shared, and known_a_symbols/known_b_symbols
    // stay empty -> classify_symbol defaults unseen symbols to ALocal.
    let partition = InterpolantPartition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
    let interpolator = CraigInterpolator::new(config, partition, PremiseTracker::new());

    let x = InterpolantTerm::var("x");
    let y = InterpolantTerm::var("y");
    let premises = vec![x, y];
    let conclusions = vec!["q", "(not q)"];

    let result = interpolator.mcmillan_interpolant(
        "resolution",
        &premises,
        &conclusions,
        InterpolantColor::AB,
    );

    match result {
        InterpolantTerm::Or(args) => assert_eq!(args.len(), 2),
        _ => panic!("Expected Or for an A-local pivot, got {result:?}"),
    }
}

#[test]
fn test_huang_inference_global_pivot_uses_or() {
    let config = InterpolationConfig {
        algorithm: InterpolationAlgorithm::Huang,
        ..Default::default()
    };
    let partition = InterpolantPartition::new(vec![PremiseId(0)], vec![PremiseId(1)]);
    let mut interpolator = CraigInterpolator::new(config, partition, PremiseTracker::new());
    interpolator.global_symbols.insert(Symbol::var("p"));

    let x = InterpolantTerm::var("x");
    let y = InterpolantTerm::var("y");
    let premises = vec![x, y];
    let conclusions = vec!["p", "(not p)"];

    let result =
        interpolator.huang_interpolant("resolution", &premises, &conclusions, InterpolantColor::AB);

    // `p` is global -> Huang (the McMillan dual) combines with OR.
    match result {
        InterpolantTerm::Or(args) => assert_eq!(args.len(), 2),
        _ => panic!("Expected Or for a global pivot, got {result:?}"),
    }
}

#[test]
fn test_find_resolution_pivot_detects_global_literal() {
    let pivot = find_resolution_pivot("p", "(not p)").expect("pivot should be found");
    assert_eq!(pivot.positive_index, 0);
    assert_eq!(pivot.symbol, Symbol::var("p"));
}

#[test]
fn test_find_resolution_pivot_ambiguous_returns_none() {
    // Two complementary pairs -> ambiguous, must not guess.
    let pivot = find_resolution_pivot("(or p q)", "(or (not p) (not q))");
    assert!(pivot.is_none());
}

#[test]
fn test_find_resolution_pivot_no_complement_returns_none() {
    let pivot = find_resolution_pivot("p", "q");
    assert!(pivot.is_none());
}

/// The core regression test for this fix: a minimal unsat A/B pair whose
/// resolution refutation must produce a *genuine, non-trivial*
/// interpolant (previously this collapsed to the trivial constant
/// `true` because every axiom was unconditionally colored `A`).
#[test]
fn test_extract_nontrivial_interpolant_for_small_unsat_pair() {
    // A = {p}, B = {(not p)}; A ∧ B is UNSAT via resolution on shared `p`.
    let mut tracker = PremiseTracker::new();
    let a_premise = tracker.add_assertion("p");
    let b_premise = tracker.add_assertion("(not p)");

    let mut proof = Proof::new();
    let a_axiom = proof.add_axiom("p");
    let b_axiom = proof.add_axiom("(not p)");
    proof.add_inference("resolution", vec![a_axiom, b_axiom], "false");

    let partition = InterpolantPartition::new(vec![a_premise], vec![b_premise]);
    let config = InterpolationConfig {
        algorithm: InterpolationAlgorithm::McMillan,
        ..Default::default()
    };
    let mut interpolator = CraigInterpolator::new(config, partition, tracker);

    let interpolant = interpolator
        .extract(&proof)
        .expect("extraction should succeed");

    // Must be a genuine, non-trivial interpolant -- neither constant.
    assert!(
        !interpolant.is_true(),
        "interpolant collapsed to trivial `true`"
    );
    assert!(
        !interpolant.is_false(),
        "interpolant collapsed to trivial `false`"
    );
    assert_eq!(interpolant, InterpolantTerm::var("p"));

    // Vocabulary check: only shared symbols may appear.
    let mut symbols = FxHashSet::default();
    interpolant.collect_symbols(&mut symbols);
    assert!(symbols.iter().all(|s| s.name == "p"));

    // The axioms must have been colored from the user partition, not
    // defaulted to A.
    assert_eq!(
        interpolator.colors.get(&a_axiom),
        Some(&InterpolantColor::A)
    );
    assert_eq!(
        interpolator.colors.get(&b_axiom),
        Some(&InterpolantColor::B)
    );
}

#[test]
fn test_axiom_coloring_respects_user_partition_for_both_sides() {
    let mut tracker = PremiseTracker::new();
    let a1 = tracker.add_assertion("p");
    let a2 = tracker.add_assertion("q");
    let b1 = tracker.add_assertion("(not p)");

    let mut proof = Proof::new();
    let axiom_p = proof.add_axiom("p");
    let axiom_q = proof.add_axiom("q");
    let axiom_not_p = proof.add_axiom("(not p)");
    proof.add_inference("resolution", vec![axiom_p, axiom_not_p], "false");

    let partition = InterpolantPartition::new(vec![a1, a2], vec![b1]);
    let mut interpolator =
        CraigInterpolator::new(InterpolationConfig::default(), partition, tracker);

    interpolator.precompute_axiom_partition(&proof);

    assert_eq!(
        interpolator.direct_axiom_colors.get(&axiom_p),
        Some(&InterpolantColor::A)
    );
    assert_eq!(
        interpolator.direct_axiom_colors.get(&axiom_q),
        Some(&InterpolantColor::A)
    );
    assert_eq!(
        interpolator.direct_axiom_colors.get(&axiom_not_p),
        Some(&InterpolantColor::B)
    );
}

#[test]
fn test_symbol_fallback_colors_unregistered_theory_lemma() {
    // `p` is registered as an A-premise; an unregistered axiom that only
    // mentions `p` (e.g. a theory lemma the solver synthesized) should
    // fall back to A via the symbol heuristic, not silently default
    // without regard to vocabulary.
    let mut tracker = PremiseTracker::new();
    let a1 = tracker.add_assertion("p");

    let mut proof = Proof::new();
    let axiom_p = proof.add_axiom("p");
    let lemma = proof.add_axiom("(or p r)"); // never registered with the tracker

    let partition = InterpolantPartition::new(vec![a1], Vec::new());
    let mut interpolator =
        CraigInterpolator::new(InterpolationConfig::default(), partition, tracker);
    interpolator.precompute_axiom_partition(&proof);

    assert_eq!(
        interpolator.direct_axiom_colors.get(&axiom_p),
        Some(&InterpolantColor::A)
    );
    assert_eq!(
        interpolator.color_axiom(lemma, "(or p r)"),
        InterpolantColor::A
    );
}
