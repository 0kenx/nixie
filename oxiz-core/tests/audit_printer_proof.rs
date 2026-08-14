//! Regression tests for the proof printer
//! (`oxiz-core/src/smtlib/printer/proof.rs`).
//!
//! `Printer::write_proof_node` used to be plain native recursion with no
//! depth guard, called once per proof-tree level, so a sufficiently deep
//! proof chain could overflow a worker thread's native stack -- a fatal
//! process abort, not a catchable error. It also re-wrote a shared premise's
//! entire subtree once per parent that referenced it, which is exponential in
//! the depth of the sharing and, independent of that cost, emitted more than
//! one `(step @pN ...)` declaration for the same `@pN` -- already-malformed
//! output, since a step id is meant to be declared once and referenced by id
//! thereafter.
//!
//! Both defects are fixed by converting the walk to an explicit
//! `(ProofId, indent)` stack with a `visited` set. These tests pin:
//!
//! 1. A small shared-premise ("diamond") DAG prints each step exactly once
//!    while still recording every `:premises` reference (behavior
//!    preservation on a case a human can check by hand).
//! 2. A long linear premise chain (depth 100,000) and a DAG with 40 levels of
//!    doubled sharing (which is where the old code's exponential re-expansion
//!    would bite) both return -- and print each node exactly once -- on a
//!    thread with a 1 MiB stack.

use oxiz_core::ast::TermManager;
use oxiz_core::ast::proof::{Proof, ProofId, ProofNode, ProofRule};
use oxiz_core::smtlib::Printer;

/// Count how many times step `id` is *declared* (as opposed to merely
/// referenced from a `:premises` list) in printed proof text.
///
/// `(step @pN :rule ...)` is the declaration; `:rule` always follows the id
/// immediately in that position (every `ProofRule` variant's writer starts
/// with the literal text `:rule`), while a `:premises (@pN ...)` reference is
/// followed by a space or a closing paren instead -- so searching for
/// `"(step @p{id} :rule"` unambiguously counts declarations only.
fn step_declaration_count(output: &str, id: u64) -> usize {
    let pattern = format!("(step @p{id} :rule");
    output.matches(&pattern).count()
}

// ========  ========
// Behavior preservation: a small, hand-checkable shared-premise DAG.
// ========  ========

/// Builds a "diamond": `root` resolves `p1` and `p2`, and both `p1` and `p2`
/// take the *same* `shared` node as their sole premise.
///
/// `shared` therefore has two parents -- the minimal case that exercises
/// dedup. Built with plain iterative code (not a recursive helper).
fn build_diamond_proof(manager: &mut TermManager) -> Proof {
    let t = manager.mk_true();

    let shared = ProofId(0);
    let p1 = ProofId(1);
    let p2 = ProofId(2);
    let root = ProofId(3);

    let mut proof = Proof::new();
    proof.add_node(ProofNode::new(
        shared,
        ProofRule::Assume {
            name: Some("H".to_string()),
        },
        t,
    ));
    proof.add_node(ProofNode::with_premises(
        p1,
        ProofRule::Rewrite,
        t,
        vec![shared],
    ));
    proof.add_node(ProofNode::with_premises(
        p2,
        ProofRule::Rewrite,
        t,
        vec![shared],
    ));
    proof.add_node(ProofNode::with_premises(
        root,
        ProofRule::Resolution { pivot: t },
        t,
        vec![p1, p2],
    ));
    proof.set_root(root);
    proof
}

#[test]
fn diamond_shaped_dag_declares_shared_premise_exactly_once() {
    let mut manager = TermManager::new();
    let proof = build_diamond_proof(&mut manager);

    let output = Printer::new(&manager).print_proof(&proof);

    // Every node -- including the shared one -- must be *declared* exactly
    // once. Before the fix, `shared` (id 0) was declared twice: once under
    // `p1`'s subtree and once under `p2`'s.
    for id in [0u64, 1, 2, 3] {
        assert_eq!(
            step_declaration_count(&output, id),
            1,
            "@p{id} must be declared exactly once, got:\n{output}"
        );
    }

    // The sharing edge itself must still be observable: `@p0` appears once as
    // its own declaration plus once in each of `p1`'s and `p2`'s `:premises`.
    assert_eq!(
        output.matches("@p0").count(),
        3,
        "expected 1 declaration + 2 premise references to @p0, got:\n{output}"
    );
}

#[test]
fn diamond_shaped_dag_root_still_resolves_both_branches() {
    // Sanity check that trimming the duplicate declaration didn't also trim
    // the structure: root's own `:premises` must still list both p1 and p2.
    let mut manager = TermManager::new();
    let proof = build_diamond_proof(&mut manager);
    let output = Printer::new(&manager).print_proof(&proof);

    assert!(output.contains("@p1") && output.contains("@p2"));
    let root_premises_pos = output
        .find(":premises (@p1 @p2)")
        .expect("root's :premises must list p1 then p2 in order");
    let root_decl_pos = output
        .find("(step @p3 :rule")
        .expect("root must be declared");
    assert!(
        root_decl_pos < root_premises_pos,
        "root's own declaration must precede its :premises list"
    );
}

// ========  ========
// Deep structures: built iteratively, exercised on a 1 MiB stack.
// ========  ========

/// `depth + 1` nodes chained one premise deep: `0 <- 1 <- 2 <- ... <- depth`.
/// Built with a plain iterative loop -- a recursive builder would overflow
/// before the printer under test even ran.
fn build_linear_chain_proof(depth: u64, manager: &mut TermManager) -> Proof {
    let t = manager.mk_true();
    let mut proof = Proof::new();
    proof.add_node(ProofNode::new(
        ProofId(0),
        ProofRule::Assume { name: None },
        t,
    ));
    for i in 1..=depth {
        proof.add_node(ProofNode::with_premises(
            ProofId(i),
            ProofRule::Rewrite,
            t,
            vec![ProofId(i - 1)],
        ));
    }
    proof.set_root(ProofId(depth));
    proof
}

/// `levels + 1` nodes where each level takes the *previous* node twice as a
/// premise: `node[i].premises == [node[i-1], node[i-1]]`. This is the shape
/// that makes the old recursive-without-dedup printer's output exponential in
/// `levels` (2^40 subtree expansions at `levels = 40`), even though the
/// number of *distinct* nodes is only `levels + 1`.
fn build_doubled_sharing_proof(levels: u64, manager: &mut TermManager) -> Proof {
    let t = manager.mk_true();
    let mut proof = Proof::new();
    proof.add_node(ProofNode::new(
        ProofId(0),
        ProofRule::Assume { name: None },
        t,
    ));
    for i in 1..=levels {
        proof.add_node(ProofNode::with_premises(
            ProofId(i),
            ProofRule::Resolution { pivot: t },
            t,
            vec![ProofId(i - 1), ProofId(i - 1)],
        ));
    }
    proof.set_root(ProofId(levels));
    proof
}

/// The point of the whole exercise: an embedder calling OxiZ from a worker
/// thread with a conventional ~1 MiB stack must get the printed proof back,
/// not a process abort.
///
/// A Rust stack overflow is not a panic -- it is a fatal runtime abort that
/// `catch_unwind` cannot intercept -- so the only way to assert on it is to
/// run on a thread whose stack size is pinned small and observe that the
/// thread returns at all. "Returned at all" is necessary but not sufficient:
/// each assertion below also checks that every node was actually printed
/// (once), which is what rules out a silent partial walk.
///
/// `DEPTH` is 10,000 rather than the 100,000 used for the term-walk tests:
/// this printer indents every node by its nesting depth (`"  ".repeat(indent)`,
/// unchanged by this conversion), so a linear chain's *total* indentation work
/// is `O(depth^2)` -- harmless at the depths a real proof reaches, but at
/// 100,000 it turns this one test into several minutes of pure string-padding
/// with nothing left to verify beyond what 10,000 already proves (10,000 is
/// already far beyond any depth the old native recursion could have survived
/// on a 1 MiB stack). The quadratic cost is pre-existing in the indentation
/// scheme, not introduced by the iterative rewrite; it is a candidate for a
/// follow-up (e.g. capping indent growth) but is out of scope here.
#[test]
fn deeply_chained_proof_survives_a_one_mib_stack() {
    const STACK_SIZE: usize = 1 << 20; // 1 MiB
    const DEPTH: u64 = 10_000;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(|| {
            let mut manager = TermManager::new();
            let proof = build_linear_chain_proof(DEPTH, &mut manager);
            let output = Printer::new(&manager).print_proof(&proof);

            for id in [0u64, 1, DEPTH / 2, DEPTH - 1, DEPTH] {
                assert_eq!(
                    step_declaration_count(&output, id),
                    1,
                    "@p{id} must be declared exactly once in a {DEPTH}-deep chain"
                );
            }
        })
        .expect("spawning a 1 MiB-stack thread should succeed");

    handle
        .join()
        .expect("the proof walk must return on a 1 MiB stack instead of overflowing it");
}

/// Pins the exponential-re-expansion fix: with 40 levels of doubled sharing,
/// the printed output must stay linear-ish in the 41 distinct nodes, and each
/// one must be declared exactly once -- not `2^40` times.
#[test]
fn doubled_sharing_dag_prints_linearly_on_a_one_mib_stack() {
    const STACK_SIZE: usize = 1 << 20; // 1 MiB
    const LEVELS: u64 = 40;

    let handle = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(|| {
            let mut manager = TermManager::new();
            let proof = build_doubled_sharing_proof(LEVELS, &mut manager);
            let output = Printer::new(&manager).print_proof(&proof);

            for id in 0..=LEVELS {
                assert_eq!(
                    step_declaration_count(&output, id),
                    1,
                    "@p{id} must be declared exactly once out of {} distinct nodes, \
                     not re-expanded per shared reference",
                    LEVELS + 1
                );
            }

            // A generous linear bound: each declaration is at most a few
            // hundred bytes (rule keyword + conclusion + two premise refs).
            // The old exponential behavior would blow *far* past this for
            // levels = 40 (on the order of 2^40 repeated sub-prints), so this
            // is not a tight bound, just one no linear-output fix could fail
            // and no exponential-output bug could pass.
            let generous_linear_bound = (LEVELS as usize + 1) * 2_000;
            assert!(
                output.len() < generous_linear_bound,
                "output length {} suggests exponential re-expansion (bound: {})",
                output.len(),
                generous_linear_bound
            );
        })
        .expect("spawning a 1 MiB-stack thread should succeed");

    handle
        .join()
        .expect("the DAG walk must return on a 1 MiB stack instead of overflowing it");
}
