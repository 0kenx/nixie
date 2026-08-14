//! Regression tests for audited EUF soundness defects.
//!
//! Covers two confirmed critical findings:
//!  1. `union_find.rs`: path compression inside `find()` must be undone on
//!     `pop()` so a pointer compressed to a deep root at a deeper scope cannot
//!     survive a backtrack and corrupt equivalence classes.
//!  2. `euf/solver.rs`: `pop()` must remove proof-forest edges appended to
//!     *pre-existing* nodes during the popped scope, so conflict explanations
//!     never cite retracted assertions.

use oxiz_core::ast::TermId;
use oxiz_theories::Theory;
use oxiz_theories::euf::EufSolver;

/// Finding 1 – direct reproduction at the solver level.
///
/// Base: b = a (so root(b) walks through a). Push. In the scope, merge a = c and
/// force a `find(b)` (via `are_equal`) that would path-compress b straight to the
/// c-root. After `pop`, b must be back with a and NOT equal to c.
#[test]
fn find_path_compression_is_undone_on_pop() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));

    // Base level: b = a.
    solver.merge(b, a, TermId::new(10)).expect("merge b=a");
    assert!(solver.are_equal(a, b));

    solver.push();
    // Scope: a = c. Now root of {a,b} is unified with c.
    solver.merge(a, c, TermId::new(11)).expect("merge a=c");
    // Force path compression on b: are_equal walks find(b), which may rewrite
    // parent[b] to point directly at the c-root.
    assert!(solver.are_equal(b, c), "b, a, c all equal inside the scope");
    assert!(solver.are_equal(a, c));

    // Pop: the a=c union is retracted. If compression on b survived, b would
    // still be wrongly equal to c.
    solver.pop();

    assert!(
        solver.are_equal(a, b),
        "b=a from the base level must persist after pop"
    );
    assert!(
        !solver.are_equal(b, c),
        "b must NOT be equal to c after the a=c scope is popped \
         (path compression must be trail-undone)"
    );
    assert!(
        !solver.are_equal(a, c),
        "a must NOT be equal to c after pop"
    );
}

/// Finding 1 – deeper stress: multiple compressions across nested scopes must all
/// unwind exactly, leaving only the base-level equalities.
#[test]
fn nested_scope_compression_unwinds_exactly() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    let d = solver.intern(TermId::new(4));

    // Base: chain b = a.
    solver.merge(b, a, TermId::new(10)).expect("merge b=a");

    solver.push(); // level 1
    solver.merge(a, c, TermId::new(11)).expect("merge a=c");
    assert!(solver.are_equal(b, c)); // compress b -> c-root

    solver.push(); // level 2
    solver.merge(c, d, TermId::new(12)).expect("merge c=d");
    assert!(solver.are_equal(b, d)); // compress b -> d-root

    solver.pop(); // undo c=d
    assert!(solver.are_equal(b, c), "b=c should hold at level 1");
    assert!(!solver.are_equal(b, d), "b=d must be undone");

    solver.pop(); // undo a=c
    assert!(solver.are_equal(a, b), "base b=a persists");
    assert!(!solver.are_equal(b, c), "b=c must be undone");
    assert!(!solver.are_equal(a, c));
    assert!(!solver.are_equal(a, d));
}

/// Finding 2 – proof-forest edges on pre-existing nodes must not leak past a pop
/// and let a later conflict be "explained" by a retracted assertion.
///
/// a, b pre-exist the scope. Inside the scope we assert a = b (reason 21). We pop.
/// Now, at the base level, we assert a != b and then a = b with a DIFFERENT reason
/// (31). The conflict explanation must cite reason 31 (the live assertion) and
/// must NOT cite the retracted reason 21.
#[test]
fn popped_proof_edges_do_not_pollute_explanations() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    solver.push();
    // Merge inside the scope, appending proof-forest edges onto pre-existing
    // nodes a and b with reason 21.
    solver
        .merge(a, b, TermId::new(21))
        .expect("merge a=b in scope");
    assert!(solver.are_equal(a, b));
    solver.pop();

    // After pop the merge is retracted.
    assert!(
        !solver.are_equal(a, b),
        "a=b asserted inside the scope must be retracted by pop"
    );

    // Fresh, live conflict at the base level with a different reason.
    solver.assert_diseq(a, b, TermId::new(30));
    solver.merge(a, b, TermId::new(31)).expect("merge a=b live");

    let conflict = solver
        .check_conflicts()
        .expect("a=b together with a!=b is a conflict");

    assert!(
        conflict.contains(&TermId::new(31)),
        "explanation must cite the live equality reason 31, got {conflict:?}"
    );
    assert!(
        !conflict.contains(&TermId::new(21)),
        "explanation must NOT cite the retracted reason 21 from the popped scope, \
         got {conflict:?}"
    );
}

/// Finding 2 – congruence edges appended to pre-existing nodes during a scope must
/// also be removed on pop.
#[test]
fn popped_congruence_edges_do_not_pollute_explanations() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let f_sym = 7u32;
    let fa = solver.intern_app(TermId::new(10), f_sym, [a]);
    let fb = solver.intern_app(TermId::new(11), f_sym, [b]);

    solver.push();
    // a=b inside the scope forces congruence f(a)=f(b), appending congruence
    // proof edges onto the pre-existing fa/fb nodes.
    solver
        .merge(a, b, TermId::new(50))
        .expect("merge a=b in scope");
    assert!(solver.are_equal(fa, fb));
    solver.pop();

    assert!(
        !solver.are_equal(fa, fb),
        "congruence f(a)=f(b) must be retracted after pop"
    );
    assert!(!solver.are_equal(a, b), "a=b must be retracted after pop");

    // Re-establish congruence with a fresh reason and check the explanation is
    // built only from live edges.
    solver.assert_diseq(fa, fb, TermId::new(60));
    solver.merge(a, b, TermId::new(61)).expect("merge a=b live");
    let conflict = solver
        .check_conflicts()
        .expect("f(a)=f(b) with f(a)!=f(b) is a conflict");
    assert!(
        conflict.contains(&TermId::new(60)),
        "explanation must cite live diseq reason 60, got {conflict:?}"
    );
    assert!(
        !conflict.contains(&TermId::new(50)),
        "explanation must NOT cite the retracted scope reason 50, got {conflict:?}"
    );
}

/// GitHub issue #18 – explaining a congruence must not recurse over its argument
/// sub-goals.
///
/// `f^k(a)` and `f^k(b)` are merged by a cascade of `k` congruence steps once
/// `a = b` is asserted. Explaining the top-level equality therefore has to
/// discharge `k` nested argument equalities. The former implementation did this
/// with a self-call per level, so a chain this deep exhausted the stack; the
/// worklist form runs in constant stack space.
///
/// The body runs on a thread with an explicit 8 MiB stack – the usual main-thread
/// size – so the test measures a normal stack budget rather than whatever the test
/// harness happens to hand out. `DEPTH` is chosen so the old recursion (~3 KiB per
/// frame) would overrun that budget, while the iterative version finishes in well
/// under a second.
#[test]
fn test_issue_18_deep_congruence_explanation_terminates() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(deep_congruence_explanation_body)
        .expect("spawn worker thread")
        .join()
        .expect("explanation must not overflow the stack");
}

fn deep_congruence_explanation_body() {
    const DEPTH: u32 = 3000;
    const F_SYM: u32 = 7;
    const DISEQ_REASON: u32 = 9_000_001;
    const EQ_REASON: u32 = 9_000_002;

    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    // Build f^DEPTH(a) and f^DEPTH(b).
    let mut chain_a = a;
    let mut chain_b = b;
    let mut next_term = 100u32;
    for _ in 0..DEPTH {
        chain_a = solver.intern_app(TermId::new(next_term), F_SYM, [chain_a]);
        next_term += 1;
        chain_b = solver.intern_app(TermId::new(next_term), F_SYM, [chain_b]);
        next_term += 1;
    }

    solver.assert_diseq(chain_a, chain_b, TermId::new(DISEQ_REASON));
    solver
        .merge(a, b, TermId::new(EQ_REASON))
        .expect("merge a=b");

    assert!(
        solver.are_equal(chain_a, chain_b),
        "congruence must propagate a=b through all {DEPTH} applications"
    );

    let conflict = solver
        .check_conflicts()
        .expect("f^k(a)=f^k(b) together with f^k(a)!=f^k(b) is a conflict");

    assert!(
        conflict.contains(&TermId::new(EQ_REASON)),
        "explanation must cite the a=b assertion that drove the congruence cascade, \
         got {conflict:?}"
    );
    assert!(
        conflict.contains(&TermId::new(DISEQ_REASON)),
        "explanation must cite the violated disequality, got {conflict:?}"
    );
}

/// Sanity: repeated push/pop cycles keep state consistent (no drift in either the
/// union-find trail or the proof-forest trail).
#[test]
fn repeated_push_pop_cycles_are_stable() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let c = solver.intern(TermId::new(3));
    solver.merge(a, b, TermId::new(5)).expect("base a=b");

    for round in 0..8u32 {
        solver.push();
        solver
            .merge(b, c, TermId::new(100 + round))
            .expect("scope b=c");
        assert!(solver.are_equal(a, c));
        solver.pop();
        assert!(
            solver.are_equal(a, b),
            "base equality survives round {round}"
        );
        assert!(
            !solver.are_equal(b, c),
            "scope equality retracted round {round}"
        );
    }
}

// ========  ========
// Congruence discovered at intern time must not outlive its justification
//
// `intern_app` used to hand a new term the node of an already-interned
// *congruent* application ("f(0) is f(a), because a = 0 right now").  The
// equality that made them congruent lives on the trail and is retracted by
// `pop`; the `term_to_node` entry does not, because `pop` drops entries by node
// index and the borrowed index belongs to an older, still-live node.  After the
// backtrack the term therefore denoted a different application for good – and,
// worse, had no node, no use-list entry and no signature of its own, so every
// congruence that would have gone *through* it was silently unreachable.
// ========  ========

const F_SYM: u32 = 7;

/// Direct reproduction: an application interned while its argument was already
/// merged must still be a node of its own, and must be retracted by `pop`.
#[test]
fn intern_time_congruence_is_a_retractable_merge_not_an_alias() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let zero = solver.intern(TermId::new(2));
    let fa = solver.intern_app(TermId::new(10), F_SYM, [a]);

    solver.push();
    solver.merge(a, zero, TermId::new(20)).expect("merge a=0");

    // f(0) is congruent to f(a) at this instant.
    let f0_scoped = solver.intern_app(TermId::new(11), F_SYM, [zero]);
    assert_ne!(
        f0_scoped, fa,
        "every new term must get a node of its own; sharing f(a)'s node makes \
         the congruence permanent"
    );
    assert!(
        solver.are_equal(fa, f0_scoped),
        "f(a) and f(0) must be merged while a = 0 holds"
    );

    solver.pop();

    assert!(
        solver.term_to_node(TermId::new(11)).is_none(),
        "the node f(0) acquired inside the scope must be gone after pop; if the \
         term still resolves, it is pinned to a node whose congruence has been \
         retracted"
    );

    // Re-interning at the base level, where a = 0 no longer holds, must produce
    // an independent application.
    let f0 = solver.intern_app(TermId::new(11), F_SYM, [zero]);
    assert!(
        !solver.are_equal(fa, f0),
        "f(0) must not remain equal to f(a) once a = 0 has been retracted"
    );
}

/// The consequence the direct reproduction is about: with `f(0)` pinned to
/// `f(a)`'s node it had no signature of its own, so the *second* congruence step
/// – `f(f(a)) = f(0)` once `f(a) = 0` – could never be discovered.  That is the
/// EUF half of the false `sat` on
/// `a ∈ {0,1} ∧ f(0), f(1) ∈ {0,1} ∧ f(f(a)) > 1`.
#[test]
fn nested_congruence_is_discovered_after_the_alias_scope_is_popped() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let zero = solver.intern(TermId::new(2));
    let fa = solver.intern_app(TermId::new(10), F_SYM, [a]);
    let ffa = solver.intern_app(TermId::new(12), F_SYM, [fa]);

    // A scope that makes f(0) congruent to f(a) at intern time, then retracts it.
    solver.push();
    solver.merge(a, zero, TermId::new(20)).expect("merge a=0");
    let _f0_scoped = solver.intern_app(TermId::new(11), F_SYM, [zero]);
    solver.pop();

    // f(0) now interned in a state where a ≠ 0.
    let f0 = solver.intern_app(TermId::new(11), F_SYM, [zero]);

    // f(a) = 0 must make f(f(a)) congruent to f(0).  This needs f(0) to own a
    // live signature entry keyed on 0's class – exactly what the alias destroyed.
    solver
        .merge(fa, zero, TermId::new(31))
        .expect("merge f(a)=0");
    assert!(
        solver.are_equal(ffa, f0),
        "f(f(a)) must be congruent to f(0) once f(a) = 0"
    );

    // And the derived equality must be explainable in full.
    let expl = solver
        .try_explain_eq(ffa, f0)
        .expect("the congruence must have a complete explanation");
    assert!(
        expl.contains(&TermId::new(31)),
        "the explanation must cite f(a) = 0, got {expl:?}"
    );
}

/// Sibling defect: an application must be registered on the *representative* of
/// each argument, not on the raw argument node.
///
/// `f(b)` is interned while `b` is a non-root member of `{a, b}`.  A later merge
/// that makes the *other* side the surviving root scans the absorbed root's
/// use-list; if `f(b)` was filed under `b` it is not there, is never
/// re-canonicalized, and the congruence with `f(d)` is lost – a missed
/// congruence, i.e. a false `sat`.
///
/// The two rank-1 trees below are built deliberately: union-by-rank only lets
/// the *second* class win when the ranks are equal, which is what puts `f(b)`'s
/// class on the absorbed side.
#[test]
fn use_list_registers_applications_on_the_argument_representative() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));
    let d = solver.intern(TermId::new(3));
    let e = solver.intern(TermId::new(4));

    // Two rank-1 trees: root(d,e) = d, root(a,b) = a.
    solver.merge(d, e, TermId::new(10)).expect("merge d=e");
    solver.merge(a, b, TermId::new(11)).expect("merge a=b");

    // f(b) interned while b is *not* the representative of its class.
    let fb = solver.intern_app(TermId::new(20), F_SYM, [b]);

    // Equal ranks, so d's class wins and a's class is the one whose use-list is
    // scanned.  f(b) has to be in it.
    solver.merge(d, a, TermId::new(12)).expect("merge d=a");

    let fd = solver.intern_app(TermId::new(21), F_SYM, [d]);
    assert!(
        solver.are_equal(fb, fd),
        "b and d are in one class, so f(b) and f(d) must be congruent"
    );
    let expl = solver
        .try_explain_eq(fb, fd)
        .expect("congruence must be explainable");
    assert!(
        expl.contains(&TermId::new(12)) || expl.contains(&TermId::new(11)),
        "the explanation must cite the merges that put b and d together, got {expl:?}"
    );
}

// ========  ========
// The explanation engine never answers with a partial justification
//
// `explain_equality` used to `continue` past a failed path search and return
// whatever reasons it had already collected.  A conflict core built from such an
// answer is not a weaker clause but an unsound one: it asserts that the literals
// it *does* name are by themselves contradictory.  The two tests below pin the
// invariant from both ends – every equality the union-find reports is
// explainable in full, and the core a conflict comes with really does entail the
// conflict.
// ========  ========

/// A deterministic xorshift64* so the operation sequence is byte-for-byte
/// reproducible across runs and machines.  No wall-clock, no thread scheduling.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Build a fixed e-graph shape: four leaves, the four unary applications over
/// them, and two nested applications.  Returns every node index.
fn build_shape(solver: &mut EufSolver) -> Vec<u32> {
    let leaves: Vec<u32> = (1..=4u32).map(|i| solver.intern(TermId::new(i))).collect();
    let mut nodes = leaves.clone();
    for (k, &leaf) in leaves.iter().enumerate() {
        nodes.push(solver.intern_app(TermId::new(100 + k as u32), F_SYM, [leaf]));
    }
    // Two nested applications: f(f(x0)) and f(f(x1)).
    for k in 0..2usize {
        let inner = nodes[leaves.len() + k];
        nodes.push(solver.intern_app(TermId::new(200 + k as u32), F_SYM, [inner]));
    }
    nodes
}

/// Invariant: for every pair the union-find reports equal, the explanation
/// engine must produce a *complete* justification – never `None`, never a
/// silently truncated list.
///
/// The proof forest gains exactly one edge pair per applied union and `pop`
/// rewinds edges and unions together, so it spans every class and the path
/// search cannot fail.  This test asserts that property directly over a long
/// randomized sequence of merges, disequalities and push/pop cycles.
#[test]
fn every_equal_pair_has_a_complete_explanation() {
    let mut rng = Rng(0x5DEE_CE66_D1CE_4B1D);
    let mut solver = EufSolver::new();
    let nodes = build_shape(&mut solver);
    let mut depth = 0usize;
    let mut reason = 1_000u32;

    for step in 0..600 {
        match rng.below(8) {
            0..=3 => {
                let x = nodes[rng.below(nodes.len())];
                let y = nodes[rng.below(nodes.len())];
                reason += 1;
                solver.merge(x, y, TermId::new(reason)).expect("merge");
            }
            4 => {
                let x = nodes[rng.below(nodes.len())];
                let y = nodes[rng.below(nodes.len())];
                reason += 1;
                solver.assert_diseq(x, y, TermId::new(reason));
            }
            5..=6 => {
                if depth < 4 {
                    solver.push();
                    depth += 1;
                }
            }
            _ => {
                if depth > 0 {
                    solver.pop();
                    depth -= 1;
                }
            }
        }

        // Every equality currently held must be explainable in full.
        for i in 0..nodes.len() {
            for j in (i + 1)..nodes.len() {
                let (x, y) = (nodes[i], nodes[j]);
                if solver.are_equal_immutable(x, y) {
                    assert!(
                        solver.try_explain_eq(x, y).is_some(),
                        "step {step}: nodes {x} and {y} are equal but the proof \
                         forest yielded no complete explanation"
                    );
                } else {
                    assert!(
                        solver.try_explain_eq(x, y).is_none(),
                        "step {step}: nodes {x} and {y} are NOT equal, yet an \
                         explanation was produced"
                    );
                }
            }
        }
    }
}

/// A conflict core must *entail* the conflict.
///
/// The core is replayed into a fresh solver that is given nothing else: only the
/// assertions whose reason terms the core names.  If that solver still finds the
/// conflict, the core really does support the refutation; if it does not, the
/// core was missing part of its justification and the clause built from it would
/// have been unsound.
#[test]
fn conflict_core_entails_the_conflict() {
    #[derive(Clone, Copy)]
    enum Step {
        Merge(usize, usize, u32),
        Diseq(usize, usize, u32),
    }

    let mut rng = Rng(0x1234_5678_9ABC_DEF0);
    let mut checked = 0usize;

    for trial in 0..80u32 {
        // Build a fresh candidate assertion sequence.
        let mut steps: Vec<Step> = Vec::new();
        let mut reason = 500u32;
        for _ in 0..10 {
            let i = rng.below(10);
            let j = rng.below(10);
            reason += 1;
            steps.push(if rng.below(4) == 0 {
                Step::Diseq(i, j, reason)
            } else {
                Step::Merge(i, j, reason)
            });
        }

        // Replay it, stopping at the first conflict.
        let mut solver = EufSolver::new();
        let nodes = build_shape(&mut solver);
        let mut core: Option<Vec<TermId>> = None;
        for step in &steps {
            match *step {
                Step::Merge(i, j, r) => {
                    solver
                        .merge(
                            nodes[i % nodes.len()],
                            nodes[j % nodes.len()],
                            TermId::new(r),
                        )
                        .expect("merge");
                }
                Step::Diseq(i, j, r) => {
                    solver.assert_diseq(
                        nodes[i % nodes.len()],
                        nodes[j % nodes.len()],
                        TermId::new(r),
                    );
                }
            }
            if let Some(c) = solver.check_conflicts() {
                core = Some(c);
                break;
            }
        }

        let Some(core) = core else {
            continue;
        };
        checked += 1;

        // Replay ONLY the assertions the core names.
        let mut replay = EufSolver::new();
        let replay_nodes = build_shape(&mut replay);
        for step in &steps {
            let (i, j, r, is_merge) = match *step {
                Step::Merge(i, j, r) => (i, j, r, true),
                Step::Diseq(i, j, r) => (i, j, r, false),
            };
            if !core.contains(&TermId::new(r)) {
                continue;
            }
            let (x, y) = (
                replay_nodes[i % replay_nodes.len()],
                replay_nodes[j % replay_nodes.len()],
            );
            if is_merge {
                replay.merge(x, y, TermId::new(r)).expect("merge");
            } else {
                replay.assert_diseq(x, y, TermId::new(r));
            }
        }

        assert!(
            replay.check_conflicts().is_some(),
            "trial {trial}: the conflict core {core:?} does not entail a \
             conflict on its own – a clause built from it would claim that its \
             literals alone are contradictory"
        );
    }

    assert!(
        checked >= 10,
        "the generator produced only {checked} conflicts; the test would not be \
         exercising the core-entailment path"
    );
}

/// `try_explain_eq` distinguishes "justified by nothing" from "no justification".
#[test]
fn try_explain_eq_reports_absence_rather_than_an_empty_answer() {
    let mut solver = EufSolver::new();
    let a = solver.intern(TermId::new(1));
    let b = solver.intern(TermId::new(2));

    // Same node: the equality is structural and rests on no assertion.
    assert_eq!(
        solver.try_explain_eq(a, a),
        Some(Vec::new()),
        "a node is equal to itself for free"
    );

    // Distinct, unequal nodes: there is nothing to explain, and saying so with
    // an empty list would be indistinguishable from the case above.
    assert_eq!(
        solver.try_explain_eq(a, b),
        None,
        "unequal nodes have no explanation, not an empty one"
    );
    assert!(solver.explain_eq(a, b).is_empty());

    // Out-of-range indices are reported as absent, never as "trivially equal".
    assert_eq!(solver.try_explain_eq(a, 9999), None);

    solver.merge(a, b, TermId::new(30)).expect("merge a=b");
    assert_eq!(
        solver.try_explain_eq(a, b),
        Some(vec![TermId::new(30)]),
        "the live assertion is the whole explanation"
    );
}
