//! A directly nested `and`/`or` joins its parent's operand list in the
//! parser (`Parser::close_or_absorb`, `nixie-core/src/smtlib/parser/terms.rs`).
//!
//! `mk_and` flattens a nested `and`, so closing each nesting level on its own
//! copied and interned the whole prefix read so far: n − 1 nodes holding
//! 2 + 3 + … + n operands for n leaves (8,390,655 stored operands at 4,096).
//! The driver now hands an `and` that closes directly under an `and` (an `or`
//! under an `or`) to its parent as operands, and only the outermost level is
//! interned. These tests pin what that must preserve:
//!
//! 1. every spelling of one conjunction – right-nested, left-nested, flat –
//!    builds the same term, with the same ordered operands, and no other;
//! 2. the term built is the one the level-by-level construction built – the
//!    retired rule, kept here as the oracle over random trees that mix `and`,
//!    `or`, `true`, `false` and single-operand levels (the simplifications
//!    that make the two spellings agree are not obvious, so they are checked,
//!    not asserted);
//! 3. a `let`, an annotation, a `not` or the other operator between the two
//!    levels keeps the inner term a term: it is built, as it always was;
//! 4. the nesting depth of the input is still charged while the frames are
//!    open – the absorbed frame was on the stack, and counted.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::smtlib::{Command, parse_script, parse_term};

/// Parse a script, returning the manager plus the asserted term ids in order.
fn parse_asserts(script: &str) -> (TermManager, Vec<TermId>) {
    let mut manager = TermManager::new();
    let commands = parse_script(script, &mut manager).expect("script should parse");
    let asserts = commands
        .into_iter()
        .filter_map(|c| match c {
            Command::Assert(t) => Some(t),
            _ => None,
        })
        .collect();
    (manager, asserts)
}

fn declare_bools(n: usize) -> String {
    (0..n)
        .map(|i| format!("(declare-const p{i} Bool)\n"))
        .collect()
}

/// `(and p0 (and p1 (and p2 p3)))`.
fn right_nested(op: &str, leaves: &[String]) -> String {
    let mut out = leaves.last().cloned().expect("a leaf");
    for leaf in leaves[..leaves.len() - 1].iter().rev() {
        out = format!("({op} {leaf} {out})");
    }
    out
}

/// `(and (and (and p0 p1) p2) p3)`.
fn left_nested(op: &str, leaves: &[String]) -> String {
    let mut out = leaves[0].clone();
    for leaf in &leaves[1..] {
        out = format!("({op} {out} {leaf})");
    }
    out
}

/// `(and p0 p1 p2 p3)`.
fn flat(op: &str, leaves: &[String]) -> String {
    let names: Vec<&str> = leaves.iter().map(String::as_str).collect();
    format!("({op} {})", names.join(" "))
}

/// The operands of `t` when it is an `And`/`Or` node of the expected kind.
fn operands(manager: &TermManager, t: TermId, or: bool) -> Vec<TermId> {
    match &manager.get(t).expect("term").kind {
        TermKind::And(args) if !or => args.iter().copied().collect(),
        TermKind::Or(args) if or => args.iter().copied().collect(),
        other => panic!("expected a conjunction/disjunction, got {other:?}"),
    }
}

/// How many `And`/`Or` nodes the arena holds.
fn connective_nodes(manager: &TermManager) -> usize {
    (0..manager.len() as u32)
        .filter_map(|i| manager.get(TermId(i)))
        .filter(|t| matches!(t.kind, TermKind::And(_) | TermKind::Or(_)))
        .count()
}

/// A structural spelling of a Boolean term over variables and connectives –
/// the same text from two managers means the same term.
fn shape(manager: &TermManager, t: TermId) -> String {
    match &manager.get(t).expect("term").kind {
        TermKind::True => "true".to_string(),
        TermKind::False => "false".to_string(),
        TermKind::Var(name) => manager.resolve_str(*name).to_string(),
        TermKind::Not(inner) => format!("(not {})", shape(manager, *inner)),
        TermKind::And(args) => {
            let parts: Vec<String> = args.iter().map(|&a| shape(manager, a)).collect();
            format!("(and {})", parts.join(" "))
        }
        TermKind::Or(args) => {
            let parts: Vec<String> = args.iter().map(|&a| shape(manager, a)).collect();
            format!("(or {})", parts.join(" "))
        }
        other => panic!("unexpected term {other:?}"),
    }
}

/// The variable named `name` anywhere under `t`.
fn find_var(manager: &TermManager, t: TermId, name: &str) -> Option<TermId> {
    let kind = &manager.get(t).expect("term").kind;
    if let TermKind::Var(spur) = kind {
        return (manager.resolve_str(*spur) == name).then_some(t);
    }
    nixie_core::ast::get_children(kind)
        .into_iter()
        .find_map(|child| find_var(manager, child, name))
}

/// The shape of a script's single `(assert …)` over the declared `a`, `b`,
/// `c`; an assertion that folds to `true` produces no command at all, and
/// reads as that.
fn shape_of_assert(assertion: &str) -> String {
    let script = format!(
        "(declare-const a Bool) (declare-const b Bool) (declare-const c Bool) (assert {assertion})"
    );
    let (manager, asserts) = parse_asserts(&script);
    match asserts.as_slice() {
        [] => "true".to_string(),
        [only] => shape(&manager, *only),
        more => panic!("{} assertions, one expected", more.len()),
    }
}

#[test]
fn every_spelling_of_one_conjunction_builds_the_flat_term_and_no_other() {
    const MAX_PARSE_DEPTH: usize = 65536;
    for (op, or) in [("and", false), ("or", true)] {
        for n in [2usize, 3, 4, 7, 64, 1024, 4096, MAX_PARSE_DEPTH - 1] {
            let leaves: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
            let spellings = [
                right_nested(op, &leaves),
                left_nested(op, &leaves),
                flat(op, &leaves),
            ];
            let mut built = Vec::new();
            for spelling in &spellings {
                let script = format!("{}(assert {spelling})", declare_bools(n));
                let (manager, asserts) = parse_asserts(&script);
                let arena_len = manager.len();
                built.push((manager, asserts[0], arena_len));
            }
            let (flat_manager, flat_term, flat_len) = &built[2];
            for (_, term, arena_len) in &built[..2] {
                assert_eq!(
                    term, flat_term,
                    "{op}, n = {n}: a nested spelling of one {op}"
                );
                assert_eq!(
                    arena_len, flat_len,
                    "{op}, n = {n}: the arena of a nested spelling"
                );
            }
            let args = operands(flat_manager, *flat_term, or);
            assert_eq!(args.len(), n, "{op}, n = {n}");
            for (i, &leaf) in args.iter().enumerate() {
                let leaf_term = flat_manager.get(leaf).expect("operand");
                let name = match &leaf_term.kind {
                    TermKind::Var(name) => *name,
                    other => panic!("{op}, n = {n}: operand {i} is {other:?}"),
                };
                assert_eq!(
                    flat_manager.resolve_str(name),
                    format!("p{i}"),
                    "{op}, n = {n}: operand order"
                );
            }
            assert_eq!(
                connective_nodes(flat_manager),
                1,
                "{op}, n = {n}: exactly one {op} node is interned"
            );
        }
    }
}

/// A small deterministic generator – no dependency, reproducible everywhere.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }

    fn below(&mut self, n: u64) -> usize {
        (self.next() % n) as usize
    }
}

enum Tree {
    Leaf(bool),
    Var(u8),
    /// `true` for `or`; every node is spelled as a right-nested binary chain.
    Node(bool, Vec<Tree>),
}

impl Tree {
    fn grow(rng: &mut Lcg, depth: usize) -> Tree {
        if depth == 0 || rng.below(3) == 0 {
            match rng.below(5) {
                0 => Tree::Leaf(true),
                1 => Tree::Leaf(false),
                k => Tree::Var((k - 2) as u8),
            }
        } else {
            let count = 1 + rng.below(3);
            Tree::Node(
                rng.below(2) == 1,
                (0..count).map(|_| Tree::grow(rng, depth - 1)).collect(),
            )
        }
    }

    fn spell_nested(&self) -> String {
        match self {
            Tree::Leaf(true) => "true".to_string(),
            Tree::Leaf(false) => "false".to_string(),
            Tree::Var(i) => format!("q{i}"),
            Tree::Node(or, children) => {
                let op = if *or { "or" } else { "and" };
                let mut out = children.last().expect("a child").spell_nested();
                for child in children[..children.len() - 1].iter().rev() {
                    out = format!("({op} {} {out})", child.spell_nested());
                }
                out
            }
        }
    }

    /// The same tree with some levels spelled flat.
    fn spell_partly_flat(&self, rng: &mut Lcg) -> String {
        match self {
            Tree::Leaf(true) => "true".to_string(),
            Tree::Leaf(false) => "false".to_string(),
            Tree::Var(i) => format!("q{i}"),
            Tree::Node(or, children) => {
                let op = if *or { "or" } else { "and" };
                if children.len() > 1 && rng.below(2) == 0 {
                    let spelled: Vec<String> =
                        children.iter().map(|c| c.spell_partly_flat(rng)).collect();
                    format!("({op} {})", spelled.join(" "))
                } else {
                    let mut out = children.last().expect("a child").spell_partly_flat(rng);
                    for child in children[..children.len() - 1].iter().rev() {
                        out = format!("({op} {} {out})", child.spell_partly_flat(rng));
                    }
                    out
                }
            }
        }
    }
}

/// The retired rule, kept as the oracle: every level is closed through
/// `mk_and`/`mk_or` on its children's terms, exactly as the parser did when
/// each nesting level built a term of its own.
fn build_level_by_level(manager: &mut TermManager, tree: &Tree) -> TermId {
    match tree {
        Tree::Leaf(true) => manager.mk_true(),
        Tree::Leaf(false) => manager.mk_false(),
        Tree::Var(i) => manager.mk_var(&format!("q{i}"), manager.sorts.bool_sort),
        Tree::Node(or, children) => {
            let ids: Vec<TermId> = children
                .iter()
                .map(|c| build_level_by_level(manager, c))
                .collect();
            if *or {
                manager.mk_or(ids)
            } else {
                manager.mk_and(ids)
            }
        }
    }
}

#[test]
fn a_nested_tree_builds_what_the_level_by_level_construction_built() {
    let declared: String = (0..3)
        .map(|i| format!("(declare-const q{i} Bool)\n"))
        .collect();
    let mut rng = Lcg(0x5eed_1234_abcd);
    let mut fewer = 0;
    for round in 0..3000 {
        let tree = Tree::grow(&mut rng, 6);
        let script = format!("{declared}(assert {})", tree.spell_nested());
        let (mut manager, asserts) = parse_asserts(&script);
        let parsed = asserts[0];
        let parser_connectives = connective_nodes(&manager);

        // The oracle runs in the parser's own arena: hash-consing answers
        // the retired rule's root with the parser's term exactly when the
        // two built one term.
        let expected = build_level_by_level(&mut manager, &tree);
        assert_eq!(parsed, expected, "round {round}: {}", tree.spell_nested());
        assert!(
            connective_nodes(&manager) >= parser_connectives,
            "round {round}: the oracle interned fewer connectives than the parser"
        );
        fewer += (connective_nodes(&manager) > parser_connectives) as usize;

        // A second spelling of the same tree, some levels flat, reads the
        // same term – the flat spelling was always the reference.
        let flat_script = format!("{declared}(assert {})", tree.spell_partly_flat(&mut rng));
        let (flat_manager, flat_asserts) = parse_asserts(&flat_script);
        assert_eq!(
            shape(&flat_manager, flat_asserts[0]),
            shape(&manager, parsed),
            "round {round}: a partly flat spelling"
        );
    }
    assert!(
        fewer > 1000,
        "the oracle must exercise trees of more than one level: {fewer}"
    );
}

#[test]
fn a_boundary_between_two_levels_keeps_the_inner_term() {
    // Directly nested: the inner conjunction is never a term.
    let (mut manager, asserts) = parse_asserts(
        "(declare-const a Bool)
         (declare-const b Bool)
         (declare-const c Bool)
         (assert (and a (and b c)))",
    );
    let len_after_parse = manager.len();
    let b = find_var(&manager, asserts[0], "b").expect("b under the assertion");
    let c = find_var(&manager, asserts[0], "c").expect("c under the assertion");
    assert_ne!(b, c, "two distinct variables");
    let inner = manager.mk_and([b, c]);
    assert!(
        inner.raw() as usize >= len_after_parse,
        "a directly nested `and` must not be interned"
    );
    assert_eq!(shape(&manager, asserts[0]), "(and a b c)");

    // A `let` around the inner level: its body is a term of its own – the
    // value the binding stands for – built as before; the outer level still
    // flattens it, so the assertion is the same term.
    let (mut manager, asserts) = parse_asserts(
        "(declare-const a Bool)
         (declare-const b Bool)
         (declare-const c Bool)
         (assert (and a (let ((x b)) (and x c))))",
    );
    let len_after_parse = manager.len();
    let b = find_var(&manager, asserts[0], "b").expect("b under the assertion");
    let c = find_var(&manager, asserts[0], "c").expect("c under the assertion");
    assert_ne!(b, c, "two distinct variables");
    let inner = manager.mk_and([b, c]);
    assert!(
        (inner.raw() as usize) < len_after_parse,
        "the body of a `let` is built"
    );
    assert_eq!(shape(&manager, asserts[0]), "(and a b c)");

    // An annotation on the inner level: the annotated term is built (the
    // annotation is keyed by it) and the outer level flattens it.
    let (mut manager, asserts) = parse_asserts(
        "(declare-const a Bool)
         (declare-const b Bool)
         (declare-const c Bool)
         (assert (and a (! (and b c) :named inner)))",
    );
    let len_after_parse = manager.len();
    let b = find_var(&manager, asserts[0], "b").expect("b under the assertion");
    let c = find_var(&manager, asserts[0], "c").expect("c under the assertion");
    assert_ne!(b, c, "two distinct variables");
    let inner = manager.mk_and([b, c]);
    assert!(
        (inner.raw() as usize) < len_after_parse,
        "an annotated term is built"
    );
    assert_eq!(shape(&manager, asserts[0]), "(and a b c)");

    // `not` between the two: the negated conjunction is a term.
    let (mut manager, asserts) = parse_asserts(
        "(declare-const a Bool)
         (declare-const b Bool)
         (declare-const c Bool)
         (assert (and a (not (and b c))))",
    );
    let len_after_parse = manager.len();
    let b = find_var(&manager, asserts[0], "b").expect("b under the assertion");
    let c = find_var(&manager, asserts[0], "c").expect("c under the assertion");
    assert_ne!(b, c, "two distinct variables");
    let inner = manager.mk_and([b, c]);
    assert!(
        (inner.raw() as usize) < len_after_parse,
        "a negated `and` is built"
    );
    assert_eq!(shape(&manager, asserts[0]), "(and a (not (and b c)))");

    // The other operator: an `or` under an `and` is a term of its own, and
    // its own directly nested levels join it.
    let (manager, asserts) = parse_asserts(
        "(declare-const a Bool)
         (declare-const b Bool)
         (declare-const c Bool)
         (assert (and a (or b (or c a))))",
    );
    assert_eq!(shape(&manager, asserts[0]), "(and a (or b c a))");
    assert_eq!(connective_nodes(&manager), 2, "one `and`, one `or`");
}

#[test]
fn a_degenerate_level_reads_as_it_closed_before() {
    // (An empty `(and)` is a parse error in this parser, as it always was:
    // the driver reads an operand the moment a frame opens. Single-operand
    // levels, `true` and `false` are the degenerate cases that parse.)
    let cases = [
        ("(and a (and b))", "(and a b)"),
        ("(and (and a) b)", "(and a b)"),
        ("(and (and a) (and b))", "(and a b)"),
        ("(and true (and false b))", "(and true false b)"),
        ("(or false (or true b))", "(or false true b)"),
        (
            "(and a (and b true (and c false)))",
            "(and a b true c false)",
        ),
        ("(or (or a) (or (or b)))", "(or a b)"),
        (
            "(and (and true (and true a)) (and b (and true (and c true))))",
            "(and a b c)",
        ),
    ];
    for (nested, reference) in cases {
        let (nested, reference) = (shape_of_assert(nested), shape_of_assert(reference));
        assert_ne!(nested, "?", "a case that parsed to nothing");
        assert_eq!(nested, reference, "{nested}");
    }
    // What the degenerate levels fold to.
    // A repeated operand is kept, as `mk_and` keeps it.
    assert_eq!(shape_of_assert("(and (and a) (and a))"), "(and a a)");
    assert_eq!(shape_of_assert("(and (and a))"), "a");
    assert_eq!(shape_of_assert("(and true (and false b))"), "false");
    assert_eq!(shape_of_assert("(or false (or true b))"), "true");
}

#[test]
fn the_nesting_depth_of_the_input_is_still_charged() {
    // One level past the budget: the frames were open, and counted, even
    // though none of them built a term.
    let depth = 65537;
    let script = format!("{}true{}", "(and true ".repeat(depth), ")".repeat(depth));
    let mut manager = TermManager::new();
    let err = parse_term(&script, &mut manager).expect_err("one level past the budget");
    assert!(err.to_string().contains("term nesting too deep"), "{err}");

    // The deepest nesting the budget admits – 65,535 levels, the innermost
    // operand sitting one level below the outermost frame – parses to the
    // term it denotes, and one level more does not.
    let depth = 65535;
    let script = format!("{}true{}", "(and true ".repeat(depth), ")".repeat(depth));
    let mut manager = TermManager::new();
    let term = parse_term(&script, &mut manager).expect("at the budget");
    assert_eq!(term, manager.mk_true());
    assert_eq!(connective_nodes(&manager), 0, "every operand is `true`");
}
