//! Whole-specification acceptance, over the checked-in corpus.
//!
//! The seed of the parser differential suite in `docs/TLA_FRONTEND_DESIGN.md`
//! §5. `tests/corpus/` holds specifications in the style real TLA+ users
//! write — `DieHard` and `EWD998` are standard examples, `Paxos` exercises the
//! record-set and message-type idiom that protocol specs are built from, and
//! `Torture` collects the constructs most likely to break a parser.
//!
//! Growing this directory with the Apalache test suite and the public TLA+
//! examples corpus is milestone 1's acceptance gate; until those are vendored,
//! this is the standing regression.

use std::path::Path;

fn corpus_dir() -> &'static Path {
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/corpus"))
}

#[test]
fn every_corpus_file_parses() {
    let dir = corpus_dir();
    let entries = std::fs::read_dir(dir).expect("corpus directory exists");
    let mut seen = 0usize;
    for entry in entries {
        let path = entry.expect("readable directory entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("tla") {
            continue;
        }
        seen += 1;
        let src = std::fs::read_to_string(&path).expect("readable corpus file");
        match nixie_tla_syntax::parse_file(&src) {
            Ok(parsed) => {
                assert!(
                    !parsed.module.units.is_empty(),
                    "{} parsed to an empty module",
                    path.display()
                );
            }
            Err(e) => panic!("{} failed to parse: {e}", path.display()),
        }
    }
    assert!(seen >= 4, "expected at least four corpus files, saw {seen}");
}

#[test]
fn cartesian_product_chains() {
    // `A \X B \X C` is a legal ternary product. Marking `\X` non-associative
    // rejected it, which is how this regression was found.
    let e = nixie_tla_syntax::parse_expr_str("A \\X B \\X C").expect("ternary product parses");
    assert!(matches!(
        e.kind,
        nixie_tla_syntax::ExprKind::Infix { ref op, .. } if op == "\\X"
    ));
}

#[test]
fn set_operators_still_may_not_be_mixed_unparenthesised() {
    // The flip side of the fix: `\cup` and `\cap` both sit at 8-8 and mixing
    // them without parentheses stays an error, as TLA+ requires.
    let err = nixie_tla_syntax::parse_expr_str("a \\cup b \\cap c")
        .map(|_| ())
        .unwrap_err();
    assert!(
        matches!(
            err.kind,
            nixie_tla_syntax::ErrorKind::PrecedenceConflict { .. }
        ),
        "got {:?}",
        err.kind
    );
    nixie_tla_syntax::parse_expr_str("(a \\cup b) \\cap c").expect("parenthesised form parses");
}
