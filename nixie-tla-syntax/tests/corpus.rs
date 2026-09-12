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

/// Acceptance over the external TLA+ corpora, when they are checked out.
///
/// `AGENTS.md` keeps reference material in sibling directories, read-only:
///
/// ```text
/// ../temp/tlaplus-examples   github.com/tlaplus/Examples
/// ../temp/apalache           github.com/apalache-mc/apalache
/// ```
///
/// Together those are ~900 `.tla` files and are the real acceptance gate from
/// `docs/TLA_FRONTEND_DESIGN.md` §5 — every construct the parser now handles
/// beyond the basics was found by running them. The test **skips** when the
/// checkouts are absent, so it never fails a clean clone of this repo.
///
/// It asserts a *floor* rather than an exact count, because the corpora are
/// upstream repositories that move. Two files are expected to fail and should
/// stay failing: `FoldDefined.tla` writes `==` where `EXCEPT` requires `=`,
/// and `test30-true.tla` writes `=` where a definition requires `==`. Both are
/// invalid TLA+ that SANY rejects too.
#[test]
fn external_corpora_acceptance_rate() {
    const CORPORA: &[&str] = &[
        concat!(env!("CARGO_MANIFEST_DIR"), "/../../temp/tlaplus-examples"),
        concat!(env!("CARGO_MANIFEST_DIR"), "/../../temp/apalache"),
    ];
    /// Accept at least this fraction. Measured at 905/907 = 99.78%.
    const FLOOR: f64 = 0.995;

    let mut files = Vec::new();
    for root in CORPORA {
        collect_tla(Path::new(root), &mut files);
    }
    if files.len() < 100 {
        eprintln!(
            "skipping: external TLA+ corpora not checked out (found {} files)",
            files.len()
        );
        return;
    }

    let mut failures = Vec::new();
    let mut level_errors = Vec::new();
    for path in &files {
        let Ok(src) = std::fs::read_to_string(path) else {
            continue;
        };
        match nixie_tla_syntax::parse_file(&src) {
            Err(e) => failures.push(format!("{}: {e}", path.display())),
            Ok(parsed) => {
                // The level checker's contract is that it never rejects a
                // correct specification. These are overwhelmingly correct
                // specifications, so any violation reported here is a false
                // positive until proven otherwise.
                let report = nixie_tla_syntax::check_module(&parsed.module);
                for e in report.errors {
                    level_errors.push(format!("{}: {e}", path.display()));
                }
            }
        }
    }
    for e in level_errors.iter().take(20) {
        eprintln!("  level: {e}");
    }
    assert!(
        level_errors.is_empty(),
        "{} level violations reported on real specifications; \
         the checker must not reject correct input",
        level_errors.len()
    );
    let accepted = files.len() - failures.len();
    let rate = accepted as f64 / files.len() as f64;
    for f in failures.iter().take(20) {
        eprintln!("  reject: {f}");
    }
    assert!(
        rate >= FLOOR,
        "acceptance {accepted}/{} = {rate:.4} fell below the {FLOOR} floor",
        files.len()
    );
}

fn collect_tla(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_tla(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("tla") {
            out.push(path);
        }
    }
}
