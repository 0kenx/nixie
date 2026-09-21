//! The PlusCal translator: `(* --algorithm … *)` to plain TLA+.
//!
//! PlusCal bodies are TLA+ *comments*, which is why a TLA+ front end can
//! parse every PlusCal specification and never see the algorithm: the
//! comment scanner skips it. This module is the missing layer — the piece
//! three handoffs have carried as "the PlusCal wall".
//!
//! The reference is `tla2tools`' `pcal` package (consulted as source, never
//! linked — the same relationship `bench/z3_parity` has to Z3). The
//! pipeline mirrors its phases exactly, because the label-placement rules
//! *are* the semantics and each phase decides part of them:
//!
//! 1. [`extract`] — find the algorithm comment.
//! 2. [`parse`] — the grammar, macro expansion included, over the front
//!    end's own TLA+ token stream.
//! 3. [`labels`] — required-label insertion, then the split into labeled
//!    clusters (one cluster = one atomic step) and the `pc`-elision check.
//! 4. [`symtab`] — name disambiguation and renaming.
//! 5. [`explode`] — control flow (`while`, labeled `if`/`either`, `goto`)
//!    becomes `pc` guards and updates.
//! 6. `emit` — the TLA+ text: `VARIABLES`, `vars`, `ProcSet`, `Init`, one
//!    action per cluster, `Next`, `Terminating`, `Spec`.
//!
//! The output is ordinary TLA+ text placed in a `BEGIN/END TRANSLATION`
//! region exactly where `pcal.trans` puts it, so every downstream consumer
//! — SANY, TLC, the parity harnesses, the BMC checker — reads it unchanged.
//!
//! Constructs outside the corpus-sized subset are **declined with a named
//! error**, never approximated: `procedure`/`call`/`return` (the stack
//! machine), and any grammar violation the reference rejects. A wrong
//! translation of an algorithm is worse than no translation.

pub mod ast;
pub mod emit;
pub mod explode;
pub mod extract;
pub mod labels;
pub mod parse;
pub mod subst;
pub mod symtab;

use crate::error::{ErrorKind, Result, SyntaxError};
use crate::span::Span;
use std::collections::HashSet;

/// The result of translating a file.
#[derive(Debug, Clone)]
pub struct Translation {
    /// The complete output file: the original with the translation region
    /// inserted or replaced.
    pub text: String,
    /// Whether an existing translation region was replaced (rather than a
    /// new one inserted after the algorithm).
    pub replaced: bool,
}

/// Translate the PlusCal algorithm in a TLA+ source file.
///
/// # Errors
///
/// A [`SyntaxError`] naming the first construct this translator does not
/// implement or the first grammar violation — never a guess.
pub fn translate_file(src: &str) -> Result<Translation> {
    let found = extract::find_algorithm(src)?;
    let mut parsed = parse::parse(&found)?;

    // Procedures: parsed, declined. The stack machine they need is a
    // stateful encoding this subset does not carry; a partial one would be
    // a silent wrong answer.
    if !parsed.alg.procedures().is_empty() {
        return Err(SyntaxError::new(
            ErrorKind::Unsupported {
                construct: "PlusCal procedure".into(),
                note: "procedures (call/return with the stack variable) are not translated \
                       yet; nothing in the corpus uses them"
                    .into(),
            },
            found.comment,
        ));
    }

    // The label pass, per body. Uniprocess bodies share one pc elision;
    // multiprocess ORs the stuttering elision across processes (matching
    // the reference's quirk, documented at `checkBody`).
    let mut omit_pc = !parsed.force_pc && !parsed.goto_used;
    let mut omit_stuttering;
    let mut labeled_bodies: Vec<Vec<ast::LabeledStmt>> = Vec::new();
    let label_set: HashSet<String> = parsed.all_labels.iter().cloned().collect();
    match &mut parsed.alg {
        ast::Algorithm::Uniprocess { body, .. } => {
            let added = labels::add_labels(body, &label_set);
            reject_added(&added, parsed.has_label, &found)?;
            let split = labels::split(std::mem::take(body))?;
            let (o_pc, o_st) = labels::check_body(&split);
            omit_pc = omit_pc && o_pc && !parsed.goto_done_used;
            omit_stuttering = o_st && !parsed.goto_done_used;
            labeled_bodies.push(split);
        }
        ast::Algorithm::Multiprocess { processes, .. } => {
            omit_stuttering = false;
            for p in processes.iter_mut() {
                let added = labels::add_labels(&mut p.body, &label_set);
                reject_added(&added, true, &found)?;
                let split = labels::split(std::mem::take(&mut p.body))?;
                let (o_pc, o_st) = labels::check_body(&split);
                omit_pc = omit_pc && o_pc;
                omit_stuttering = omit_stuttering || o_st;
                labeled_bodies.push(split);
            }
            omit_pc = omit_pc && !parsed.goto_done_used;
            omit_stuttering = omit_stuttering && !parsed.goto_done_used;
        }
    }

    // Disambiguation and renaming, then explosion, on the labeled form.
    let mut labeled = parsed.alg.labeled(labeled_bodies);
    let tab = symtab::SymTab::build(&labeled)?;
    symtab::fix(&mut labeled, &tab);
    match &mut labeled {
        ast::LabeledAlgorithm::Uniprocess { body, .. } => {
            *body = explode::explode(body, omit_pc);
        }
        ast::LabeledAlgorithm::Multiprocess { processes, .. } => {
            for p in processes.iter_mut() {
                p.body = explode::explode(&p.body, omit_pc);
            }
        }
    }

    let input = emit::GenInput {
        alg: &labeled,
        tab: &tab,
        omit_pc,
        omit_stuttering,
        has_default_init: parsed.has_default_initialization,
        fair_algorithm: parsed.fair_algorithm,
    };
    let region = emit::generate(&input);

    let (text, replaced) = splice(src, &found, &region);
    Ok(Translation { text, replaced })
}

/// Auto-inserted labels are an error, matching the reference's default
/// (`-label` off): they change what the atomic steps are.
fn reject_added(added: &[String], strict: bool, found: &extract::Found) -> Result<()> {
    if added.is_empty() {
        return Ok(());
    }
    if !strict {
        // Uniprocess, no user labels at all: the reference adds silently.
        return Ok(());
    }
    Err(SyntaxError::new(
        ErrorKind::Unsupported {
            construct: "PlusCal algorithm".into(),
            note: labels_note(added),
        },
        found.comment,
    ))
}

fn labels_note(added: &[String]) -> String {
    if added.len() > 1 {
        format!(
            "missing labels where the grammar requires them ({}); the reference translator \
             rejects these by default too",
            added.join(", ")
        )
    } else {
        "a missing label where the grammar requires one; the reference \
         translator rejects this by default too"
            .into()
    }
}

/// Insert `region` into `src` between BEGIN/END TRANSLATION markers,
/// replacing any existing region, or insert a new one after the algorithm
/// comment.
fn splice(src: &str, found: &extract::Found, region: &str) -> (String, bool) {
    let lines: Vec<&str> = src.lines().collect();
    // `findTokenPair`: a line containing the two tokens `BEGIN` and
    // `TRANSLATION` — `\*`, `\**` and Toolbox variants all match.
    let marker = |l: &str, word: &str| {
        let t = l.trim_start().trim_start_matches(['\\', '*']).trim_start();
        t.starts_with(word)
    };
    let begin_line = lines.iter().position(|l| marker(l, "BEGIN TRANSLATION"));
    if let Some(b) = begin_line {
        let end_line = lines
            .iter()
            .skip(b + 1)
            .position(|l| marker(l, "END TRANSLATION"))
            .map(|e| e + b + 1);
        let e = end_line.unwrap_or(b);
        let mut out = String::new();
        for l in &lines[..b] {
            out.push_str(l);
            out.push('\n');
        }
        out.push_str(
            "\\* BEGIN TRANSLATION (chksum(pcal) \\in STRING /\\ chksum(tla) \\in STRING)\n",
        );
        out.push_str(region);
        out.push_str("\\* END TRANSLATION\n");
        for l in &lines[e + 1..] {
            out.push_str(l);
            out.push('\n');
        }
        return (out, true);
    }
    // New region right after the algorithm's comment ends.
    let insert_at = found.comment.end.line as usize;
    let mut out = String::new();
    for (i, l) in lines.iter().enumerate() {
        out.push_str(l);
        out.push('\n');
        if i + 1 == insert_at {
            out.push('\n');
            out.push_str(
                "\\* BEGIN TRANSLATION (chksum(pcal) \\in STRING /\\ chksum(tla) \\in STRING)\n",
            );
            out.push_str(region);
            out.push_str("\\* END TRANSLATION\n");
        }
    }
    if lines.len() < insert_at {
        // The comment ends at the last line; append.
        out.push('\n');
        out.push_str(
            "\\* BEGIN TRANSLATION (chksum(pcal) \\in STRING /\\ chksum(tla) \\in STRING)\n",
        );
        out.push_str(region);
        out.push_str("\\* END TRANSLATION\n");
    }
    (out, false)
}

/// The span helper used above, re-exported for the module's diagnostics.
#[allow(dead_code)]
fn _span() -> Span {
    Span::default()
}
