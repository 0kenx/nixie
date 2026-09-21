//! Label placement — the pass that decides what a PlusCal *step* is.
//!
//! Everything a specification claims depends on this: a statement cluster
//! between labels is one atomic step, and the same variable may not be
//! assigned twice inside one. This module is a direct port of the three
//! `ParseAlgorithm` passes that establish it, in their order:
//!
//! 1. [`add_labels`] — `InnerAddLabels`: insert the labels the grammar
//!    requires (`while`, statements after `goto`/`call`/`return`, and a
//!    second assignment to a variable already assigned in the step) and
//!    reject the placements the grammar forbids (a label inside `with`).
//!    Like the reference's default options, auto-insertion is an **error**,
//!    not a service: a label the author did not write changes what the
//!    atomic steps are, and a silent one is a silent wrong answer.
//! 2. [`split`] — `MakeLabeledStmtSeq` + `FixStmtSeq` + `ClassifyStmtSeq`:
//!    cut the statement sequence into [`LabeledStmt`] clusters, and inside
//!    every branch keep the unlabeled prefix (part of the enclosing step)
//!    apart from the labeled remainder (its own steps).
//! 3. [`check_body`] — `checkBody`: whether the whole body is one
//!    `while TRUE` cluster with no labels inside, the one shape whose `pc`
//!    and `Terminating` the reference generator elides.

use super::ast::*;
use crate::error::{ErrorKind, Result, SyntaxError};
use crate::span::Span;
use std::collections::HashSet;

/// Why the label pass rejected an algorithm.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LabelError {
    /// A label was inserted that the author did not write.
    Missing(Vec<String>),
    /// A construct the grammar forbids, at a location.
    Forbidden(String, Span),
}

impl LabelError {
    /// The diagnostic rendering.
    #[must_use]
    pub fn message(&self) -> String {
        match self {
            Self::Missing(locs) => {
                if locs.len() > 1 {
                    format!("missing labels at: {}", locs.join(", "))
                } else {
                    format!("missing label at: {}", locs[0])
                }
            }
            Self::Forbidden(what, span) => format!("{span}: {what}"),
        }
    }
}

fn err(what: impl Into<String>, span: Span) -> SyntaxError {
    SyntaxError::new(
        ErrorKind::Unsupported {
            construct: "PlusCal algorithm".into(),
            note: what.into(),
        },
        span,
    )
}

/// Insert required labels into a statement sequence.
///
/// Returns the labels it would have inserted; by the reference's default
/// policy (no `-label` flag) the caller treats a non-empty result as an
/// error.
pub fn add_labels(stmts: &mut [Stmt], all_labels: &HashSet<String>) -> Vec<String> {
    let mut ctx = Ctx {
        next_label_num: 1,
        all_labels: all_labels.clone(),
        added: Vec::new(),
    };
    let mut out_assigned = Vec::new();
    inner_add_labels(stmts, true, false, Vec::new(), &mut out_assigned, &mut ctx);
    ctx.added
}

struct Ctx {
    next_label_num: usize,
    all_labels: HashSet<String>,
    added: Vec<String>,
}

impl Ctx {
    /// `NeedsLabel`: label a statement that has none, using the `Lbl_N`
    /// root and skipping the labels the author already used.
    fn needs_label(&mut self, stmt: &mut Stmt) {
        if stmt.lbl().is_none() {
            let mut n = self.next_label_num;
            let mut lbl = format!("Lbl_{n}");
            while self.all_labels.contains(&lbl) {
                n += 1;
                lbl = format!("Lbl_{n}");
            }
            self.next_label_num = n + 1;
            *stmt.lbl_mut() = Some(lbl.clone());
            self.all_labels.insert(lbl.clone());
            self.added.push(lbl);
        }
    }
}

/// `InnerAddLabels`. Returns `had_or_added_label || next_step_needs_label`.
fn inner_add_labels(
    stmts: &mut [Stmt],
    first_labeled: bool,
    in_with: bool,
    in_assigned: Vec<String>,
    out_assigned: &mut Vec<String>,
    ctx: &mut Ctx,
) -> bool {
    *out_assigned = in_assigned.clone();
    let mut next_needs_label = first_labeled;
    let mut had_or_added = false;
    for stmt in stmts.iter_mut() {
        if stmt.lbl().is_some() {
            had_or_added = true;
            out_assigned.clear();
            if in_with {
                // The location is lost in this port; the construct names it.
                ctx.added_label_in_with();
            }
        }
        // Every statement arm below assigns `next_needs_label` before the
        // loop can read it again, so no reset is needed here.
        let this_step_needs_label = next_needs_label;
        if this_step_needs_label {
            if in_with {
                ctx.added_label_in_with();
            }
            ctx.needs_label(stmt);
            had_or_added = true;
            out_assigned.clear();
        }
        match stmt {
            Stmt::If { then, els, .. } => {
                let mut then_assigned = Vec::new();
                let mut els_assigned = Vec::new();
                let r1 = inner_add_labels(
                    then,
                    false,
                    in_with,
                    out_assigned.clone(),
                    &mut then_assigned,
                    ctx,
                );
                let r2 = inner_add_labels(
                    els,
                    false,
                    in_with,
                    out_assigned.clone(),
                    &mut els_assigned,
                    ctx,
                );
                next_needs_label = r1 || r2;
                union_into(out_assigned, &then_assigned);
                union_into(out_assigned, &els_assigned);
            }
            Stmt::Either { ors, .. } => {
                let mut any = false;
                let mut union = Vec::new();
                for or in ors.iter_mut() {
                    let mut or_assigned = Vec::new();
                    let r = inner_add_labels(
                        or,
                        false,
                        in_with,
                        out_assigned.clone(),
                        &mut or_assigned,
                        ctx,
                    );
                    any = any || r;
                    union_into(&mut union, &or_assigned);
                }
                next_needs_label = any;
                *out_assigned = union;
            }
            Stmt::While { .. } => {
                if in_with {
                    ctx.while_in_with();
                }
                ctx.needs_label(stmt);
                had_or_added = true;
                out_assigned.clear();
                next_needs_label = false;
                // `stmt` is fully borrowed by `needs_label`; re-match to
                // reach the body afterwards.
                if let Stmt::While { unlab_do, .. } = stmt {
                    let mut ignored = Vec::new();
                    inner_add_labels(unlab_do, false, false, Vec::new(), &mut ignored, ctx);
                }
            }
            Stmt::With { body, .. } => {
                let new_in = if in_with {
                    in_assigned.clone()
                } else {
                    Vec::new()
                };
                let mut new_out = Vec::new();
                next_needs_label = inner_add_labels(body, false, true, new_in, &mut new_out, ctx);
                *out_assigned = new_out.clone();
                if !in_with && !disjoint(&in_assigned, &new_out) {
                    ctx.needs_label(stmt);
                    had_or_added = true;
                    out_assigned.clear();
                }
            }
            Stmt::Assign { ass, .. } => {
                let assigned: Vec<String> = ass.iter().map(|a| a.var.clone()).collect();
                if disjoint(out_assigned, &assigned) {
                    union_into(out_assigned, &assigned);
                } else {
                    ctx.needs_label(stmt);
                    had_or_added = true;
                    *out_assigned = assigned;
                }
                next_needs_label = false;
            }
            Stmt::Goto { .. } => {
                next_needs_label = true;
            }
            Stmt::Call { .. } | Stmt::Return { .. } => {
                next_needs_label = true;
                // A call assigns the stack; without procedure support the
                // conservative set is the name itself, which no variable can
                // collide with (declined later in translation).
                let assigned = vec!["stack".to_string()];
                if disjoint(out_assigned, &assigned) {
                    union_into(out_assigned, &assigned);
                } else {
                    ctx.needs_label(stmt);
                    had_or_added = true;
                    *out_assigned = assigned;
                }
            }
            Stmt::When { .. } | Stmt::Print { .. } | Stmt::Assert { .. } | Stmt::Skip { .. } => {
                next_needs_label = false;
            }
            Stmt::MacroCall { .. } => unreachable!("macros are expanded during parsing"),
        }
    }
    had_or_added || next_needs_label
}

impl Ctx {
    fn added_label_in_with(&mut self) {
        if self.added.is_empty() || !self.added.iter().any(|l| l.starts_with("in with")) {
            self.added
                .push("a label inside a `with' statement (forbidden)".into());
        }
    }

    fn while_in_with(&mut self) {
        self.added
            .push("a `while' inside a `with' statement (forbidden)".into());
    }
}

fn disjoint(a: &[String], b: &[String]) -> bool {
    a.iter().all(|x| !b.iter().any(|y| x == y))
}

fn union_into(target: &mut Vec<String>, from: &[String]) {
    for x in from {
        if !target.iter().any(|y| y == x) {
            target.push(x.clone());
        }
    }
}

// ---- splitting ------------------------------------------------------------

/// Cut a labeled statement sequence into clusters, splitting branch bodies
/// into their unlabeled prefixes and labeled remainders.
///
/// # Errors
///
/// A [`SyntaxError`] when a cluster would be empty or a statement sequence
/// begins without a label.
pub fn split(stmts: Vec<Stmt>) -> Result<Vec<LabeledStmt>> {
    let mut out = Vec::new();
    let mut i = 0;
    let first = stmts.first().ok_or_else(|| {
        err(
            "an empty statement sequence where a labeled one is required",
            Span::default(),
        )
    })?;
    if first.lbl().is_none() {
        return Err(err(
            "a statement sequence must begin with a labeled statement",
            Span::default(),
        ));
    }
    while i < stmts.len() {
        let label = stmts[i].lbl().clone().unwrap_or_default();
        let mut cluster: Vec<Stmt> = Vec::new();
        let mut first_in = true;
        while i < stmts.len() && (first_in || stmts[i].lbl().is_none()) {
            first_in = false;
            cluster.push(stmts[i].clone());
            i += 1;
        }
        if cluster.is_empty() {
            return Err(err("an empty labeled statement", Span::default()));
        }
        out.push(LabeledStmt {
            label,
            stmts: flatten_all(cluster)?,
        });
    }
    Ok(out)
}

fn flatten_all(stmts: Vec<Stmt>) -> Result<Vec<FlatStmt>> {
    stmts.into_iter().map(flatten).collect()
}

/// `FixStmtSeq` + `ClassifyStmtSeq` for one statement.
fn flatten(stmt: Stmt) -> Result<FlatStmt> {
    Ok(match stmt {
        Stmt::Assign { ass, .. } => FlatStmt::Assign(ass),
        Stmt::When { exp, .. } => FlatStmt::When(exp),
        Stmt::Print { exp, .. } => FlatStmt::Print(exp),
        Stmt::Assert { exp, .. } => FlatStmt::Assert(exp),
        Stmt::Skip { .. } => FlatStmt::Skip,
        Stmt::Goto { to, .. } => FlatStmt::Goto(to),
        Stmt::Call { to, .. } => {
            return Err(err(
                format!("a `call' of procedure `{to}' (procedures are not translated)"),
                Span::default(),
            ));
        }
        Stmt::Return { .. } => {
            return Err(err(
                "`return' outside a procedure is not translated",
                Span::default(),
            ));
        }
        Stmt::MacroCall { .. } => unreachable!("macros are expanded during parsing"),
        Stmt::With {
            var,
            is_eq,
            exp,
            body,
            ..
        } => FlatStmt::With {
            var,
            is_eq,
            exp,
            body: flatten_all(body)?,
        },
        Stmt::If {
            test, then, els, ..
        } => {
            let (then_unlab, then_lab) = branch(then)?;
            let (els_unlab, els_lab) = branch(els)?;
            if then_lab.is_empty() && els_lab.is_empty() {
                FlatStmt::If {
                    test,
                    then: then_unlab,
                    els: els_unlab,
                }
            } else {
                FlatStmt::LabelIf {
                    test,
                    then_unlab,
                    then_lab,
                    els_unlab,
                    els_lab,
                }
            }
        }
        Stmt::Either { ors, .. } => {
            let mut clauses = Vec::new();
            let mut any_lab = false;
            for or in ors {
                let (unlab, lab) = branch(or)?;
                any_lab = any_lab || !lab.is_empty();
                clauses.push((unlab, lab));
            }
            if any_lab {
                FlatStmt::LabelEither { clauses }
            } else {
                FlatStmt::Either {
                    ors: clauses.into_iter().map(|(u, _)| u).collect(),
                }
            }
        }
        Stmt::While { test, unlab_do, .. } => {
            let (unlab_flat, lab) = branch(unlab_do)?;
            FlatStmt::While {
                test,
                unlab_do: unlab_flat,
                lab_do: lab,
            }
        }
    })
}

/// Split a branch's statements into the unlabeled prefix and the labeled
/// remainder, and flatten both.
fn branch(mut stmts: Vec<Stmt>) -> Result<(Vec<FlatStmt>, Vec<LabeledStmt>)> {
    let mut prefix = Vec::new();
    let mut i = 0;
    while i < stmts.len() && stmts[i].lbl().is_none() {
        prefix.push(flatten(stmts[i].clone())?);
        i += 1;
    }
    let labeled = if i < stmts.len() {
        split(stmts.split_off(i))?
    } else {
        Vec::new()
    };
    Ok((prefix, labeled))
}

// ---- pc elision -------------------------------------------------------------

/// `checkBody`: whether `pc` (and `Terminating`) can be elided for this
/// body — true only for a single cluster that is exactly one `while TRUE`
/// with no labels inside.
#[must_use]
pub fn check_body(body: &[LabeledStmt]) -> (bool, bool) {
    // (omit_pc, omit_stuttering_when_done) — both start true and survive
    // only the narrowest shape.
    if body.len() != 1 || body[0].stmts.len() != 1 {
        return (false, false);
    }
    let FlatStmt::While {
        test,
        unlab_do,
        lab_do,
    } = &body[0].stmts[0]
    else {
        return (false, false);
    };
    let is_true = matches!(
        &test.kind,
        crate::ast::ExprKind::Name(q) if q.path.len() == 1 && q.path[0].name == "TRUE"
    );
    if !is_true {
        return (false, false);
    }
    let mut omit_pc = lab_do.is_empty();
    for s in unlab_do {
        if matches!(s, FlatStmt::LabelIf { .. } | FlatStmt::LabelEither { .. }) {
            omit_pc = false;
            break;
        }
    }
    (omit_pc, true)
}
