//! Control-flow explosion — the pass that turns labeled clusters into flat
//! next-state actions (`PcalTranslate.Explode`).
//!
//! `while`, a labeled `if`/`either`, and `goto` are all control flow the
//! TLA+ translation expresses through the `pc` variable. This pass removes
//! them from the tree:
//!
//! * a `while` becomes a guard `pc = "L"` and an `IF` whose branches update
//!   `pc` — back to the loop head, into the body's first label, or out of
//!   the loop;
//! * a labeled `if` becomes an `IF` whose branches each end in a `pc` update
//!   toward their own first labels, with the labeled clusters lifted out as
//!   sibling actions;
//! * a `goto L` becomes `pc := "L"`.
//!
//! When `pc` is elided (`while TRUE` bodies with no labels inside), the
//! guards and updates disappear and the cluster's action is simply its body
//! — which is why the elision decision is made before this pass runs.

use super::ast::*;
use crate::ast::{Expr, ExprKind};
use crate::span::Span;

/// Explode one body (a process or the uniprocess algorithm).
#[must_use]
pub fn explode(body: &[LabeledStmt], omit_pc: bool) -> Vec<LabeledStmt> {
    let mut out = Vec::new();
    for (i, ls) in body.iter().enumerate() {
        let next = body
            .get(i + 1)
            .map_or_else(|| "Done".to_string(), |n| n.label.clone());
        out.extend(explode_labeled(ls, &next, omit_pc));
    }
    out
}

/// `ExplodeLabeledStmt`.
fn explode_labeled(ls: &LabeledStmt, next: &str, omit_pc: bool) -> Vec<LabeledStmt> {
    if let Some(FlatStmt::While { .. }) = ls.stmts.first() {
        return explode_while(ls, next, omit_pc);
    }
    let (stmts, lifted) = with_goto(&ls.stmts, next, omit_pc);
    let mut stmts = stmts;
    if !omit_pc {
        stmts.insert(0, FlatStmt::When(pc_check(&ls.label)));
    }
    let mut out = vec![LabeledStmt {
        label: ls.label.clone(),
        stmts,
    }];
    out.extend(lifted);
    out
}

/// `ExplodeWhile`.
fn explode_while(ls: &LabeledStmt, next: &str, omit_pc: bool) -> Vec<LabeledStmt> {
    let FlatStmt::While {
        test,
        unlab_do,
        lab_do,
    } = &ls.stmts[0]
    else {
        unreachable!("checked by the caller");
    };
    let rest: Vec<FlatStmt> = ls.stmts[1..].to_vec();
    let mut stmts: Vec<FlatStmt> = Vec::new();
    if !omit_pc {
        stmts.push(FlatStmt::When(pc_check(&ls.label)));
    }
    let unlab_next = lab_do
        .first()
        .map_or_else(|| ls.label.clone(), |f| f.label.clone());
    let (then_stmts, then_lifted) = with_goto(unlab_do, &unlab_next, omit_pc);
    let (else_stmts, else_lifted) = with_goto(&rest, next, omit_pc);
    if is_true(test) {
        stmts.extend(then_stmts);
    } else {
        stmts.push(FlatStmt::If {
            test: test.clone(),
            then: then_stmts,
            els: else_stmts,
        });
    }
    let mut out = vec![LabeledStmt {
        label: ls.label.clone(),
        stmts,
    }];
    for (i, sub) in lab_do.iter().enumerate() {
        let sub_next = lab_do
            .get(i + 1)
            .map_or_else(|| ls.label.clone(), |n| n.label.clone());
        out.extend(explode_labeled(sub, &sub_next, omit_pc));
    }
    out.extend(then_lifted);
    if !is_true(test) {
        out.extend(else_lifted);
    }
    out
}

/// The result of exploding a statement sequence at its last statement:
/// the statements that stay in the enclosing cluster, the labeled clusters
/// lifted out of it, and whether the sequence still needs an explicit `pc`
/// transfer to `next`.
struct Exploded {
    stays: Vec<FlatStmt>,
    lifted: Vec<LabeledStmt>,
    needs_goto: bool,
}

/// `CopyAndExplodeLastStmt` + the goto-appending wrapper.
fn with_goto(stmts: &[FlatStmt], next: &str, omit_pc: bool) -> (Vec<FlatStmt>, Vec<LabeledStmt>) {
    let mut e = copy_and_explode_last(stmts, next, omit_pc);
    if e.needs_goto {
        e.stays.push(pc_update(next));
    }
    (e.stays, e.lifted)
}

fn copy_and_explode_last(stmts: &[FlatStmt], next: &str, omit_pc: bool) -> Exploded {
    if stmts.is_empty() {
        return Exploded {
            stays: Vec::new(),
            lifted: Vec::new(),
            needs_goto: true,
        };
    }
    let (head, last) = stmts.split_at(stmts.len() - 1);
    let mut stays: Vec<FlatStmt> = head.to_vec();
    let mut lifted: Vec<LabeledStmt> = Vec::new();
    #[allow(unused_assignments)]
    let mut needs_goto: bool = true;
    match &last[0] {
        FlatStmt::Goto(to) => {
            stays.push(pc_update(to));
            needs_goto = false;
        }
        FlatStmt::LabelIf {
            test,
            then_unlab,
            then_lab,
            els_unlab,
            els_lab,
        } => {
            let then_next = then_lab
                .first()
                .map_or_else(|| next.to_string(), |f| f.label.clone());
            let els_next = els_lab
                .first()
                .map_or_else(|| next.to_string(), |f| f.label.clone());
            let (tn, tl) = with_goto(then_unlab, &then_next, omit_pc);
            let (en, el) = with_goto(els_unlab, &els_next, omit_pc);
            stays.push(FlatStmt::If {
                test: test.clone(),
                then: tn,
                els: en,
            });
            let mut lift = Vec::new();
            lift.extend(explode_seq(then_lab, next, omit_pc));
            lift.extend(explode_seq(els_lab, next, omit_pc));
            lift.extend(tl);
            lift.extend(el);
            lifted = lift;
            needs_goto = false;
        }
        FlatStmt::LabelEither { clauses } => {
            // `ExplodeLabelEither` always appends the `pc` transfer to every
            // clause: the clause's own labeled part continues elsewhere.
            let mut ors: Vec<Vec<FlatStmt>> = Vec::new();
            let mut lift = Vec::new();
            for (unlab, lab) in clauses {
                let lab_next = lab
                    .first()
                    .map_or_else(|| next.to_string(), |f| f.label.clone());
                let (cn, cl) = with_goto(unlab, &lab_next, omit_pc);
                ors.push(cn);
                lift.extend(cl);
                lift.extend(explode_seq(lab, next, omit_pc));
            }
            stays.push(FlatStmt::Either { ors });
            lifted = lift;
            needs_goto = false;
        }
        FlatStmt::If { test, then, els } => {
            let t = copy_and_explode_last(then, next, omit_pc);
            let e = copy_and_explode_last(els, next, omit_pc);
            let mut tn = t.stays;
            let mut en = e.stays;
            let then_needs = t.needs_goto;
            let else_needs = e.needs_goto;
            let ng = then_needs && else_needs;
            if !ng {
                if then_needs {
                    tn.push(pc_update(next));
                }
                if else_needs {
                    en.push(pc_update(next));
                }
            }
            stays.push(FlatStmt::If {
                test: test.clone(),
                then: tn,
                els: en,
            });
            let mut lift = t.lifted;
            lift.extend(e.lifted);
            lifted = lift;
            needs_goto = ng;
        }
        FlatStmt::Either { ors } => {
            let mut new_ors: Vec<Vec<FlatStmt>> = Vec::new();
            let mut lift = Vec::new();
            let mut all_need = true;
            let mut clause_need = Vec::new();
            for or in ors {
                let c = copy_and_explode_last(or, next, omit_pc);
                clause_need.push(c.needs_goto);
                all_need = all_need && c.needs_goto;
                new_ors.push(c.stays);
                lift.extend(c.lifted);
            }
            if !all_need {
                for (or, needs) in new_ors.iter_mut().zip(&clause_need) {
                    if *needs {
                        or.push(pc_update(next));
                    }
                }
            }
            stays.push(FlatStmt::Either { ors: new_ors });
            lifted = lift;
            needs_goto = all_need;
        }
        FlatStmt::With {
            var,
            is_eq,
            exp,
            body,
        } => {
            let inner = copy_and_explode_last(body, next, omit_pc);
            let mut inner_stays = inner.stays;
            if inner.needs_goto {
                inner_stays.push(pc_update(next));
            }
            stays.push(FlatStmt::With {
                var: var.clone(),
                is_eq: *is_eq,
                exp: exp.clone(),
                body: inner_stays,
            });
            lifted = inner.lifted;
            needs_goto = false;
        }
        FlatStmt::Assign(_)
        | FlatStmt::When(_)
        | FlatStmt::Print(_)
        | FlatStmt::Assert(_)
        | FlatStmt::Skip => {
            stays.push(last[0].clone());
            needs_goto = true;
        }
        FlatStmt::While { .. } => {
            // A `while` is always the first statement of its cluster, so it
            // is never the *last* statement of an exploded sequence; a
            // single-statement while cluster is handled by `explode_labeled`.
            // Reaching this arm means the grammar was violated upstream.
            stays.push(last[0].clone());
            needs_goto = true;
        }
    }
    Exploded {
        stays,
        lifted,
        needs_goto: needs_goto && !omit_pc,
    }
}

/// `ExplodeLabeledStmtSeq`.
fn explode_seq(seq: &[LabeledStmt], next: &str, omit_pc: bool) -> Vec<LabeledStmt> {
    let mut out = Vec::new();
    for (i, ls) in seq.iter().enumerate() {
        let n = seq
            .get(i + 1)
            .map_or_else(|| next.to_string(), |x| x.label.clone());
        out.extend(explode_labeled(ls, &n, omit_pc));
    }
    out
}

/// `CheckPC`: the `pc = "L"` guard, later self-subscripted like any process
/// variable read.
fn pc_check(label: &str) -> Expr {
    super::subst::infix_expr(
        "=",
        super::subst::name_expr("pc", Span::default()),
        Expr {
            kind: ExprKind::Str(label.to_string()),
            span: Span::default(),
        },
        Span::default(),
    )
}

/// `UpdatePC`: the `pc := "L"` assignment.
fn pc_update(next: &str) -> FlatStmt {
    FlatStmt::Assign(vec![SingleAssign {
        var: "pc".to_string(),
        sels: Vec::new(),
        rhs: Expr {
            kind: ExprKind::Str(next.to_string()),
            span: Span::default(),
        },
    }])
}

fn is_true(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Name(q) if q.path.len() == 1 && q.path[0].name == "TRUE")
}
