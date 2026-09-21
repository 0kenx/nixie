//! Expression substitution and rendering for the PlusCal translator.
//!
//! The reference translator works on raw token vectors, substituting by
//! token string and parenthesising by token count. This port already has a
//! real expression AST — the same one the whole front end uses — so it
//! substitutes structurally instead: shadowing-aware for free names, and
//! with precedence handled by the printer rather than by counting tokens.
//!
//! Three substitutions exist, all from `PcalTLAGen` and `PcalFixIDs`:
//!
//! * **macro expansion** — `SubstituteInStmtSeq`, replacing a parameter by
//!   an argument expression, parenthesised when it is not atomic;
//! * **self-subscripting and priming** — `AddSubscriptsToExpr`, turning a
//!   process-local variable `v` into `v[self]` (or `v'` when the step has
//!   already assigned it, `v'[self]` when both);
//! * **renaming** — `PcalFixIDs.FixExpr`, rewriting a variable to its
//!   disambiguated name.
//!
//! All three descend through binders and stop at shadowed names, which the
//! token-level original cannot do. Every walk here is explicit-stack, per
//! the repository rule against unbounded recursion over user input.

use crate::ast::{
    Bound, CaseArm, ExceptSel, ExceptUpdate, Expr, ExprKind, Ident, OpDecl, Pattern, QualName,
    Unit, UnitKind,
};
use crate::op;
use crate::span::Span;
use std::collections::HashSet;

/// The variables assigned so far in the step being translated — the
/// reference's `Changed` object, reduced to the query the generator makes of
/// it ("has this variable been assigned yet?").
pub type Changed = HashSet<String>;

/// Whether an expression needs parentheses at a substitution site: anything
/// that is not a single token or a bracketed form.
fn is_atomic(e: &Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::Name(_)
            | ExprKind::Int { .. }
            | ExprKind::Real(_)
            | ExprKind::Str(_)
            | ExprKind::At
            | ExprKind::Tuple(_)
            | ExprKind::SetEnum(_)
            | ExprKind::RecordLit(_)
            | ExprKind::FnConstruct { .. }
            | ExprKind::FnSet { .. }
            | ExprKind::RecordSet(_)
    )
}

/// Rewrite `root`, replacing subexpressions per `f`.
///
/// `f` sees each subexpression and the set of names bound around it; a
/// `Some` return replaces the node wholesale. The walk is post-order over an
/// explicit stack: children are rebuilt bottom-up, so replacements compose.
fn rewrite<F>(root: &Expr, shadow: HashSet<String>, f: &F) -> Expr
where
    F: Fn(&Expr, &HashSet<String>) -> Option<Expr>,
{
    enum Task<'a> {
        Visit(&'a Expr, HashSet<String>),
        Build(&'a Expr, usize),
    }
    let mut tasks: Vec<Task<'_>> = vec![Task::Visit(root, shadow)];
    let mut done: Vec<Expr> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(e, sh) => {
                if let Some(replacement) = f(e, &sh) {
                    done.push(replacement);
                    continue;
                }
                let mark = done.len();
                tasks.push(Task::Build(e, mark));
                for (child, child_sh) in children_with_shadows(e, &sh).into_iter().rev() {
                    tasks.push(Task::Visit(child, child_sh));
                }
            }
            Task::Build(e, mark) => {
                let args: Vec<Expr> = done.drain(mark..).collect();
                done.push(rebuild(e, args));
            }
        }
    }
    done.pop().unwrap_or_else(|| root.clone())
}

/// The children of a node paired with the shadow set each is visited under.
///
/// Order matters: it is the order [`rebuild`] consumes them in.
fn children_with_shadows<'a>(
    e: &'a Expr,
    sh: &HashSet<String>,
) -> Vec<(&'a Expr, HashSet<String>)> {
    let plain = |c: &'a Expr| (c, sh.clone());
    match &e.kind {
        ExprKind::Name(_)
        | ExprKind::Int { .. }
        | ExprKind::Real(_)
        | ExprKind::Str(_)
        | ExprKind::At => Vec::new(),
        ExprKind::Paren(inner) => vec![plain(inner)],
        ExprKind::Apply { head: _, args } => args.iter().map(plain).collect(),
        ExprKind::FnApply { func, args } => {
            let mut v = vec![plain(func)];
            v.extend(args.iter().map(plain));
            v
        }
        ExprKind::Qualified { base, args, .. } => {
            let mut v = vec![plain(base)];
            v.extend(args.iter().map(plain));
            v
        }
        ExprKind::Field { record, .. } => vec![plain(record)],
        ExprKind::Prefix { operand, .. } | ExprKind::Postfix { operand, .. } => {
            vec![plain(operand)]
        }
        ExprKind::Infix { lhs, rhs, .. } => vec![plain(lhs), plain(rhs)],
        ExprKind::Junction { items, .. } => items.iter().map(plain).collect(),
        ExprKind::Quant { bounds, body, .. } => {
            let mut v: Vec<(&'a Expr, HashSet<String>)> = Vec::new();
            for b in bounds {
                v.push(plain(&b.domain));
            }
            v.push((body, shadow_extend(sh, &bound_names(bounds))));
            v
        }
        ExprKind::UnboundedQuant { vars, body, .. } => {
            let inner: HashSet<String> = sh
                .iter()
                .cloned()
                .chain(vars.iter().map(|v| v.name.clone()))
                .collect();
            vec![(body, inner)]
        }
        ExprKind::Choose {
            pattern,
            domain,
            body,
        } => {
            let mut v: Vec<(&'a Expr, HashSet<String>)> = Vec::new();
            if let Some(d) = domain {
                v.push(plain(d));
            }
            let inner = shadow_extend(sh, &pattern_names(pattern));
            v.push((body, inner));
            v
        }
        ExprKind::SetFilter {
            pattern,
            domain,
            pred,
        } => vec![
            plain(domain),
            (pred, shadow_extend(sh, &pattern_names(pattern))),
        ],
        ExprKind::SetMap { expr, bounds } => {
            let mut v: Vec<(&'a Expr, HashSet<String>)> = Vec::new();
            for b in bounds {
                v.push(plain(&b.domain));
            }
            v.push((expr, shadow_extend(sh, &bound_names(bounds))));
            v
        }
        ExprKind::Tuple(items) | ExprKind::SetEnum(items) => items.iter().map(plain).collect(),
        ExprKind::FnConstruct { bounds, body } => {
            let mut v: Vec<(&'a Expr, HashSet<String>)> = Vec::new();
            for b in bounds {
                v.push(plain(&b.domain));
            }
            v.push((body, shadow_extend(sh, &bound_names(bounds))));
            v
        }
        ExprKind::FnSet { domain, codomain } => vec![plain(domain), plain(codomain)],
        ExprKind::RecordLit(fields) | ExprKind::RecordSet(fields) => {
            fields.iter().map(|(_, v)| plain(v)).collect()
        }
        ExprKind::Except { base, updates } => {
            let mut v: Vec<(&'a Expr, HashSet<String>)> = vec![plain(base)];
            for u in updates {
                for sel in &u.path {
                    if let ExceptSel::Index(ix) = sel {
                        for e in ix {
                            v.push(plain(e));
                        }
                    }
                }
                v.push(plain(&u.value));
            }
            v
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            vec![plain(cond), plain(then_branch), plain(else_branch)]
        }
        ExprKind::Case { arms, other } => {
            let mut v: Vec<(&'a Expr, HashSet<String>)> = Vec::new();
            for a in arms {
                v.push(plain(&a.guard));
                v.push(plain(&a.value));
            }
            if let Some(o) = other {
                v.push(plain(o));
            }
            v
        }
        ExprKind::Let { defs, body } => {
            // LET definitions see the outer scope shadowed by every
            // definition's own parameters; the body additionally sees every
            // definition's name. The conservative choice (all definition
            // names shadow everywhere inside) only declines to rename under
            // a genuine name collision, which the token-level reference
            // would have mis-substituted anyway.
            let mut v: Vec<(&'a Expr, HashSet<String>)> = Vec::new();
            let mut all: Vec<String> = Vec::new();
            for u in defs {
                match &u.kind {
                    UnitKind::OpDef { params, body, .. } => {
                        let mut inner = sh.clone();
                        for p in params {
                            inner.insert(p.name.name.clone());
                        }
                        v.push((body, inner));
                        all.push(def_name(u).unwrap_or_default());
                    }
                    UnitKind::FnDef { bounds, body, .. } => {
                        let mut inner = sh.clone();
                        for b in bounds {
                            inner.extend(bound_names(std::slice::from_ref(b)));
                        }
                        v.push((body, inner));
                        all.push(def_name(u).unwrap_or_default());
                    }
                    _ => {}
                }
            }
            let body_sh = shadow_extend(sh, &all);
            v.push((body, body_sh));
            v
        }
        ExprKind::Action {
            body, subscript, ..
        }
        | ExprKind::Fairness {
            body, subscript, ..
        } => {
            vec![plain(body), plain(subscript)]
        }
        ExprKind::Lambda { params, body } => {
            let names: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            vec![(body, shadow_extend(sh, &names))]
        }
        ExprKind::Label { params, body, .. } => {
            let names: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            vec![(body, shadow_extend(sh, &names))]
        }
        ExprKind::AssumeProve { assumptions, goal } => {
            let mut v: Vec<(&'a Expr, HashSet<String>)> = Vec::new();
            for a in assumptions {
                if let crate::ast::AssumeItem::Expr(e) = a {
                    v.push(plain(e));
                }
            }
            v.push(plain(goal));
            v
        }
    }
}

fn shadow_extend(sh: &HashSet<String>, names: &[String]) -> HashSet<String> {
    sh.iter().cloned().chain(names.iter().cloned()).collect()
}

fn bound_names(bounds: &[Bound]) -> Vec<String> {
    let mut out = Vec::new();
    for b in bounds {
        for p in &b.patterns {
            out.extend(pattern_names(p));
        }
    }
    out
}

fn pattern_names(p: &Pattern) -> Vec<String> {
    match p {
        Pattern::Name(n) => vec![n.name.clone()],
        Pattern::Tuple(ids) => ids.iter().map(|i| i.name.clone()).collect(),
    }
}

fn def_name(u: &Unit) -> Option<String> {
    match &u.kind {
        UnitKind::OpDef { name, .. } | UnitKind::FnDef { name, .. } => Some(name.name.clone()),
        _ => None,
    }
}

/// Rebuild a combinator node from rewritten children, consuming `args` in
/// the order [`children_with_shadows`] produced them.
fn rebuild(e: &Expr, mut args: Vec<Expr>) -> Expr {
    let kind = match &e.kind {
        ExprKind::Name(_)
        | ExprKind::Int { .. }
        | ExprKind::Real(_)
        | ExprKind::Str(_)
        | ExprKind::At => e.kind.clone(),
        ExprKind::Apply { head, .. } => ExprKind::Apply {
            head: head.clone(),
            args: std::mem::take(&mut args),
        },
        ExprKind::FnApply { .. } => ExprKind::FnApply {
            func: Box::new(args.remove(0)),
            args: std::mem::take(&mut args),
        },
        ExprKind::Qualified { selector, .. } => ExprKind::Qualified {
            base: Box::new(args.remove(0)),
            selector: selector.clone(),
            args: std::mem::take(&mut args),
        },
        ExprKind::Field { field, .. } => ExprKind::Field {
            record: Box::new(args.remove(0)),
            field: field.clone(),
        },
        ExprKind::Prefix { op, op_span, .. } => ExprKind::Prefix {
            op: op.clone(),
            op_span: *op_span,
            operand: Box::new(args.remove(0)),
        },
        ExprKind::Postfix { op, op_span, .. } => ExprKind::Postfix {
            op: op.clone(),
            op_span: *op_span,
            operand: Box::new(args.remove(0)),
        },
        ExprKind::Infix { op, op_span, .. } => ExprKind::Infix {
            op: op.clone(),
            op_span: *op_span,
            lhs: Box::new(args.remove(0)),
            rhs: Box::new(args.remove(0)),
        },
        ExprKind::Junction { kind, .. } => ExprKind::Junction {
            kind: *kind,
            items: std::mem::take(&mut args),
        },
        ExprKind::Quant { kind, bounds, .. } => {
            let bounds = rebuild_bounds(bounds, &mut args);
            ExprKind::Quant {
                kind: *kind,
                bounds,
                body: Box::new(args.remove(0)),
            }
        }
        ExprKind::UnboundedQuant { kind, vars, .. } => ExprKind::UnboundedQuant {
            kind: *kind,
            vars: vars.clone(),
            body: Box::new(args.remove(0)),
        },
        ExprKind::Choose {
            pattern, domain, ..
        } => {
            let d = domain.as_ref().map(|_| Box::new(args.remove(0)));
            ExprKind::Choose {
                pattern: pattern.clone(),
                domain: d,
                body: Box::new(args.remove(0)),
            }
        }
        ExprKind::SetFilter { pattern, .. } => ExprKind::SetFilter {
            pattern: pattern.clone(),
            domain: Box::new(args.remove(0)),
            pred: Box::new(args.remove(0)),
        },
        ExprKind::SetMap { bounds, .. } => {
            let bounds = rebuild_bounds(bounds, &mut args);
            ExprKind::SetMap {
                bounds,
                expr: Box::new(args.remove(0)),
            }
        }
        ExprKind::Tuple(_) => ExprKind::Tuple(std::mem::take(&mut args)),
        ExprKind::SetEnum(_) => ExprKind::SetEnum(std::mem::take(&mut args)),
        ExprKind::FnConstruct { bounds, .. } => {
            let bounds = rebuild_bounds(bounds, &mut args);
            ExprKind::FnConstruct {
                bounds,
                body: Box::new(args.remove(0)),
            }
        }
        ExprKind::FnSet { .. } => ExprKind::FnSet {
            domain: Box::new(args.remove(0)),
            codomain: Box::new(args.remove(0)),
        },
        ExprKind::RecordLit(fields) => ExprKind::RecordLit(
            fields
                .iter()
                .map(|(n, _)| (n.clone(), args.remove(0)))
                .collect(),
        ),
        ExprKind::RecordSet(fields) => ExprKind::RecordSet(
            fields
                .iter()
                .map(|(n, _)| (n.clone(), args.remove(0)))
                .collect(),
        ),
        ExprKind::Except { updates, .. } => {
            let base = args.remove(0);
            let mut new_updates = Vec::new();
            for u in updates {
                let path = u
                    .path
                    .iter()
                    .map(|sel| match sel {
                        ExceptSel::Index(ix) => {
                            ExceptSel::Index(ix.iter().map(|_| args.remove(0)).collect())
                        }
                        ExceptSel::Field(f) => ExceptSel::Field(f.clone()),
                    })
                    .collect();
                new_updates.push(ExceptUpdate {
                    path,
                    value: args.remove(0),
                });
            }
            ExprKind::Except {
                base: Box::new(base),
                updates: new_updates,
            }
        }
        ExprKind::If { .. } => ExprKind::If {
            cond: Box::new(args.remove(0)),
            then_branch: Box::new(args.remove(0)),
            else_branch: Box::new(args.remove(0)),
        },
        ExprKind::Case { other, .. } => {
            let CaseParts { arms, other_val } = case_parts(e, &mut args);
            let _ = other;
            ExprKind::Case {
                arms,
                other: other_val,
            }
        }
        ExprKind::Let { defs, .. } => {
            let mut new_defs = defs.clone();
            let mut i = 0;
            while i < new_defs.len() {
                let u = &mut new_defs[i];
                match &mut u.kind {
                    UnitKind::OpDef { body, .. } | UnitKind::FnDef { body, .. } => {
                        *body = args.remove(0);
                    }
                    _ => {}
                }
                i += 1;
            }
            ExprKind::Let {
                defs: new_defs,
                body: Box::new(args.remove(0)),
            }
        }
        ExprKind::Action { kind, .. } => ExprKind::Action {
            kind: *kind,
            body: Box::new(args.remove(0)),
            subscript: Box::new(args.remove(0)),
        },
        ExprKind::Fairness { kind, .. } => ExprKind::Fairness {
            kind: *kind,
            subscript: Box::new(args.remove(0)),
            body: Box::new(args.remove(0)),
        },
        ExprKind::Lambda { params, .. } => ExprKind::Lambda {
            params: params.clone(),
            body: Box::new(args.remove(0)),
        },
        ExprKind::Label { name, params, .. } => ExprKind::Label {
            name: name.clone(),
            params: params.clone(),
            body: Box::new(args.remove(0)),
        },
        ExprKind::AssumeProve { assumptions, .. } => {
            let mut new_assumptions = Vec::new();
            for a in assumptions {
                match a {
                    crate::ast::AssumeItem::Expr(_) => {
                        new_assumptions.push(crate::ast::AssumeItem::Expr(args.remove(0)));
                    }
                    other => new_assumptions.push(other.clone()),
                }
            }
            ExprKind::AssumeProve {
                assumptions: new_assumptions,
                goal: Box::new(args.remove(0)),
            }
        }
        ExprKind::Paren(_) => ExprKind::Paren(Box::new(args.remove(0))),
    };
    Expr { kind, span: e.span }
}

struct CaseParts {
    arms: Vec<CaseArm>,
    other_val: Option<Box<Expr>>,
}

fn case_parts(e: &Expr, args: &mut Vec<Expr>) -> CaseParts {
    let ExprKind::Case { arms, other } = &e.kind else {
        return CaseParts {
            arms: Vec::new(),
            other_val: None,
        };
    };
    let mut new_arms = Vec::new();
    for _ in arms {
        let guard = args.remove(0);
        let value = args.remove(0);
        new_arms.push(CaseArm { guard, value });
    }
    let other_val = other.as_ref().map(|_| Box::new(args.remove(0)));
    CaseParts {
        arms: new_arms,
        other_val,
    }
}

/// Rebuild bound groups, consuming one rewritten domain per group from
/// `args` (in the order [`children_with_shadows`] emitted them).
fn rebuild_bounds(bounds: &[Bound], args: &mut Vec<Expr>) -> Vec<Bound> {
    bounds
        .iter()
        .map(|b| Bound {
            patterns: b.patterns.clone(),
            domain: args.remove(0),
        })
        .collect()
}

/// Substitute `replacement` for free occurrences of `name` in `expr`.
///
/// Shadowing-aware: an occurrence under a binder of the same name is left
/// alone. Non-atomic replacements are parenthesised, as the reference's
/// `substituteForAll` does.
#[must_use]
pub fn subst_free(expr: &Expr, name: &str, replacement: &Expr) -> Expr {
    rewrite(expr, HashSet::new(), &|e, sh| {
        if let ExprKind::Name(q) = &e.kind
            && !q.is_qualified()
            && q.base().map(|b| b.name.as_str()) == Some(name)
            && !sh.contains(name)
        {
            Some(if is_atomic(replacement) {
                replacement.clone()
            } else {
                Expr {
                    kind: ExprKind::Paren(Box::new(replacement.clone())),
                    span: replacement.span,
                }
            })
        } else {
            None
        }
    })
}

/// Rewrite process-local variable reads and already-assigned variable reads
/// in one pass — `AddSubscriptsToExpr`.
///
/// * `sub` is the `self` expression (or the single-process id); `None` in a
///   uniprocess algorithm.
/// * `self_vars` are the names that take the `[self]` subscript: process-set
///   and procedure variables, and `pc`, which the explosion introduces as an
///   added token exactly as the reference does.
/// * `changed` are the variables already assigned in this step, whose reads
///   become primed.
#[must_use]
pub fn self_and_prime(
    expr: &Expr,
    sub: Option<&Expr>,
    self_vars: &HashSet<String>,
    changed: &Changed,
) -> Expr {
    rewrite(expr, HashSet::new(), &|e, sh| {
        let ExprKind::Name(q) = &e.kind else {
            return None;
        };
        if q.is_qualified() {
            return None;
        }
        let base = q.base()?;
        let name = base.name.as_str();
        if sh.contains(name) {
            return None;
        }
        let prime = changed.contains(name);
        let takes_sub = sub.is_some() && self_vars.contains(name);
        if !prime && !takes_sub {
            return None;
        }
        let var = Expr {
            kind: ExprKind::Name(q.clone()),
            span: e.span,
        };
        let primed = if prime {
            Expr {
                kind: ExprKind::Postfix {
                    op: "'".into(),
                    op_span: e.span,
                    operand: Box::new(var),
                },
                span: e.span,
            }
        } else {
            var
        };
        if takes_sub {
            let Some(sub_expr) = sub else {
                unreachable!("takes_sub implies sub")
            };
            Some(Expr {
                kind: ExprKind::FnApply {
                    func: Box::new(primed),
                    args: vec![sub_expr.clone()],
                },
                span: e.span,
            })
        } else {
            Some(primed)
        }
    })
}

/// Rename variables per the disambiguated symbol table — `FixExpr`. Only
/// free occurrences are renamed; binders shadow as usual.
#[must_use]
pub fn rename_vars(expr: &Expr, map: &dyn Fn(&str) -> Option<String>) -> Expr {
    rewrite(expr, HashSet::new(), &|e, sh| {
        if let ExprKind::Name(q) = &e.kind
            && !q.is_qualified()
            && let Some(base) = q.base()
            && !sh.contains(base.name.as_str())
            && let Some(new) = map(base.name.as_str())
            && new != base.name
        {
            let mut nq = q.clone();
            if let Some(last) = nq.path.last_mut() {
                last.name = new;
            }
            Some(Expr {
                kind: ExprKind::Name(nq),
                span: e.span,
            })
        } else {
            None
        }
    })
}

// ---- rendering -----------------------------------------------------------

/// Render an expression back to TLA+ source, precedence-faithfully.
#[must_use]
pub fn render(e: &Expr) -> String {
    let mut s = String::new();
    render_at(e, 0, &mut s);
    s
}

/// Render `e` where it must bind at least `min_bp` (see [`render_at`]).
pub(super) fn render_at_min(e: &Expr, min_bp: u8, out: &mut String) {
    render_at(e, min_bp, out);
}

/// Render `e` where it must bind at least `min_bp`.
fn render_at(e: &Expr, min_bp: u8, out: &mut String) {
    match &e.kind {
        ExprKind::Name(q) => {
            let parts: Vec<&str> = q.path.iter().map(|i| i.name.as_str()).collect();
            out.push_str(&parts.join("!"));
        }
        ExprKind::Int { base, digits } => {
            out.push_str(num_base_prefix(base));
            out.push_str(digits);
        }
        ExprKind::Real(r) => out.push_str(r),
        ExprKind::Str(s) => {
            out.push('"');
            for c in s.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\t' => out.push_str("\\t"),
                    '\n' => out.push_str("\\n"),
                    '\r' => out.push_str("\\r"),
                    '\u{c}' => out.push_str("\\f"),
                    other => out.push(other),
                }
            }
            out.push('"');
        }
        ExprKind::Apply { head, args } => {
            let parts: Vec<String> = head.path.iter().map(|i| i.name.clone()).collect();
            out.push_str(&parts.join("!"));
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_at(a, 0, out);
            }
            out.push(')');
        }
        ExprKind::FnApply { func, args } => {
            render_postfix_operand(func, out);
            out.push('[');
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_at(a, 0, out);
            }
            out.push(']');
        }
        ExprKind::Qualified {
            base,
            selector,
            args,
        } => {
            render_postfix_operand(base, out);
            out.push('!');
            out.push_str(&selector.name);
            if !args.is_empty() {
                out.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    render_at(a, 0, out);
                }
                out.push(')');
            }
        }
        ExprKind::Field { record, field } => {
            render_postfix_operand(record, out);
            out.push('.');
            out.push_str(&field.name);
        }
        ExprKind::Prefix { op, operand, .. } => {
            let info = op::prefix_info(op);
            let need = info.is_none_or(|i| i.lo < min_bp);
            if need {
                out.push('(');
            }
            // The AST spells unary minus `-.` so it cannot be confused
            // with subtraction; the source spelling is a bare `-`.
            if op == "-." {
                out.push('-');
            } else {
                out.push_str(op);
                out.push(' ');
            }
            render_at(operand, info.map_or(0, |i| i.lo), out);
            if need {
                out.push(')');
            }
        }
        ExprKind::Infix { op, lhs, rhs, .. } => {
            let info = op::infix_info(op);
            let need = info.is_none_or(|i| i.lo < min_bp);
            if need {
                out.push('(');
            }
            let lo = info.map_or(0, |i| i.lo);
            render_at(lhs, lo, out);
            out.push(' ');
            out.push_str(op);
            out.push(' ');
            render_at(rhs, lo + 1, out);
            if need {
                out.push(')');
            }
        }
        ExprKind::Postfix { op, operand, .. } => {
            let info = op::postfix_info(op);
            let need = info.is_none_or(|i| i.lo < min_bp);
            if need {
                out.push('(');
            }
            render_postfix_operand(operand, out);
            out.push_str(op);
            if need {
                out.push(')');
            }
        }
        ExprKind::Junction { kind, items } => {
            // A junction binds loosely; parenthesise unless at the top.
            if min_bp > 0 {
                out.push('(');
            }
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                    out.push_str(kind.as_str());
                    out.push(' ');
                }
                // A conjunction item inside a disjunction (or vice versa)
                // must be parenthesised: their precedence intervals overlap.
                let nested_other = matches!(
                    &item.kind,
                    ExprKind::Junction { kind: k, .. } if *k != *kind
                );
                if nested_other {
                    out.push('(');
                    render_at(item, 0, out);
                    out.push(')');
                } else {
                    render_at(item, 0, out);
                }
            }
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::Quant { kind, bounds, body } => {
            if min_bp > 0 {
                out.push('(');
            }
            out.push_str(quant_spell(*kind));
            out.push(' ');
            render_bound_list(bounds, out);
            out.push_str(" : ");
            render_at(body, 0, out);
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::UnboundedQuant { kind, vars, body } => {
            if min_bp > 0 {
                out.push('(');
            }
            out.push_str(quant_spell(*kind));
            out.push(' ');
            let names: Vec<&str> = vars.iter().map(|v| v.name.as_str()).collect();
            out.push_str(&names.join(", "));
            out.push_str(" : ");
            render_at(body, 0, out);
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::Choose {
            pattern,
            domain,
            body,
        } => {
            if min_bp > 0 {
                out.push('(');
            }
            out.push_str("CHOOSE ");
            out.push_str(&pattern_text(pattern));
            if let Some(d) = domain {
                out.push_str(" \\in ");
                render_at(d, 0, out);
            }
            out.push_str(" : ");
            render_at(body, 0, out);
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::SetEnum(items) => {
            out.push('{');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_at(item, 0, out);
            }
            out.push('}');
        }
        ExprKind::SetFilter {
            pattern,
            domain,
            pred,
        } => {
            out.push('{');
            out.push_str(&pattern_text(pattern));
            out.push_str(" \\in ");
            render_at(domain, 0, out);
            out.push_str(" : ");
            render_at(pred, 0, out);
            out.push('}');
        }
        ExprKind::SetMap { expr, bounds } => {
            out.push('{');
            render_at(expr, 0, out);
            out.push_str(" : ");
            render_bound_list(bounds, out);
            out.push('}');
        }
        ExprKind::Tuple(items) => {
            out.push_str("<<");
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                render_at(item, 0, out);
            }
            out.push_str(">>");
        }
        ExprKind::FnConstruct { bounds, body } => {
            out.push('[');
            render_bound_list(bounds, out);
            out.push_str(" |-> ");
            render_at(body, 0, out);
            out.push(']');
        }
        ExprKind::FnSet { domain, codomain } => {
            out.push('[');
            render_at(domain, 0, out);
            out.push_str(" -> ");
            render_at(codomain, 0, out);
            out.push(']');
        }
        ExprKind::RecordLit(fields) => {
            out.push('[');
            for (i, (n, v)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&n.name);
                out.push_str(" |-> ");
                render_at(v, 0, out);
            }
            out.push(']');
        }
        ExprKind::RecordSet(fields) => {
            out.push('[');
            for (i, (n, v)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&n.name);
                out.push_str(" : ");
                render_at(v, 0, out);
            }
            out.push(']');
        }
        ExprKind::Except { base, updates } => {
            out.push('[');
            render_at(base, 0, out);
            out.push_str(" EXCEPT ");
            for (i, u) in updates.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push('!');
                for sel in &u.path {
                    match sel {
                        ExceptSel::Index(ix) => {
                            out.push('[');
                            for (k, e) in ix.iter().enumerate() {
                                if k > 0 {
                                    out.push_str(", ");
                                }
                                render_at(e, 0, out);
                            }
                            out.push(']');
                        }
                        ExceptSel::Field(f) => {
                            out.push('.');
                            out.push_str(&f.name);
                        }
                    }
                }
                out.push_str(" = ");
                render_at(&u.value, 0, out);
            }
            out.push(']');
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            if min_bp > 0 {
                out.push('(');
            }
            out.push_str("IF ");
            // A conjunction/disjunction as a test must be parenthesised:
            // written inline it reads as another bullet of whatever junction
            // list the `IF` itself sits in, and the intervals overlap.
            if matches!(cond.kind, ExprKind::Junction { .. })
                || matches!(&cond.kind, ExprKind::Infix { op, .. } if op == "/\\" || op == "\\>")
            {
                out.push('(');
                render_at(cond, 0, out);
                out.push(')');
            } else {
                render_at(cond, 0, out);
            }
            out.push_str(" THEN ");
            render_at(then_branch, 0, out);
            out.push_str(" ELSE ");
            render_at(else_branch, 0, out);
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::Case { arms, other } => {
            if min_bp > 0 {
                out.push('(');
            }
            out.push_str("CASE ");
            for (i, a) in arms.iter().enumerate() {
                if i > 0 {
                    out.push_str(" [] ");
                }
                render_at(&a.guard, 0, out);
                out.push_str(" -> ");
                render_at(&a.value, 0, out);
            }
            if let Some(o) = other {
                out.push_str(" [] OTHER -> ");
                render_at(o, 0, out);
            }
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::Let { defs, body } => {
            if min_bp > 0 {
                out.push('(');
            }
            out.push_str("LET ");
            for (i, u) in defs.iter().enumerate() {
                if i > 0 {
                    out.push(' ');
                }
                out.push_str(&render_unit(u));
            }
            out.push_str(" IN ");
            render_at(body, 0, out);
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::Action {
            kind,
            body,
            subscript,
        } => {
            match kind {
                crate::ast::ActionKind::Stuttering => out.push('['),
                crate::ast::ActionKind::NonStuttering => out.push_str("<<"),
            }
            render_at(body, 0, out);
            match kind {
                crate::ast::ActionKind::Stuttering => out.push(']'),
                crate::ast::ActionKind::NonStuttering => out.push_str(">>"),
            }
            out.push('_');
            render_postfix_operand(subscript, out);
        }
        ExprKind::Fairness {
            kind,
            subscript,
            body,
        } => {
            out.push_str(match kind {
                crate::ast::FairnessKind::Weak => "WF_",
                crate::ast::FairnessKind::Strong => "SF_",
            });
            render_postfix_operand(subscript, out);
            out.push('(');
            render_at(body, 0, out);
            out.push(')');
        }
        ExprKind::Lambda { params, body } => {
            if min_bp > 0 {
                out.push('(');
            }
            out.push_str("LAMBDA ");
            let names: Vec<&str> = params.iter().map(|p| p.name.as_str()).collect();
            out.push_str(&names.join(", "));
            out.push_str(" : ");
            render_at(body, 0, out);
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::Label { name, params, body } => {
            if min_bp > 0 {
                out.push('(');
            }
            out.push_str(&name.name);
            if !params.is_empty() {
                out.push('(');
                let names: Vec<&str> = params.iter().map(|p| p.name.as_str()).collect();
                out.push_str(&names.join(", "));
                out.push(')');
            }
            out.push_str(" :: ");
            render_at(body, 0, out);
            if min_bp > 0 {
                out.push(')');
            }
        }
        ExprKind::At => out.push('@'),
        ExprKind::AssumeProve { .. } => out.push_str("TRUE"),
        ExprKind::Paren(inner) => {
            out.push('(');
            render_at(inner, 0, out);
            out.push(')');
        }
    }
}

/// An operand of a construct that binds tighter than every operator: needs
/// parentheses unless it is itself atomic or postfix-shaped.
fn render_postfix_operand(e: &Expr, out: &mut String) {
    let plain = matches!(
        e.kind,
        ExprKind::Name(_)
            | ExprKind::Int { .. }
            | ExprKind::Real(_)
            | ExprKind::Str(_)
            | ExprKind::At
            | ExprKind::FnApply { .. }
            | ExprKind::Field { .. }
            | ExprKind::Postfix { .. }
            | ExprKind::Tuple(_)
            | ExprKind::Paren(_)
    );
    if plain {
        render_at(e, 0, out);
    } else {
        out.push('(');
        render_at(e, 0, out);
        out.push(')');
    }
}

fn quant_spell(kind: crate::ast::QuantKind) -> &'static str {
    use crate::ast::QuantKind as Q;
    match kind {
        Q::Forall => "\\A",
        Q::Exists => "\\E",
        Q::TemporalForall => "\\AA",
        Q::TemporalExists => "\\EE",
    }
}

fn num_base_prefix(base: &crate::token::NumBase) -> &'static str {
    use crate::token::NumBase as B;
    match base {
        B::Decimal => "",
        B::Binary => "\\b",
        B::Octal => "\\o",
        B::Hex => "\\h",
    }
}

fn render_bound_list(bounds: &[Bound], out: &mut String) {
    for (i, b) in bounds.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        for (j, p) in b.patterns.iter().enumerate() {
            if j > 0 {
                out.push_str(", ");
            }
            out.push_str(&pattern_text(p));
        }
        out.push_str(" \\in ");
        render_at(&b.domain, 0, out);
    }
}

fn pattern_text(p: &Pattern) -> String {
    match p {
        Pattern::Name(n) => n.name.clone(),
        Pattern::Tuple(ids) => {
            let names: Vec<&str> = ids.iter().map(|i| i.name.as_str()).collect();
            format!("<<{}>>", names.join(", "))
        }
    }
}

fn render_unit(u: &Unit) -> String {
    let mut s = String::new();
    match &u.kind {
        UnitKind::OpDef {
            name, params, body, ..
        } => {
            s.push_str(&name.name);
            if !params.is_empty() {
                s.push('(');
                let ps: Vec<&str> = params.iter().map(|p| p.name.name.as_str()).collect();
                s.push_str(&ps.join(", "));
                s.push(')');
            }
            s.push_str(" == ");
            s.push_str(&render(body));
        }
        UnitKind::FnDef {
            name, bounds, body, ..
        } => {
            s.push_str(&name.name);
            s.push('[');
            render_bound_list(bounds, &mut s);
            s.push_str("] == ");
            s.push_str(&render(body));
        }
        _ => {}
    }
    s
}

/// Construct a name expression, for the pieces the translator synthesises.
#[must_use]
pub fn name_expr(name: &str, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Name(QualName {
            path: vec![Ident {
                name: name.to_string(),
                span,
            }],
            span,
        }),
        span,
    }
}

/// Construct an infix application, for the pieces the translator synthesises.
#[must_use]
pub fn infix_expr(op: &str, lhs: Expr, rhs: Expr, span: Span) -> Expr {
    Expr {
        kind: ExprKind::Infix {
            op: op.to_string(),
            op_span: span,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
        span,
    }
}

/// The parameter names of an operator declaration list.
#[must_use]
pub fn decl_param_names(decls: &[OpDecl]) -> Vec<String> {
    decls.iter().map(|d| d.name.name.clone()).collect()
}

/// Whether the word is a PlusCal statement keyword — the set
/// `Tokenize.IsDelimiter` uses, plus the declaration words.
#[must_use]
pub fn is_pcal_keyword(word: &str) -> bool {
    matches!(
        word,
        "if" | "then"
            | "else"
            | "elsif"
            | "either"
            | "or"
            | "end"
            | "while"
            | "do"
            | "with"
            | "when"
            | "await"
            | "skip"
            | "call"
            | "return"
            | "goto"
            | "print"
            | "assert"
            | "begin"
            | "variable"
            | "variables"
            | "define"
            | "macro"
            | "macros"
            | "procedure"
            | "process"
            | "fair"
            | "algorithm"
    )
}
