//! TLA+ generation — `PcalTLAGen`, reduced to the parts that carry meaning.
//!
//! Line wrapping is not reproduced: the reference formats to a 78-column
//! target with a hand-rolled wrapper, and parity is checked on parse, levels
//! and evaluated states, not on bytes. Everything that *is* reproduced is
//! semantic:
//!
//! * the `VARIABLES`/`vars`/`ProcSet`/`Init` skeleton, including the
//!   `pc`-first ordering and the `define`-block split between global and
//!   local variable declarations;
//! * the per-cluster actions — the `pc` guard, each statement's conjuncts
//!   with `EXCEPT`-based updates, self-subscripts on process-local
//!   variables, primes on variables the step has already assigned, and the
//!   `UNCHANGED` bookkeeping that closes each action and each branch;
//! * `Next`, `Terminating`, and `Spec` with the reference's fairness shape
//!   for `fair process` declarations and `--fair` algorithms.
//!
//! UNCHANGED placement follows `Changed`: an action conjunct-list closes
//! with every variable it never assigned; an `if` branch closes with the
//! variables the *other* branch assigned; an `either` clause with the union
//! of the others'.

use super::ast::*;
use super::subst::{self, Changed, render, render_at_min};
use crate::ast::Expr;
use crate::span::Span;
use std::collections::HashSet;

/// Everything the generator needs to know about the algorithm.
pub struct GenInput<'a> {
    /// The exploded algorithm.
    pub alg: &'a LabeledAlgorithm,
    /// The disambiguated symbol table.
    pub tab: &'a super::symtab::SymTab,
    /// Whether `pc` was elided.
    pub omit_pc: bool,
    /// Whether the `Terminating` disjunct was elided.
    pub omit_stuttering: bool,
    /// Whether any variable needs the `CONSTANT defaultInitValue` declaration.
    pub has_default_init: bool,
    /// Whether the algorithm was `--fair`.
    pub fair_algorithm: bool,
}

/// Generate the translation region: the text between the BEGIN/END
/// TRANSLATION markers.
#[must_use]
pub fn generate(input: &GenInput) -> String {
    let mut g = Gen {
        omit_pc: input.omit_pc,
        mp: matches!(input.alg, LabeledAlgorithm::Multiprocess { .. }),
        out: String::new(),
    };
    let globals = input.alg.decls().clone();
    let defs = input.alg.defs().cloned();
    // pcal 1.7.4 declares the globals first and `pc` (then `stack`) last —
    // the reverse ordering in current git master postdates the oracle.
    let mut g_vars: Vec<String> = Vec::new();
    for d in &globals {
        g_vars.push(d.var.clone());
    }
    if !input.omit_pc {
        g_vars.push("pc".to_string());
    }
    if g.mp && !input.alg.procedures().is_empty() {
        g_vars.push("stack".to_string());
    }
    let mut l_vars: Vec<String> = Vec::new();
    for p in input.alg.procedures() {
        for d in &p.params {
            l_vars.push(d.var.clone());
        }
        for d in &p.decls {
            l_vars.push(d.var.clone());
        }
    }
    if let LabeledAlgorithm::Multiprocess { processes, .. } = input.alg {
        for p in processes {
            for d in &p.decls {
                l_vars.push(d.var.clone());
            }
        }
    }
    // The self-subscript set: `pc`, `stack`, procedure variables, and the
    // variables of every process *set* (`psV`/`pcV` in the reference).
    let mut self_vars: HashSet<String> = HashSet::new();
    self_vars.insert("pc".to_string());
    self_vars.insert("stack".to_string());
    for v in input.tab.procedure_vars() {
        self_vars.insert(v);
    }
    if let LabeledAlgorithm::Multiprocess { processes, .. } = input.alg {
        for p in processes {
            if !p.is_eq {
                for d in &p.decls {
                    self_vars.insert(d.var.clone());
                }
            }
        }
    }
    let all_vars: Vec<String> = g_vars.iter().chain(l_vars.iter()).cloned().collect();

    for r in input.tab.reports() {
        g.line(r);
    }
    if input.has_default_init {
        g.line("CONSTANT defaultInitValue");
    }
    // With a `define` block, the reference splits the declarations around
    // it (globals, then the block, then locals); without one, a single
    // `VARIABLES` declares everything. Locals must be declared either way.
    if let Some(d) = &defs {
        g.var_decl(&g_vars);
        g.blank();
        g.line("(* define statement *)");
        for l in d.lines() {
            g.line(l);
        }
        g.var_decl(&l_vars);
    } else {
        let all: Vec<String> = g_vars.iter().chain(l_vars.iter()).cloned().collect();
        g.var_decl(&all);
    }
    g.blank();
    if all_vars.is_empty() {
        // The reference rejects an algorithm with no variables; mirror that
        // by refusing to invent one.
        g.line("\\* error: the algorithm has no variables");
        return g.out;
    }
    g.line(&format!("vars == << {} >>", all_vars.join(", ")));
    g.blank();
    if g.mp {
        // ProcSet: the union of every process's set (or singleton).
        let parts: Vec<String> = match input.alg {
            LabeledAlgorithm::Multiprocess { processes, .. } => processes
                .iter()
                .map(|p| {
                    let (open, close) = if p.is_eq { ("{", "}") } else { ("(", ")") };
                    format!("{open}{}{close}", render(&p.id))
                })
                .collect(),
            _ => Vec::new(),
        };
        g.line(&format!("ProcSet == {}", parts.join(" \\cup ")));
        g.blank();
    }
    g.init(input, &globals);
    match input.alg {
        LabeledAlgorithm::Uniprocess { body, .. } => {
            for ls in body {
                let name = if input.omit_pc {
                    "Next".to_string()
                } else {
                    ls.label.clone()
                };
                g.action(&name, ls, None, &self_vars, &all_vars, false);
            }
        }
        LabeledAlgorithm::Multiprocess { processes, .. } => {
            for p in processes {
                let self_expr = Some(if p.is_eq {
                    p.id.clone()
                } else {
                    subst::name_expr("self", Span::default())
                });
                // The action scope is the full `vars` list: process
                // variables are already in it.
                let scope: Vec<String> = all_vars.clone();
                let mut names: Vec<String> = Vec::new();
                for ls in &p.body {
                    let name = if input.omit_pc {
                        p.name.clone()
                    } else {
                        ls.label.clone()
                    };
                    if !names.contains(&name) {
                        names.push(name.clone());
                    }
                    if names.len() > 1 && input.omit_pc {
                        // With pc elided there is exactly one action; a
                        // second cluster contradicts the elision decision.
                    }
                    g.action(&name, ls, self_expr.as_ref(), &self_vars, &scope, !p.is_eq);
                }
                if !input.omit_pc {
                    let arg = if p.is_eq { "" } else { "(self)" };
                    let disjuncts = names
                        .iter()
                        .map(|n| format!("({n}{arg})"))
                        .collect::<Vec<_>>()
                        .join(" \\/ ");
                    g.line(&format!("{}{} == {}", p.name, arg, disjuncts));
                    g.blank();
                }
            }
        }
    }
    g.next(input);
    g.spec(input);
    g.termination(input);
    g.out
}

struct Gen {
    omit_pc: bool,
    mp: bool,
    out: String,
}

impl Gen {
    fn line(&mut self, s: &str) {
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn blank(&mut self) {
        self.out.push('\n');
    }

    fn var_decl(&mut self, names: &[String]) {
        if names.is_empty() {
            return;
        }
        let kw = if names.len() > 1 {
            "VARIABLES"
        } else {
            "VARIABLE"
        };
        self.line(&format!("{kw} {}", names.join(", ")));
    }

    // ---- Init ---------------------------------------------------------------

    fn init(&mut self, input: &GenInput, globals: &[VarDecl]) {
        let mut lines: Vec<String> = Vec::new();
        let prefix = "        ";
        if !globals.is_empty() {
            lines.push("Init == (* Global variables *)".into());
            for d in globals {
                lines.push(format!(
                    "{prefix}/\\ {} {} {}",
                    d.var,
                    if d.is_eq { "=" } else { "\\in" },
                    init_val(d)
                ));
            }
        } else {
            lines.push("Init == ".into());
        }
        if let LabeledAlgorithm::Multiprocess { processes, .. } = input.alg {
            for p in processes {
                if p.decls.is_empty() {
                    continue;
                }
                lines.push(format!("{prefix}(* Process {} *)", p.name));
                for d in &p.decls {
                    lines.push(format!("{prefix}/\\ {}", process_init(p, d)));
                }
            }
            if !input.omit_pc {
                if processes.len() > 1 {
                    let arms: Vec<String> = processes
                        .iter()
                        .map(|p| {
                            let cmp = if p.is_eq { "=" } else { "\\in" };
                            format!("self {cmp} {} -> \"{}\"", render(&p.id), first_label(p))
                        })
                        .collect();
                    lines.push(format!(
                        "{prefix}/\\ pc = [self \\in ProcSet |-> CASE {}]",
                        arms.join(" [] ")
                    ));
                } else if let Some(p) = processes.first() {
                    lines.push(format!(
                        "{prefix}/\\ pc = [self \\in ProcSet |-> \"{}\"]",
                        first_label(p)
                    ));
                }
            }
        } else if let LabeledAlgorithm::Uniprocess { body, .. } = input.alg
            && !input.omit_pc
        {
            let lbl = body
                .first()
                .map_or_else(|| "Done".to_string(), |b| b.label.clone());
            lines.push(format!("{prefix}/\\ pc = \"{lbl}\""));
        }
        for mut l in lines {
            if l.starts_with("Init ==") {
                l = l.trim_start().to_string();
            }
            self.line(&l);
        }
        self.blank();
    }

    // ---- actions --------------------------------------------------------------

    /// Emit one cluster's action definition.
    fn action(
        &mut self,
        name: &str,
        ls: &LabeledStmt,
        self_expr: Option<&Expr>,
        self_vars: &HashSet<String>,
        scope: &[String],
        takes_self_param: bool,
    ) {
        let header = format!("{name}{} == ", if takes_self_param { "(self)" } else { "" });
        let col = header.len() + 3;
        let mut changed: Changed = HashSet::new();
        let mut items: Vec<String> = Vec::new();
        for stmt in &ls.stmts {
            self.stmt(
                stmt,
                col,
                self_expr,
                self_vars,
                &mut changed,
                &mut items,
                scope,
            );
        }
        let unchanged: Vec<String> = scope
            .iter()
            .filter(|v| !changed.contains(*v))
            .cloned()
            .collect();
        if !unchanged.is_empty() {
            items.push(format!("UNCHANGED << {} >>", unchanged.join(", ")));
        }
        let mut out = String::new();
        if items.is_empty() {
            out.push_str(&header);
            out.push_str("TRUE");
        }
        for (i, item) in items.iter().enumerate() {
            if i == 0 {
                out.push_str(&header);
                out.push_str("/\\ ");
            } else {
                out.push('\n');
                out.push_str(&" ".repeat(header.len()));
                out.push_str("/\\ ");
            }
            append_item(&mut out, item, col);
        }
        self.line(&out);
        self.blank();
    }

    /// Append one conjunct (which may carry pre-aligned continuation lines).
    #[allow(clippy::too_many_arguments)] // the walk's invariant context, threaded as one
    fn stmt(
        &mut self,
        stmt: &FlatStmt,
        col: usize,
        self_expr: Option<&Expr>,
        self_vars: &HashSet<String>,
        changed: &mut Changed,
        items: &mut Vec<String>,
        scope: &[String],
    ) {
        match stmt {
            FlatStmt::Assign(ass) => {
                for group in group_assigns(ass, self_expr, self_vars, changed) {
                    items.push(group);
                }
            }
            FlatStmt::When(e) => {
                let e2 = subst::self_and_prime(e, self_expr, self_vars, changed);
                items.push(render_guard(&e2));
            }
            FlatStmt::Print(e) => {
                let e2 = subst::self_and_prime(e, self_expr, self_vars, changed);
                items.push(format!("PrintT({})", render(&e2)));
            }
            FlatStmt::Assert(e) => {
                let e2 = subst::self_and_prime(e, self_expr, self_vars, changed);
                items.push(format!(
                    "Assert({}, \"Failure of assertion.\")",
                    render(&e2)
                ));
            }
            FlatStmt::Skip => items.push("TRUE".into()),
            FlatStmt::With {
                var,
                is_eq,
                exp,
                body,
            } => {
                let e2 = subst::self_and_prime(exp, self_expr, self_vars, changed);
                let head = if *is_eq {
                    format!("LET {var} == {} IN", render(&e2))
                } else {
                    format!("\\E {var} \\in {} :", render(&e2))
                };
                let mut inner_items: Vec<String> = Vec::new();
                for s in body {
                    self.stmt(
                        s,
                        col + 2,
                        self_expr,
                        self_vars,
                        changed,
                        &mut inner_items,
                        scope,
                    );
                }
                let mut text = head;
                if inner_items.is_empty() {
                    text.push_str("TRUE");
                }
                for (i, item) in inner_items.iter().enumerate() {
                    text.push('\n');
                    text.push_str(&" ".repeat(col + 2));
                    if inner_items.len() > 1 || i > 0 {
                        text.push_str("/\\ ");
                    }
                    append_item(&mut text, item, col + 2);
                }
                items.push(text);
            }
            FlatStmt::If { test, then, els } => {
                let t2 = subst::self_and_prime(test, self_expr, self_vars, changed);
                let mut c_then = changed.clone();
                let mut c_els = changed.clone();
                let mut then_items =
                    self.stmt_items(then, col + 9, self_expr, self_vars, &mut c_then, scope);
                let mut els_items =
                    self.stmt_items(els, col + 9, self_expr, self_vars, &mut c_els, scope);
                let un_then: Vec<String> = scope
                    .iter()
                    .filter(|v| !c_then.contains(*v) && c_els.contains(*v))
                    .cloned()
                    .collect();
                let un_els: Vec<String> = scope
                    .iter()
                    .filter(|v| !c_els.contains(*v) && c_then.contains(v.as_str()))
                    .cloned()
                    .collect();
                if !un_then.is_empty() {
                    then_items.push(format!("UNCHANGED << {} >>", un_then.join(", ")));
                }
                if !un_els.is_empty() {
                    els_items.push(format!("UNCHANGED << {} >>", un_els.join(", ")));
                }
                if then_items.is_empty() {
                    then_items.push("TRUE".into());
                }
                if els_items.is_empty() {
                    els_items.push("TRUE".into());
                }
                let mut text = format!("IF {}", render(&t2));
                text.push_str(&branch_block("THEN", &then_items, col));
                text.push_str(&branch_block("ELSE", &els_items, col));
                items.push(text);
                changed.extend(c_then.iter().cloned());
                changed.extend(c_els.iter().cloned());
            }
            FlatStmt::Either { ors } => {
                let mut clause_items: Vec<Vec<String>> = Vec::new();
                let mut all_changed: Changed = HashSet::new();
                let mut per_clause: Vec<Changed> = Vec::new();
                for or in ors {
                    let mut c = changed.clone();
                    // Clause items sit at col+6, where their `//\` bullets are drawn;
                    // the statement renderers must agree or nested constructs
                    // (a `with` inside a clause) indent left of their binder.
                    let items = self.stmt_items(or, col + 6, self_expr, self_vars, &mut c, scope);
                    clause_items.push(items);
                    per_clause.push(c.clone());
                    all_changed.extend(c.iter().cloned());
                }
                let mut text = String::new();
                for (i, (items, c)) in clause_items.iter_mut().zip(&per_clause).enumerate() {
                    let un: Vec<String> = scope
                        .iter()
                        .filter(|v| !c.contains(*v) && all_changed.contains(*v))
                        .cloned()
                        .collect();
                    if !un.is_empty() {
                        items.push(format!("UNCHANGED << {} >>", un.join(", ")));
                    }
                    if items.is_empty() {
                        items.push("TRUE".into());
                    }
                    if i > 0 {
                        text.push('\n');
                        // One column right of every enclosing bullet: the
                        // disjunction's own list must nest strictly inside
                        // the conjunct list it appears in.
                        text.push_str(&" ".repeat(col + 3));
                    }
                    text.push_str("\\/ /\\ ");
                    for (j, item) in items.iter().enumerate() {
                        if j > 0 {
                            text.push('\n');
                            text.push_str(&" ".repeat(col + 6));
                            text.push_str("/\\ ");
                        }
                        append_item(&mut text, item, col + 6);
                    }
                }
                items.push(text);
                changed.extend(all_changed.iter().cloned());
            }
            FlatStmt::Goto { .. }
            | FlatStmt::While { .. }
            | FlatStmt::LabelIf { .. }
            | FlatStmt::LabelEither { .. } => {
                // All four are consumed by the explosion pass.
                unreachable!("explosion removes control flow before generation");
            }
        }
    }

    fn stmt_items(
        &mut self,
        stmts: &[FlatStmt],
        col: usize,
        self_expr: Option<&Expr>,
        self_vars: &HashSet<String>,
        changed: &mut Changed,
        scope: &[String],
    ) -> Vec<String> {
        let mut items = Vec::new();
        for s in stmts {
            self.stmt(s, col, self_expr, self_vars, changed, &mut items, scope);
        }
        items
    }

    // ---- Next / Terminating / Spec ---------------------------------------------

    fn next(&mut self, input: &GenInput) {
        if !self.mp && self.omit_pc {
            // Uniprocess with pc elided: the one action *is* `Next`.
            return;
        }
        let mut disjuncts: Vec<String> = Vec::new();
        if let LabeledAlgorithm::Uniprocess { body, .. } = input.alg {
            for ls in body {
                disjuncts.push(ls.label.clone());
            }
        } else if let LabeledAlgorithm::Multiprocess { processes, .. } = input.alg {
            for p in processes {
                if p.is_eq {
                    disjuncts.push(p.name.clone());
                } else {
                    disjuncts.push(format!(
                        "(\\E self \\in {} : {}(self))",
                        render(&p.id),
                        p.name
                    ));
                }
            }
        }
        if !input.omit_stuttering {
            self.line("(* Allow infinite stuttering to prevent deadlock on termination. *)");
            if self.mp {
                self.line("Terminating == /\\ \\A self \\in ProcSet : pc[self] = \"Done\"");
                self.line("               /\\ UNCHANGED vars");
            } else {
                self.line("Terminating == pc = \"Done\" /\\ UNCHANGED vars");
            }
            self.blank();
            disjuncts.push("Terminating".into());
        }
        self.line(&format!("Next == {}", disjuncts.join("\n           \\/ ")));
        self.blank();
    }

    fn spec(&mut self, input: &GenInput) {
        let safety = "Init /\\ [][Next]_vars";
        let mut conjuncts: Vec<String> = Vec::new();
        if input.fair_algorithm {
            conjuncts.push("WF_vars(Next)".into());
        }
        if let LabeledAlgorithm::Multiprocess { processes, .. } = input.alg {
            for p in processes {
                let Some(fairness) = fair_conjunct(p) else {
                    continue;
                };
                let prefix = if p.is_eq {
                    String::new()
                } else {
                    format!("\\A self \\in {} : ", render(&p.id))
                };
                conjuncts.push(format!("{prefix}{fairness}"));
            }
        }
        if conjuncts.is_empty() {
            self.line(&format!("Spec == {safety}"));
        } else {
            self.line(&format!("Spec == /\\ {safety}"));
            for c in conjuncts {
                self.line(&format!("        /\\ {c}"));
            }
        }
        self.blank();
    }

    /// `GenTermination` — elided exactly when the Terminating action was.
    fn termination(&mut self, input: &GenInput) {
        if input.omit_pc || input.omit_stuttering {
            return;
        }
        if self.mp {
            self.line("Termination == <>(\\A self \\in ProcSet : pc[self] = \"Done\")");
        } else {
            self.line("Termination == <>(pc = \"Done\")");
        }
        self.blank();
    }
}

/// A guard expression as a conjunct item: a top-level junction is
/// parenthesised, because written inline its bullets merge with the conjunct
/// list it sits in (overlapping precedence intervals).
fn render_guard(e: &Expr) -> String {
    if is_bool_chain(e) {
        format!("({})", render(e))
    } else {
        render(e)
    }
}

/// Whether the expression is a conjunction/disjunction at its top level —
/// bulleted (`Junction`) or single-line (`Infix`). Written inline after a
/// bullet, either shape merges with the list it sits in.
fn is_bool_chain(e: &Expr) -> bool {
    match &e.kind {
        crate::ast::ExprKind::Junction { .. } => true,
        crate::ast::ExprKind::Infix { op, .. } => op == "/\\" || op == "\\/",
        _ => false,
    }
}

fn init_val(d: &VarDecl) -> String {
    match &d.val {
        Some(v) => render(v),
        None => "defaultInitValue".into(),
    }
}

/// The Init conjunct for one process variable.
fn process_init(p: &LabeledProcess, d: &VarDecl) -> String {
    let default = default_init_expr();
    let val = d.val.as_ref().unwrap_or(&default);
    if p.is_eq {
        return format!(
            "{} {} {}",
            d.var,
            if d.is_eq { "=" } else { "\\in" },
            render(val)
        );
    }
    let mut vars = HashSet::new();
    vars.insert("pc".to_string());
    vars.insert("stack".to_string());
    for x in &p.decls {
        vars.insert(x.var.clone());
    }
    if d.is_eq {
        let substituted = subst::self_and_prime(
            val,
            Some(&subst::name_expr("self", Span::default())),
            &vars,
            &HashSet::new(),
        );
        format!(
            "{} = [self \\in {} |-> {}]",
            d.var,
            render(&p.id),
            render(&substituted)
        )
    } else {
        // `v \in Val` becomes `v \in [S -> ValBar]`, with ValBar reading the
        // process's own variables at an arbitrary self.
        let choose_self = choose_self(&p.id);
        let substituted = subst::self_and_prime(val, Some(&choose_self), &vars, &HashSet::new());
        format!(
            "{} \\in [{} -> {}]",
            d.var,
            render(&p.id),
            render(&substituted)
        )
    }
}

fn default_init_expr() -> Expr {
    subst::name_expr("defaultInitValue", Span::default())
}

fn choose_self(set: &Expr) -> Expr {
    use crate::ast::{Ident, Pattern};
    Expr {
        kind: crate::ast::ExprKind::Choose {
            pattern: Pattern::Name(Ident {
                name: "self".into(),
                span: Span::default(),
            }),
            domain: Some(Box::new(set.clone())),
            body: Box::new(subst::name_expr("TRUE", Span::default())),
        },
        span: Span::default(),
    }
}

fn first_label(p: &LabeledProcess) -> String {
    p.body
        .first()
        .map_or_else(|| "Done".to_string(), |b| b.label.clone())
}

/// The WF/SF conjunct for a fair process, or `None` when unfair.
fn fair_conjunct(p: &LabeledProcess) -> Option<String> {
    let xf = match p.fairness {
        Fairness::Unfair => return None,
        Fairness::Weak => "WF",
        Fairness::Strong => "SF",
    };
    let p_name = if p.is_eq {
        p.name.clone()
    } else {
        format!("{}(self)", p.name)
    };
    let body = if p.minus_labels.is_empty() {
        p_name
    } else if p.minus_labels.len() == 1 {
        format!("(pc[self] # \"{}\") /\\ {p_name}", p.minus_labels[0])
    } else {
        let set = p
            .minus_labels
            .iter()
            .map(|l| format!("\"{l}\""))
            .collect::<Vec<_>>()
            .join(", ");
        format!("(pc[self] \\notin {{{set}}}) /\\ {p_name}")
    };
    Some(format!("{xf}_vars({body})"))
}

/// Render the assignment conjuncts, grouped per variable, updating
/// `changed`.
fn group_assigns(
    ass: &[SingleAssign],
    self_expr: Option<&Expr>,
    self_vars: &HashSet<String>,
    changed: &mut Changed,
) -> Vec<String> {
    let mut order: Vec<String> = Vec::new();
    let mut groups: Vec<Vec<&SingleAssign>> = Vec::new();
    for a in ass {
        if let Some(i) = order.iter().position(|v| *v == a.var) {
            groups[i].push(a);
        } else {
            order.push(a.var.clone());
            groups.push(vec![a]);
        }
    }
    let mut out = Vec::new();
    for (var, group) in order.iter().zip(groups) {
        let takes_self = self_expr.is_some() && self_vars.contains(var);
        let single = group.len() == 1 && group[0].sels.is_empty();
        if single {
            let rhs = subst::self_and_prime(&group[0].rhs, self_expr, self_vars, changed);
            if takes_self {
                let Some(se) = self_expr else {
                    unreachable!("takes_self implies self")
                };
                out.push(format!(
                    "{var}' = [{var} EXCEPT ![{}] = {}]",
                    render(se),
                    render(&rhs)
                ));
            } else {
                let mut s = String::new();
                render_at_min(&rhs, 6, &mut s);
                out.push(format!("{var}' = {s}"));
            }
        } else {
            let sel_prefix = if takes_self {
                let Some(se) = self_expr else {
                    unreachable!("takes_self implies self")
                };
                format!("![{}]", render(se))
            } else {
                String::new()
            };
            let updates = group
                .iter()
                .map(|a| {
                    let sels = a
                        .sels
                        .iter()
                        .map(|sel| match sel {
                            Selector::Index(e) => {
                                let e2 = subst::self_and_prime(e, self_expr, self_vars, changed);
                                format!("[{}]", render(&e2))
                            }
                            Selector::Field(f) => format!(".{f}"),
                        })
                        .collect::<String>();
                    let rhs = subst::self_and_prime(&a.rhs, self_expr, self_vars, changed);
                    format!("!{sels} = {}", render(&rhs))
                })
                .collect::<Vec<_>>()
                .join(", ");
            out.push(format!("{var}' = [{var} EXCEPT {sel_prefix}{updates}"));
            out.last_mut().map_or_else(|| {}, |s| s.push(']'));
        }
        changed.insert(var.clone());
    }
    out
}

fn append_item(out: &mut String, item: &str, _col: usize) {
    out.push_str(item);
}

/// The `THEN …`/`ELSE …` block of an `IF`, aligned the way the reference
/// lays it out.
fn branch_block(kw: &str, items: &[String], col: usize) -> String {
    let mut text = String::new();
    text.push('\n');
    text.push_str(&" ".repeat(col + 4));
    text.push_str(kw);
    for (i, item) in items.iter().enumerate() {
        if i == 0 {
            text.push_str(" /\\ ");
        } else {
            text.push('\n');
            text.push_str(&" ".repeat(col + 9));
            text.push_str("/\\ ");
        }
        text.push_str(item);
    }
    text
}
