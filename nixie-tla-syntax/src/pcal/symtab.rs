//! The symbol table, its disambiguation, and the renaming pass — a port of
//! `PcalSymTab`, `PcalSymTab.Disambiguate` and `PcalFixIDs`.
//!
//! PlusCal's four name spaces (variables, labels, processes, procedures)
//! overlap freely in the source; the TLA+ translation has one. The
//! disambiguation algorithm is reproduced exactly, because its choices are
//! visible in every generated definition name: names are considered in type
//! order (global, label, procedure, process, process variable, procedure
//! variable, parameter), earlier types keep their spelling, and each later
//! collision grows a suffix — `_`, then characters of the defining context,
//! then the type number — until unique. Two labels spelled alike in
//! different processes are the corpus's live example (`l0` → `l0_`).

use super::ast::*;
use super::subst::rename_vars;
use crate::error::{ErrorKind, Result, SyntaxError};
use crate::span::Span;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SymType {
    Global = 0,
    Label = 1,
    Procedure = 2,
    Process = 3,
    ProcessVar = 4,
    ProcedureVar = 5,
    Parameter = 6,
}

impl SymType {
    fn name(self) -> &'static str {
        match self {
            Self::Global => "Global variable",
            Self::Label => "Label",
            Self::Procedure => "Procedure",
            Self::Process => "Process",
            Self::ProcessVar => "Process variable",
            Self::ProcedureVar => "Procedure variable",
            Self::Parameter => "Parameter",
        }
    }
}

#[derive(Debug, Clone)]
struct Entry {
    ty: SymType,
    id: String,
    context: String,
    use_this: String,
}

/// The built table: the disambiguated names plus the per-context lookup the
/// generator and renaming pass need.
pub struct SymTab {
    entries: Vec<Entry>,
    /// The initial `pc` value of a uniprocess algorithm.
    pub ipc: Option<String>,
    /// Processes in declaration order: (name, is_eq, id-expression, ipc).
    pub processes: Vec<ProcEntry>,
    reports: Vec<String>,
}

/// One process in the table.
pub struct ProcEntry {
    /// The disambiguated process name.
    pub name: String,
    /// Whether the process is a single `= id` process.
    pub is_eq: bool,
}

impl SymTab {
    /// Build and disambiguate the table for an algorithm.
    ///
    /// # Errors
    ///
    /// A [`SyntaxError`] for every redeclaration the reference rejects
    /// (duplicate label, duplicate variable, process name reused).
    pub fn build(alg: &LabeledAlgorithm) -> Result<Self> {
        let mut t = Self {
            entries: Vec::new(),
            ipc: None,
            processes: Vec::new(),
            reports: Vec::new(),
        };
        t.insert(SymType::Global, "pc", "", 0, 0)?;
        match alg {
            LabeledAlgorithm::Uniprocess {
                decls,
                procedures,
                body,
                ..
            } => {
                if !procedures.is_empty() {
                    t.insert(SymType::Global, "stack", "", 0, 0)?;
                }
                for d in decls {
                    t.insert(SymType::Global, &d.var, "", 0, 0)?;
                }
                // Procedures are declined before this point; the list is
                // empty and contributes no names.
                let _ = procedures;
                if let Some(first) = body.first() {
                    t.ipc = Some(first.label.clone());
                }
                for ls in body {
                    t.walk_labeled(ls, "", "")?;
                }
            }
            LabeledAlgorithm::Multiprocess {
                decls,
                procedures,
                processes,
                ..
            } => {
                if !procedures.is_empty() {
                    t.insert(SymType::Global, "stack", "", 0, 0)?;
                }
                for d in decls {
                    t.insert(SymType::Global, &d.var, "", 0, 0)?;
                }
                // Procedures are declined before this point; the list is
                // empty and contributes no names.
                let _ = procedures;
                for p in processes {
                    t.insert(SymType::Process, &p.name, "", 0, 0)?;
                    for d in &p.decls {
                        t.insert(SymType::ProcessVar, &d.var, &p.name, 0, 0)?;
                    }
                    for ls in &p.body {
                        t.walk_labeled(ls, &p.name, "process")?;
                    }
                }
            }
        }
        t.disambiguate();
        Ok(t)
    }

    fn walk_labeled(&mut self, ls: &LabeledStmt, context: &str, ctype: &str) -> Result<()> {
        self.insert(SymType::Label, &ls.label, context, 0, 0)
            .map_err(|_| dup_error(SymType::Label, &ls.label, context, ctype))?;
        self.walk_stmts(&ls.stmts, context)
    }

    fn walk_stmts(&mut self, stmts: &[FlatStmt], context: &str) -> Result<()> {
        for s in stmts {
            match s {
                FlatStmt::While {
                    unlab_do, lab_do, ..
                } => {
                    self.walk_stmts(unlab_do, context)?;
                    for ls in lab_do {
                        self.walk_labeled(ls, context, "process")?;
                    }
                }
                FlatStmt::If { then, els, .. } => {
                    self.walk_stmts(then, context)?;
                    self.walk_stmts(els, context)?;
                }
                FlatStmt::LabelIf {
                    then_unlab,
                    then_lab,
                    els_unlab,
                    els_lab,
                    ..
                } => {
                    self.walk_stmts(then_unlab, context)?;
                    for ls in then_lab {
                        self.walk_labeled(ls, context, "process")?;
                    }
                    self.walk_stmts(els_unlab, context)?;
                    for ls in els_lab {
                        self.walk_labeled(ls, context, "process")?;
                    }
                }
                FlatStmt::Either { ors } => {
                    for or in ors {
                        self.walk_stmts(or, context)?;
                    }
                }
                FlatStmt::LabelEither { clauses } => {
                    for (unlab, lab) in clauses {
                        self.walk_stmts(unlab, context)?;
                        for ls in lab {
                            self.walk_labeled(ls, context, "process")?;
                        }
                    }
                }
                FlatStmt::With { body, .. } => self.walk_stmts(body, context)?,
                _ => {}
            }
        }
        Ok(())
    }

    fn insert(
        &mut self,
        ty: SymType,
        id: &str,
        context: &str,
        _line: u32,
        _col: u32,
    ) -> Result<()> {
        if matches!(
            ty,
            SymType::ProcedureVar | SymType::ProcessVar | SymType::Parameter
        ) {
            if self
                .entries
                .iter()
                .any(|e| e.ty == SymType::Global && e.id == id)
            {
                return Err(dup_error(ty, id, context, ""));
            }
            if self
                .entries
                .iter()
                .any(|e| e.id == id && e.context == context)
            {
                return Err(dup_error(ty, id, context, ""));
            }
        } else if self
            .entries
            .iter()
            .any(|e| e.ty == ty && e.id == id && e.context == context)
        {
            return Err(dup_error(ty, id, context, ""));
        }
        self.entries.push(Entry {
            ty,
            id: id.to_string(),
            context: context.to_string(),
            use_this: id.to_string(),
        });
        Ok(())
    }

    /// `Disambiguate`.
    fn disambiguate(&mut self) {
        for vtype in [
            SymType::Global,
            SymType::Label,
            SymType::Procedure,
            SymType::Process,
            SymType::ProcessVar,
            SymType::ProcedureVar,
            SymType::Parameter,
        ] {
            for i in 0..self.entries.len() {
                if self.entries[i].ty != vtype {
                    continue;
                }
                let mut use_this = self.entries[i].id.clone();
                if vtype != SymType::Global {
                    let mut suffix_length = 0usize;
                    while self.ambiguous(&use_this) {
                        suffix_length += 1;
                        let context = self.entries[i].context.clone();
                        let vtype_num = vtype as usize;
                        if suffix_length == 1 {
                            use_this.push('_');
                        } else if suffix_length > context.chars().count() + 1 {
                            use_this.push_str(&vtype_num.to_string());
                        } else {
                            let ch = context.chars().nth(suffix_length - 2).unwrap_or('_');
                            use_this.push(ch);
                        }
                    }
                }
                self.entries[i].use_this = use_this;
            }
        }
        for e in &self.entries {
            if e.id != e.use_this {
                self.reports.push(format!(
                    "\\* {} {}{} changed to {}",
                    e.ty.name(),
                    e.id,
                    if e.context.is_empty() {
                        String::new()
                    } else {
                        format!(" of {}", e.context)
                    },
                    e.use_this
                ));
            }
        }
    }

    fn ambiguous(&self, id: &str) -> bool {
        self.entries.iter().filter(|e| e.use_this == id).count() > 1
    }

    /// `UseThis` for a typed name.
    #[must_use]
    pub fn use_this(&self, kind: NameKind, id: &str, context: &str) -> String {
        let ty = match kind {
            NameKind::Label => SymType::Label,
            NameKind::Procedure => SymType::Procedure,
            NameKind::Process => SymType::Process,
        };
        self.entries
            .iter()
            .find(|e| e.ty == ty && e.id == id && e.context == context)
            .map_or_else(|| id.to_string(), |e| e.use_this.clone())
    }

    /// `UseThisVar`: the disambiguated spelling of a variable-ish name.
    #[must_use]
    pub fn use_this_var(&self, id: &str, context: &str) -> String {
        let var_like = |e: &Entry| {
            matches!(
                e.ty,
                SymType::Global | SymType::ProcessVar | SymType::ProcedureVar | SymType::Parameter
            )
        };
        if let Some(e) = self
            .entries
            .iter()
            .find(|e| e.id == id && e.context == context)
            && var_like(e)
        {
            return e.use_this.clone();
        }
        if let Some(e) = self
            .entries
            .iter()
            .find(|e| e.id == id && e.context.is_empty() && e.ty == SymType::Global)
        {
            return e.use_this.clone();
        }
        id.to_string()
    }

    /// The variable-renaming map for one context, for [`rename_vars`].
    #[must_use]
    pub fn var_map(&self, context: &str) -> HashMap<String, String> {
        let mut m = HashMap::new();
        for e in &self.entries {
            if matches!(
                e.ty,
                SymType::Global | SymType::ProcessVar | SymType::ProcedureVar | SymType::Parameter
            ) && (e.context == context || e.context.is_empty() && e.ty == SymType::Global)
                && e.id != e.use_this
            {
                m.insert(e.id.clone(), e.use_this.clone());
            }
        }
        m
    }

    /// Whether a name is a global variable.
    #[must_use]
    pub fn is_global_var(&self, id: &str) -> bool {
        self.entries
            .iter()
            .any(|e| e.ty == SymType::Global && e.id == id)
    }

    /// The names of all global variables, disambiguated, in declaration
    /// order (`pc` and `stack` included).
    #[must_use]
    pub fn global_vars(&self) -> Vec<String> {
        self.entries
            .iter()
            .filter(|e| e.ty == SymType::Global)
            .map(|e| e.use_this.clone())
            .collect()
    }

    /// The process-local variable names of one process.
    #[must_use]
    pub fn process_vars(&self, process: &str) -> Vec<String> {
        self.entries
            .iter()
            .filter(|e| e.ty == SymType::ProcessVar && e.context == process)
            .map(|e| e.use_this.clone())
            .collect()
    }

    /// The procedure-variable and parameter names (all procedures).
    #[must_use]
    pub fn procedure_vars(&self) -> Vec<String> {
        self.entries
            .iter()
            .filter(|e| matches!(e.ty, SymType::ProcedureVar | SymType::Parameter))
            .map(|e| e.use_this.clone())
            .collect()
    }

    /// The renaming report lines (`disambiguateReport`).
    #[must_use]
    pub fn reports(&self) -> &[String] {
        &self.reports
    }
}

/// Which name space a `UseThis` lookup addresses.
#[derive(Debug, Clone, Copy)]
pub enum NameKind {
    /// A label.
    Label,
    /// A procedure name.
    Procedure,
    /// A process name.
    Process,
}

fn dup_error(ty: SymType, id: &str, context: &str, ctype: &str) -> SyntaxError {
    SyntaxError::new(
        ErrorKind::Unsupported {
            construct: "PlusCal algorithm".into(),
            note: format!(
                "{} `{id}' redefined{}",
                ty.name(),
                if context.is_empty() {
                    String::new()
                } else {
                    format!(" in {ctype} {context}")
                }
            ),
        },
        Span::default(),
    )
}

/// `PcalFixIDs.Fix`: rewrite an algorithm's names to their disambiguated
/// spellings.
pub fn fix(alg: &mut LabeledAlgorithm, tab: &SymTab) {
    match alg {
        LabeledAlgorithm::Uniprocess {
            decls,
            body,
            procedures,
            ..
        } => {
            for d in decls {
                fix_decl(d, "", tab);
            }
            // Procedures are declined before this point; the list is
            // empty and needs no renaming.
            let _ = procedures;
            for ls in body {
                fix_labeled(ls, "", tab);
            }
        }
        LabeledAlgorithm::Multiprocess {
            decls,
            procedures,
            processes,
            ..
        } => {
            for d in decls {
                fix_decl(d, "", tab);
            }
            // Procedures are declined before this point; the list is
            // empty and needs no renaming.
            let _ = procedures;
            for p in processes {
                let ctx = p.name.clone();
                for d in &mut p.decls {
                    fix_decl(d, &ctx, tab);
                }
                fix_expr(&mut p.id, "", tab);
                for lbl in &mut p.plus_labels {
                    *lbl = tab.use_this(NameKind::Label, lbl, &ctx);
                }
                for lbl in &mut p.minus_labels {
                    *lbl = tab.use_this(NameKind::Label, lbl, &ctx);
                }
                for ls in &mut p.body {
                    fix_labeled(ls, &ctx, tab);
                }
                p.name = tab.use_this(NameKind::Process, &p.name, "");
            }
        }
    }
}

fn fix_decl(d: &mut VarDecl, context: &str, tab: &SymTab) {
    let new = tab.use_this_var(&d.var, context);
    if let Some(v) = &mut d.val {
        fix_expr(v, context, tab);
    }
    let _ = new;
    d.var = new;
}

fn fix_labeled(ls: &mut LabeledStmt, context: &str, tab: &SymTab) {
    ls.label = tab.use_this(NameKind::Label, &ls.label, context);
    fix_stmts(&mut ls.stmts, context, tab);
}

fn fix_stmts(stmts: &mut [FlatStmt], context: &str, tab: &SymTab) {
    for s in stmts {
        match s {
            FlatStmt::Assign(ass) => {
                for a in ass {
                    a.var = tab.use_this_var(&a.var, context);
                    for sel in &mut a.sels {
                        if let Selector::Index(e) = sel {
                            fix_expr(e, context, tab);
                        }
                    }
                    fix_expr(&mut a.rhs, context, tab);
                }
            }
            FlatStmt::If { test, then, els } => {
                fix_expr(test, context, tab);
                fix_stmts(then, context, tab);
                fix_stmts(els, context, tab);
            }
            FlatStmt::LabelIf {
                test,
                then_unlab,
                then_lab,
                els_unlab,
                els_lab,
            } => {
                fix_expr(test, context, tab);
                fix_stmts(then_unlab, context, tab);
                for ls in then_lab {
                    fix_labeled(ls, context, tab);
                }
                fix_stmts(els_unlab, context, tab);
                for ls in els_lab {
                    fix_labeled(ls, context, tab);
                }
            }
            FlatStmt::Either { ors } => {
                for or in ors {
                    fix_stmts(or, context, tab);
                }
            }
            FlatStmt::LabelEither { clauses } => {
                for (unlab, lab) in clauses {
                    fix_stmts(unlab, context, tab);
                    for ls in lab {
                        fix_labeled(ls, context, tab);
                    }
                }
            }
            FlatStmt::With { exp, body, .. } => {
                fix_expr(exp, context, tab);
                fix_stmts(body, context, tab);
            }
            FlatStmt::When(e) | FlatStmt::Print(e) | FlatStmt::Assert(e) => {
                fix_expr(e, context, tab);
            }
            FlatStmt::Skip => {}
            FlatStmt::While {
                test,
                unlab_do,
                lab_do,
            } => {
                fix_expr(test, context, tab);
                fix_stmts(unlab_do, context, tab);
                for ls in lab_do {
                    fix_labeled(ls, context, tab);
                }
            }
            FlatStmt::Goto(to) => {
                *to = tab.use_this(NameKind::Label, to, context);
            }
        }
    }
}

fn fix_expr(e: &mut crate::ast::Expr, context: &str, tab: &SymTab) {
    let map = tab.var_map(context);
    if map.is_empty() {
        return;
    }
    *e = rename_vars(e, &|name: &str| map.get(name).cloned());
}
