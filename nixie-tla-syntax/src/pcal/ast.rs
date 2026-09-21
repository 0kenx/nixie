//! The PlusCal AST — the shape `pcal/AST.java` defines, at the level of
//! detail this translator needs.
//!
//! Two generations of node live here deliberately. The **preliminary**
//! statements ([`Stmt`]) are what the parser produces: a flat sequence in
//! which an `if` is always a [`Stmt::If`] with `unlab_then`/`unlab_else`
//! fields, matching `AST.LabelIf` with empty `labThen`/`labElse`. Label
//! insertion and statement-sequence splitting then produce the **labeled**
//! form ([`LabeledStmt`] of [`FlatStmt`]), in which a `while` owns both an
//! unlabeled body prefix and a sequence of labeled sub-statements, and an
//! `if`/`either` either contains no labels at all (it stayed a
//! [`FlatStmt::If`]/[`FlatStmt::Either`]) or has been split by the explosion
//! pass. Keeping the two apart mirrors the reference translator's phases and
//! is what makes the label-placement rules checkable where they are decided.

use crate::ast::Expr;

/// Whether a process is fair, and in which sense.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fairness {
    /// `process` — no fairness conjunct.
    Unfair,
    /// `fair process` — weak fairness.
    Weak,
    /// `fair+ process` — strong fairness.
    Strong,
}

/// A variable declaration: `v = e` or `v \in e`, with the default
/// (`defaultInitValue`) when written bare.
#[derive(Debug, Clone)]
pub struct VarDecl {
    /// The declared name.
    pub var: String,
    /// `true` for `=`, `false` for `\in`.
    pub is_eq: bool,
    /// The initializing expression. `None` when the declaration was bare,
    /// which the translation spells `defaultInitValue` and flags with a
    /// `CONSTANT defaultInitValue` declaration.
    pub val: Option<Expr>,
}

/// One `lhs := rhs` of an assignment statement.
#[derive(Debug, Clone)]
pub struct SingleAssign {
    /// The assigned variable's name.
    pub var: String,
    /// The selector chain between the name and `:=`, outermost first:
    /// `forks[f].clean` has selectors `[f]`, `.clean`.
    pub sels: Vec<Selector>,
    /// The right-hand side.
    pub rhs: Expr,
}

/// One step of an assignment's left-hand selector path.
#[derive(Debug, Clone)]
pub enum Selector {
    /// `[e]` — function application.
    Index(Expr),
    /// `.f` — record field.
    Field(String),
}

/// A label: the name plus whether the statement carried one at all. An empty
/// string is "unlabeled", exactly as `AST.lbl == ""` in the reference.
pub type Label = Option<String>;

/// A preliminary statement, as produced by the parser.
#[derive(Debug, Clone)]
pub enum Stmt {
    /// `lhs := rhs [|| lhs := rhs …] ;`
    Assign {
        /// The simultaneous assignments.
        ass: Vec<SingleAssign>,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `if … then … [elsif|else …] end if` — a `LabelIf` with empty labelled
    /// parts; the splitting pass decides what actually belongs where.
    If {
        /// The test.
        test: Expr,
        /// The `then` sequence.
        then: Vec<Stmt>,
        /// The `else`/`elsif` sequence, possibly empty.
        els: Vec<Stmt>,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `either … or … end either`.
    Either {
        /// The `or` clauses.
        ors: Vec<Vec<Stmt>>,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `with v = e / v \in e do … end with` (or the c-syntax forms). Nested
    /// `with` bindings parse as nested [`Stmt::With`] nodes.
    With {
        /// The bound name.
        var: String,
        /// `true` for `=`, `false` for `\in`.
        is_eq: bool,
        /// The bound expression.
        exp: Expr,
        /// The body.
        body: Vec<Stmt>,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `await e ;` / `when e ;`
    When {
        /// The guard.
        exp: Expr,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `print e ;`
    Print {
        /// The printed expression.
        exp: Expr,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `assert e ;`
    Assert {
        /// The asserted expression.
        exp: Expr,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `skip ;`
    Skip {
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `while e do … end while` — owns the unlabeled prefix of its body; the
    /// labeled remainder arrives when statement sequences are split.
    While {
        /// The test.
        test: Expr,
        /// The unlabeled prefix of the body.
        unlab_do: Vec<Stmt>,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `goto L ;`
    Goto {
        /// The target label (or `Done`).
        to: String,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `call P(a, b) ;` — a procedure call. Parsed, and declined at
    /// translation time with a named error: nothing in the corpus uses
    /// procedures, and a stack-machine half-implementation would be a
    /// silent wrong answer, not a subset.
    Call {
        /// The callee.
        to: String,
        /// The arguments.
        args: Vec<Expr>,
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `return ;`
    Return {
        /// The statement's label, if any.
        lbl: Label,
    },
    /// `Name(a, b) ;` — a macro invocation, expanded during parsing.
    MacroCall {
        /// The macro's name.
        name: String,
        /// The arguments.
        args: Vec<Expr>,
        /// The statement's label, if any.
        lbl: Label,
    },
}

impl Stmt {
    /// The statement's label, if any.
    #[must_use]
    pub fn lbl(&self) -> &Label {
        match self {
            Self::Assign { lbl, .. }
            | Self::If { lbl, .. }
            | Self::Either { lbl, .. }
            | Self::With { lbl, .. }
            | Self::When { lbl, .. }
            | Self::Print { lbl, .. }
            | Self::Assert { lbl, .. }
            | Self::Skip { lbl, .. }
            | Self::While { lbl, .. }
            | Self::Goto { lbl, .. }
            | Self::Call { lbl, .. }
            | Self::Return { lbl, .. }
            | Self::MacroCall { lbl, .. } => lbl,
        }
    }

    /// The statement's label, mutably.
    pub fn lbl_mut(&mut self) -> &mut Label {
        match self {
            Self::Assign { lbl, .. }
            | Self::If { lbl, .. }
            | Self::Either { lbl, .. }
            | Self::With { lbl, .. }
            | Self::When { lbl, .. }
            | Self::Print { lbl, .. }
            | Self::Assert { lbl, .. }
            | Self::Skip { lbl, .. }
            | Self::While { lbl, .. }
            | Self::Goto { lbl, .. }
            | Self::Call { lbl, .. }
            | Self::Return { lbl, .. }
            | Self::MacroCall { lbl, .. } => lbl,
        }
    }
}

/// A `macro Name(p, q) begin … end macro`.
#[derive(Debug, Clone)]
pub struct Macro {
    /// The macro's name.
    pub name: String,
    /// The parameters.
    pub params: Vec<String>,
    /// The body — preliminary statements, already free of macro calls.
    pub body: Vec<Stmt>,
}

/// A `process` / `fair process` declaration.
#[derive(Debug, Clone)]
pub struct Process {
    /// The process's name.
    pub name: String,
    /// The fairness modifier.
    pub fairness: Fairness,
    /// `true` for `= id`, `false` for `\in id`.
    pub is_eq: bool,
    /// The process-set expression (or the single process's value).
    pub id: Expr,
    /// The process's local variables.
    pub decls: Vec<VarDecl>,
    /// The body — preliminary statements until the label pass runs, labeled
    /// clusters after it.
    pub body: Vec<Stmt>,
    /// Labels carrying a `+` fairness modifier.
    pub plus_labels: Vec<String>,
    /// Labels carrying a `-` fairness modifier.
    pub minus_labels: Vec<String>,
}

/// A `procedure` declaration — parsed, and declined at translation time.
#[derive(Debug, Clone)]
pub struct Procedure {
    /// The procedure's name.
    pub name: String,
    /// The parameters.
    pub params: Vec<VarDecl>,
    /// The local variables.
    pub decls: Vec<VarDecl>,
    /// The body.
    pub body: Vec<Stmt>,
}

/// A whole algorithm.
#[derive(Debug, Clone)]
pub enum Algorithm {
    /// `--algorithm Name variables … [define …] [macros] [procedures] begin … end algorithm`.
    Uniprocess {
        /// The algorithm's name.
        name: String,
        /// The global variables.
        decls: Vec<VarDecl>,
        /// The `define` block's verbatim text, if any.
        defs: Option<String>,
        /// The macros.
        macros: Vec<Macro>,
        /// The procedures (declines translation).
        procedures: Vec<Procedure>,
        /// The body — preliminary statements until the label pass runs.
        body: Vec<Stmt>,
    },
    /// The multiprocess form.
    Multiprocess {
        /// The algorithm's name.
        name: String,
        /// The global variables.
        decls: Vec<VarDecl>,
        /// The `define` block's verbatim text, if any.
        defs: Option<String>,
        /// The macros.
        macros: Vec<Macro>,
        /// The procedures (declines translation).
        procedures: Vec<Procedure>,
        /// The processes.
        processes: Vec<Process>,
    },
}

impl Algorithm {
    /// The global variable declarations.
    #[must_use]
    pub fn decls(&self) -> &Vec<VarDecl> {
        match self {
            Self::Uniprocess { decls, .. } | Self::Multiprocess { decls, .. } => decls,
        }
    }

    /// The `define` block text.
    #[must_use]
    pub fn defs(&self) -> Option<&String> {
        match self {
            Self::Uniprocess { defs, .. } | Self::Multiprocess { defs, .. } => defs.as_ref(),
        }
    }

    /// The procedures.
    #[must_use]
    pub fn procedures(&self) -> &Vec<Procedure> {
        match self {
            Self::Uniprocess { procedures, .. } | Self::Multiprocess { procedures, .. } => {
                procedures
            }
        }
    }

    /// The macros.
    #[must_use]
    pub fn macros(&self) -> &Vec<Macro> {
        match self {
            Self::Uniprocess { macros, .. } | Self::Multiprocess { macros, .. } => macros,
        }
    }

    /// The label-pass result: the same algorithm with every body cut into
    /// labeled clusters.
    #[must_use]
    pub fn labeled(self, labeled_bodies: Vec<Vec<LabeledStmt>>) -> LabeledAlgorithm {
        match self {
            Self::Uniprocess {
                decls,
                defs,
                procedures,
                ..
            } => LabeledAlgorithm::Uniprocess {
                decls,
                defs,
                procedures,
                body: labeled_bodies.into_iter().next().unwrap_or_default(),
            },
            Self::Multiprocess {
                decls,
                defs,
                procedures,
                processes,
                ..
            } => {
                let processes = processes
                    .into_iter()
                    .enumerate()
                    .map(|(i, p)| LabeledProcess {
                        name: p.name,
                        fairness: p.fairness,
                        is_eq: p.is_eq,
                        id: p.id,
                        decls: p.decls,
                        body: labeled_bodies.get(i).cloned().unwrap_or_default(),
                        plus_labels: p.plus_labels,
                        minus_labels: p.minus_labels,
                    })
                    .collect();
                LabeledAlgorithm::Multiprocess {
                    decls,
                    defs,
                    procedures,
                    processes,
                }
            }
        }
    }
}

/// A process whose body has been cut into labeled clusters.
#[derive(Debug, Clone)]
pub struct LabeledProcess {
    /// The process's name.
    pub name: String,
    /// The fairness modifier.
    pub fairness: Fairness,
    /// `true` for `= id`, `false` for `\in id`.
    pub is_eq: bool,
    /// The process-set expression (or the single process's value).
    pub id: Expr,
    /// The process's local variables.
    pub decls: Vec<VarDecl>,
    /// The body, in labeled clusters.
    pub body: Vec<LabeledStmt>,
    /// Labels carrying a `+` fairness modifier.
    pub plus_labels: Vec<String>,
    /// Labels carrying a `-` fairness modifier.
    pub minus_labels: Vec<String>,
}

/// An algorithm whose bodies have been cut into labeled clusters — the form
/// the symbol table, renaming, explosion and generator all work on.
#[derive(Debug, Clone)]
pub enum LabeledAlgorithm {
    /// The uniprocess form.
    Uniprocess {
        /// The global variables.
        decls: Vec<VarDecl>,
        /// The `define` block's verbatim text, if any.
        defs: Option<String>,
        /// The procedures (declines translation).
        procedures: Vec<Procedure>,
        /// The body, in labeled clusters.
        body: Vec<LabeledStmt>,
    },
    /// The multiprocess form.
    Multiprocess {
        /// The global variables.
        decls: Vec<VarDecl>,
        /// The `define` block's verbatim text, if any.
        defs: Option<String>,
        /// The procedures (declines translation).
        procedures: Vec<Procedure>,
        /// The processes.
        processes: Vec<LabeledProcess>,
    },
}

impl LabeledAlgorithm {
    /// The global variable declarations.
    #[must_use]
    pub fn decls(&self) -> &Vec<VarDecl> {
        match self {
            Self::Uniprocess { decls, .. } | Self::Multiprocess { decls, .. } => decls,
        }
    }

    /// The `define` block text.
    #[must_use]
    pub fn defs(&self) -> Option<&String> {
        match self {
            Self::Uniprocess { defs, .. } | Self::Multiprocess { defs, .. } => defs.as_ref(),
        }
    }

    /// The procedures.
    #[must_use]
    pub fn procedures(&self) -> &Vec<Procedure> {
        match self {
            Self::Uniprocess { procedures, .. } | Self::Multiprocess { procedures, .. } => {
                procedures
            }
        }
    }
}

/// A statement of a labeled cluster, after sequences have been split.
#[derive(Debug, Clone)]
pub enum FlatStmt {
    /// One simultaneous assignment.
    Assign(Vec<SingleAssign>),
    /// An `if` with no labels nested inside.
    If {
        /// The test.
        test: Expr,
        /// The `then` sequence.
        then: Vec<FlatStmt>,
        /// The `else` sequence.
        els: Vec<FlatStmt>,
    },
    /// An `if` whose branches contain labeled statements — present between
    /// the splitting and explosion passes, which lift the labeled parts out
    /// into their own clusters.
    LabelIf {
        /// The test.
        test: Expr,
        /// The unlabeled prefix of the `then` branch.
        then_unlab: Vec<FlatStmt>,
        /// The labeled remainder of the `then` branch.
        then_lab: Vec<LabeledStmt>,
        /// The unlabeled prefix of the `else` branch.
        els_unlab: Vec<FlatStmt>,
        /// The labeled remainder of the `else` branch.
        els_lab: Vec<LabeledStmt>,
    },
    /// An `either` with no labels nested inside.
    Either {
        /// The clauses.
        ors: Vec<Vec<FlatStmt>>,
    },
    /// An `either` whose clauses contain labeled statements.
    LabelEither {
        /// The clauses: unlabeled prefix and labeled remainder each.
        clauses: Vec<(Vec<FlatStmt>, Vec<LabeledStmt>)>,
    },
    /// A `with`.
    With {
        /// The bound name.
        var: String,
        /// `=` or `\in`.
        is_eq: bool,
        /// The bound expression.
        exp: Expr,
        /// The body.
        body: Vec<FlatStmt>,
    },
    /// A guard.
    When(Expr),
    /// `print`.
    Print(Expr),
    /// `assert`.
    Assert(Expr),
    /// `skip`.
    Skip,
    /// A `while` at the head of its cluster; the cluster's remaining
    /// statements are its exit path. Populated only between the splitting
    /// and explosion passes.
    While {
        /// The test.
        test: Expr,
        /// The unlabeled body prefix.
        unlab_do: Vec<FlatStmt>,
        /// The labeled body statements.
        lab_do: Vec<LabeledStmt>,
    },
    /// A `goto`, present only before the explosion pass replaces it.
    Goto(String),
}

/// One labeled cluster: the statements between this label and the next.
#[derive(Debug, Clone)]
pub struct LabeledStmt {
    /// The cluster's label.
    pub label: String,
    /// Its statements.
    pub stmts: Vec<FlatStmt>,
}
