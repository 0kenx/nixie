//! The PlusCal grammar, as a recursive-descent parser over the TLA+ token
//! stream of the algorithm body.
//!
//! The grammar followed is the one `ParseAlgorithm.java` implements: the
//! appendix of the +CAL user manual in two syntaxes — p-syntax
//! (`if … then … end if`) and c-syntax (`if (…) { … }`), decided by whether
//! the algorithm name is followed by `{`.
//!
//! Expressions are not re-implemented. The algorithm body is lexed with the
//! front end's own TLA+ lexer — so Unicode spellings, based numerals and
//! layout-sensitive junction lists behave exactly as they do in the module
//! around the algorithm — and each expression position hands the token
//! slice up to the next structural keyword to [`crate::parser::Parser`].
//! The slice boundaries are the delimiter set `Tokenize.IsDelimiter` uses,
//! with the same record-field protection (`m.type` after `.`/`[`/`,` is a
//! field, not a keyword) and the same quantifier exception for `,`.

use super::ast::*;
use super::extract::Found;
use super::subst::subst_free;
use crate::ast::Expr;
use crate::error::{ErrorKind, Result, SyntaxError};
use crate::lexer;
use crate::parser::Parser;
use crate::span::Span;
use crate::token::{Token, TokenKind};

/// Words that terminate a PlusCal expression, from `Tokenize.IsDelimiter`.
const DELIMITER_WORDS: &[&str] = &[
    "if",
    "then",
    "else",
    "elsif",
    "either",
    "or",
    "end",
    "while",
    "do",
    "with",
    "when",
    "await",
    "skip",
    "call",
    "return",
    "goto",
    "print",
    "assert",
    "begin",
    "variable",
    "variables",
    "define",
    "process",
    "fair",
    "procedure",
    "macro",
    "algorithm",
];

/// Words that can never be labels (`IsLabelNext`'s keyword list).
const NON_LABEL_WORDS: &[&str] = &[
    "while", "if", "assert", "print", "else", "elsif", "either", "or", "end", "with", "when",
    "await", "skip", "call", "return", "goto",
];

/// Outcome of parsing an algorithm body.
#[derive(Debug)]
pub struct Parsed {
    /// The algorithm.
    pub alg: Algorithm,
    /// Whether any statement carried a user label (`hasLabel`).
    pub has_label: bool,
    /// Every user-written label, spelled as written.
    pub all_labels: Vec<String>,
    /// Whether any variable was declared without an initializer.
    pub has_default_initialization: bool,
    /// Whether a `goto` appeared (`gotoUsed`).
    pub goto_used: bool,
    /// Whether a `goto Done` appeared (`gotoDoneUsed`).
    pub goto_done_used: bool,
    /// Whether the algorithm was `--fair` (uniprocess: forces `-wf`).
    pub fair_algorithm: bool,
    /// Whether the pc-elision optimisation is forbidden: procedures, or a
    /// label with a `+`/`-` fairness modifier.
    pub force_pc: bool,
}

/// Parse an algorithm located by [`super::extract::find_algorithm`].
///
/// # Errors
///
/// A [`SyntaxError`] at the offending token for every grammar violation.
pub fn parse(found: &Found) -> Result<Parsed> {
    let lexed = lexer::lex(&found.body)?;
    let mut p = PcalParser {
        source: found.body.clone(),
        tokens: lexed.tokens,
        pos: 0,
        c_syntax: false,
        p_syntax: false,
        fair_algorithm: found.fair,
        has_label: false,
        all_labels: Vec::new(),
        has_default_initialization: false,
        goto_used: false,
        goto_done_used: false,
        force_pc: false,
        plus_labels: Vec::new(),
        minus_labels: Vec::new(),
    };
    // The lexer's stream is Eof-terminated; keep that invariant even for a
    // hand-truncated slice.
    p.tokens.push(eof_token());
    let alg = p.algorithm()?;
    Ok(Parsed {
        alg,
        has_label: p.has_label,
        all_labels: p.all_labels,
        has_default_initialization: p.has_default_initialization,
        goto_used: p.goto_used,
        goto_done_used: p.goto_done_used,
        fair_algorithm: p.fair_algorithm,
        force_pc: p.force_pc,
    })
}

fn eof_token() -> Token {
    Token {
        kind: TokenKind::Eof,
        text: String::new(),
        span: Span::new(crate::span::Pos::START, crate::span::Pos::START),
    }
}

struct PcalParser {
    source: String,
    tokens: Vec<Token>,
    pos: usize,
    c_syntax: bool,
    p_syntax: bool,
    fair_algorithm: bool,
    has_label: bool,
    all_labels: Vec<String>,
    has_default_initialization: bool,
    goto_used: bool,
    goto_done_used: bool,
    force_pc: bool,
    plus_labels: Vec<String>,
    minus_labels: Vec<String>,
}

impl PcalParser {
    // ---- token plumbing ---------------------------------------------------

    fn tok(&self) -> &Token {
        self.tokens
            .get(self.pos)
            .unwrap_or(&self.tokens[self.tokens.len() - 1])
    }

    fn peek(&self, n: usize) -> &Token {
        let idx = (self.pos + n).min(self.tokens.len() - 1);
        &self.tokens[idx]
    }

    fn advance(&mut self) -> Token {
        let t = self.tok().clone();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn at_eof(&self) -> bool {
        self.tok().kind == TokenKind::Eof
    }

    fn at_word(&self, w: &str) -> bool {
        self.tok().kind == TokenKind::Ident && self.tok().text == w
    }

    fn peek_word(&self, n: usize, w: &str) -> bool {
        let t = self.peek(n);
        t.kind == TokenKind::Ident && t.text == w
    }

    fn must_word(&mut self, w: &str) -> Result<()> {
        if self.at_word(w) {
            self.advance();
            Ok(())
        } else {
            Err(self.err(&format!("`{w}'")))
        }
    }

    fn at_sym(&self, s: &str) -> bool {
        self.tok().is_sym(s)
    }

    fn eat_sym(&mut self, s: &str) -> bool {
        if self.at_sym(s) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn must_sym(&mut self, s: &str) -> Result<()> {
        if self.at_sym(s) {
            self.advance();
            Ok(())
        } else {
            Err(self.err(&format!("`{s}'")))
        }
    }

    fn err(&self, expected: &str) -> SyntaxError {
        SyntaxError::new(
            ErrorKind::Unexpected {
                expected: format!("PlusCal {expected}"),
                found: match self.tok().kind {
                    TokenKind::Eof => "end of algorithm".to_string(),
                    _ => format!("`{}'", self.tok().text),
                },
            },
            self.tok().span,
        )
    }

    /// `GobbleThis(";")`: a `;` that is silently optional before the
    /// tokens that make it obviously unnecessary (`end`, `}`, `begin`,
    /// …), and a *missing-semicolon* error before a statement keyword —
    /// where swallowing it would silently move a label into the previous
    /// statement.
    fn eat_semicolon(&mut self) -> Result<()> {
        const FORGIVEN: &[&str] = &[
            "end",
            "begin",
            "else",
            "elsif",
            "or",
            "do",
            "macro",
            "procedure",
            "process",
            "fair",
            "define",
        ];
        const STATEMENT_STARTERS: &[&str] = &[
            "if", "either", "while", "with", "call", "return", "goto", "print", "assert", "skip",
        ];
        if self.at_sym(";") {
            self.advance();
            return Ok(());
        }
        if self.at_sym("}") || self.at_sym("{") {
            return Ok(());
        }
        if self.tok().kind == TokenKind::Ident {
            let w = self.tok().text.as_str();
            if FORGIVEN.contains(&w) {
                return Ok(());
            }
            if STATEMENT_STARTERS.contains(&w) {
                return Err(self.err("`;' before the next statement"));
            }
        }
        Err(self.err("`;'"))
    }

    fn eat_comma_or_semicolon(&mut self) {
        if self.at_sym(",") || self.at_sym(";") {
            self.advance();
        }
    }

    /// `GobbleEqualOrIf`: `=` or `\in`.
    fn equal_or_in(&mut self) -> Result<bool> {
        if self.eat_sym("=") {
            Ok(true)
        } else if self.eat_sym("\\in") {
            Ok(false)
        } else {
            Err(self.err("`=' or `\\in'"))
        }
    }

    // ---- expressions -------------------------------------------------------

    /// Parse the expression starting at the cursor, stopping at the next
    /// PlusCal structural token. Mirrors `Tokenize.TokenizeExpr`.
    fn expr(&mut self) -> Result<Expr> {
        let start = self.pos;
        let end = self.expr_end();
        if start == end {
            return Err(self.err("expression"));
        }
        let mut slice: Vec<Token> = self.tokens[start..end].to_vec();
        slice.push(eof_token());
        let mut parser = Parser::new(slice);
        let e = parser.parse_expr(0)?;
        if !parser.exhausted() {
            return Err(self.err("end of expression"));
        }
        self.pos = end;
        Ok(e)
    }

    /// The index of the first token after the expression starting at
    /// `self.pos`.
    fn expr_end(&self) -> usize {
        let mut depth: i32 = 0;
        let mut quant: i32 = 0;
        let mut i = self.pos;
        let mut prev_field_open = false;
        while i < self.tokens.len() {
            let t = &self.tokens[i];
            match &t.kind {
                TokenKind::Sym => {
                    match t.text.as_str() {
                        "(" | "[" | "{" | "<<" => depth += 1,
                        ")" | "]" | "}" | ">>" => {
                            if depth == 0 {
                                if std::env::var("PCAL_DEBUG").is_ok() {
                                    eprintln!("stop@{i} {} d{depth} q{quant}", t.text);
                                }
                                return i;
                            }
                            depth -= 1;
                        }
                        ";" | "||" | ":=" if depth == 0 => {
                            if std::env::var("PCAL_DEBUG").is_ok() {
                                eprintln!("stop@{i} {} d{depth} q{quant}", t.text);
                            }
                            return i;
                        }
                        "," if depth == 0 && quant == 0 => {
                            if std::env::var("PCAL_DEBUG").is_ok() {
                                eprintln!("stop@{i} , d{depth} q{quant}");
                            }
                            return i;
                        }
                        ":" => {
                            if quant > 0 {
                                quant -= 1;
                            }
                        }
                        "\\A" | "\\E" | "\\AA" | "\\EE" => quant += 1,
                        _ => {}
                    }
                    prev_field_open = matches!(t.text.as_str(), "[" | "{" | ",");
                }
                TokenKind::Ident => {
                    if !prev_field_open && DELIMITER_WORDS.contains(&t.text.as_str()) {
                        return i;
                    }
                    prev_field_open = false;
                }
                TokenKind::Eof => return i,
                _ => prev_field_open = false,
            }
            i += 1;
        }
        i
    }

    // ---- labels -------------------------------------------------------------

    /// `GetLabel`: consume `name : [+|-]` if present.
    fn label(&mut self) -> Result<Label> {
        if !self.label_next() {
            return Ok(None);
        }
        let name = self.advance();
        if name.text == "Done" || name.text == "Error" {
            return Err(SyntaxError::new(
                ErrorKind::Unexpected {
                    expected: "a label other than `Done' or `Error'".into(),
                    found: name.text.clone(),
                },
                name.span,
            ));
        }
        self.must_sym(":")?;
        self.has_label = true;
        self.all_labels.push(name.text.clone());
        if self.eat_sym("+") {
            self.plus_labels.push(name.text.clone());
            self.force_pc = true;
        } else if self.eat_sym("-") {
            self.minus_labels.push(name.text.clone());
            self.force_pc = true;
        }
        Ok(Some(name.text))
    }

    /// `IsLabelNext`.
    fn label_next(&self) -> bool {
        let t = self.tok();
        if t.kind != TokenKind::Ident || NON_LABEL_WORDS.contains(&t.text.as_str()) {
            return false;
        }
        self.peek(1).is_sym(":")
    }

    // ---- declarations --------------------------------------------------------

    fn var_decls(&mut self) -> Result<Vec<VarDecl>> {
        if self.at_word("variables") {
            self.advance();
        } else {
            self.must_word("variable")?;
        }
        let mut out = Vec::new();
        while !(self.at_word("begin")
            || self.at_sym("{")
            || self.at_word("procedure")
            || self.at_word("process")
            || self.at_word("fair")
            || self.at_word("define")
            || self.at_word("macro"))
        {
            out.push(self.var_decl()?);
        }
        Ok(out)
    }

    fn var_decl(&mut self) -> Result<VarDecl> {
        let t = self.tok().clone();
        if t.kind != TokenKind::Ident {
            return Err(self.err("variable name"));
        }
        self.advance();
        if self.at_sym("=") || self.at_sym("\\in") {
            let is_eq = self.equal_or_in()?;
            let val = self.expr()?;
            self.eat_comma_or_semicolon();
            Ok(VarDecl {
                var: t.text,
                is_eq,
                val: Some(val),
            })
        } else {
            self.has_default_initialization = true;
            self.eat_comma_or_semicolon();
            Ok(VarDecl {
                var: t.text,
                is_eq: true,
                val: None,
            })
        }
    }

    /// The `define` block, captured as verbatim text between its delimiters.
    fn define_block(&mut self) -> Result<String> {
        self.must_word("define")?;
        if self.c_syntax {
            self.must_sym("{")?;
        }
        let start = self.pos;
        let mut depth: i32 = 0;
        while !self.at_eof() {
            if self.p_syntax && self.at_word("end") && self.peek_word(1, "define") && depth == 0 {
                break;
            }
            if self.c_syntax && self.at_sym("}") && depth == 0 {
                break;
            }
            if matches!(self.tok().text.as_str(), "(" | "[" | "{" | "<<")
                && self.tok().kind == TokenKind::Sym
            {
                depth += 1;
            } else if matches!(self.tok().text.as_str(), ")" | "]" | "}" | ">>")
                && self.tok().kind == TokenKind::Sym
            {
                depth -= 1;
            }
            self.advance();
        }
        let end = self.pos;
        let start_off = self.tokens[start].span.start.offset as usize;
        let end_off = self.tokens[end].span.start.offset as usize;
        let text = self
            .source
            .get(start_off..end_off)
            .unwrap_or_default()
            .to_string();
        if self.p_syntax {
            self.must_word("end")?;
            self.must_word("define")?;
            self.eat_sym(";");
        } else {
            self.must_sym("}")?;
            self.eat_sym(";");
        }
        Ok(text)
    }

    // ---- macros --------------------------------------------------------------

    fn macro_def(&mut self, macros: &mut Vec<Macro>) -> Result<()> {
        self.must_word("macro")?;
        let name = self.advance();
        if name.kind != TokenKind::Ident {
            return Err(self.err("macro name"));
        }
        self.must_sym("(")?;
        let mut params = Vec::new();
        while !self.at_sym(")") {
            if !params.is_empty() {
                self.must_sym(",")?;
            }
            let p = self.advance();
            if p.kind != TokenKind::Ident {
                return Err(self.err("macro parameter"));
            }
            params.push(p.text);
        }
        self.must_sym(")")?;
        self.begin()?;
        let body = self.stmt_seq()?;
        self.end_block("macro")?;
        self.eat_sym(";");
        let expanded = self.expand_macros(body, macros, &name.text)?;
        macros.push(Macro {
            name: name.text,
            params,
            body: expanded,
        });
        Ok(())
    }

    // ---- procedures -----------------------------------------------------------

    fn procedure(&mut self) -> Result<Procedure> {
        self.must_word("procedure")?;
        let name = self.advance();
        if name.kind != TokenKind::Ident {
            return Err(self.err("procedure name"));
        }
        let mut params = Vec::new();
        if self.at_sym("(") {
            self.advance();
            while !self.at_sym(")") {
                if !params.is_empty() {
                    self.must_sym(",")?;
                }
                let p = self.advance();
                if p.kind != TokenKind::Ident {
                    return Err(self.err("procedure parameter"));
                }
                params.push(VarDecl {
                    var: p.text,
                    is_eq: true,
                    val: None,
                });
            }
            self.must_sym(")")?;
        }
        let decls = if self.at_word("variables") || self.at_word("variable") {
            self.var_decls()?
        } else {
            Vec::new()
        };
        self.begin()?;
        let body = self.stmt_seq()?;
        self.end_block("procedure")?;
        self.eat_sym(";");
        Ok(Procedure {
            name: name.text,
            params,
            decls,
            body,
        })
    }

    // ---- processes ------------------------------------------------------------

    fn process(&mut self, fairness: Fairness) -> Result<Process> {
        self.must_word("process")?;
        if self.c_syntax {
            self.must_sym("(")?;
        }
        let name = self.advance();
        if name.kind != TokenKind::Ident {
            return Err(self.err("process name"));
        }
        let is_eq = self.equal_or_in()?;
        let id = self.expr()?;
        if self.c_syntax {
            self.must_sym(")")?;
        }
        let decls = if self.at_word("begin") || self.at_sym("{") {
            Vec::new()
        } else {
            self.var_decls()?
        };
        self.begin()?;
        self.plus_labels.clear();
        self.minus_labels.clear();
        let body = self.stmt_seq()?;
        self.end_block("process")?;
        self.eat_sym(";");
        Ok(Process {
            name: name.text,
            fairness,
            is_eq,
            id,
            decls,
            body,
            plus_labels: std::mem::take(&mut self.plus_labels),
            minus_labels: std::mem::take(&mut self.minus_labels),
        })
    }

    // ---- statements -------------------------------------------------------------

    fn begin(&mut self) -> Result<()> {
        if self.p_syntax {
            self.must_word("begin")?;
        } else {
            self.must_sym("{")?;
        }
        Ok(())
    }

    fn end_block(&mut self, what: &str) -> Result<()> {
        if self.p_syntax {
            self.must_word("end")?;
            self.must_word(what)?;
            self.eat_sym(";");
        } else {
            self.must_sym("}")?;
        }
        Ok(())
    }

    /// `GetStmtSeq`: statements until `end`/`else`/`elsif`/`or` (p) or `}` (c).
    fn stmt_seq(&mut self) -> Result<Vec<Stmt>> {
        let mut out: Vec<Stmt> = Vec::new();
        loop {
            if self.at_eof() {
                return Err(self.err("statement"));
            }
            if self.c_syntax && self.at_sym("}") {
                break;
            }
            if self.p_syntax
                && (self.at_word("end")
                    || self.at_word("else")
                    || self.at_word("elsif")
                    || self.at_word("or"))
            {
                break;
            }
            if self.c_syntax && self.at_sym("{") {
                let lbl = self.label()?;
                out.extend(self.c_stmt_seq(&lbl)?);
            } else {
                let lbl = self.label()?;
                let mut stmt = self.stmt()?;
                *stmt.lbl_mut() = lbl;
                out.push(stmt);
            }
        }
        Ok(out)
    }

    /// `GetCStmt`: one statement or braced sequence, possibly labeled.
    fn c_stmt(&mut self) -> Result<Vec<Stmt>> {
        let lbl = self.label()?;
        if self.at_sym("{") {
            return self.c_stmt_seq(&lbl);
        }
        let mut stmt = self.stmt()?;
        *stmt.lbl_mut() = lbl;
        Ok(vec![stmt])
    }

    fn c_stmt_seq(&mut self, lbl: &Label) -> Result<Vec<Stmt>> {
        self.must_sym("{")?;
        let mut seq = self.stmt_seq()?;
        self.must_sym("}")?;
        self.eat_sym(";");
        if let Some(l) = lbl {
            if seq.first().is_some_and(|s| s.lbl().is_some()) {
                return Err(SyntaxError::new(
                    ErrorKind::Unexpected {
                        expected: "a statement sequence labeled once".into(),
                        found: format!("label `{l}' applied twice"),
                    },
                    self.tok().span,
                ));
            }
            if let Some(first) = seq.first_mut() {
                *first.lbl_mut() = Some(l.clone());
            }
        }
        Ok(seq)
    }

    /// `GetStmt`: dispatch on the leading keyword.
    fn stmt(&mut self) -> Result<Stmt> {
        if self.at_word("if") {
            return self.if_stmt();
        }
        if self.at_word("either") {
            return self.either();
        }
        if self.at_word("with") {
            return self.with();
        }
        if self.at_word("when") || self.at_word("await") {
            self.advance();
            let exp = self.expr()?;
            self.eat_semicolon()?;
            return Ok(Stmt::When { exp, lbl: None });
        }
        if self.at_word("print") || self.at_word("assert") {
            let is_print = self.at_word("print");
            self.advance();
            let exp = self.expr()?;
            self.eat_semicolon()?;
            return Ok(if is_print {
                Stmt::Print { exp, lbl: None }
            } else {
                Stmt::Assert { exp, lbl: None }
            });
        }
        if self.at_word("skip") {
            self.advance();
            self.eat_semicolon()?;
            return Ok(Stmt::Skip { lbl: None });
        }
        if self.at_word("call") {
            return self.call();
        }
        if self.at_word("return") {
            self.advance();
            self.eat_semicolon()?;
            return Ok(Stmt::Return { lbl: None });
        }
        if self.at_word("goto") {
            self.advance();
            let to = self.advance();
            if to.kind != TokenKind::Ident {
                return Err(self.err("label name"));
            }
            self.goto_used = true;
            if to.text == "Done" {
                self.goto_done_used = true;
            }
            self.eat_semicolon()?;
            return Ok(Stmt::Goto {
                to: to.text,
                lbl: None,
            });
        }
        if self.at_word("while") {
            return self.while_stmt();
        }
        if self.at_macro_call() {
            return self.macro_call();
        }
        self.assign()
    }

    fn if_stmt(&mut self) -> Result<Stmt> {
        self.must_word("if")?;
        let test = self.paren_expr_c()?;
        let then = if self.p_syntax {
            self.must_word("then")?;
            self.stmt_seq()?
        } else {
            self.c_stmt()?
        };
        let els = if self.p_syntax {
            if self.at_word("else") {
                self.advance();
                self.stmt_seq()?
            } else if self.at_word("elsif") {
                vec![self.elsif_chain()?]
            } else {
                Vec::new()
            }
        } else if self.at_word("else") {
            self.advance();
            self.c_stmt()?
        } else {
            Vec::new()
        };
        if self.p_syntax {
            self.must_word("end")?;
            self.must_word("if")?;
            self.eat_sym(";");
        }
        Ok(Stmt::If {
            test,
            then,
            els,
            lbl: None,
        })
    }

    fn paren_expr_c(&mut self) -> Result<Expr> {
        if self.c_syntax {
            self.must_sym("(")?;
            let e = self.expr()?;
            self.must_sym(")")?;
            Ok(e)
        } else {
            self.expr()
        }
    }

    /// An `elsif` continuation parses as a nested `if` sharing the outer
    /// `end if`.
    fn elsif_chain(&mut self) -> Result<Stmt> {
        self.must_word("elsif")?;
        let test = self.expr()?;
        self.must_word("then")?;
        let then = self.stmt_seq()?;
        let els = if self.at_word("else") {
            self.advance();
            self.stmt_seq()?
        } else if self.at_word("elsif") {
            vec![self.elsif_chain()?]
        } else {
            Vec::new()
        };
        Ok(Stmt::If {
            test,
            then,
            els,
            lbl: None,
        })
    }

    fn either(&mut self) -> Result<Stmt> {
        self.must_word("either")?;
        let mut ors = Vec::new();
        let mut has_or = false;
        loop {
            let clause = if self.p_syntax {
                self.stmt_seq()?
            } else {
                self.c_stmt()?
            };
            if clause.is_empty() {
                return Err(self.err("non-empty `or' clause"));
            }
            ors.push(clause);
            if self.at_word("or") {
                self.advance();
                has_or = true;
            } else {
                break;
            }
        }
        if self.p_syntax {
            self.must_word("end")?;
            self.must_word("either")?;
            self.eat_sym(";");
        }
        if !has_or {
            return Err(self.err("`or' in an `either'"));
        }
        Ok(Stmt::Either { ors, lbl: None })
    }

    /// A `with` statement; nested bindings parse as nested statements.
    fn with(&mut self) -> Result<Stmt> {
        self.must_word("with")?;
        if self.c_syntax {
            self.must_sym("(")?;
        }
        self.with_binding()
    }

    /// One `v = e` / `v \in e` binding and its body (`InnerGetWith`).
    fn with_binding(&mut self) -> Result<Stmt> {
        let var = self.advance();
        if var.kind != TokenKind::Ident {
            return Err(self.err("`with' variable"));
        }
        let is_eq = self.equal_or_in()?;
        let exp = self.expr()?;
        if self.p_syntax || !self.at_sym(")") {
            self.eat_comma_or_semicolon();
        }
        let body = if self.p_syntax && self.at_word("do") {
            self.advance();
            let body = self.stmt_seq()?;
            self.must_word("end")?;
            self.must_word("with")?;
            self.eat_sym(";");
            body
        } else if self.c_syntax && self.at_sym(")") {
            self.advance();
            self.c_stmt()?
        } else {
            vec![self.with_binding()?]
        };
        Ok(Stmt::With {
            var: var.text,
            is_eq,
            exp,
            body,
            lbl: None,
        })
    }

    fn while_stmt(&mut self) -> Result<Stmt> {
        self.must_word("while")?;
        let test = self.paren_expr_c()?;
        let unlab_do = if self.p_syntax {
            self.must_word("do")?;
            let body = self.stmt_seq()?;
            self.must_word("end")?;
            self.must_word("while")?;
            self.eat_sym(";");
            body
        } else {
            self.c_stmt()?
        };
        if unlab_do.is_empty() {
            return Err(self.err("body of `while'"));
        }
        Ok(Stmt::While {
            test,
            unlab_do,
            lbl: None,
        })
    }

    fn assign(&mut self) -> Result<Stmt> {
        let mut ass = vec![self.single_assign()?];
        while self.at_sym("||") {
            self.advance();
            ass.push(self.single_assign()?);
        }
        self.eat_semicolon()?;
        Ok(Stmt::Assign { ass, lbl: None })
    }

    fn single_assign(&mut self) -> Result<SingleAssign> {
        let var = self.advance();
        if var.kind != TokenKind::Ident {
            return Err(self.err("variable"));
        }
        let mut sels = Vec::new();
        while !self.at_sym(":=") {
            if self.at_sym("[") {
                self.advance();
                let ix = self.expr()?;
                self.must_sym("]")?;
                sels.push(Selector::Index(ix));
            } else if self.at_sym(".") {
                self.advance();
                let f = self.advance();
                if f.kind != TokenKind::Ident {
                    return Err(self.err("record field"));
                }
                sels.push(Selector::Field(f.text));
            } else {
                return Err(self.err("`[' or `.' in an assignment left-hand side"));
            }
        }
        self.must_sym(":=")?;
        let rhs = self.expr()?;
        Ok(SingleAssign {
            var: var.text,
            sels,
            rhs,
        })
    }

    /// `call P(a, b) ;`, optionally followed by `return` or `goto`.
    fn call(&mut self) -> Result<Stmt> {
        self.must_word("call")?;
        let to = self.advance();
        if to.kind != TokenKind::Ident {
            return Err(self.err("procedure name"));
        }
        self.must_sym("(")?;
        let mut args = Vec::new();
        while !self.at_sym(")") {
            if !args.is_empty() {
                self.must_sym(",")?;
            }
            args.push(self.expr()?);
        }
        self.must_sym(")")?;
        self.must_sym(";")?;
        if self.at_word("return") {
            self.advance();
            self.eat_semicolon()?;
            return Ok(Stmt::Return { lbl: None });
        }
        if self.at_word("goto") {
            self.advance();
            let t = self.advance();
            if t.kind != TokenKind::Ident {
                return Err(self.err("label name"));
            }
            self.goto_used = true;
            if t.text == "Done" {
                self.goto_done_used = true;
            }
            self.eat_semicolon()?;
            return Ok(Stmt::Goto {
                to: t.text,
                lbl: None,
            });
        }
        Ok(Stmt::Call {
            to: to.text,
            args,
            lbl: None,
        })
    }

    fn at_macro_call(&self) -> bool {
        self.tok().kind == TokenKind::Ident && self.peek(1).is_sym("(")
    }

    fn macro_call(&mut self) -> Result<Stmt> {
        let name = self.advance();
        self.must_sym("(")?;
        let mut args = Vec::new();
        while !self.at_sym(")") {
            if !args.is_empty() {
                self.must_sym(",")?;
            }
            args.push(self.expr()?);
        }
        self.must_sym(")")?;
        self.eat_semicolon()?;
        Ok(Stmt::MacroCall {
            name: name.text,
            args,
            lbl: None,
        })
    }

    // ---- macro expansion ---------------------------------------------------

    /// Expand every macro call in a statement sequence, substituting
    /// arguments for parameters (`ExpandMacroCall` and friends).
    fn expand_macros(&self, stmts: Vec<Stmt>, macros: &[Macro], at: &str) -> Result<Vec<Stmt>> {
        let mut out = Vec::new();
        for stmt in stmts {
            match stmt {
                Stmt::MacroCall { name, args, lbl } => {
                    let def = macros.iter().find(|m| m.name == name).ok_or_else(|| {
                        SyntaxError::new(
                            ErrorKind::Unexpected {
                                expected: format!("a defined macro (called from `{at}')"),
                                found: format!("macro `{name}'"),
                            },
                            Span::default(),
                        )
                    })?;
                    if def.params.len() != args.len() {
                        return Err(SyntaxError::new(
                            ErrorKind::Unexpected {
                                expected: format!(
                                    "macro `{name}' called with {} arguments",
                                    def.params.len()
                                ),
                                found: format!("{} arguments", args.len()),
                            },
                            Span::default(),
                        ));
                    }
                    let mut body = def.body.clone();
                    for (p, a) in def.params.iter().zip(&args) {
                        body = body
                            .into_iter()
                            .map(|s| subst_stmt(s, p, a))
                            .collect::<Vec<_>>();
                    }
                    if let (Some(first_lbl), Some(first)) = (lbl, body.first_mut())
                        && first.lbl().is_none()
                    {
                        *first.lbl_mut() = Some(first_lbl);
                    }
                    out.extend(body);
                }
                other => out.extend(self.expand_macros_stmt(other, macros, at)?),
            }
        }
        Ok(out)
    }

    /// Walk one compound statement, expanding macro calls in its children.
    fn expand_macros_stmt(&self, stmt: Stmt, macros: &[Macro], at: &str) -> Result<Vec<Stmt>> {
        match stmt {
            Stmt::Assign { .. }
            | Stmt::When { .. }
            | Stmt::Print { .. }
            | Stmt::Assert { .. }
            | Stmt::Skip { .. }
            | Stmt::Goto { .. }
            | Stmt::Call { .. }
            | Stmt::Return { .. } => Ok(vec![stmt]),
            Stmt::If {
                test,
                then,
                els,
                lbl,
            } => Ok(vec![Stmt::If {
                test,
                then: self.expand_macros(then, macros, at)?,
                els: self.expand_macros(els, macros, at)?,
                lbl,
            }]),
            Stmt::Either { ors, lbl } => {
                let mut new_ors = Vec::new();
                for or in ors {
                    new_ors.push(self.expand_macros(or, macros, at)?);
                }
                Ok(vec![Stmt::Either { ors: new_ors, lbl }])
            }
            Stmt::With {
                var,
                is_eq,
                exp,
                body,
                lbl,
            } => Ok(vec![Stmt::With {
                var,
                is_eq,
                exp,
                body: self.expand_macros(body, macros, at)?,
                lbl,
            }]),
            Stmt::While {
                test,
                unlab_do,
                lbl,
            } => Ok(vec![Stmt::While {
                test,
                unlab_do: self.expand_macros(unlab_do, macros, at)?,
                lbl,
            }]),
            Stmt::MacroCall { .. } => unreachable!("matched by the caller"),
        }
    }

    // ---- top level ----------------------------------------------------------

    fn algorithm(&mut self) -> Result<Algorithm> {
        if self.fair_algorithm {
            self.must_word("algorithm")?;
        }
        let name = self.advance();
        if name.kind != TokenKind::Ident {
            return Err(self.err("algorithm name"));
        }
        if self.at_sym("{") {
            self.advance();
            self.c_syntax = true;
        } else {
            self.p_syntax = true;
        }
        let decls = if self.at_word("variable") || self.at_word("variables") {
            self.var_decls()?
        } else {
            Vec::new()
        };
        let defs = if self.at_word("define") {
            Some(self.define_block()?)
        } else {
            None
        };
        let mut macros = Vec::new();
        while self.at_word("macro") {
            self.macro_def(&mut macros)?;
        }
        let mut procedures = Vec::new();
        while self.at_word("procedure") {
            self.force_pc = true;
            procedures.push(self.procedure()?);
        }
        let is_process_next = self.at_word("process")
            || (self.at_word("fair")
                && (self.peek_word(1, "process")
                    || (self.peek_word(1, "+") && self.peek_word(2, "process"))));
        if is_process_next {
            let mut processes = Vec::new();
            while self.at_word("fair") || self.at_word("process") {
                let mut fairness = Fairness::Unfair;
                if self.at_word("fair") {
                    self.advance();
                    if self.eat_sym("+") {
                        fairness = Fairness::Strong;
                    } else {
                        fairness = Fairness::Weak;
                    }
                }
                processes.push(self.process(fairness)?);
            }
            self.end_block("algorithm")?;
            let processes = processes
                .into_iter()
                .map(|p| {
                    let body =
                        self.expand_macros(p.body, &macros, &format!("process {}", p.name))?;
                    Ok(Process { body, ..p })
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(Algorithm::Multiprocess {
                name: name.text,
                decls,
                defs,
                macros,
                procedures,
                processes,
            })
        } else {
            self.begin()?;
            let body = self.stmt_seq()?;
            self.end_block("algorithm")?;
            let body = self.expand_macros(body, &macros, &name.text)?;
            Ok(Algorithm::Uniprocess {
                name: name.text,
                decls,
                defs,
                macros,
                procedures,
                body,
            })
        }
    }
}

/// Substitute an argument expression for a parameter through a statement
/// (`SubstituteInStmtSeq`).
fn subst_stmt(stmt: Stmt, param: &str, arg: &Expr) -> Stmt {
    match stmt {
        Stmt::Assign { ass, lbl } => Stmt::Assign {
            ass: ass
                .into_iter()
                .map(|a| subst_single_assign(a, param, arg))
                .collect(),
            lbl,
        },
        Stmt::If {
            test,
            then,
            els,
            lbl,
        } => Stmt::If {
            test: subst_free(&test, param, arg),
            then: then
                .into_iter()
                .map(|s| subst_stmt(s, param, arg))
                .collect(),
            els: els.into_iter().map(|s| subst_stmt(s, param, arg)).collect(),
            lbl,
        },
        Stmt::Either { ors, lbl } => Stmt::Either {
            ors: ors
                .into_iter()
                .map(|o| o.into_iter().map(|s| subst_stmt(s, param, arg)).collect())
                .collect(),
            lbl,
        },
        Stmt::With {
            var,
            is_eq,
            exp,
            body,
            lbl,
        } => {
            let shadowed = var == param;
            Stmt::With {
                var,
                is_eq,
                exp: subst_free(&exp, param, arg),
                body: if shadowed {
                    body
                } else {
                    body.into_iter()
                        .map(|s| subst_stmt(s, param, arg))
                        .collect()
                },
                lbl,
            }
        }
        Stmt::When { exp, lbl } => Stmt::When {
            exp: subst_free(&exp, param, arg),
            lbl,
        },
        Stmt::Print { exp, lbl } => Stmt::Print {
            exp: subst_free(&exp, param, arg),
            lbl,
        },
        Stmt::Assert { exp, lbl } => Stmt::Assert {
            exp: subst_free(&exp, param, arg),
            lbl,
        },
        Stmt::Skip { lbl } => Stmt::Skip { lbl },
        Stmt::While {
            test,
            unlab_do,
            lbl,
        } => Stmt::While {
            test: subst_free(&test, param, arg),
            unlab_do: unlab_do
                .into_iter()
                .map(|s| subst_stmt(s, param, arg))
                .collect(),
            lbl,
        },
        Stmt::Goto { to, lbl } => Stmt::Goto { to, lbl },
        Stmt::Call { to, args, lbl } => Stmt::Call {
            to,
            args: args
                .into_iter()
                .map(|a| subst_free(&a, param, arg))
                .collect(),
            lbl,
        },
        Stmt::Return { lbl } => Stmt::Return { lbl },
        Stmt::MacroCall { name, args, lbl } => Stmt::MacroCall {
            name,
            args: args
                .into_iter()
                .map(|a| subst_free(&a, param, arg))
                .collect(),
            lbl,
        },
    }
}

/// A macro parameter substituted on a left-hand side becomes the target's
/// head and prepends its selectors (`x[y] := 1` with `a[1]` for `x` yields
/// `a[1][y] := 1`).
fn subst_single_assign(a: SingleAssign, param: &str, arg: &Expr) -> SingleAssign {
    let rhs = subst_free(&a.rhs, param, arg);
    if a.var != param {
        return SingleAssign {
            var: a.var,
            sels: a
                .sels
                .into_iter()
                .map(|s| match s {
                    Selector::Index(e) => Selector::Index(subst_free(&e, param, arg)),
                    Selector::Field(f) => Selector::Field(f),
                })
                .collect(),
            rhs,
        };
    }
    let mut head = None;
    let mut sels: Vec<Selector> = Vec::new();
    decompose(arg, &mut head, &mut sels);
    match head {
        Some(h) => {
            let mut all = sels;
            all.extend(a.sels);
            SingleAssign {
                var: h,
                sels: all,
                rhs,
            }
        }
        None => SingleAssign {
            var: a.var,
            sels: a.sels,
            rhs,
        },
    }
}

fn decompose(e: &Expr, head: &mut Option<String>, sels: &mut Vec<Selector>) {
    use crate::ast::ExprKind;
    match &e.kind {
        ExprKind::Name(q) => {
            if let Some(b) = q.base() {
                *head = Some(b.name.clone());
            }
        }
        ExprKind::FnApply { func, args } => {
            decompose(func, head, sels);
            if args.len() == 1 {
                sels.push(Selector::Index(args[0].clone()));
            }
        }
        ExprKind::Field { record, field } => {
            decompose(record, head, sels);
            sels.push(Selector::Field(field.name.clone()));
        }
        ExprKind::Paren(inner) => decompose(inner, head, sels),
        _ => {}
    }
}

// Re-exported for the later passes.
