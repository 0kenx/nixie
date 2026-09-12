//! The TLA+ parser: recursive descent for units, Pratt for expressions.
//!
//! # Why layout lives here and not in the lexer
//!
//! `docs/TLA_FRONTEND_DESIGN.md` §1.1 proposed handling junction lists as a
//! Haskell-style token-stream transformer that inserts virtual brackets, so
//! that the grammar proper stays context-free. **Implementation found that
//! this does not work**, and the reason is worth recording.
//!
//! A `/\` opens a bulleted list only when it appears where an *expression* is
//! expected. In `x == a /\ b` the same token is an ordinary infix operator, and
//! a lexical pass cannot tell the two apart without reconstructing
//! expression-position — the same problem as regex-vs-division in a JavaScript
//! lexer, and equally prone to misfiring. The parser already knows, exactly, so
//! layout is decided here: `parse_prefix` treats `/\` in prefix
//! position as a list, and `at_layout_boundary` stops the Pratt loop
//! at a token that would close an enclosing list.
//!
//! # Recursion depth
//!
//! `AGENTS.md` forbids unbounded native recursion over user-controlled input.
//! A recursive-descent parser *is* recursion over user-controlled input, so
//! depth is counted and [`ErrorKind::RecursionLimit`] is returned before the
//! native stack can overflow. Deep input yields a diagnostic, never a crash.

use crate::ast::*;
use crate::error::{ErrorKind, Result, SyntaxError};
use crate::lexer;
use crate::op::{self, Fixity, OpInfo};
use crate::span::Span;
use crate::token::{Comment, Keyword, Token, TokenKind};

/// Default maximum expression nesting depth.
pub const DEFAULT_MAX_DEPTH: usize = 400;

/// A parsed source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedFile {
    /// The top-level module.
    pub module: Module,
    /// Comments retained by the lexer, for `@type:` annotation extraction.
    pub comments: Vec<Comment>,
}

/// The parser.
pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    /// Columns of the junction lists currently open, innermost last. Strictly
    /// increasing, so only the top needs consulting.
    juncts: Vec<(u32, Junct)>,
    /// Column at or left of which a token ends the unit body currently being
    /// parsed. TLA+ starts every top-level unit at column 1, so a token there
    /// terminates the previous definition however it would otherwise continue.
    /// Consulted only at the bracket depth the floor was established at.
    unit_floor: u32,
    /// Bracket depth at which the unit floor was established. A `LET`
    /// definition inside parentheses still gets a floor; it just applies at
    /// that depth rather than at depth zero.
    unit_floor_depth: usize,
    /// Nesting depth of `(`, `[`, `{`, `<<`. Inside brackets a column-1 token
    /// is ordinary continuation, not a new unit.
    bracket_depth: usize,
    depth: usize,
    max_depth: usize,
}

impl Parser {
    /// Create a parser over an already-lexed token stream.
    #[must_use]
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            pos: 0,
            juncts: Vec::new(),
            unit_floor: 0,
            unit_floor_depth: 0,
            bracket_depth: 0,
            depth: 0,
            max_depth: DEFAULT_MAX_DEPTH,
        }
    }

    /// Override the maximum expression nesting depth.
    #[must_use]
    pub fn with_max_depth(mut self, max_depth: usize) -> Self {
        self.max_depth = max_depth;
        self
    }

    // ---- token plumbing -----------------------------------------------------

    /// The token at `self.pos + n`, saturating at the trailing `Eof`.
    fn peek_at(&self, n: usize) -> &Token {
        let idx = (self.pos + n).min(self.tokens.len().saturating_sub(1));
        match self.tokens.get(idx) {
            Some(t) => t,
            // The stream always ends in `Eof`, so this is unreachable for a
            // stream built by the lexer. Returning the last token rather than
            // panicking keeps the "no unwrap in production" rule honest even
            // if a caller hands us a hand-built stream.
            None => self.eof_fallback(),
        }
    }

    fn eof_fallback(&self) -> &Token {
        match self.tokens.last() {
            Some(t) => t,
            None => &EOF_TOKEN_SENTINEL,
        }
    }

    fn peek(&self) -> &Token {
        self.peek_at(0)
    }

    fn at_eof(&self) -> bool {
        self.peek().kind == TokenKind::Eof
    }

    fn advance(&mut self) -> Token {
        let tok = self.peek().clone();
        if self.pos < self.tokens.len().saturating_sub(1) {
            self.pos += 1;
        }
        tok
    }

    fn describe(tok: &Token) -> String {
        match tok.kind {
            TokenKind::Eof => "end of input".to_string(),
            TokenKind::Ident => format!("identifier `{}`", tok.text),
            TokenKind::Keyword(kw) => format!("`{}`", kw.as_str()),
            TokenKind::Str => format!("string {:?}", tok.text),
            _ => format!("`{}`", tok.text),
        }
    }

    fn err<T>(&self, expected: &str) -> Result<T> {
        let tok = self.peek();
        Err(SyntaxError::new(
            ErrorKind::Unexpected {
                expected: expected.to_string(),
                found: Self::describe(tok),
            },
            tok.span,
        ))
    }

    fn expect_sym(&mut self, canonical: &str) -> Result<Token> {
        if self.peek().is_sym(canonical) {
            Ok(self.advance())
        } else {
            self.err(&format!("`{canonical}`"))
        }
    }

    fn expect_kw(&mut self, kw: Keyword) -> Result<Token> {
        if self.peek().is_kw(kw) {
            Ok(self.advance())
        } else {
            self.err(&format!("`{}`", kw.as_str()))
        }
    }

    fn eat_sym(&mut self, canonical: &str) -> bool {
        if self.peek().is_sym(canonical) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: Keyword) -> bool {
        if self.peek().is_kw(kw) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// A record field name.
    ///
    /// Reserved words are legal field names: `bar.NEW` and `[f EXCEPT !.NEW =
    /// 0]` both occur in the TLA+ test suite. `NEW` and friends are only
    /// reserved in the positions that actually use them.
    fn expect_field_name(&mut self) -> Result<Ident> {
        let tok = self.peek().clone();
        match tok.kind {
            TokenKind::Ident | TokenKind::Keyword(_) | TokenKind::Sym => {
                // A symbol is only a field name if it reads as a word
                // (`DOMAIN`, `SUBSET`, …); punctuation never is.
                if tok.kind == TokenKind::Sym
                    && !tok.text.chars().next().is_some_and(char::is_alphabetic)
                {
                    return self.err("a record field name");
                }
                self.advance();
                Ok(Ident {
                    name: tok.text,
                    span: tok.span,
                })
            }
            _ => self.err("a record field name"),
        }
    }

    fn expect_ident(&mut self) -> Result<Ident> {
        if self.peek().kind == TokenKind::Ident {
            let tok = self.advance();
            Ok(Ident {
                name: tok.text,
                span: tok.span,
            })
        } else {
            self.err("an identifier")
        }
    }

    // ---- modules and units --------------------------------------------------

    /// Parse a whole file: one top-level module.
    ///
    /// # Errors
    ///
    /// Returns the first [`SyntaxError`] encountered.
    pub fn parse_file(&mut self) -> Result<Module> {
        self.skip_to_module_header();
        self.parse_module()
    }

    /// Discard everything before the first `---- MODULE` header.
    ///
    /// A `.tla` file may legally open with prose, a copyright block, or
    /// typesetting escapes; SANY ignores all of it and so must we. Only done
    /// at the top level -- inside a module, stray tokens are real errors.
    fn skip_to_module_header(&mut self) {
        while !self.at_eof() {
            if self.peek().kind == TokenKind::Dashes && self.peek_at(1).is_kw(Keyword::Module) {
                return;
            }
            self.advance();
        }
    }

    fn parse_module(&mut self) -> Result<Module> {
        let start = self.peek().span;
        if self.peek().kind != TokenKind::Dashes {
            return self.err("a module header `---- MODULE Name ----`");
        }
        self.advance();
        self.expect_kw(Keyword::Module)?;
        let name = self.expect_ident()?;
        if self.peek().kind != TokenKind::Dashes {
            return self.err("`----` to close the module header");
        }
        self.advance();

        let mut units = Vec::new();
        loop {
            if self.peek().kind == TokenKind::ModuleFooter {
                let end = self.advance().span;
                return Ok(Module {
                    name,
                    units,
                    span: start.merge(end),
                });
            }
            if self.at_eof() {
                return self.err("`====` to close the module");
            }
            units.push(self.parse_unit()?);
        }
    }

    fn parse_unit(&mut self) -> Result<Unit> {
        let floor = self.peek().col();
        self.with_unit_floor(floor, Self::parse_unit_inner)
    }

    fn parse_unit_inner(&mut self) -> Result<Unit> {
        let start = self.peek().span;

        // `----` is either a separator or the header of a nested module.
        if self.peek().kind == TokenKind::Dashes {
            if self.peek_at(1).is_kw(Keyword::Module) {
                let sub = self.parse_module()?;
                let span = sub.span;
                return Ok(Unit {
                    kind: UnitKind::Submodule(Box::new(sub)),
                    span,
                });
            }
            let span = self.advance().span;
            return Ok(Unit {
                kind: UnitKind::Separator,
                span,
            });
        }

        let local = self.eat_kw(Keyword::Local);

        let tok = self.peek().clone();
        match tok.kind {
            TokenKind::Keyword(Keyword::Extends) => {
                if local {
                    return Err(SyntaxError::new(
                        ErrorKind::Unexpected {
                            expected: "a definition after `LOCAL`".to_string(),
                            found: "`EXTENDS`".to_string(),
                        },
                        tok.span,
                    ));
                }
                self.advance();
                let mut names = vec![self.expect_ident()?];
                while self.eat_sym(",") {
                    names.push(self.expect_ident()?);
                }
                let span = start.merge(self.prev_span());
                Ok(Unit {
                    kind: UnitKind::Extends(names),
                    span,
                })
            }
            TokenKind::Keyword(Keyword::Constant | Keyword::Constants) => {
                self.advance();
                let mut decls = vec![self.parse_op_decl()?];
                while self.eat_sym(",") {
                    decls.push(self.parse_op_decl()?);
                }
                let span = start.merge(self.prev_span());
                Ok(Unit {
                    kind: UnitKind::ConstantDecl(decls),
                    span,
                })
            }
            TokenKind::Keyword(Keyword::Variable | Keyword::Variables) => {
                self.advance();
                let mut names = vec![self.expect_ident()?];
                while self.eat_sym(",") {
                    names.push(self.expect_ident()?);
                }
                let span = start.merge(self.prev_span());
                Ok(Unit {
                    kind: UnitKind::VariableDecl(names),
                    span,
                })
            }
            TokenKind::Keyword(Keyword::Recursive) => {
                self.advance();
                let mut decls = vec![self.parse_op_decl()?];
                while self.eat_sym(",") {
                    decls.push(self.parse_op_decl()?);
                }
                let span = start.merge(self.prev_span());
                Ok(Unit {
                    kind: UnitKind::Recursive(decls),
                    span,
                })
            }
            TokenKind::Keyword(Keyword::Instance) => {
                let instance = self.parse_instance()?;
                let span = start.merge(instance.span);
                Ok(Unit {
                    kind: UnitKind::Instance { local, instance },
                    span,
                })
            }
            TokenKind::Keyword(Keyword::Assume | Keyword::Assumption | Keyword::Axiom) => {
                self.advance();
                let name = self.try_parse_named_prefix();
                let body = self.parse_expr(0)?;
                let span = start.merge(body.span);
                Ok(Unit {
                    kind: UnitKind::Assume { name, body },
                    span,
                })
            }
            TokenKind::Keyword(
                Keyword::Theorem | Keyword::Lemma | Keyword::Corollary | Keyword::Proposition,
            ) => {
                self.advance();
                let name = self.try_parse_named_prefix();
                let body = self.parse_expr(0)?;
                let proof = self.parse_proof_opt(start.start.col)?;
                let span = start.merge(self.prev_span());
                Ok(Unit {
                    kind: UnitKind::Theorem { name, body, proof },
                    span,
                })
            }
            // TLAPS proof directives at unit level. Apalache ignores proofs,
            // so these are consumed with their extent recorded and nothing
            // else; they are represented as a proof-only unit.
            TokenKind::Keyword(Keyword::Use | Keyword::Hide | Keyword::ProofKw) => {
                self.advance();
                self.skip_proof_tokens(start.start.col);
                // `PROOF` is followed by the proof body, which is usually a
                // run of `<n>` steps; consume those too, or the first step
                // marker is left for the unit parser to choke on.
                while self.at_proof_step_marker() {
                    self.consume_proof_step_marker();
                    self.skip_proof_tokens(start.start.col);
                }
                let span = start.merge(self.prev_span());
                Ok(Unit {
                    kind: UnitKind::ProofDirective(Proof { span }),
                    span,
                })
            }
            _ => self.parse_definition(local, start),
        }
    }

    /// `THEOREM Name == e` and `ASSUME Name == e` name their unit. Only commit
    /// to that reading when `Ident ==` is actually there.
    fn try_parse_named_prefix(&mut self) -> Option<Ident> {
        if self.peek().kind == TokenKind::Ident && self.peek_at(1).is_sym("==") {
            let tok = self.advance();
            self.advance();
            return Some(Ident {
                name: tok.text,
                span: tok.span,
            });
        }
        None
    }

    fn prev_span(&self) -> Span {
        let idx = self.pos.saturating_sub(1);
        match self.tokens.get(idx) {
            Some(t) => t.span,
            None => Span::default(),
        }
    }

    /// The operator-symbol spelling in a declaration, if one starts here.
    ///
    /// `CONSTANT _++_, Plus(_, _)` declares an infix operator alongside an
    /// ordinary one, and `BoxTest(-._)` takes a prefix operator as a
    /// parameter. The three shapes are `_ op _` (infix, arity 2), `op _`
    /// (prefix, arity 1) and `_ op` (postfix, arity 1). Returns `None` when
    /// this is not an operator declaration, having consumed nothing.
    fn try_parse_operator_decl(&mut self) -> Option<OpDecl> {
        let start = self.peek().span;

        // `-` `.` is the prefix-minus spelling `-.`; the lexer keeps them
        // apart so that `x-.5` is not mis-lexed.
        let (sym_len, spelling) = if self.peek().is_sym("_") {
            // `_ op _` or `_ op`.
            let at = 1;
            let (len, spell) = if self.peek_at(at).is_sym("-") && self.peek_at(at + 1).is_sym(".") {
                (2usize, "-.".to_string())
            } else if self.peek_at(at).kind == TokenKind::Sym {
                (1usize, self.peek_at(at).text.clone())
            } else {
                return None;
            };
            let after = 1 + len;
            let arity = if self.peek_at(after).is_sym("_") {
                2
            } else {
                1
            };
            if arity == 2 && op::infix_info(&spell).is_none() {
                return None;
            }
            if arity == 1 && op::postfix_info(&spell).is_none() {
                return None;
            }
            let total = after + if arity == 2 { 1 } else { 0 };
            for _ in 0..total {
                self.advance();
            }
            let span = start.merge(self.prev_span());
            return Some(OpDecl {
                name: Ident { name: spell, span },
                arity,
                span,
            });
        } else if self.peek().is_sym("-") && self.peek_at(1).is_sym(".") {
            (2usize, "-.".to_string())
        } else if self.peek().kind == TokenKind::Sym {
            (1usize, self.peek().text.clone())
        } else {
            return None;
        };

        // `op _` — a prefix operator.
        if op::prefix_info(&spelling).is_none() && spelling != "-." {
            return None;
        }
        if !self.peek_at(sym_len).is_sym("_") {
            return None;
        }
        for _ in 0..=sym_len {
            self.advance();
        }
        let span = start.merge(self.prev_span());
        Some(OpDecl {
            name: Ident {
                name: spelling,
                span,
            },
            arity: 1,
            span,
        })
    }

    /// `Op`, or `Op(_, _)` declaring arity, or an operator symbol.
    fn parse_op_decl(&mut self) -> Result<OpDecl> {
        if let Some(decl) = self.try_parse_operator_decl() {
            return Ok(decl);
        }
        let start = self.peek().span;
        let name = self.expect_ident()?;
        let mut arity = 0;
        if self.peek().is_sym("(") {
            self.advance();
            loop {
                if self.eat_sym("_") {
                    arity += 1;
                } else {
                    return self.err("`_` in an arity declaration");
                }
                if !self.eat_sym(",") {
                    break;
                }
            }
            self.expect_sym(")")?;
        }
        let span = start.merge(self.prev_span());
        Ok(OpDecl { name, arity, span })
    }

    fn parse_instance(&mut self) -> Result<Instance> {
        let start = self.expect_kw(Keyword::Instance)?.span;
        let module = self.expect_ident()?;
        let mut substitutions = Vec::new();
        if self.eat_kw(Keyword::With) {
            loop {
                let lhs = self.parse_subst_lhs()?;
                self.expect_sym("<-")?;
                let rhs = self.parse_expr(0)?;
                substitutions.push((lhs, rhs));
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        let span = start.merge(self.prev_span());
        Ok(Instance {
            module,
            substitutions,
            span,
        })
    }

    /// The left side of a `WITH` substitution is a declared name, which may be
    /// an operator symbol rather than an identifier.
    fn parse_subst_lhs(&mut self) -> Result<Ident> {
        let tok = self.peek().clone();
        match tok.kind {
            TokenKind::Ident => self.expect_ident(),
            TokenKind::Sym
                if op::infix_info(&tok.text).is_some()
                    || op::prefix_info(&tok.text).is_some()
                    || op::postfix_info(&tok.text).is_some() =>
            {
                self.advance();
                Ok(Ident {
                    name: tok.text,
                    span: tok.span,
                })
            }
            _ => self.err("a name or operator symbol to substitute for"),
        }
    }

    /// Record a proof's extent without interpreting its statements.
    ///
    /// Apalache does not check proofs, so parity needs the proof *found and
    /// skipped with the right extent*, not understood. What it must never do
    /// is guess the extent and swallow a following unit — so the skip is
    /// driven by the proof's own structure rather than by indentation alone:
    ///
    /// * a terminal proof is `OBVIOUS`, `OMITTED`, or `BY …`;
    /// * a structured proof is a run of steps, each introduced by a
    ///   `<level>name` marker, ending at the `QED` step.
    ///
    /// Step markers are the anchor. Between them the tokens are skipped with
    /// bracket depth tracked, and the run stops at a token that can only begin
    /// a new unit. Proof *statements* are not built into the AST; the span is
    /// recorded so a later milestone can come back and parse them.
    fn parse_proof_opt(&mut self, theorem_col: u32) -> Result<Option<Proof>> {
        let tok = self.peek().clone();
        let start = tok.span;
        match tok.kind {
            TokenKind::Keyword(Keyword::Obvious | Keyword::Omitted) => {
                let span = self.advance().span;
                Ok(Some(Proof { span }))
            }
            TokenKind::Keyword(Keyword::By) => {
                self.advance();
                self.skip_proof_tokens(theorem_col);
                Ok(Some(Proof {
                    span: start.merge(self.prev_span()),
                }))
            }
            _ if self.at_proof_step_marker() => {
                while self.at_proof_step_marker() {
                    self.consume_proof_step_marker();
                    self.skip_proof_tokens(theorem_col);
                }
                Ok(Some(Proof {
                    span: start.merge(self.prev_span()),
                }))
            }
            _ => Ok(None),
        }
    }

    /// Is the cursor the first token on its source line?
    ///
    /// Proof-step markers always are, which is what makes it safe to treat
    /// `<1>` as a marker rather than as a `<` that happens to be followed by
    /// a numeral and a `>`.
    fn at_line_start(&self) -> bool {
        let here = self.peek().span.start.line;
        match self.pos.checked_sub(1).and_then(|i| self.tokens.get(i)) {
            Some(prev) => prev.span.end.line < here,
            None => true,
        }
    }

    /// Is the cursor on a `<level>name` proof-step marker?
    ///
    /// The lexer has no reason to know about proof steps, so `<1>2a.` arrives
    /// as `<` `1` `>` `2a` `.`; recognising it here keeps that knowledge in
    /// the one place that needs it.
    fn at_proof_step_marker(&self) -> bool {
        if !self.peek().is_sym("<") {
            return false;
        }
        if !matches!(self.peek_at(1).kind, TokenKind::Int(_)) {
            return false;
        }
        // `<1>` and `<+>` / `<*>` are all legal level markers.
        self.peek_at(2).is_sym(">")
    }

    fn consume_proof_step_marker(&mut self) {
        self.advance(); // `<`
        self.advance(); // level
        self.advance(); // `>`
        // An optional step name, then an optional `.`.
        if matches!(self.peek().kind, TokenKind::Ident | TokenKind::Int(_)) {
            self.advance();
        }
        if self.peek().is_sym(".") {
            self.advance();
        }
    }

    /// Skip the body of one proof step, stopping before the next step marker
    /// or the start of the next unit.
    fn skip_proof_tokens(&mut self, theorem_col: u32) {
        let mut depth = 0i32;
        while !self.at_eof() {
            let tok = self.peek();
            if depth == 0 {
                if matches!(tok.kind, TokenKind::ModuleFooter | TokenKind::Dashes) {
                    return;
                }
                if self.at_proof_step_marker() {
                    return;
                }
                if tok.col() <= theorem_col && self.starts_new_unit() {
                    return;
                }
            }
            if tok.kind == TokenKind::Sym {
                match tok.text.as_str() {
                    "(" | "[" | "{" | "<<" => depth += 1,
                    ")" | "]" | "}" | ">>" => depth -= 1,
                    _ => {}
                }
            }
            self.advance();
        }
    }

    /// Could the cursor be the first token of a new top-level unit?
    ///
    /// Used only to bound a proof skip, so it errs towards *not* stopping:
    /// a false positive would truncate a proof and produce a spurious error,
    /// while a false negative merely swallows a little more of the proof.
    fn starts_new_unit(&self) -> bool {
        let tok = self.peek();
        match tok.kind {
            TokenKind::Keyword(
                Keyword::Extends
                | Keyword::Constant
                | Keyword::Constants
                | Keyword::Variable
                | Keyword::Variables
                | Keyword::Local
                | Keyword::Instance
                | Keyword::Recursive
                | Keyword::Assume
                | Keyword::Assumption
                | Keyword::Axiom
                | Keyword::Theorem
                | Keyword::Lemma
                | Keyword::Corollary
                | Keyword::Proposition,
            ) => true,
            // `Name ==`, `Name(…) ==`, `Name[…] ==`.
            TokenKind::Ident => {
                self.peek_at(1).is_sym("==")
                    || self.peek_at(1).is_sym("(")
                    || self.peek_at(1).is_sym("[")
            }
            _ => false,
        }
    }

    /// A definition. Six shapes, distinguished by bounded lookahead:
    /// `Op == e`, `Op(a, b) == e`, `f[x \in S] == e`, `a \oplus b == e`,
    /// `-. x == e`, `x ^+ == e` — plus the `INSTANCE` variants of the first two.
    fn parse_definition(&mut self, local: bool, start: Span) -> Result<Unit> {
        let tok = self.peek().clone();

        // Prefix-operator definition: `SUBSET x == …`, or `-. z == …` where
        // the lexer emits `-` and `.` separately.
        let minus_dot = tok.is_sym("-")
            && self.peek_at(1).is_sym(".")
            && self.peek_at(2).kind == TokenKind::Ident
            && self.peek_at(3).is_sym("==");
        if minus_dot {
            let op_span = tok.span.merge(self.peek_at(1).span);
            self.advance();
            self.advance();
            let param = self.expect_ident()?;
            self.advance(); // `==`
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span);
            return Ok(Unit {
                kind: UnitKind::OpDef {
                    local,
                    name: Ident {
                        name: "-.".to_string(),
                        span: op_span,
                    },
                    params: vec![OpDecl {
                        span: param.span,
                        name: param,
                        arity: 0,
                    }],
                    body,
                },
                span,
            });
        }
        if tok.kind == TokenKind::Sym
            && op::prefix_info(&tok.text).is_some()
            && self.peek_at(1).kind == TokenKind::Ident
            && self.peek_at(2).is_sym("==")
        {
            self.advance();
            let param = self.expect_ident()?;
            self.advance(); // `==`
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span);
            return Ok(Unit {
                kind: UnitKind::OpDef {
                    local,
                    name: Ident {
                        name: tok.text,
                        span: tok.span,
                    },
                    params: vec![OpDecl {
                        span: param.span,
                        name: param,
                        arity: 0,
                    }],
                    body,
                },
                span,
            });
        }

        if tok.kind != TokenKind::Ident {
            return self.err("a definition, declaration, or `====`");
        }

        // Infix-operator definition: `a \oplus b == …`.
        if self.peek_at(1).kind == TokenKind::Sym
            && op::infix_info(&self.peek_at(1).text).is_some()
            && self.peek_at(2).kind == TokenKind::Ident
            && self.peek_at(3).is_sym("==")
        {
            let lhs = self.expect_ident()?;
            let opsym = self.advance();
            let rhs = self.expect_ident()?;
            self.advance(); // `==`
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span);
            return Ok(Unit {
                kind: UnitKind::OpDef {
                    local,
                    name: Ident {
                        name: opsym.text,
                        span: opsym.span,
                    },
                    params: vec![
                        OpDecl {
                            span: lhs.span,
                            name: lhs,
                            arity: 0,
                        },
                        OpDecl {
                            span: rhs.span,
                            name: rhs,
                            arity: 0,
                        },
                    ],
                    body,
                },
                span,
            });
        }

        // Postfix-operator definition: `x ^+ == …`.
        if self.peek_at(1).kind == TokenKind::Sym
            && op::postfix_info(&self.peek_at(1).text).is_some()
            && self.peek_at(2).is_sym("==")
        {
            let param = self.expect_ident()?;
            let opsym = self.advance();
            self.advance(); // `==`
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span);
            return Ok(Unit {
                kind: UnitKind::OpDef {
                    local,
                    name: Ident {
                        name: opsym.text,
                        span: opsym.span,
                    },
                    params: vec![OpDecl {
                        span: param.span,
                        name: param,
                        arity: 0,
                    }],
                    body,
                },
                span,
            });
        }

        let name = self.expect_ident()?;

        // Function definition: `f[x \in S] == …`.
        if self.peek().is_sym("[") {
            self.advance();
            let bounds = self.parse_bounds()?;
            self.expect_sym("]")?;
            self.expect_sym("==")?;
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span);
            return Ok(Unit {
                kind: UnitKind::FnDef {
                    local,
                    name,
                    bounds,
                    body,
                },
                span,
            });
        }

        // Parameters, if any.
        let mut params = Vec::new();
        if self.peek().is_sym("(") {
            self.advance();
            loop {
                params.push(self.parse_param_decl()?);
                if !self.eat_sym(",") {
                    break;
                }
            }
            self.expect_sym(")")?;
        }

        self.expect_sym("==")?;

        // `I(x) == INSTANCE M WITH …`.
        if self.peek().is_kw(Keyword::Instance) {
            let instance = self.parse_instance()?;
            let span = start.merge(instance.span);
            return Ok(Unit {
                kind: UnitKind::ModuleDef {
                    local,
                    name,
                    params,
                    instance,
                },
                span,
            });
        }

        let body = self.parse_expr(0)?;
        let span = start.merge(body.span);
        Ok(Unit {
            kind: UnitKind::OpDef {
                local,
                name,
                params,
                body,
            },
            span,
        })
    }

    /// A formal parameter: `x`, or the higher-order form `F(_, _)`.
    fn parse_param_decl(&mut self) -> Result<OpDecl> {
        if let Some(decl) = self.try_parse_operator_decl() {
            return Ok(decl);
        }
        let tok = self.peek().clone();
        // An operator symbol may itself be a formal parameter: `Op(_+_)`.
        if tok.kind == TokenKind::Sym
            && (op::infix_info(&tok.text).is_some() || op::prefix_info(&tok.text).is_some())
        {
            self.advance();
            return Ok(OpDecl {
                span: tok.span,
                name: Ident {
                    name: tok.text,
                    span: tok.span,
                },
                arity: 0,
            });
        }
        self.parse_op_decl()
    }

    // ---- layout -------------------------------------------------------------

    /// Would `tok` close an enclosing junction list, or start a new unit?
    ///
    /// Two layout rules, both column-based:
    ///
    /// * the junction stack has strictly increasing columns, so the innermost
    ///   open list is the binding one;
    /// * a token at or left of the unit floor begins a new unit, which
    ///   is what stops `A == 1` from absorbing a following `<1>1.` proof step
    ///   or a `- 5` written at column 1.
    ///
    /// The unit rule does not apply inside brackets opened *after* the floor
    /// was established: a column-1 token in the middle of a parenthesised
    /// expression is ordinary continuation, not a new unit.
    fn at_layout_boundary(&self, tok: &Token) -> bool {
        if tok.kind == TokenKind::Eof {
            return false;
        }
        // A proof-step marker ends the statement it follows. Without this,
        // `LEMMA L == Spec => []TypeOK` followed by `<1>1.` absorbs the marker
        // and reports a bogus `<`/`>` precedence conflict.
        if self.at_proof_step_marker() && self.at_line_start() {
            return true;
        }
        if self.bracket_depth == self.unit_floor_depth && tok.col() <= self.unit_floor {
            return true;
        }
        match self.juncts.last() {
            Some(&(col, _)) => tok.col() <= col,
            None => false,
        }
    }

    /// Parse `f` with the unit floor set to `floor`, restoring the previous
    /// floor afterwards so that a nested `LET` cannot leak layout state into
    /// its enclosing definition.
    fn with_unit_floor<T>(
        &mut self,
        floor: u32,
        f: impl FnOnce(&mut Self) -> Result<T>,
    ) -> Result<T> {
        let saved_floor = self.unit_floor;
        let saved_depth = self.unit_floor_depth;
        self.unit_floor = floor;
        self.unit_floor_depth = self.bracket_depth;
        let out = f(self);
        self.unit_floor = saved_floor;
        self.unit_floor_depth = saved_depth;
        out
    }

    /// Parse a bulleted list starting at the current `/\` or `\/`.
    fn parse_junction_list(&mut self, kind: Junct) -> Result<Expr> {
        let start = self.peek().span;
        let col = self.peek().col();
        self.juncts.push((col, kind));

        let mut items = Vec::new();
        let result = (|| -> Result<()> {
            loop {
                // Consume the bullet.
                let bullet = self.peek().clone();
                if !(bullet.kind == TokenKind::Sym && bullet.text == kind.as_str()) {
                    return Err(SyntaxError::new(
                        ErrorKind::Unexpected {
                            expected: format!("`{}`", kind.as_str()),
                            found: Self::describe(&bullet),
                        },
                        bullet.span,
                    ));
                }
                if bullet.col() != col {
                    return Err(SyntaxError::new(
                        ErrorKind::JunctionMisaligned {
                            expected: col,
                            found: bullet.col(),
                        },
                        bullet.span,
                    ));
                }
                self.advance();
                items.push(self.parse_expr(0)?);

                // Another bullet of the same list?
                let next = self.peek();
                let continues =
                    next.kind == TokenKind::Sym && next.text == kind.as_str() && next.col() == col;
                if !continues {
                    return Ok(());
                }
            }
        })();
        self.juncts.pop();
        result?;

        let span = start.merge(self.prev_span());
        Ok(Expr {
            kind: ExprKind::Junction { kind, items },
            span,
        })
    }

    // ---- expressions --------------------------------------------------------

    /// Parse an expression with the given minimum binding power.
    ///
    /// # Errors
    ///
    /// Returns the first [`SyntaxError`] encountered.
    pub fn parse_expr(&mut self, min_bp: u8) -> Result<Expr> {
        self.depth += 1;
        if self.depth > self.max_depth {
            let span = self.peek().span;
            self.depth -= 1;
            return Err(SyntaxError::new(
                ErrorKind::RecursionLimit {
                    limit: self.max_depth,
                },
                span,
            ));
        }
        let out = self.parse_expr_inner(min_bp);
        self.depth -= 1;
        out
    }

    fn parse_expr_inner(&mut self, min_bp: u8) -> Result<Expr> {
        let mut lhs = self.parse_prefix()?;
        // The operator most recently applied at this level, for the
        // overlapping-range check that gives TLA+ its non-associativity.
        let mut last: Option<OpInfo> = None;

        loop {
            let tok = self.peek().clone();
            if tok.kind != TokenKind::Sym || self.at_layout_boundary(&tok) {
                break;
            }

            // Function application binds tighter than every real operator
            // except `.`; it is written as a bracket, not a table entry.
            if tok.text == "[" && min_bp <= 16 {
                self.advance();
                self.bracket_depth += 1;
                let mut args = vec![self.parse_expr(0)?];
                while self.eat_sym(",") {
                    args.push(self.parse_expr(0)?);
                }
                self.expect_sym("]")?;
                self.bracket_depth -= 1;
                let span = lhs.span.merge(self.prev_span());
                lhs = Expr {
                    kind: ExprKind::FnApply {
                        func: Box::new(lhs),
                        args,
                    },
                    span,
                };
                continue;
            }

            if let Some(info) = op::postfix_info(&tok.text) {
                if info.lo < min_bp {
                    break;
                }
                self.check_conflict(last.as_ref(), &info, tok.span)?;
                self.advance();
                let span = lhs.span.merge(tok.span);
                lhs = Expr {
                    kind: ExprKind::Postfix {
                        op: tok.text.clone(),
                        op_span: tok.span,
                        operand: Box::new(lhs),
                    },
                    span,
                };
                last = Some(info);
                continue;
            }

            let Some(info) = op::infix_info(&tok.text) else {
                break;
            };
            if info.lo < min_bp {
                break;
            }
            self.check_conflict(last.as_ref(), &info, tok.span)?;
            self.advance();

            // `.` takes a field name, not an expression.
            if tok.text == "." {
                let field = self.expect_field_name()?;
                let span = lhs.span.merge(field.span);
                lhs = Expr {
                    kind: ExprKind::Field {
                        record: Box::new(lhs),
                        field,
                    },
                    span,
                };
                last = Some(info);
                continue;
            }

            let rhs = self.parse_expr(info.right_bp())?;
            let span = lhs.span.merge(rhs.span);
            lhs = Expr {
                kind: ExprKind::Infix {
                    op: tok.text.clone(),
                    op_span: tok.span,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
            last = Some(info);
        }

        Ok(lhs)
    }

    /// The precedence-range rule: two operators applied at the same level may
    /// not have overlapping intervals, unless they are the same associative
    /// operator.
    fn check_conflict(&self, last: Option<&OpInfo>, next: &OpInfo, span: Span) -> Result<()> {
        let Some(prev) = last else {
            return Ok(());
        };
        if !op::ranges_overlap(prev, next) {
            return Ok(());
        }
        let same_and_assoc =
            prev.canonical == next.canonical && prev.assoc && prev.fixity == next.fixity;
        if same_and_assoc {
            return Ok(());
        }
        // A postfix operator chained onto a postfix operator (`x'^+`) is fine.
        if prev.fixity == Fixity::Postfix && next.fixity == Fixity::Postfix {
            return Ok(());
        }
        Err(SyntaxError::new(
            ErrorKind::PrecedenceConflict {
                left: prev.canonical.to_string(),
                left_lo: prev.lo,
                left_hi: prev.hi,
                right: next.canonical.to_string(),
                right_lo: next.lo,
                right_hi: next.hi,
            },
            span,
        ))
    }

    fn parse_prefix(&mut self) -> Result<Expr> {
        let tok = self.peek().clone();
        let start = tok.span;

        match tok.kind {
            TokenKind::Int(base) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Int {
                        base,
                        digits: tok.text,
                    },
                    span: start,
                })
            }
            TokenKind::Real => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Real(tok.text),
                    span: start,
                })
            }
            TokenKind::Str => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Str(tok.text),
                    span: start,
                })
            }
            TokenKind::Ident => self.parse_name_or_apply(),
            TokenKind::Keyword(kw) => self.parse_keyword_expr(kw, start),
            TokenKind::Sym => self.parse_sym_prefix(&tok, start),
            TokenKind::Dashes | TokenKind::ModuleFooter | TokenKind::Eof => {
                self.err("an expression")
            }
        }
    }

    /// A subscript: the `v` in `[A]_v`, `<<A>>_v`, `WF_v(A)`.
    ///
    /// Deliberately **not** `parse_prefix`. A subscript is a primary
    /// expression, and letting it absorb a following `(` would read the `(A)`
    /// of `WF_v(A)` as an application of `v`.
    fn parse_subscript(&mut self) -> Result<Expr> {
        let start = self.peek().span;
        let tok = self.peek().clone();
        match tok.kind {
            TokenKind::Ident => {
                let mut path = vec![self.expect_ident()?];
                while self.peek().is_sym("!") && self.peek_at(1).kind == TokenKind::Ident {
                    self.advance();
                    path.push(self.expect_ident()?);
                }
                let span = start.merge(self.prev_span());
                Ok(Expr {
                    kind: ExprKind::Name(QualName { path, span }),
                    span,
                })
            }
            TokenKind::Sym if tok.text == "<<" => self.parse_angle(start),
            TokenKind::Sym if tok.text == "(" => {
                self.advance();
                self.bracket_depth += 1;
                let inner = self.parse_expr(0)?;
                self.expect_sym(")")?;
                self.bracket_depth -= 1;
                let span = start.merge(self.prev_span());
                Ok(Expr {
                    kind: ExprKind::Paren(Box::new(inner)),
                    span,
                })
            }
            _ => self.err("a subscript: a name, a tuple, or a parenthesised expression"),
        }
    }

    /// The selector following a `!`, and how many tokens it spans.
    ///
    /// `!` introduces an instance qualifier (`I!Op`), a subexpression index
    /// (`A!1`), a positional selector (`A!:`, `A!<<`, `A!>>`), the operator
    /// itself (`A!@`), or an operator name (`R!+`, `F!^#`, `F!-.`). The
    /// standard modules are written with these: `Naturals` is literally
    /// `a + b == R!+(a, b)`.
    fn selector_at(&self, n: usize) -> Option<(Ident, usize)> {
        let tok = self.peek_at(n);
        // `-.` reaches the parser as `-` then `.`, so it spans two tokens.
        if tok.is_sym("-") && self.peek_at(n + 1).is_sym(".") {
            let span = tok.span.merge(self.peek_at(n + 1).span);
            return Some((
                Ident {
                    name: "-.".to_string(),
                    span,
                },
                2,
            ));
        }
        let ok = match tok.kind {
            TokenKind::Ident | TokenKind::Int(_) => true,
            TokenKind::Sym => {
                matches!(tok.text.as_str(), ":" | "<<" | ">>" | "@")
                    || op::infix_info(&tok.text).is_some()
                    || op::prefix_info(&tok.text).is_some()
                    || op::postfix_info(&tok.text).is_some()
            }
            _ => false,
        };
        ok.then(|| {
            (
                Ident {
                    name: tok.text.clone(),
                    span: tok.span,
                },
                1,
            )
        })
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>> {
        self.expect_sym("(")?;
        self.bracket_depth += 1;
        let mut args = Vec::new();
        if !self.peek().is_sym(")") {
            loop {
                args.push(self.parse_expr(0)?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(")")?;
        self.bracket_depth -= 1;
        Ok(args)
    }

    fn parse_name_or_apply(&mut self) -> Result<Expr> {
        let start = self.peek().span;

        // Gather the leading `!`-separated path while it stays a pure name.
        let mut path = vec![self.expect_ident()?];
        while self.peek().is_sym("!") {
            let Some((sel, width)) = self.selector_at(1) else {
                break;
            };
            self.advance();
            for _ in 0..width {
                self.advance();
            }
            path.push(sel);
        }
        let name = QualName {
            path,
            span: start.merge(self.prev_span()),
        };

        // A label, `lbl :: e` or `lbl(a, b) :: e`.
        if self.peek().is_sym("(") && self.call_is_label() {
            let args = self.parse_call_args()?;
            self.expect_sym("::")?;
            let params = args
                .iter()
                .map(|a| match &a.kind {
                    ExprKind::Name(n) if !n.is_qualified() => n
                        .base()
                        .cloned()
                        .ok_or_else(|| self.label_param_error(a.span)),
                    _ => Err(self.label_param_error(a.span)),
                })
                .collect::<Result<Vec<_>>>()?;
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span);
            let label_name = match name.base() {
                Some(id) => id.clone(),
                None => return self.err("a label name"),
            };
            return Ok(Expr {
                kind: ExprKind::Label {
                    name: label_name,
                    params,
                    body: Box::new(body),
                },
                span,
            });
        }
        if self.peek().is_sym("::") && !name.is_qualified() {
            self.advance();
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span);
            let label_name = match name.base() {
                Some(id) => id.clone(),
                None => return self.err("a label name"),
            };
            return Ok(Expr {
                kind: ExprKind::Label {
                    name: label_name,
                    params: Vec::new(),
                    body: Box::new(body),
                },
                span,
            });
        }

        let mut expr = if self.peek().is_sym("(") {
            let args = self.parse_call_args()?;
            Expr {
                kind: ExprKind::Apply { head: name, args },
                span: start.merge(self.prev_span()),
            }
        } else {
            let span = name.span;
            Expr {
                kind: ExprKind::Name(name),
                span,
            }
        };

        // Further `!` selections, now that the base is an expression:
        // `Inner(q)!Spec`.
        while self.peek().is_sym("!") {
            // `A!(1, 2)` instantiates the arguments of the subexpression
            // selected so far; the selector is the reserved spelling `()`.
            if self.peek_at(1).is_sym("(") {
                let bang = self.advance().span;
                let args = self.parse_call_args()?;
                let span = expr.span.merge(self.prev_span());
                expr = Expr {
                    kind: ExprKind::Qualified {
                        base: Box::new(expr),
                        selector: Ident {
                            name: "()".to_string(),
                            span: bang,
                        },
                        args,
                    },
                    span,
                };
                continue;
            }
            let Some((sel, width)) = self.selector_at(1) else {
                break;
            };
            self.advance();
            for _ in 0..width {
                self.advance();
            }
            let args = if self.peek().is_sym("(") {
                self.parse_call_args()?
            } else {
                Vec::new()
            };
            let span = expr.span.merge(self.prev_span());
            expr = Expr {
                kind: ExprKind::Qualified {
                    base: Box::new(expr),
                    selector: sel,
                    args,
                },
                span,
            };
        }

        Ok(expr)
    }

    /// Does the `(` at the cursor open a label's parameter list rather than an
    /// argument list? Decided by whether a `::` follows the matching `)`.
    fn call_is_label(&self) -> bool {
        let mut depth = 0i32;
        let mut n = 0usize;
        loop {
            let tok = self.peek_at(n);
            match tok.kind {
                TokenKind::Eof => return false,
                TokenKind::Sym => match tok.text.as_str() {
                    "(" | "[" | "{" | "<<" => depth += 1,
                    ")" | "]" | "}" | ">>" => {
                        depth -= 1;
                        if depth == 0 {
                            return self.peek_at(n + 1).is_sym("::");
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
            n += 1;
        }
    }

    fn label_param_error(&self, span: Span) -> SyntaxError {
        SyntaxError::new(
            ErrorKind::Unexpected {
                expected: "a plain identifier as a label parameter".to_string(),
                found: "an expression".to_string(),
            },
            span,
        )
    }

    fn parse_keyword_expr(&mut self, kw: Keyword, start: Span) -> Result<Expr> {
        match kw {
            Keyword::If => {
                self.advance();
                let cond = self.parse_expr(0)?;
                self.expect_kw(Keyword::Then)?;
                let then_branch = self.parse_expr(0)?;
                self.expect_kw(Keyword::Else)?;
                let else_branch = self.parse_expr(0)?;
                let span = start.merge(else_branch.span);
                Ok(Expr {
                    kind: ExprKind::If {
                        cond: Box::new(cond),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                    span,
                })
            }
            Keyword::Case => self.parse_case(start),
            Keyword::Assume | Keyword::Assumption => self.parse_assume_prove(start),
            Keyword::Let => {
                self.advance();
                let mut defs = Vec::new();
                while !self.peek().is_kw(Keyword::In) {
                    if self.at_eof() {
                        return self.err("`IN` to close a `LET`");
                    }
                    let unit_start = self.peek().span;
                    // No column floor here. A `LET` definition ends where the
                    // next one begins, and the next one begins with an
                    // identifier or `IN` -- neither of which can continue an
                    // expression, so the Pratt loop already stops. Imposing a
                    // column floor instead breaks a definition whose
                    // continuation lines happen to sit at the definition's own
                    // column, which `TLAPlusGrammar.tla` does throughout.
                    let def = (|p: &mut Self| {
                        // `LET RECURSIVE F(_) F(x) == … IN …` is common in the
                        // standard modules and in the examples corpus.
                        if p.peek().is_kw(Keyword::Recursive) {
                            p.advance();
                            let mut decls = vec![p.parse_op_decl()?];
                            while p.eat_sym(",") {
                                decls.push(p.parse_op_decl()?);
                            }
                            let span = unit_start.merge(p.prev_span());
                            return Ok(Unit {
                                kind: UnitKind::Recursive(decls),
                                span,
                            });
                        }
                        let local = p.eat_kw(Keyword::Local);
                        p.parse_definition(local, unit_start)
                    })(self)?;
                    defs.push(def);
                }
                self.expect_kw(Keyword::In)?;
                let body = self.parse_expr(0)?;
                let span = start.merge(body.span);
                Ok(Expr {
                    kind: ExprKind::Let {
                        defs,
                        body: Box::new(body),
                    },
                    span,
                })
            }
            Keyword::Choose => {
                self.advance();
                let pattern = self.parse_pattern()?;
                let domain = if self.eat_sym("\\in") {
                    Some(Box::new(self.parse_expr(0)?))
                } else {
                    None
                };
                self.expect_sym(":")?;
                let body = self.parse_expr(0)?;
                let span = start.merge(body.span);
                Ok(Expr {
                    kind: ExprKind::Choose {
                        pattern,
                        domain,
                        body: Box::new(body),
                    },
                    span,
                })
            }
            Keyword::Lambda => {
                self.advance();
                let mut params = vec![self.expect_ident()?];
                while self.eat_sym(",") {
                    params.push(self.expect_ident()?);
                }
                self.expect_sym(":")?;
                let body = self.parse_expr(0)?;
                let span = start.merge(body.span);
                Ok(Expr {
                    kind: ExprKind::Lambda {
                        params,
                        body: Box::new(body),
                    },
                    span,
                })
            }
            Keyword::WeakFairness | Keyword::StrongFairness => {
                self.advance();
                let fk = if kw == Keyword::WeakFairness {
                    FairnessKind::Weak
                } else {
                    FairnessKind::Strong
                };
                let subscript = self.parse_subscript()?;
                self.expect_sym("(")?;
                let body = self.parse_expr(0)?;
                self.expect_sym(")")?;
                let span = start.merge(self.prev_span());
                Ok(Expr {
                    kind: ExprKind::Fairness {
                        kind: fk,
                        subscript: Box::new(subscript),
                        body: Box::new(body),
                    },
                    span,
                })
            }
            _ => self.err("an expression"),
        }
    }

    /// `ASSUME a, NEW CONSTANT x \in S, b PROVE g` — the sequent form of a
    /// theorem statement. Only valid where an expression is expected; a
    /// top-level `ASSUME` unit is handled by [`Parser::parse_unit`].
    fn parse_assume_prove(&mut self, start: Span) -> Result<Expr> {
        self.advance(); // ASSUME
        let mut assumptions = Vec::new();
        loop {
            assumptions.push(self.parse_assume_item()?);
            if !self.eat_sym(",") {
                break;
            }
        }
        self.expect_kw(Keyword::Prove)?;
        let goal = self.parse_expr(0)?;
        let span = start.merge(goal.span);
        Ok(Expr {
            kind: ExprKind::AssumeProve {
                assumptions,
                goal: Box::new(goal),
            },
            span,
        })
    }

    fn parse_assume_item(&mut self) -> Result<AssumeItem> {
        if !self.peek().is_kw(Keyword::New) {
            return Ok(AssumeItem::Expr(self.parse_expr(1)?));
        }
        self.advance(); // NEW
        let kind = if self.eat_kw(Keyword::Variable) {
            NewKind::Variable
        } else if self.eat_kw(Keyword::State) {
            NewKind::State
        } else if self.eat_kw(Keyword::Action) {
            NewKind::Action
        } else if self.eat_kw(Keyword::Temporal) {
            NewKind::Temporal
        } else {
            // `NEW CONSTANT x` and a bare `NEW x` mean the same thing.
            let _ = self.eat_kw(Keyword::Constant);
            NewKind::Constant
        };
        let decl = self.parse_op_decl()?;
        let domain = if self.eat_sym("\\in") {
            Some(self.parse_expr(1)?)
        } else {
            None
        };
        Ok(AssumeItem::New { kind, decl, domain })
    }

    fn parse_case(&mut self, start: Span) -> Result<Expr> {
        self.expect_kw(Keyword::Case)?;
        let mut arms = Vec::new();
        let mut other = None;
        loop {
            if self.eat_kw(Keyword::Other) {
                self.expect_sym("->")?;
                other = Some(Box::new(self.parse_expr(0)?));
            } else {
                let guard = self.parse_expr(0)?;
                self.expect_sym("->")?;
                let value = self.parse_expr(0)?;
                arms.push(CaseArm { guard, value });
            }
            // Arms are separated by `[]`, which the lexer produces as one
            // token — the same token as temporal `[]`, distinguished here by
            // position rather than by a lexer hack.
            if !self.peek().is_sym("[]") {
                break;
            }
            self.advance();
        }
        let span = start.merge(self.prev_span());
        Ok(Expr {
            kind: ExprKind::Case { arms, other },
            span,
        })
    }

    fn parse_sym_prefix(&mut self, tok: &Token, start: Span) -> Result<Expr> {
        // An operator with nothing after it that could be an operand is being
        // passed as a *value*: `TestOpArg( - )`, `BoxTest([])`. Checked before
        // the prefix readings below so that `-` and `[]` are covered too.
        if self.operator_used_as_value(tok) {
            self.advance();
            return Ok(Expr {
                kind: ExprKind::Name(QualName {
                    path: vec![Ident {
                        name: tok.text.clone(),
                        span: start,
                    }],
                    span: start,
                }),
                span: start,
            });
        }
        match tok.text.as_str() {
            "/\\" => return self.parse_junction_list(Junct::And),
            "\\/" => return self.parse_junction_list(Junct::Or),
            "(" => {
                self.advance();
                self.bracket_depth += 1;
                let inner = self.parse_expr(0)?;
                self.expect_sym(")")?;
                self.bracket_depth -= 1;
                let span = start.merge(self.prev_span());
                return Ok(Expr {
                    kind: ExprKind::Paren(Box::new(inner)),
                    span,
                });
            }
            "{" => return self.parse_brace(start),
            "[" => return self.parse_bracket(start),
            "<<" => return self.parse_angle(start),
            "@" => {
                self.advance();
                return Ok(Expr {
                    kind: ExprKind::At,
                    span: start,
                });
            }
            "\\A" | "\\E" | "\\AA" | "\\EE" => return self.parse_quant(tok, start),
            "-" => {
                // Unary minus. The lexer emits `-`; position decides, and the
                // AST records the distinct `-.` spelling so that nothing
                // downstream can confuse it with subtraction.
                self.advance();
                let info = op::prefix_info("-.").ok_or_else(|| {
                    SyntaxError::new(ErrorKind::UnknownOperator("-.".to_string()), start)
                })?;
                let operand = self.parse_expr(info.right_bp())?;
                let span = start.merge(operand.span);
                return Ok(Expr {
                    kind: ExprKind::Prefix {
                        op: "-.".to_string(),
                        op_span: start,
                        operand: Box::new(operand),
                    },
                    span,
                });
            }
            _ => {}
        }

        // An operator symbol with no prefix reading can be applied like an
        // ordinary operator: `+(4, 6)`, `^#(4)`.
        if op::prefix_info(&tok.text).is_none()
            && (op::infix_info(&tok.text).is_some() || op::postfix_info(&tok.text).is_some())
        {
            self.advance();
            let name = QualName {
                path: vec![Ident {
                    name: tok.text.clone(),
                    span: start,
                }],
                span: start,
            };
            if self.peek().is_sym("(") {
                self.advance();
                self.bracket_depth += 1;
                let mut args = Vec::new();
                if !self.peek().is_sym(")") {
                    loop {
                        args.push(self.parse_expr(0)?);
                        if !self.eat_sym(",") {
                            break;
                        }
                    }
                }
                self.expect_sym(")")?;
                self.bracket_depth -= 1;
                let span = start.merge(self.prev_span());
                return Ok(Expr {
                    kind: ExprKind::Apply { head: name, args },
                    span,
                });
            }
            return Ok(Expr {
                kind: ExprKind::Name(name),
                span: start,
            });
        }

        if let Some(info) = op::prefix_info(&tok.text) {
            self.advance();
            let operand = self.parse_expr(info.right_bp())?;
            let span = start.merge(operand.span);
            return Ok(Expr {
                kind: ExprKind::Prefix {
                    op: tok.text.clone(),
                    op_span: start,
                    operand: Box::new(operand),
                },
                span,
            });
        }

        self.err("an expression")
    }

    /// Is this operator token being passed as a value rather than applied?
    ///
    /// True exactly when the next token closes an argument list or separates
    /// arguments, which is the only position where a bare operator is legal.
    fn operator_used_as_value(&self, tok: &Token) -> bool {
        let is_operator = op::infix_info(&tok.text).is_some()
            || op::postfix_info(&tok.text).is_some()
            || op::prefix_info(&tok.text).is_some();
        is_operator && (self.peek_at(1).is_sym(")") || self.peek_at(1).is_sym(","))
    }

    fn parse_quant(&mut self, tok: &Token, start: Span) -> Result<Expr> {
        let kind = match tok.text.as_str() {
            "\\A" => QuantKind::Forall,
            "\\E" => QuantKind::Exists,
            "\\AA" => QuantKind::TemporalForall,
            "\\EE" => QuantKind::TemporalExists,
            _ => return self.err("a quantifier"),
        };
        self.advance();

        // Bounded or unbounded? `\A x \in S : P` versus `\A x : P`. Scan the
        // comma-separated variable list for a following `\in`.
        let unbounded = {
            let mut n = 0;
            while self.peek_at(n).kind == TokenKind::Ident {
                n += 1;
                if self.peek_at(n).is_sym(",") {
                    n += 1;
                } else {
                    break;
                }
            }
            self.peek_at(n).is_sym(":")
        };

        if unbounded {
            let mut vars = vec![self.expect_ident()?];
            while self.eat_sym(",") {
                vars.push(self.expect_ident()?);
            }
            self.expect_sym(":")?;
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span);
            return Ok(Expr {
                kind: ExprKind::UnboundedQuant {
                    kind,
                    vars,
                    body: Box::new(body),
                },
                span,
            });
        }

        let bounds = self.parse_bounds()?;
        self.expect_sym(":")?;
        let body = self.parse_expr(0)?;
        let span = start.merge(body.span);
        Ok(Expr {
            kind: ExprKind::Quant {
                kind,
                bounds,
                body: Box::new(body),
            },
            span,
        })
    }

    fn parse_pattern(&mut self) -> Result<Pattern> {
        if self.peek().is_sym("<<") {
            self.advance();
            let mut names = vec![self.expect_ident()?];
            while self.eat_sym(",") {
                names.push(self.expect_ident()?);
            }
            self.expect_sym(">>")?;
            return Ok(Pattern::Tuple(names));
        }
        Ok(Pattern::Name(self.expect_ident()?))
    }

    /// `x, y \in S, <<a, b>> \in T`
    fn parse_bounds(&mut self) -> Result<Vec<Bound>> {
        let mut bounds = Vec::new();
        loop {
            // `x, y \in S` shares one domain across two patterns; the outer
            // loop below handles `x \in S, y \in T`, where the comma
            // separates whole groups. Both spellings reach the same comma, so
            // patterns are accumulated greedily and the `\in` that follows
            // closes the group.
            let mut patterns = vec![self.parse_pattern()?];
            while self.peek().is_sym(",") {
                self.advance();
                patterns.push(self.parse_pattern()?);
            }
            self.expect_sym("\\in")?;
            // A bound's domain must not swallow the `:` or `|->` that follows,
            // and must not absorb the `,` separating bound groups. Parsing at
            // binding power 1 stops before `,` and `:`, which are not
            // operators, while still admitting every real domain expression.
            let domain = self.parse_expr(1)?;
            bounds.push(Bound { patterns, domain });
            if self.peek().is_sym(",") {
                self.advance();
                continue;
            }
            break;
        }
        Ok(bounds)
    }

    fn parse_angle(&mut self, start: Span) -> Result<Expr> {
        self.expect_sym("<<")?;
        self.bracket_depth += 1;
        let out = self.parse_angle_body(start);
        self.bracket_depth -= 1;
        out
    }

    fn parse_angle_body(&mut self, start: Span) -> Result<Expr> {
        let mut items = Vec::new();
        if !self.peek().is_sym(">>") {
            loop {
                items.push(self.parse_expr(0)?);
                if !self.eat_sym(",") {
                    break;
                }
            }
        }
        self.expect_sym(">>")?;
        let close = self.prev_span();

        // `<<A>>_v` — an angle action rather than a tuple.
        if self.peek().is_sym("_") {
            self.advance();
            let subscript = self.parse_subscript()?;
            let span = start.merge(subscript.span);
            let body = match items.len() {
                1 => match items.into_iter().next() {
                    Some(e) => e,
                    None => return self.err("an action inside `<< >>_`"),
                },
                _ => {
                    return Err(SyntaxError::new(
                        ErrorKind::Unexpected {
                            expected: "a single action inside `<< >>_`".to_string(),
                            found: format!("{} components", items.len()),
                        },
                        start.merge(close),
                    ));
                }
            };
            return Ok(Expr {
                kind: ExprKind::Action {
                    kind: ActionKind::NonStuttering,
                    body: Box::new(body),
                    subscript: Box::new(subscript),
                },
                span,
            });
        }

        Ok(Expr {
            kind: ExprKind::Tuple(items),
            span: start.merge(close),
        })
    }

    /// Classify a `{ … }` form by scanning at bracket depth zero.
    ///
    /// `{a, b}` has no top-level `:`; `{x \in S : P}` has a `\in` before its
    /// `:`; `{e : x \in S}` does not. This is the arbitrary lookahead that
    /// `docs/TLA_FRONTEND_DESIGN.md` §1.0 names as an obstacle to LR(1) — a
    /// Pratt parser can simply look.
    fn parse_brace(&mut self, start: Span) -> Result<Expr> {
        self.expect_sym("{")?;
        self.bracket_depth += 1;
        let out = self.parse_brace_body(start);
        self.bracket_depth -= 1;
        out
    }

    fn parse_brace_body(&mut self, start: Span) -> Result<Expr> {
        if self.eat_sym("}") {
            return Ok(Expr {
                kind: ExprKind::SetEnum(Vec::new()),
                span: start.merge(self.prev_span()),
            });
        }

        let (colon_at, in_before_colon) = self.scan_brace_shape();

        if colon_at.is_none() {
            let mut items = vec![self.parse_expr(0)?];
            while self.eat_sym(",") {
                items.push(self.parse_expr(0)?);
            }
            self.expect_sym("}")?;
            return Ok(Expr {
                kind: ExprKind::SetEnum(items),
                span: start.merge(self.prev_span()),
            });
        }

        if in_before_colon {
            let pattern = self.parse_pattern()?;
            self.expect_sym("\\in")?;
            let domain = self.parse_expr(1)?;
            self.expect_sym(":")?;
            let pred = self.parse_expr(0)?;
            self.expect_sym("}")?;
            return Ok(Expr {
                kind: ExprKind::SetFilter {
                    pattern,
                    domain: Box::new(domain),
                    pred: Box::new(pred),
                },
                span: start.merge(self.prev_span()),
            });
        }

        let expr = self.parse_expr(1)?;
        self.expect_sym(":")?;
        let bounds = self.parse_bounds()?;
        self.expect_sym("}")?;
        Ok(Expr {
            kind: ExprKind::SetMap {
                expr: Box::new(expr),
                bounds,
            },
            span: start.merge(self.prev_span()),
        })
    }

    /// Returns `(offset of the top-level ':', whether a top-level '\in'
    /// precedes it)`. The cursor is just past the opening `{`.
    fn scan_brace_shape(&self) -> (Option<usize>, bool) {
        let mut depth = 0i32;
        let mut saw_in = false;
        let mut n = 0usize;
        // Binders bring their own `:`. In `{CHOOSE x : x \in T}` the colon
        // belongs to the `CHOOSE`, and reading it as a set-map separator was
        // what broke the standard `FiniteSets` module.
        let mut pending_binder_colons = 0usize;
        loop {
            let tok = self.peek_at(n);
            match tok.kind {
                TokenKind::Eof => return (None, false),
                TokenKind::Keyword(Keyword::Choose | Keyword::Lambda) if depth == 0 => {
                    pending_binder_colons += 1;
                }
                TokenKind::Sym => match tok.text.as_str() {
                    "\\A" | "\\E" | "\\AA" | "\\EE" if depth == 0 => {
                        pending_binder_colons += 1;
                    }
                    "{" | "[" | "(" | "<<" => depth += 1,
                    "}" if depth == 0 => return (None, saw_in),
                    "}" | "]" | ")" | ">>" => depth -= 1,
                    "\\in" if depth == 0 && pending_binder_colons == 0 => saw_in = true,
                    ":" if depth == 0 => {
                        if pending_binder_colons > 0 {
                            pending_binder_colons -= 1;
                        } else {
                            return (Some(n), saw_in);
                        }
                    }
                    _ => {}
                },
                _ => {}
            }
            n += 1;
        }
    }

    /// Parse a `[ … ]` form, classified by [`Parser::scan_bracket_shape`].
    fn parse_bracket(&mut self, start: Span) -> Result<Expr> {
        self.expect_sym("[")?;
        self.bracket_depth += 1;
        let out = self.parse_bracket_body(start);
        self.bracket_depth -= 1;
        out
    }

    fn parse_bracket_body(&mut self, start: Span) -> Result<Expr> {
        match self.scan_bracket_shape() {
            BracketShape::FnConstruct => {
                let bounds = self.parse_bounds()?;
                self.expect_sym("|->")?;
                let body = self.parse_expr(0)?;
                self.expect_sym("]")?;
                Ok(Expr {
                    kind: ExprKind::FnConstruct {
                        bounds,
                        body: Box::new(body),
                    },
                    span: start.merge(self.prev_span()),
                })
            }
            BracketShape::RecordLit => {
                let mut fields = Vec::new();
                loop {
                    let name = self.expect_field_name()?;
                    self.expect_sym("|->")?;
                    let value = self.parse_expr(1)?;
                    fields.push((name, value));
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                self.expect_sym("]")?;
                Ok(Expr {
                    kind: ExprKind::RecordLit(fields),
                    span: start.merge(self.prev_span()),
                })
            }
            BracketShape::RecordSet => {
                let mut fields = Vec::new();
                loop {
                    let name = self.expect_field_name()?;
                    self.expect_sym(":")?;
                    let value = self.parse_expr(1)?;
                    fields.push((name, value));
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                self.expect_sym("]")?;
                Ok(Expr {
                    kind: ExprKind::RecordSet(fields),
                    span: start.merge(self.prev_span()),
                })
            }
            BracketShape::FnSet => {
                let domain = self.parse_expr(0)?;
                self.expect_sym("->")?;
                let codomain = self.parse_expr(0)?;
                self.expect_sym("]")?;
                Ok(Expr {
                    kind: ExprKind::FnSet {
                        domain: Box::new(domain),
                        codomain: Box::new(codomain),
                    },
                    span: start.merge(self.prev_span()),
                })
            }
            BracketShape::Except => {
                let base = self.parse_expr(0)?;
                self.expect_kw(Keyword::Except)?;
                let mut updates = Vec::new();
                loop {
                    self.expect_sym("!")?;
                    let mut path = Vec::new();
                    loop {
                        if self.peek().is_sym("[") {
                            self.advance();
                            let mut idx = vec![self.parse_expr(0)?];
                            while self.eat_sym(",") {
                                idx.push(self.parse_expr(0)?);
                            }
                            self.expect_sym("]")?;
                            path.push(ExceptSel::Index(idx));
                        } else if self.peek().is_sym(".") {
                            self.advance();
                            path.push(ExceptSel::Field(self.expect_field_name()?));
                        } else {
                            break;
                        }
                    }
                    if path.is_empty() {
                        return self.err("`[…]` or `.field` after `!` in an `EXCEPT`");
                    }
                    self.expect_sym("=")?;
                    let value = self.parse_expr(1)?;
                    updates.push(ExceptUpdate { path, value });
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                self.expect_sym("]")?;
                Ok(Expr {
                    kind: ExprKind::Except {
                        base: Box::new(base),
                        updates,
                    },
                    span: start.merge(self.prev_span()),
                })
            }
            BracketShape::Action => {
                let body = self.parse_expr(0)?;
                self.expect_sym("]")?;
                self.expect_sym("_")?;
                let subscript = self.parse_subscript()?;
                let span = start.merge(subscript.span);
                Ok(Expr {
                    kind: ExprKind::Action {
                        kind: ActionKind::Stuttering,
                        body: Box::new(body),
                        subscript: Box::new(subscript),
                    },
                    span,
                })
            }
        }
    }

    /// Classify a `[ … ]` form by scanning at bracket depth zero.
    ///
    /// A decisive token is only decisive when what precedes it has the right
    /// shape, which is what separates the six forms:
    ///
    /// * `\in` means a function constructor only if everything before it is a
    ///   pattern list (identifiers, commas, `<<`, `>>`). In
    ///   `[\A i \in Proc : P]_vars` the `\in` belongs to the quantifier and
    ///   the form is an action.
    /// * `|->` and `:` mean a record literal / record set only if preceded by
    ///   exactly one identifier — the field name.
    /// * `->` means a function set unless a `CASE` is open, whose arms use the
    ///   same token.
    fn scan_bracket_shape(&self) -> BracketShape {
        let mut depth = 0i32;
        let mut n = 0usize;
        // Tokens since the start, or since the last depth-0 comma.
        let mut idents_in_group = 0usize;
        let mut only_pattern_tokens = true;
        let mut in_case = false;
        loop {
            let tok = self.peek_at(n);
            match tok.kind {
                TokenKind::Eof => return BracketShape::Action,
                TokenKind::Keyword(Keyword::Except) if depth == 0 => return BracketShape::Except,
                TokenKind::Keyword(Keyword::Case) if depth == 0 => {
                    in_case = true;
                    only_pattern_tokens = false;
                }
                TokenKind::Ident if depth == 0 => idents_in_group += 1,
                TokenKind::Sym => match tok.text.as_str() {
                    "{" | "[" | "(" => {
                        depth += 1;
                        only_pattern_tokens = false;
                    }
                    "<<" => depth += 1,
                    "]" if depth == 0 => return BracketShape::Action,
                    "}" | "]" | ")" => depth -= 1,
                    ">>" => depth -= 1,
                    "," if depth == 0 => {
                        idents_in_group = 0;
                    }
                    "\\in" if depth == 0 => {
                        if only_pattern_tokens {
                            return BracketShape::FnConstruct;
                        }
                        only_pattern_tokens = false;
                    }
                    "|->" if depth == 0 && idents_in_group == 1 => {
                        return BracketShape::RecordLit;
                    }
                    ":" if depth == 0 && idents_in_group == 1 && only_pattern_tokens => {
                        return BracketShape::RecordSet;
                    }
                    "->" if depth == 0 && !in_case => return BracketShape::FnSet,
                    // Only tokens at depth zero say anything about the shape
                    // of *this* bracket. Without the guard, the comma inside
                    // `[<<p, q>> \in S |-> …]` disqualifies the pattern.
                    _ if depth == 0 => only_pattern_tokens = false,
                    _ => {}
                },
                _ if depth == 0 => only_pattern_tokens = false,
                _ => {}
            }
            n += 1;
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BracketShape {
    FnConstruct,
    RecordLit,
    RecordSet,
    FnSet,
    Except,
    Action,
}

/// Sentinel returned when a caller hands the parser an empty token stream.
///
/// The lexer always emits a trailing [`TokenKind::Eof`], so this is dead for
/// every stream this crate produces; it exists so that the "no `unwrap`"
/// rule is satisfied without an `expect("unreachable")`, which `AGENTS.md`
/// explicitly calls out as the wrong shape.
static EOF_TOKEN_SENTINEL: Token = Token {
    kind: TokenKind::Eof,
    text: String::new(),
    span: Span {
        start: crate::span::Pos {
            line: 1,
            col: 1,
            offset: 0,
        },
        end: crate::span::Pos {
            line: 1,
            col: 1,
            offset: 0,
        },
    },
};

/// Lex and parse a TLA+ source file.
///
/// # Errors
///
/// Returns the first [`SyntaxError`] encountered in either phase.
pub fn parse_file(src: &str) -> Result<ParsedFile> {
    let lexed = lexer::lex(src)?;
    let mut parser = Parser::new(lexed.tokens);
    let module = parser.parse_file()?;
    Ok(ParsedFile {
        module,
        comments: lexed.comments,
    })
}

/// Lex and parse a single expression. Useful for tests and for `@type:`
/// annotation bodies.
///
/// # Errors
///
/// Returns the first [`SyntaxError`] encountered in either phase.
pub fn parse_expr_str(src: &str) -> Result<Expr> {
    let lexed = lexer::lex(src)?;
    let mut parser = Parser::new(lexed.tokens);
    let expr = parser.parse_expr(0)?;
    if !parser.at_eof() {
        return parser.err("end of input after the expression");
    }
    Ok(expr)
}
