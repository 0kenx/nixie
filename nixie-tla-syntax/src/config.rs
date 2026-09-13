//! TLC configuration files (`.cfg`).
//!
//! A TLA+ specification does not name its own entry points or fix its own
//! constants — the `.cfg` beside it does. `MCChangRoberts.cfg` says
//! `CONSTANT N = 3`, and without it `N` is an arbitrary integer and `1..N` has
//! no enumerable member list. The checker that ignores the file is answering a
//! strictly harder question than the one the author asked, which manufactures
//! counterexamples on correct specifications.
//!
//! # The grammar is not invented here
//!
//! The syntax is TLC's, specified in *Specifying Systems* §14.7.1 and
//! implemented in `tlc2.tool.impl.ModelConfig`. This parser follows the EBNF
//! Apalache publishes (`docs/src/apalache/tlc-config.md`) and its
//! implementation in `TlcConfigLexer.scala` / `TlcConfigParserApalache.scala`,
//! which is the same grammar written down.
//!
//! ```text
//! config      ::= option+
//! option      ::= "INIT" ident | "NEXT" ident | "SPECIFICATION" ident
//!               | ("CONSTANT" | "CONSTANTS") (replacement | assignment)*
//!               | ("INVARIANT" | "INVARIANTS") ident*
//!               | ("PROPERTY" | "PROPERTIES") ident*
//!               | ("CONSTRAINT" | "CONSTRAINTS") ident*
//!               | ("ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS") ident*
//!               | "SYMMETRY" ident | "VIEW" ident | "ALIAS" ident
//!               | "POSTCONDITION" ident | "CHECK_DEADLOCK" boolean
//! replacement ::= ident "<-" ident
//! assignment  ::= ident "=" constExpr
//! constExpr   ::= modelValue | integer | string | boolean
//!               | "{" (constExpr ("," constExpr)*)? "}"
//! ```
//!
//! # What a bare identifier means
//!
//! On the right of `=`, an identifier is a **model value**: an uninterpreted
//! constant, distinct from every other model value and from every integer,
//! string and set (*Specifying Systems* §14.5.3). `CONSTANT NoVal = NoVal` is
//! not circular — it pins `NoVal` to a value nothing else can equal. That is
//! the one piece of `.cfg` semantics that is not syntax, and getting it wrong
//! in the permissive direction (two model values allowed to be equal) loses
//! counterexamples.
//!
//! # What is parsed and deliberately not acted on
//!
//! `SYMMETRY`, `VIEW`, `ALIAS` and `POSTCONDITION` are recognised and
//! recorded, never silently skipped. Apalache ignores all four. Ignoring
//! `SYMMETRY` explores *more* states than TLC would, which can manufacture a
//! counterexample but never hide one; the other three do not restrict the
//! search at all. They are kept in the parsed config so a caller can say what
//! it did with them rather than the information disappearing here.

use crate::span::{Pos, Span};
use std::collections::BTreeMap;
use thiserror::Error;

/// What went wrong reading a `.cfg`.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub struct ConfigError {
    /// The problem.
    pub kind: ConfigErrorKind,
    /// Where it is.
    pub span: Span,
}

impl core::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}: {}", self.span, self.kind)
    }
}

/// The kinds of `.cfg` error.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ConfigErrorKind {
    /// A character that cannot begin any `.cfg` lexeme.
    #[error("unexpected character {0:?}")]
    UnexpectedChar(char),
    /// A `"` string ran to end of file.
    #[error("unterminated string")]
    UnterminatedString,
    /// A `(*` comment ran to end of file.
    #[error("unterminated block comment")]
    UnterminatedComment,
    /// Punctuation that is not a TLA+ operator, where a name was expected.
    #[error("`{0}` is not a TLA+ operator")]
    NotAnOperator(String),
    /// The grammar wanted something else here.
    #[error("expected {expected}, found {found}")]
    Unexpected {
        /// What the grammar allowed.
        expected: String,
        /// What was there.
        found: String,
    },
    /// Two behaviour specifications in one file.
    ///
    /// `INIT`/`NEXT` and `SPECIFICATION` both say how the system moves, and a
    /// file that gives both does not say which to believe. Reported rather
    /// than resolved by precedence: picking one silently would check a
    /// different specification than the author configured.
    #[error("two behaviour specifications: {first} and {second}")]
    TwoBehaviourSpecs {
        /// The one already set.
        first: String,
        /// The one that conflicts with it.
        second: String,
    },
    /// `CHECK_DEADLOCK` given twice with different answers.
    #[error("conflicting CHECK_DEADLOCK declarations")]
    ConflictingCheckDeadlock,
}

/// A constant expression, as it may appear right of `=`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfigValue {
    /// A model value: an uninterpreted constant, distinct from everything.
    ModelValue(String),
    /// An integer, kept as written so a wide literal stays exact.
    Int(String),
    /// A string literal.
    Str(String),
    /// `TRUE` or `FALSE`.
    Bool(bool),
    /// A set literal, possibly empty.
    Set(Vec<ConfigValue>),
    /// `[M]d` on the right of `=`, as `MCNanoSmall.cfg` writes
    /// `NoHash = [Nano]NoHashVal`.
    ///
    /// Recorded **uninterpreted**. It is not in TLC's published EBNF and
    /// Apalache's parser rejects it, so there is no specification to follow
    /// here; the two readings available from the text — "replace `Nano`'s
    /// definition with `NoHashVal`" and "the value `NoHashVal` has inside
    /// `Nano`" — happen to agree on this file and need not agree in general.
    /// Rather than pick one, the syntax is kept as written so a consumer has
    /// to decide explicitly, and the closed enum makes that a compile error
    /// rather than an omission.
    ModuleQualified {
        /// The module named in brackets.
        module: String,
        /// The name after it.
        name: String,
    },
}

/// The right-hand side of a `<-` replacement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Replacement {
    /// The definition to use instead.
    pub to: String,
    /// For `x <- [M]d`, the instantiated module `M` the replacement applies
    /// *inside*.
    ///
    /// TLC's published EBNF does not have this form and Apalache's parser
    /// rejects it, but real configurations use it — `MCPaxos.cfg` writes
    /// `Ballot <-[Voting] MCBallot` to replace `Ballot` within the `Voting`
    /// instance rather than at the top level. Parsed and kept distinct rather
    /// than flattened onto an unqualified replacement, because the two mean
    /// different things and applying one for the other checks a different
    /// specification. See [`TlcConfig::module_qualified_replacements`].
    pub module: Option<String>,
}

/// How the configuration says the system moves.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum BehaviorSpec {
    /// No `INIT`/`NEXT` and no `SPECIFICATION`.
    #[default]
    Unspecified,
    /// `INIT i NEXT n`.
    InitNext {
        /// The initial-state predicate.
        init: String,
        /// The next-state action.
        next: String,
    },
    /// `SPECIFICATION s`, where `s` is usually `Init /\ [][Next]_vars /\ …`.
    Temporal(String),
}

/// A parsed TLC configuration.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TlcConfig {
    /// `CONSTANT x = e`, in the order written.
    ///
    /// A map because TLC takes the last binding for a name, and because a
    /// caller looks these up by name.
    pub assignments: BTreeMap<String, ConfigValue>,
    /// `CONSTANT x <- Def`: replace `x` by the module's definition `Def`.
    pub replacements: BTreeMap<String, Replacement>,
    /// How the system moves.
    pub behavior: BehaviorSpec,
    /// `INVARIANT` / `INVARIANTS`.
    pub invariants: Vec<String>,
    /// `PROPERTY` / `PROPERTIES` — temporal, not checked by a BMC pass.
    pub properties: Vec<String>,
    /// `CONSTRAINT` / `CONSTRAINTS`: a state predicate bounding the search.
    pub state_constraints: Vec<String>,
    /// `ACTION_CONSTRAINT` / `ACTION_CONSTRAINTS`: the same over a step.
    pub action_constraints: Vec<String>,
    /// `SYMMETRY` — recorded, not acted on.
    pub symmetry: Option<String>,
    /// `VIEW` — recorded, not acted on.
    pub view: Option<String>,
    /// `ALIAS` — recorded, not acted on.
    pub alias: Option<String>,
    /// `POSTCONDITION` — recorded, not acted on.
    pub postcondition: Option<String>,
    /// `CHECK_DEADLOCK`, absent when the file does not say.
    pub check_deadlock: Option<bool>,
}

impl TlcConfig {
    /// The options this parser understands but deliberately does not act on.
    ///
    /// Surfaced rather than logged, for the same reason a dropped `ASSUME` is:
    /// a caller deciding whether to trust a verdict needs to know what of the
    /// author's configuration was read and then set aside.
    #[must_use]
    pub fn unused_options(&self) -> Vec<&'static str> {
        let mut out = Vec::new();
        if self.symmetry.is_some() {
            out.push("SYMMETRY");
        }
        if self.view.is_some() {
            out.push("VIEW");
        }
        if self.alias.is_some() {
            out.push("ALIAS");
        }
        if self.postcondition.is_some() {
            out.push("POSTCONDITION");
        }
        out
    }
}

impl TlcConfig {
    /// Assignments whose right-hand side is module-qualified (`x = [M]d`).
    ///
    /// Kept uninterpreted by [`ConfigValue::ModuleQualified`]; listed here for
    /// the same reason as [`TlcConfig::module_qualified_replacements`], so a
    /// caller can say it did not act on them instead of the fact vanishing.
    #[must_use]
    pub fn module_qualified_assignments(&self) -> Vec<(&str, &str, &str)> {
        self.assignments
            .iter()
            .filter_map(|(name, v)| match v {
                ConfigValue::ModuleQualified { module, name: to } => {
                    Some((name.as_str(), module.as_str(), to.as_str()))
                }
                _ => None,
            })
            .collect()
    }

    /// Replacements that name an instantiated module (`x <- [M]d`).
    ///
    /// Reported separately because applying one needs `INSTANCE` substitution,
    /// which the lowering pass does not do yet. A caller that ignores these is
    /// checking the specification *without* the author's replacement, which
    /// can change the answer in either direction — so it has to be visible
    /// rather than absorbed.
    #[must_use]
    pub fn module_qualified_replacements(&self) -> Vec<(&str, &str, &str)> {
        self.replacements
            .iter()
            .filter_map(|(name, r)| {
                r.module
                    .as_deref()
                    .map(|m| (name.as_str(), m, r.to.as_str()))
            })
            .collect()
    }
}

/// One lexeme.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    /// A keyword, canonicalised to its singular spelling.
    Key(Key),
    Ident(String),
    Number(String),
    Str(String),
    Bool(bool),
    /// A TLA+ operator used as a name, e.g. `\\o` or `++`.
    Op(String),
    Eq,
    LeftArrow,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    Comma,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Key {
    Constant,
    Init,
    Next,
    Specification,
    Invariant,
    Property,
    Constraint,
    ActionConstraint,
    Symmetry,
    View,
    Alias,
    Postcondition,
    CheckDeadlock,
}

impl Key {
    fn name(self) -> &'static str {
        match self {
            Self::Constant => "CONSTANT",
            Self::Init => "INIT",
            Self::Next => "NEXT",
            Self::Specification => "SPECIFICATION",
            Self::Invariant => "INVARIANT",
            Self::Property => "PROPERTY",
            Self::Constraint => "CONSTRAINT",
            Self::ActionConstraint => "ACTION_CONSTRAINT",
            Self::Symmetry => "SYMMETRY",
            Self::View => "VIEW",
            Self::Alias => "ALIAS",
            Self::Postcondition => "POSTCONDITION",
            Self::CheckDeadlock => "CHECK_DEADLOCK",
        }
    }

    /// The keyword a word spells, if it spells one.
    ///
    /// Plural spellings fold onto the singular, which is what makes
    /// `INVARIANT` and `INVARIANTS` one production rather than two. `TRUE` and
    /// `FALSE` are handled by the caller, before this: they are values, and a
    /// word is only a keyword when it is not one.
    fn of(word: &str) -> Option<Self> {
        Some(match word {
            "CONSTANT" | "CONSTANTS" => Self::Constant,
            "INIT" => Self::Init,
            "NEXT" => Self::Next,
            "SPECIFICATION" => Self::Specification,
            "INVARIANT" | "INVARIANTS" => Self::Invariant,
            "PROPERTY" | "PROPERTIES" => Self::Property,
            "CONSTRAINT" | "CONSTRAINTS" => Self::Constraint,
            "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" => Self::ActionConstraint,
            "SYMMETRY" => Self::Symmetry,
            "VIEW" => Self::View,
            "ALIAS" => Self::Alias,
            "POSTCONDITION" => Self::Postcondition,
            "CHECK_DEADLOCK" => Self::CheckDeadlock,
            _ => return None,
        })
    }
}

impl Tok {
    /// How this token reads in a diagnostic.
    fn describe(&self) -> String {
        match self {
            Self::Key(k) => format!("`{}`", k.name()),
            Self::Ident(n) => format!("identifier `{n}`"),
            Self::Number(n) => format!("number `{n}`"),
            Self::Op(o) => format!("operator `{o}`"),
            Self::Str(s) => format!("string {s:?}"),
            Self::Bool(b) => format!("`{}`", if *b { "TRUE" } else { "FALSE" }),
            Self::Eq => "`=`".to_string(),
            Self::LeftArrow => "`<-`".to_string(),
            Self::LeftBrace => "`{`".to_string(),
            Self::RightBrace => "`}`".to_string(),
            Self::LeftBracket => "`[`".to_string(),
            Self::RightBracket => "`]`".to_string(),
            Self::Comma => "`,`".to_string(),
        }
    }
}

type Spanned = (Tok, Span);
type Result<T> = core::result::Result<T, ConfigError>;

/// Split a `.cfg` into tokens, dropping comments.
///
/// Explicit index walk: a `.cfg` is small, but the same discipline applies —
/// nothing here recurses on input. Line and column are tracked as the walk
/// advances, so every token carries a position an editor can jump to, which is
/// the whole crate's standard for diagnostics.
fn lex(src: &str) -> Result<Vec<Spanned>> {
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0usize;
    let mut line = 1u32;
    let mut col = 1u32;
    let mut byte = 0u32;
    let mut out = Vec::new();

    /// Advance one character, keeping line, column and byte offset in step.
    macro_rules! step {
        () => {{
            let c = chars[i];
            if c == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
            byte += c.len_utf8() as u32;
            i += 1;
        }};
    }

    while i < chars.len() {
        let c = chars[i];
        // Whitespace, newline included: unlike TLA+ proper, `.cfg` layout
        // carries no meaning, so an option's arguments may be on any line.
        if c.is_whitespace() {
            step!();
            continue;
        }
        // `\*` to end of line.
        if c == '\\' && chars.get(i + 1) == Some(&'*') {
            while i < chars.len() && chars[i] != '\n' {
                step!();
            }
            continue;
        }
        // `(* … *)`, which does not nest in TLC's lexer.
        if c == '(' && chars.get(i + 1) == Some(&'*') {
            let open = Pos::new(line, col, byte);
            step!();
            step!();
            loop {
                if i + 1 >= chars.len() {
                    return Err(ConfigError {
                        kind: ConfigErrorKind::UnterminatedComment,
                        span: Span::new(open, Pos::new(line, col, byte)),
                    });
                }
                if chars[i] == '*' && chars[i + 1] == ')' {
                    step!();
                    step!();
                    break;
                }
                step!();
            }
            continue;
        }

        let start = Pos::new(line, col, byte);
        let from = i;
        let tok = match c {
            '=' => {
                step!();
                Tok::Eq
            }
            '{' => {
                step!();
                Tok::LeftBrace
            }
            '}' => {
                step!();
                Tok::RightBrace
            }
            '[' => {
                step!();
                Tok::LeftBracket
            }
            ']' => {
                step!();
                Tok::RightBracket
            }
            ',' => {
                step!();
                Tok::Comma
            }
            '<' if chars.get(i + 1) == Some(&'-') => {
                step!();
                step!();
                Tok::LeftArrow
            }
            '"' => {
                step!();
                let text_from = i;
                while i < chars.len() && chars[i] != '"' && chars[i] != '\n' {
                    step!();
                }
                if i >= chars.len() || chars[i] != '"' {
                    return Err(ConfigError {
                        kind: ConfigErrorKind::UnterminatedString,
                        span: Span::new(start, Pos::new(line, col, byte)),
                    });
                }
                let text: String = chars[text_from..i].iter().collect();
                step!();
                Tok::Str(text)
            }
            // A leading `-` belongs to the numeral: TLC's grammar has no
            // prefix minus, only negative literals.
            '-' if chars.get(i + 1).is_some_and(char::is_ascii_digit) => {
                step!();
                while i < chars.len() && chars[i].is_ascii_digit() {
                    step!();
                }
                Tok::Number(chars[from..i].iter().collect())
            }
            d if d.is_ascii_digit() => {
                while i < chars.len() && chars[i].is_ascii_digit() {
                    step!();
                }
                Tok::Number(chars[from..i].iter().collect())
            }
            a if a.is_ascii_alphabetic() || a == '_' => {
                while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    step!();
                }
                let word: String = chars[from..i].iter().collect();
                match word.as_str() {
                    // Values, checked before keywords: a word is a keyword
                    // only when it is not one of these.
                    "TRUE" => Tok::Bool(true),
                    "FALSE" => Tok::Bool(false),
                    _ => match Key::of(&word) {
                        Some(k) => Tok::Key(k),
                        None => Tok::Ident(word),
                    },
                }
            }
            // A TLA+ operator used as a name: `\\o <- MCCat`, `++ <- PlusPlus`,
            // `Plus <- +`. Not in the published EBNF, which admits only
            // `[a-zA-Z_][a-zA-Z0-9_]*`, but TLC accepts it and the corpus uses
            // it. Validated against this crate's own operator table rather
            // than against a character class, so a run of punctuation that is
            // not a TLA+ operator is still an error.
            '\\' => {
                step!();
                while i < chars.len() && chars[i].is_ascii_alphabetic() {
                    step!();
                }
                let word: String = chars[from..i].iter().collect();
                if !is_operator(&word) {
                    return Err(ConfigError {
                        kind: ConfigErrorKind::NotAnOperator(word),
                        span: Span::new(start, Pos::new(line, col, byte)),
                    });
                }
                Tok::Op(word)
            }
            o if is_op_char(o) => {
                while i < chars.len() && is_op_char(chars[i]) {
                    step!();
                }
                let word: String = chars[from..i].iter().collect();
                if !is_operator(&word) {
                    return Err(ConfigError {
                        kind: ConfigErrorKind::NotAnOperator(word),
                        span: Span::new(start, Pos::new(line, col, byte)),
                    });
                }
                Tok::Op(word)
            }
            other => {
                return Err(ConfigError {
                    kind: ConfigErrorKind::UnexpectedChar(other),
                    span: Span::new(start, Pos::new(line, col, byte)),
                });
            }
        };
        out.push((tok, Span::new(start, Pos::new(line, col, byte))));
    }
    Ok(out)
}

/// Characters a TLA+ operator spelling is built from.
///
/// `=`, `{`, `}`, `[`, `]` and `,` are deliberately absent: they are the
/// configuration file's own punctuation and are matched before this.
fn is_op_char(c: char) -> bool {
    matches!(
        c,
        '+' | '-'
            | '*'
            | '/'
            | '<'
            | '>'
            | '~'
            | '!'
            | '@'
            | '#'
            | '$'
            | '%'
            | '^'
            | '&'
            | '|'
            | ':'
            | '.'
            | '?'
    )
}

/// Whether a spelling is a TLA+ operator this crate knows.
///
/// Uses the crate's own operator table — the same one the expression parser
/// reads — rather than a second list that could drift from it.
fn is_operator(word: &str) -> bool {
    crate::op::infix_info(word).is_some()
        || crate::op::prefix_info(word).is_some()
        || crate::op::postfix_info(word).is_some()
}

/// Token cursor.
struct P {
    toks: Vec<Spanned>,
    at: usize,
}

impl P {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at).map(|(t, _)| t)
    }

    fn span(&self) -> Span {
        match self.toks.get(self.at) {
            Some((_, s)) => *s,
            // Past the end: point at the last token there was, so the
            // diagnostic still lands inside the file.
            None => self
                .toks
                .last()
                .map_or(Span::new(Pos::START, Pos::START), |(_, s)| *s),
        }
    }

    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.at).map(|(t, _)| t.clone());
        if t.is_some() {
            self.at += 1;
        }
        t
    }

    fn err<T>(&self, expected: &str) -> Result<T> {
        Err(ConfigError {
            kind: ConfigErrorKind::Unexpected {
                expected: expected.to_string(),
                found: self
                    .peek()
                    .map_or_else(|| "end of file".to_string(), Tok::describe),
            },
            span: self.span(),
        })
    }

    fn ident(&mut self) -> Result<String> {
        match self.peek() {
            Some(Tok::Ident(_)) => match self.bump() {
                Some(Tok::Ident(n)) => Ok(n),
                // Unreachable by the peek above, and written as an error
                // rather than an `expect`: the rule against `expect` exists
                // precisely for "just matched above".
                _ => self.err("an identifier"),
            },
            _ => self.err("an identifier"),
        }
    }

    /// An identifier **or** an operator spelling.
    ///
    /// Both sides of a `<-` may name an operator (`\o <- MCCat`,
    /// `Plus <- +`), which is why the constant section uses this where the
    /// published EBNF says `ident`.
    fn name(&mut self) -> Result<String> {
        match self.peek() {
            Some(Tok::Ident(_) | Tok::Op(_)) => match self.bump() {
                Some(Tok::Ident(n) | Tok::Op(n)) => Ok(n),
                _ => self.err("a name"),
            },
            _ => self.err("a name or operator"),
        }
    }

    /// Identifiers up to the next keyword.
    ///
    /// `INVARIANT TypeOK Correctness` is a list with no separator, so it ends
    /// where the next option begins.
    fn ident_run(&mut self) -> Vec<String> {
        let mut out = Vec::new();
        while let Some(Tok::Ident(_)) = self.peek() {
            match self.bump() {
                Some(Tok::Ident(n)) => out.push(n),
                _ => break,
            }
        }
        out
    }

    fn value(&mut self) -> Result<ConfigValue> {
        match self.bump() {
            Some(Tok::Ident(n)) => Ok(ConfigValue::ModelValue(n)),
            Some(Tok::Number(n)) => Ok(ConfigValue::Int(n)),
            Some(Tok::Str(s)) => Ok(ConfigValue::Str(s)),
            Some(Tok::Bool(b)) => Ok(ConfigValue::Bool(b)),
            Some(Tok::LeftBracket) => {
                let module = self.ident()?;
                if self.bump() != Some(Tok::RightBracket) {
                    self.at = self.at.saturating_sub(1);
                    return self.err("`]` to close a module qualifier");
                }
                let name = self.name()?;
                Ok(ConfigValue::ModuleQualified { module, name })
            }
            Some(Tok::LeftBrace) => {
                let mut items = Vec::new();
                if self.peek() == Some(&Tok::RightBrace) {
                    self.bump();
                    return Ok(ConfigValue::Set(items));
                }
                loop {
                    items.push(self.value()?);
                    match self.peek() {
                        Some(Tok::Comma) => {
                            self.bump();
                        }
                        Some(Tok::RightBrace) => {
                            self.bump();
                            return Ok(ConfigValue::Set(items));
                        }
                        _ => return self.err("`,` or `}`"),
                    }
                }
            }
            _ => {
                // `bump` consumed it, so step back to point the diagnostic at
                // the offending token rather than the one after it.
                self.at = self.at.saturating_sub(1);
                self.err("a constant expression")
            }
        }
    }
}

/// Parse a TLC configuration file.
///
/// # Errors
///
/// Returns the first thing that is not in the grammar, with a span. Nothing is
/// skipped: an option this parser does not recognise is an error rather than a
/// silent omission, because a silently dropped `CONSTANT` changes which
/// specification is being checked.
pub fn parse_config(src: &str) -> Result<TlcConfig> {
    let mut p = P {
        toks: lex(src)?,
        at: 0,
    };
    let mut cfg = TlcConfig::default();
    // `INIT` and `NEXT` are separate options in the grammar but one behaviour
    // specification, so they are collected and combined at the end.
    let mut init: Option<String> = None;
    let mut next: Option<String> = None;
    let mut spec: Option<String> = None;
    let mut spec_span = Span::new(Pos::START, Pos::START);

    while p.peek().is_some() {
        let Some(Tok::Key(key)) = p.peek().cloned() else {
            return p.err("a configuration option");
        };
        let key_span = p.span();
        p.bump();
        match key {
            Key::Constant => {
                // `CONSTANT` takes a run of bindings, and a run may be empty:
                // `CONSTANTS` with nothing after it is legal and says nothing.
                while matches!(p.peek(), Some(Tok::Ident(_) | Tok::Op(_))) {
                    let name = p.name()?;
                    match p.bump() {
                        Some(Tok::Eq) => {
                            cfg.assignments.insert(name, p.value()?);
                        }
                        Some(Tok::LeftArrow) => {
                            // `x <- [M]d` scopes the replacement to the
                            // instantiated module `M`.
                            let module = if p.peek() == Some(&Tok::LeftBracket) {
                                p.bump();
                                let m = p.ident()?;
                                if p.bump() != Some(Tok::RightBracket) {
                                    p.at = p.at.saturating_sub(1);
                                    return p.err("`]` to close a module qualifier");
                                }
                                Some(m)
                            } else {
                                None
                            };
                            let to = p.name()?;
                            cfg.replacements.insert(name, Replacement { to, module });
                        }
                        _ => {
                            p.at = p.at.saturating_sub(1);
                            return p.err("`=` or `<-` after a constant name");
                        }
                    }
                }
            }
            Key::Init => init = Some(p.ident()?),
            Key::Next => next = Some(p.ident()?),
            Key::Specification => {
                spec = Some(p.ident()?);
                spec_span = key_span;
            }
            Key::Invariant => cfg.invariants.extend(p.ident_run()),
            Key::Property => cfg.properties.extend(p.ident_run()),
            Key::Constraint => cfg.state_constraints.extend(p.ident_run()),
            Key::ActionConstraint => cfg.action_constraints.extend(p.ident_run()),
            Key::Symmetry => cfg.symmetry = Some(p.ident()?),
            Key::View => cfg.view = Some(p.ident()?),
            Key::Alias => cfg.alias = Some(p.ident()?),
            Key::Postcondition => cfg.postcondition = Some(p.ident()?),
            Key::CheckDeadlock => match p.bump() {
                Some(Tok::Bool(b)) => match cfg.check_deadlock {
                    Some(prev) if prev != b => {
                        return Err(ConfigError {
                            kind: ConfigErrorKind::ConflictingCheckDeadlock,
                            span: key_span,
                        });
                    }
                    _ => cfg.check_deadlock = Some(b),
                },
                _ => {
                    p.at = p.at.saturating_sub(1);
                    return p.err("`TRUE` or `FALSE`");
                }
            },
        }
    }

    // `INIT`/`NEXT` and `SPECIFICATION` both say how the system moves. A file
    // giving both does not say which to believe, so it is reported rather than
    // resolved by a precedence rule nobody wrote down.
    cfg.behavior = match (init, next, spec) {
        (Some(init), Some(next), None) => BehaviorSpec::InitNext { init, next },
        (None, None, Some(s)) => BehaviorSpec::Temporal(s),
        (None, None, None) => BehaviorSpec::Unspecified,
        (i, n, Some(s)) => {
            return Err(ConfigError {
                kind: ConfigErrorKind::TwoBehaviourSpecs {
                    first: format!("INIT {} / NEXT {}", opt(&i), opt(&n)),
                    second: format!("SPECIFICATION {s}"),
                },
                span: spec_span,
            });
        }
        // One of the pair without the other. TLC needs both to run, and
        // guessing the missing half from a naming convention here would hide
        // that the configuration is incomplete.
        (i, _, None) => {
            return Err(ConfigError {
                kind: ConfigErrorKind::Unexpected {
                    expected: if i.is_some() {
                        "`NEXT` to go with `INIT`".to_string()
                    } else {
                        "`INIT` to go with `NEXT`".to_string()
                    },
                    found: "neither".to_string(),
                },
                span: Span::new(Pos::START, Pos::START),
            });
        }
    };
    Ok(cfg)
}

fn opt(x: &Option<String>) -> &str {
    x.as_deref().unwrap_or("<missing>")
}
