//! Tokens produced by [`crate::lexer`].

use crate::span::Span;

/// A reserved word.
///
/// The five prefix operators that are spelled as words — `DOMAIN`, `SUBSET`,
/// `UNION`, `ENABLED`, `UNCHANGED` — are deliberately **not** here. The lexer
/// emits them as [`TokenKind::Sym`] so that [`crate::op::prefix_info`] can be
/// keyed uniformly by spelling, rather than forcing the parser to translate
/// between two representations of the same concept.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[allow(missing_docs)]
pub enum Keyword {
    Module,
    Extends,
    Constant,
    Constants,
    Variable,
    Variables,
    Local,
    Instance,
    With,
    Theorem,
    Lemma,
    Corollary,
    Proposition,
    Axiom,
    Assume,
    Assumption,
    Prove,
    Let,
    In,
    If,
    Then,
    Else,
    Case,
    Other,
    Choose,
    Except,
    Lambda,
    Recursive,
    /// `WF_` — always followed by a subscript expression.
    WeakFairness,
    /// `SF_` — always followed by a subscript expression.
    StrongFairness,
    // Proof-language keywords. Accepted by the lexer so that a proof body can
    // be skipped with balanced structure rather than mis-lexed; milestone 1
    // does not interpret them.
    By,
    Obvious,
    Omitted,
    Qed,
    Def,
    Defs,
    Have,
    Take,
    Witness,
    Pick,
    Suffices,
    New,
    Use,
    Hide,
    ProofKw,
    State,
    Action,
    Temporal,
}

impl Keyword {
    /// Map a source word to a reserved word, if it is one.
    ///
    /// Named `from_word` rather than `from_str` so it is not mistaken for
    /// [`core::str::FromStr`], which would imply a fallible parse of arbitrary
    /// text rather than a lookup in a closed table.
    #[must_use]
    pub fn from_word(s: &str) -> Option<Self> {
        let kw = match s {
            "MODULE" => Self::Module,
            "EXTENDS" => Self::Extends,
            "CONSTANT" => Self::Constant,
            "CONSTANTS" => Self::Constants,
            "VARIABLE" => Self::Variable,
            "VARIABLES" => Self::Variables,
            "LOCAL" => Self::Local,
            "INSTANCE" => Self::Instance,
            "WITH" => Self::With,
            "THEOREM" => Self::Theorem,
            "LEMMA" => Self::Lemma,
            "COROLLARY" => Self::Corollary,
            "PROPOSITION" => Self::Proposition,
            "AXIOM" => Self::Axiom,
            "ASSUME" => Self::Assume,
            "ASSUMPTION" => Self::Assumption,
            "PROVE" => Self::Prove,
            "LET" => Self::Let,
            "IN" => Self::In,
            "IF" => Self::If,
            "THEN" => Self::Then,
            "ELSE" => Self::Else,
            "CASE" => Self::Case,
            "OTHER" => Self::Other,
            "CHOOSE" => Self::Choose,
            "EXCEPT" => Self::Except,
            "LAMBDA" => Self::Lambda,
            "RECURSIVE" => Self::Recursive,
            "BY" => Self::By,
            "OBVIOUS" => Self::Obvious,
            "OMITTED" => Self::Omitted,
            "QED" => Self::Qed,
            "DEF" => Self::Def,
            "DEFS" => Self::Defs,
            "HAVE" => Self::Have,
            "TAKE" => Self::Take,
            "WITNESS" => Self::Witness,
            "PICK" => Self::Pick,
            "SUFFICES" => Self::Suffices,
            "NEW" => Self::New,
            "USE" => Self::Use,
            "HIDE" => Self::Hide,
            "PROOF" => Self::ProofKw,
            "STATE" => Self::State,
            "ACTION" => Self::Action,
            "TEMPORAL" => Self::Temporal,
            _ => return None,
        };
        Some(kw)
    }

    /// The source spelling of this reserved word.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Module => "MODULE",
            Self::Extends => "EXTENDS",
            Self::Constant => "CONSTANT",
            Self::Constants => "CONSTANTS",
            Self::Variable => "VARIABLE",
            Self::Variables => "VARIABLES",
            Self::Local => "LOCAL",
            Self::Instance => "INSTANCE",
            Self::With => "WITH",
            Self::Theorem => "THEOREM",
            Self::Lemma => "LEMMA",
            Self::Corollary => "COROLLARY",
            Self::Proposition => "PROPOSITION",
            Self::Axiom => "AXIOM",
            Self::Assume => "ASSUME",
            Self::Assumption => "ASSUMPTION",
            Self::Prove => "PROVE",
            Self::Let => "LET",
            Self::In => "IN",
            Self::If => "IF",
            Self::Then => "THEN",
            Self::Else => "ELSE",
            Self::Case => "CASE",
            Self::Other => "OTHER",
            Self::Choose => "CHOOSE",
            Self::Except => "EXCEPT",
            Self::Lambda => "LAMBDA",
            Self::Recursive => "RECURSIVE",
            Self::WeakFairness => "WF_",
            Self::StrongFairness => "SF_",
            Self::By => "BY",
            Self::Obvious => "OBVIOUS",
            Self::Omitted => "OMITTED",
            Self::Qed => "QED",
            Self::Def => "DEF",
            Self::Defs => "DEFS",
            Self::Have => "HAVE",
            Self::Take => "TAKE",
            Self::Witness => "WITNESS",
            Self::Pick => "PICK",
            Self::Suffices => "SUFFICES",
            Self::New => "NEW",
            Self::Use => "USE",
            Self::Hide => "HIDE",
            Self::ProofKw => "PROOF",
            Self::State => "STATE",
            Self::Action => "ACTION",
            Self::Temporal => "TEMPORAL",
        }
    }
}

/// The base a numeral was written in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NumBase {
    /// Ordinary decimal, e.g. `42`.
    Decimal,
    /// `\b` / `\B` prefix, e.g. `\b1011`.
    Binary,
    /// `\o` / `\O` prefix, e.g. `\o777`.
    Octal,
    /// `\h` / `\H` prefix, e.g. `\hFF`.
    Hex,
}

/// What kind of lexeme a token is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TokenKind {
    /// An identifier: letters, digits and `_`, containing at least one letter.
    Ident,
    /// An integer numeral in the given base.
    Int(NumBase),
    /// A decimal numeral with a fractional part, e.g. `3.14`.
    Real,
    /// A `"…"` string literal. The token text is the *decoded* value.
    Str,
    /// A reserved word.
    Keyword(Keyword),
    /// An operator or punctuation symbol. The token text is the **canonical
    /// ASCII spelling**, so Unicode input is already normalised here.
    Sym,
    /// A run of four or more `-`. Opens and closes a module header, and also
    /// serves as a horizontal rule between units.
    Dashes,
    /// A run of four or more `=`. Closes a module.
    ModuleFooter,
    /// End of input.
    Eof,
}

/// One lexeme, with its source span and its text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    /// What kind of lexeme this is.
    pub kind: TokenKind,
    /// For [`TokenKind::Sym`] the canonical ASCII spelling; for
    /// [`TokenKind::Str`] the decoded string value; otherwise the source text.
    pub text: String,
    /// Where the token came from.
    pub span: Span,
}

impl Token {
    /// The column the token starts at. Junction-list layout is decided by this.
    #[must_use]
    pub const fn col(&self) -> u32 {
        self.span.start.col
    }

    /// Whether this is the symbol with the given canonical spelling.
    #[must_use]
    pub fn is_sym(&self, canonical: &str) -> bool {
        self.kind == TokenKind::Sym && self.text == canonical
    }

    /// Whether this is the given reserved word.
    #[must_use]
    pub fn is_kw(&self, kw: Keyword) -> bool {
        self.kind == TokenKind::Keyword(kw)
    }
}

/// A comment retained by the lexer.
///
/// Comments are **not** discarded, because `@type:` annotations — the input to
/// the Snowcat type system — live inside them. Dropping them at lex time would
/// cost the type system its input, which is an easy and expensive mistake.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Comment {
    /// Comment body, without the `\*` or `(*` `*)` delimiters.
    pub text: String,
    /// Where the comment came from, including its delimiters.
    pub span: Span,
    /// Whether this was a `(* … *)` block comment rather than a `\*` line one.
    pub block: bool,
}
