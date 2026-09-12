//! The TLA+ lexer.
//!
//! Produces a flat [`Token`] stream plus the retained [`Comment`] list. Layout
//! is **not** handled here — see [`crate::parser`] for why junction lists need
//! expression-position context that a lexical pass does not have.
//!
//! Two subtleties worth naming, because both are easy to get silently wrong:
//!
//! * **Based numerals collide with operators.** `\o` is circle-composition and
//!   `\o777` is octal 511; `\h` is nothing and `\hFF` is 255, whose digits are
//!   *letters*. `lex_backslash` resolves this by scanning the whole
//!   alphanumeric run and asking whether everything after the base letter is a
//!   digit in that base.
//! * **Comments carry semantics.** `@type:` annotations live inside `\*`
//!   comments and are the input to the type system, so comments are collected
//!   rather than discarded.

use crate::error::{ErrorKind, Result, SyntaxError};
use crate::span::{Pos, Span};
use crate::token::{Comment, Keyword, NumBase, Token, TokenKind};

/// The output of a successful lex.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lexed {
    /// The token stream, always terminated by [`TokenKind::Eof`].
    pub tokens: Vec<Token>,
    /// Comments, in source order, retained for `@type:` annotations.
    pub comments: Vec<Comment>,
}

/// Canonicalise an operator spelling.
///
/// Unicode spellings and ASCII aliases both collapse to one representative, so
/// the operator table and the AST only ever see one form. Returns the input
/// unchanged when it is already canonical (or not an alias).
#[must_use]
pub fn canonical_sym(s: &str) -> &str {
    match s {
        // ASCII aliases.
        "=<" => "<=",
        "#" => "/=",
        "\\land" => "/\\",
        "\\lor" => "\\/",
        "\\lnot" | "\\neg" => "~",
        "\\equiv" => "<=>",
        "\\leq" => "<=",
        "\\geq" => ">=",
        "\\union" => "\\cup",
        "\\intersect" => "\\cap",
        "\\circ" => "\\o",
        "\\times" => "\\X",
        "\\leadsto" => "~>",
        // `\exists` / `\forall` are genuine SANY aliases for `\E` / `\A`.
        //
        // `\mod` is deliberately NOT aliased to `%`. SANY rejects `\mod`
        // outright (`test49b.tla` fails there), so accepting it is a superset
        // extension -- but folding it onto `%` would mean `u \mod v == u`
        // silently redefines `%`, conflating two operators a spec may use
        // separately. It keeps its own identity instead; see `op::infix_info`.
        "\\exists" => "\\E",
        "\\forall" => "\\A",
        "(+)" => "\\oplus",
        "(-)" => "\\ominus",
        "(.)" => "\\odot",
        "(/)" => "\\oslash",
        "(\\X)" => "\\otimes",
        // Unicode spellings.
        "\u{2227}" => "/\\",             // ∧
        "\u{2228}" => "\\/",             // ∨
        "\u{00AC}" => "~",               // ¬
        "\u{21D2}" => "=>",              // ⇒
        "\u{2261}" => "<=>",             // ≡
        "\u{21D4}" => "<=>",             // ⇔
        "\u{2260}" => "/=",              // ≠
        "\u{2264}" => "<=",              // ≤
        "\u{2265}" => ">=",              // ≥
        "\u{2208}" => "\\in",            // ∈
        "\u{2209}" => "\\notin",         // ∉
        "\u{222A}" => "\\cup",           // ∪
        "\u{2229}" => "\\cap",           // ∩
        "\u{2286}" => "\\subseteq",      // ⊆
        "\u{2282}" => "\\subset",        // ⊂
        "\u{2287}" => "\\supseteq",      // ⊇
        "\u{2283}" => "\\supset",        // ⊃
        "\u{00D7}" => "\\X",             // ×
        "\u{00F7}" => "\\div",           // ÷
        "\u{22C5}" => "\\cdot",          // ⋅
        "\u{2218}" => "\\o",             // ∘
        "\u{2200}" => "\\A",             // ∀
        "\u{2203}" => "\\E",             // ∃
        "\u{27E8}" | "\u{3008}" => "<<", // ⟨ 〈
        "\u{27E9}" | "\u{3009}" => ">>", // ⟩ 〉
        "\u{21A6}" => "|->",             // ↦
        "\u{2192}" => "->",              // →
        "\u{225C}" => "==",              // ≜
        "\u{25A1}" => "[]",              // □
        "\u{25C7}" | "\u{22C4}" => "<>", // ◇ ⋄
        "\u{2933}" | "\u{219D}" => "~>", // ⤳ ↝
        "\u{2295}" => "\\oplus",         // ⊕
        "\u{2296}" => "\\ominus",        // ⊖
        "\u{2297}" => "\\otimes",        // ⊗
        "\u{2298}" => "\\oslash",        // ⊘
        "\u{2299}" => "\\odot",          // ⊙
        "\u{227A}" => "\\prec",          // ≺
        "\u{227B}" => "\\succ",          // ≻
        "\u{2AAF}" => "\\preceq",        // ⪯
        "\u{2AB0}" => "\\succeq",        // ⪰
        "\u{228F}" => "\\sqsubset",      // ⊏
        "\u{2290}" => "\\sqsupset",      // ⊐
        "\u{2291}" => "\\sqsubseteq",    // ⊑
        "\u{2292}" => "\\sqsupseteq",    // ⊒
        "\u{2293}" => "\\sqcap",         // ⊓
        "\u{2294}" => "\\sqcup",         // ⊔
        "\u{228E}" => "\\uplus",         // ⊎
        "\u{2248}" => "\\approx",        // ≈
        "\u{2245}" => "\\cong",          // ≅
        "\u{2250}" => "\\doteq",         // ≐
        "\u{2243}" => "\\simeq",         // ≃
        "\u{224D}" => "\\asymp",         // ≍
        "\u{226A}" => "\\ll",            // ≪
        "\u{226B}" => "\\gg",            // ≫
        "\u{221D}" => "\\propto",        // ∝
        "\u{223C}" => "\\sim",           // ∼
        "\u{2016}" => "||",              // ‖
        other => other,
    }
}

/// Multi-character ASCII symbols, **longest first**.
///
/// Order is load-bearing: maximal munch is what separates `<=>` from `<=`,
/// `-+->` from `->`, and `(+)` from a parenthesised `+`.
const MULTI_SYMS: &[&str] = &[
    "(\\X)", "-+->", "<=>", "|->", "...", "::=", "(+)", "(-)", "(.)", "(/)", "=>", "=<", "=|",
    "==", "<=", "<:", "<<", "<>", ">=", ">>", "|-", "|=", "||", "->", "-|", "--", "..", "//", "/=",
    "/\\", "<-", "[]", "^+", "^*", "^#", "^^", ":>", "::", ":=", "~>", "##", "$$", "%%", "&&",
    "**", "++", "@@", "??", "!!",
];

/// Single-character ASCII symbols.
const SINGLE_SYMS: &[char] = &[
    '=', '<', '>', '|', '-', '.', '/', '[', ']', '(', ')', '{', '}', ',', ':', ';', '~', '#', '$',
    '%', '&', '*', '+', '@', '^', '\'', '!', '_',
];

/// The TLA+ lexer.
pub struct Lexer<'a> {
    src: &'a str,
    chars: Vec<(usize, char)>,
    idx: usize,
    line: u32,
    col: u32,
    comments: Vec<Comment>,
}

impl<'a> Lexer<'a> {
    /// Create a lexer over `src`.
    #[must_use]
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            chars: src.char_indices().collect(),
            idx: 0,
            line: 1,
            col: 1,
            comments: Vec::new(),
        }
    }

    /// Discard everything before the first `---- MODULE`.
    ///
    /// A `.tla` file may legally open with prose, a copyright block, or
    /// typesetting escapes such as `` `. … .' ``. SANY ignores all of it, so
    /// this has to happen at the *lexer*: the prose frequently contains
    /// characters that are not TLA+ lexemes at all, and lexing would fail
    /// before the parser ever got to skip anything.
    fn skip_preamble(&mut self) {
        // Only skip when there is a header to skip *to*. A bare expression --
        // what `parse_expr_str` and the `@type:` annotation bodies are -- has
        // no module header, and skipping to end of input would silently
        // swallow the whole thing.
        if !self.more_modules_ahead() {
            return;
        }
        loop {
            // A module header is four or more `-`, then `MODULE`.
            if self.peek(0) == Some('-') && self.run_len('-') >= 4 {
                let mut n = self.run_len('-');
                while self.peek(n).is_some_and(char::is_whitespace) {
                    n += 1;
                }
                let mut word = String::new();
                let mut m = n;
                while self.peek(m).is_some_and(char::is_alphanumeric) {
                    if let Some(c) = self.peek(m) {
                        word.push(c);
                    }
                    m += 1;
                }
                if word == "MODULE" {
                    return;
                }
            }
            if self.peek(0).is_none() {
                return;
            }
            self.bump();
        }
    }

    /// Lex the whole input.
    ///
    /// # Errors
    ///
    /// Returns the first [`SyntaxError`] encountered.
    pub fn lex(mut self) -> Result<Lexed> {
        self.skip_preamble();
        let mut tokens = Vec::new();
        // `[A]_v` and `<<A>>_v` are the reason this flag exists. `_` is a
        // legal identifier character, so `_v` would otherwise lex as the
        // identifier `_v` and swallow the subscript marker. Immediately after
        // a closing `]` or `>>`, a `_` is the subscript operator instead.
        let mut prev_close_end: Option<u32> = None;
        let mut module_depth: usize = 0;
        let mut prev_was_dashes = false;
        loop {
            self.skip_trivia()?;
            let start = self.pos();
            let Some(c) = self.peek(0) else {
                tokens.push(Token {
                    kind: TokenKind::Eof,
                    text: String::new(),
                    span: Span::empty(start),
                });
                break;
            };
            // Adjacency matters: `[A]_v` has no space, whereas a line ending
            // in `>>` followed by a definition of `__f1` at column 1 must not
            // turn that leading `_` into a subscript marker.
            let adjacent = prev_close_end == Some(start.offset);
            let tok = self.lex_one(c, start, adjacent)?;
            if tok.kind == TokenKind::Sym && (tok.text == "]" || tok.text == ">>") {
                prev_close_end = Some(tok.span.end.offset);
            } else {
                prev_close_end = None;
            }
            // Track module nesting. TLA+ modules nest, and a `====` that
            // closes an *inner* module must not be mistaken for the end of the
            // file -- `Rec12.tla` and `AnnotationsAndInstances592.tla` both
            // close four inner modules before the outer one ends.
            if tok.kind == TokenKind::Keyword(Keyword::Module) && prev_was_dashes {
                module_depth += 1;
            }
            prev_was_dashes = tok.kind == TokenKind::Dashes;
            let mut done = false;
            if tok.kind == TokenKind::ModuleFooter {
                module_depth = module_depth.saturating_sub(1);
                // Text after the last module's `====` is not part of any
                // module -- specs routinely end with shell snippets or prose --
                // and lexing it would fail on characters that are not TLA+
                // lexemes. Stop once the outermost module has closed and no
                // further header remains.
                done = module_depth == 0 && !self.more_modules_ahead();
            }
            tokens.push(tok);
            if done {
                let end = self.pos();
                tokens.push(Token {
                    kind: TokenKind::Eof,
                    text: String::new(),
                    span: Span::empty(end),
                });
                break;
            }
        }
        Ok(Lexed {
            tokens,
            comments: self.comments,
        })
    }

    /// Is there another `---- MODULE` header in the remaining input?
    fn more_modules_ahead(&self) -> bool {
        let from = match self.chars.get(self.idx) {
            Some(&(o, _)) => o,
            None => return false,
        };
        let rest = self.src.get(from..).unwrap_or_default();
        rest.lines().any(|line| {
            let trimmed = line.trim_start();
            let dashes = trimmed.chars().take_while(|&c| c == '-').count();
            dashes >= 4
                && trimmed
                    .get(dashes..)
                    .is_some_and(|t| t.trim_start().starts_with("MODULE"))
        })
    }

    fn lex_one(&mut self, c: char, start: Pos, after_closer: bool) -> Result<Token> {
        if c == '_' && after_closer {
            self.bump();
            return Ok(self.finish(TokenKind::Sym, "_".to_string(), start));
        }
        // Run-of-dashes and run-of-equals must be tested before `-` and `=`.
        if c == '-' && self.run_len('-') >= 4 {
            let n = self.run_len('-');
            self.bump_n(n);
            return Ok(self.finish(TokenKind::Dashes, "-".repeat(n), start));
        }
        if c == '=' && self.run_len('=') >= 4 {
            let n = self.run_len('=');
            self.bump_n(n);
            return Ok(self.finish(TokenKind::ModuleFooter, "=".repeat(n), start));
        }
        if c == '"' {
            return self.lex_string(start);
        }
        if c.is_ascii_digit() {
            // A TLA+ identifier is letters, digits and `_` with *at least one
            // letter*, so it may begin with a digit: the module
            // `09_OutTransition` is a real example. Decide by scanning the
            // whole run before committing to a numeral.
            let mut n = 0;
            let mut has_letter = false;
            while let Some(ch) = self.peek(n) {
                if ch.is_alphanumeric() || ch == '_' {
                    has_letter |= ch.is_alphabetic();
                    n += 1;
                } else {
                    break;
                }
            }
            if has_letter {
                return self.lex_word(start);
            }
            return self.lex_decimal(start);
        }
        if c == '\\' {
            return self.lex_backslash(start);
        }
        if c.is_alphabetic() || c == '_' {
            return self.lex_word(start);
        }
        self.lex_symbol(c, start)
    }

    // ---- character plumbing -------------------------------------------------

    fn peek(&self, n: usize) -> Option<char> {
        self.chars.get(self.idx + n).map(|&(_, c)| c)
    }

    fn pos(&self) -> Pos {
        let offset = match self.chars.get(self.idx) {
            Some(&(o, _)) => o as u32,
            None => self.src.len() as u32,
        };
        Pos::new(self.line, self.col, offset)
    }

    fn bump(&mut self) {
        if let Some(&(_, c)) = self.chars.get(self.idx) {
            self.idx += 1;
            if c == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
        }
    }

    fn bump_n(&mut self, n: usize) {
        for _ in 0..n {
            self.bump();
        }
    }

    fn run_len(&self, c: char) -> usize {
        let mut n = 0;
        while self.peek(n) == Some(c) {
            n += 1;
        }
        n
    }

    /// Does the input at the cursor start with `s`?
    fn starts_with(&self, s: &str) -> bool {
        for (i, want) in s.chars().enumerate() {
            if self.peek(i) != Some(want) {
                return false;
            }
        }
        true
    }

    fn finish(&self, kind: TokenKind, text: String, start: Pos) -> Token {
        Token {
            kind,
            text,
            span: Span::new(start, self.pos()),
        }
    }

    // ---- trivia -------------------------------------------------------------

    fn skip_trivia(&mut self) -> Result<()> {
        loop {
            match self.peek(0) {
                Some(c) if c.is_whitespace() => self.bump(),
                Some('\\') if self.peek(1) == Some('*') => self.lex_line_comment(),
                Some('(') if self.peek(1) == Some('*') => self.lex_block_comment()?,
                _ => return Ok(()),
            }
        }
    }

    fn lex_line_comment(&mut self) {
        let start = self.pos();
        self.bump_n(2);
        let text_start = self.idx;
        while let Some(c) = self.peek(0) {
            if c == '\n' {
                break;
            }
            self.bump();
        }
        let text = self.slice(text_start, self.idx);
        let span = Span::new(start, self.pos());
        self.comments.push(Comment {
            text,
            span,
            block: false,
        });
    }

    /// Block comments nest, so this counts depth rather than scanning for the
    /// first `*)`.
    fn lex_block_comment(&mut self) -> Result<()> {
        let start = self.pos();
        self.bump_n(2);
        let text_start = self.idx;
        let mut depth = 1usize;
        while depth > 0 {
            match self.peek(0) {
                None => {
                    return Err(SyntaxError::new(
                        ErrorKind::UnterminatedComment,
                        Span::new(start, self.pos()),
                    ));
                }
                Some('(') if self.peek(1) == Some('*') => {
                    depth += 1;
                    self.bump_n(2);
                }
                Some('*') if self.peek(1) == Some(')') => {
                    depth -= 1;
                    self.bump_n(2);
                }
                Some(_) => self.bump(),
            }
        }
        // `self.idx - 2` drops the closing `*)`.
        let text = self.slice(text_start, self.idx.saturating_sub(2));
        let span = Span::new(start, self.pos());
        self.comments.push(Comment {
            text,
            span,
            block: true,
        });
        Ok(())
    }

    fn slice(&self, from: usize, to: usize) -> String {
        let lo = match self.chars.get(from) {
            Some(&(o, _)) => o,
            None => self.src.len(),
        };
        let hi = match self.chars.get(to) {
            Some(&(o, _)) => o,
            None => self.src.len(),
        };
        if lo <= hi {
            self.src.get(lo..hi).unwrap_or_default().to_string()
        } else {
            String::new()
        }
    }

    // ---- literals -----------------------------------------------------------

    fn lex_string(&mut self, start: Pos) -> Result<Token> {
        self.bump(); // opening quote
        let mut value = String::new();
        loop {
            let Some(c) = self.peek(0) else {
                return Err(SyntaxError::new(
                    ErrorKind::UnterminatedString,
                    Span::new(start, self.pos()),
                ));
            };
            match c {
                '"' => {
                    self.bump();
                    return Ok(self.finish(TokenKind::Str, value, start));
                }
                // TLA+ string literals do not span lines.
                '\n' => {
                    return Err(SyntaxError::new(
                        ErrorKind::UnterminatedString,
                        Span::new(start, self.pos()),
                    ));
                }
                '\\' => {
                    let esc_at = self.pos();
                    self.bump();
                    let Some(e) = self.peek(0) else {
                        return Err(SyntaxError::new(
                            ErrorKind::UnterminatedString,
                            Span::new(start, self.pos()),
                        ));
                    };
                    let decoded = match e {
                        '"' => '"',
                        '\\' => '\\',
                        't' => '\t',
                        'n' => '\n',
                        'f' => '\u{000C}',
                        'r' => '\r',
                        // TLA+ defines `\" \\ \t \n \f \r`, but the
                        // language's own test suite contains strings such as
                        // `"\oslash"`, so an unrecognised escape is kept
                        // literally rather than rejected. Matching the
                        // reference implementation beats matching the prose.
                        other => {
                            let _ = esc_at;
                            value.push('\\');
                            other
                        }
                    };
                    value.push(decoded);
                    self.bump();
                }
                other => {
                    value.push(other);
                    self.bump();
                }
            }
        }
    }

    fn lex_decimal(&mut self, start: Pos) -> Result<Token> {
        let text_start = self.idx;
        while self.peek(0).is_some_and(|c| c.is_ascii_digit()) {
            self.bump();
        }
        // `1..5` is the range operator applied to `1` and `5`, not `1.` then
        // `.5`, so a fractional part needs a digit after the dot.
        let is_real = self.peek(0) == Some('.') && self.peek(1).is_some_and(|c| c.is_ascii_digit());
        if is_real {
            self.bump();
            while self.peek(0).is_some_and(|c| c.is_ascii_digit()) {
                self.bump();
            }
        }
        let text = self.slice(text_start, self.idx);
        let kind = if is_real {
            TokenKind::Real
        } else {
            TokenKind::Int(NumBase::Decimal)
        };
        Ok(self.finish(kind, text, start))
    }

    /// Lex something beginning with `\`.
    ///
    /// In order: the `\/` operator, then a based numeral, then a `\`-word
    /// operator, then bare `\` (set difference). `\*` is already consumed as a
    /// comment by `skip_trivia` before we get here.
    fn lex_backslash(&mut self, start: Pos) -> Result<Token> {
        if self.starts_with("\\/") {
            self.bump_n(2);
            return Ok(self.finish(TokenKind::Sym, "\\/".to_string(), start));
        }

        // Scan the alphanumeric run after the backslash without consuming it.
        let mut run = String::new();
        let mut n = 1;
        while let Some(c) = self.peek(n) {
            if c.is_alphanumeric() {
                run.push(c);
                n += 1;
            } else {
                break;
            }
        }

        if run.is_empty() {
            // Bare `\` — set difference.
            self.bump();
            return Ok(self.finish(TokenKind::Sym, "\\".to_string(), start));
        }

        // Based numeral? The base letter is the first char of the run and the
        // remainder must be a non-empty string of digits in that base. This is
        // what keeps `\o777` (octal) apart from `\o` (composition) and `\hFF`
        // (hex, whose digits are letters) apart from a `\`-word.
        let mut base_chars = run.chars();
        if let Some(base_ch) = base_chars.next() {
            let rest: String = base_chars.collect();
            let base = match base_ch {
                'b' | 'B' => Some((NumBase::Binary, 2u32)),
                'o' | 'O' => Some((NumBase::Octal, 8)),
                'h' | 'H' => Some((NumBase::Hex, 16)),
                _ => None,
            };
            if let Some((num_base, radix)) = base
                && !rest.is_empty()
                && rest.chars().all(|c| c.is_digit(radix))
            {
                self.bump_n(1 + run.chars().count());
                return Ok(self.finish(TokenKind::Int(num_base), rest, start));
            }
            // A base letter with nothing usable after it: `\h` alone is not an
            // operator either, so report the more specific diagnostic.
            if base.is_some() && rest.is_empty() && run.chars().count() == 1 {
                let word = format!("\\{run}");
                if crate::op::infix_info(canonical_sym(&word)).is_none()
                    && crate::op::prefix_info(canonical_sym(&word)).is_none()
                {
                    self.bump_n(1 + run.chars().count());
                    return Err(SyntaxError::new(
                        ErrorKind::EmptyNumeral(word),
                        Span::new(start, self.pos()),
                    ));
                }
            }
        }

        let word = format!("\\{run}");
        self.bump_n(1 + run.chars().count());
        let canonical = canonical_sym(&word).to_string();
        if !is_known_backslash_word(&canonical) {
            return Err(SyntaxError::new(
                ErrorKind::UnknownOperator(word),
                Span::new(start, self.pos()),
            ));
        }
        Ok(self.finish(TokenKind::Sym, canonical, start))
    }

    fn lex_word(&mut self, start: Pos) -> Result<Token> {
        // Scan the full identifier run first, then decide how much to consume:
        // `WF_x` is the token `WF_` followed by the identifier `x`, so the
        // decision has to be made before anything is committed.
        let mut run = String::new();
        let mut n = 0;
        while let Some(c) = self.peek(n) {
            if c.is_alphanumeric() || c == '_' {
                run.push(c);
                n += 1;
            } else {
                break;
            }
        }

        for (prefix, kw) in [
            ("WF_", Keyword::WeakFairness),
            ("SF_", Keyword::StrongFairness),
        ] {
            if run.starts_with(prefix) {
                self.bump_n(3);
                return Ok(self.finish(TokenKind::Keyword(kw), prefix.to_string(), start));
            }
        }

        self.bump_n(run.chars().count());

        // A lone `_` is the arity placeholder in `Op(_, _)` and the subscript
        // marker, never an identifier -- even though `_` is a legal identifier
        // character and `_foo` is a legal identifier.
        if run == "_" {
            return Ok(self.finish(TokenKind::Sym, run, start));
        }

        // The word-spelled prefix operators are emitted as symbols so that the
        // operator table can be keyed uniformly by spelling.
        if matches!(
            run.as_str(),
            "DOMAIN" | "SUBSET" | "UNION" | "ENABLED" | "UNCHANGED"
        ) {
            return Ok(self.finish(TokenKind::Sym, run, start));
        }

        let kind = match Keyword::from_word(&run) {
            Some(kw) => TokenKind::Keyword(kw),
            None => TokenKind::Ident,
        };
        Ok(self.finish(kind, run, start))
    }

    fn lex_symbol(&mut self, c: char, start: Pos) -> Result<Token> {
        for &cand in MULTI_SYMS {
            if self.starts_with(cand) {
                self.bump_n(cand.chars().count());
                return Ok(self.finish(TokenKind::Sym, canonical_sym(cand).to_string(), start));
            }
        }
        if SINGLE_SYMS.contains(&c) {
            self.bump();
            let s = c.to_string();
            return Ok(self.finish(TokenKind::Sym, canonical_sym(&s).to_string(), start));
        }
        // A non-ASCII operator spelling.
        let s = c.to_string();
        let canonical = canonical_sym(&s);
        if canonical != s.as_str() {
            self.bump();
            return Ok(self.finish(TokenKind::Sym, canonical.to_string(), start));
        }
        self.bump();
        Err(SyntaxError::new(
            ErrorKind::UnexpectedChar(c),
            Span::new(start, self.pos()),
        ))
    }
}

/// Whether a canonicalised `\`-word is a TLA+ operator or binder.
///
/// The set is closed (TLA+ admits no new glyphs), so anything outside it is a
/// typo and is reported rather than passed through as an opaque name.
fn is_known_backslash_word(canonical: &str) -> bool {
    // Binders and the two set-of-functions spellings are not in the precedence
    // table but are legitimate lexemes.
    if matches!(canonical, "\\A" | "\\E" | "\\AA" | "\\EE" | "\\X" | "\\") {
        return true;
    }
    crate::op::infix_info(canonical).is_some() || crate::op::prefix_info(canonical).is_some()
}

/// Lex `src` into tokens and comments.
///
/// # Errors
///
/// Returns the first [`SyntaxError`] encountered.
pub fn lex(src: &str) -> Result<Lexed> {
    Lexer::new(src).lex()
}
