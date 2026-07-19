//! SMT-LIB2 Lexer

#[allow(unused_imports)]
use crate::prelude::*;

/// Token kind
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    /// Left parenthesis
    LParen,
    /// Right parenthesis
    RParen,
    /// Symbol (identifier)
    Symbol(String),
    /// Keyword (prefixed with :)
    Keyword(String),
    /// Numeral (integer)
    Numeral(String),
    /// Decimal (floating point)
    Decimal(String),
    /// Hexadecimal (#x...)
    Hexadecimal(String),
    /// Binary (#b...)
    Binary(String),
    /// String literal
    StringLit(String),
    /// End of file
    Eof,
}

/// A token with position information
#[derive(Debug, Clone)]
pub struct Token {
    /// The kind of token
    pub kind: TokenKind,
    /// Start position in input
    pub start: usize,
    /// End position in input
    pub end: usize,
}

/// A lexical error detected while scanning.
///
/// `Lexer::next_token` keeps returning `Some(Token)` even when it hits one
/// of these conditions (unterminated string/quoted-symbol literals used to
/// be accepted silently, consuming the rest of the input as their content;
/// a bare `#` not followed by `x`/`X`/`b`/`B` used to be accepted silently
/// as a one-character `Symbol`, even though `#` cannot start a valid
/// SMT-LIB symbol) so that callers depending on the existing `Option<Token>`
/// token stream keep working unchanged. Callers that want to reject
/// malformed input should check [`Lexer::errors`] after lexing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    /// Human-readable description of the problem.
    pub message: String,
    /// Byte offset where the problem was detected.
    pub pos: usize,
}

/// Lexer for SMT-LIB2
pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
    /// Lexical errors accumulated so far. See [`LexError`] for why these
    /// don't abort tokenization outright.
    errors: Vec<LexError>,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            pos: 0,
            errors: Vec::new(),
        }
    }

    /// Get the current position
    #[must_use]
    pub fn position(&self) -> usize {
        self.pos
    }

    /// Lexical errors accumulated so far (unterminated string/quoted-symbol
    /// literals, bare `#` tokens, ...). Empty for well-formed input.
    #[must_use]
    pub fn errors(&self) -> &[LexError] {
        &self.errors
    }

    /// Whether any lexical error has been recorded so far.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Peek at the next token without consuming it
    #[must_use]
    pub fn peek(&self) -> Option<Token> {
        let mut lexer = Self {
            input: self.input,
            pos: self.pos,
            errors: Vec::new(),
        };
        lexer.next_token()
    }

    /// Get the next token
    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace_and_comments();

        if self.pos >= self.input.len() {
            return Some(Token {
                kind: TokenKind::Eof,
                start: self.pos,
                end: self.pos,
            });
        }

        let start = self.pos;
        let remaining = &self.input[self.pos..];
        let first = remaining.chars().next()?;

        let kind = match first {
            '(' => {
                self.pos += 1;
                TokenKind::LParen
            }
            ')' => {
                self.pos += 1;
                TokenKind::RParen
            }
            ':' => {
                self.pos += 1;
                let sym = self.read_symbol_chars();
                TokenKind::Keyword(sym)
            }
            '"' => {
                self.pos += 1;
                let s = self.read_string_lit(start);
                TokenKind::StringLit(s)
            }
            '#' => {
                self.pos += 1;
                if let Some(next) = remaining.chars().nth(1) {
                    match next {
                        'x' | 'X' => {
                            self.pos += 1;
                            let hex = self.read_hex_chars();
                            TokenKind::Hexadecimal(hex)
                        }
                        'b' | 'B' => {
                            self.pos += 1;
                            let bin = self.read_binary_chars();
                            TokenKind::Binary(bin)
                        }
                        _ => {
                            // A bare `#` (not `#x...`/`#b...`) cannot start a
                            // valid SMT-LIB symbol; record it instead of
                            // silently minting a one-character `Symbol("#")`
                            // that would otherwise surface downstream as a
                            // confusing "undefined symbol" rather than a
                            // lex-level error.
                            self.errors.push(LexError {
                                message: "bare '#' is not a valid token (expected #x... or #b...)"
                                    .to_string(),
                                pos: start,
                            });
                            TokenKind::Symbol("#".to_string())
                        }
                    }
                } else {
                    self.errors.push(LexError {
                        message: "unexpected end of input after '#' (expected #x... or #b...)"
                            .to_string(),
                        pos: start,
                    });
                    TokenKind::Symbol("#".to_string())
                }
            }
            '0'..='9' => {
                let num = self.read_numeral();
                if self.pos < self.input.len() && self.input[self.pos..].starts_with('.') {
                    self.pos += 1;
                    let frac = self.read_numeral();
                    TokenKind::Decimal(format!("{num}.{frac}"))
                } else {
                    TokenKind::Numeral(num)
                }
            }
            '|' => {
                self.pos += 1;
                let sym = self.read_quoted_symbol(start);
                TokenKind::Symbol(sym)
            }
            _ => {
                let sym = self.read_symbol_chars();
                TokenKind::Symbol(sym)
            }
        };

        Some(Token {
            kind,
            start,
            end: self.pos,
        })
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace
            while self.pos < self.input.len() {
                if let Some(c) = self.input[self.pos..].chars().next() {
                    if c.is_whitespace() {
                        self.pos += c.len_utf8();
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }

            // Skip comments
            if self.pos < self.input.len() && self.input[self.pos..].starts_with(';') {
                while self.pos < self.input.len() {
                    if let Some(c) = self.input[self.pos..].chars().next() {
                        self.pos += c.len_utf8();
                        if c == '\n' {
                            break;
                        }
                    } else {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn read_symbol_chars(&mut self) -> String {
        let start = self.pos;
        while self.pos < self.input.len() {
            if let Some(c) = self.input[self.pos..].chars().next() {
                if c.is_alphanumeric()
                    || matches!(
                        c,
                        '+' | '-'
                            | '/'
                            | '*'
                            | '='
                            | '%'
                            | '?'
                            | '!'
                            | '.'
                            | '$'
                            | '_'
                            | '~'
                            | '&'
                            | '^'
                            | '<'
                            | '>'
                            | '@'
                    )
                {
                    self.pos += c.len_utf8();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        self.input[start..self.pos].to_string()
    }

    /// Read a `|...|`-quoted symbol body, starting just past the opening
    /// `|` (i.e. `self.pos` already advanced past it by the caller).
    ///
    /// The `start_of_token` argument is the position of the opening `|`,
    /// used only to anchor an error if the closing `|` is never found.
    fn read_quoted_symbol(&mut self, start_of_token: usize) -> String {
        let start = self.pos;
        while self.pos < self.input.len() {
            if let Some(c) = self.input[self.pos..].chars().next() {
                self.pos += c.len_utf8();
                if c == '|' {
                    return self.input[start..self.pos - 1].to_string();
                }
            } else {
                break;
            }
        }
        // Ran off the end of input without finding the closing `|`: the
        // rest of the file was silently swallowed as symbol content. Record
        // it rather than pretending this was a well-formed token.
        self.errors.push(LexError {
            message: "unterminated quoted symbol (missing closing '|')".to_string(),
            pos: start_of_token,
        });
        self.input[start..self.pos].to_string()
    }

    /// Read a `"..."`-quoted string literal body, starting just past the
    /// opening `"`. `start_of_token` is the opening `"`'s position, used
    /// only to anchor an error if the closing `"` is never found.
    fn read_string_lit(&mut self, start_of_token: usize) -> String {
        let mut result = String::new();
        let mut terminated = false;
        while self.pos < self.input.len() {
            if let Some(c) = self.input[self.pos..].chars().next() {
                self.pos += c.len_utf8();
                if c == '"' {
                    // Check for escaped quote
                    if self.pos < self.input.len() && self.input[self.pos..].starts_with('"') {
                        result.push('"');
                        self.pos += 1;
                    } else {
                        terminated = true;
                        break;
                    }
                } else {
                    result.push(c);
                }
            } else {
                break;
            }
        }
        if !terminated {
            self.errors.push(LexError {
                message: "unterminated string literal (missing closing '\"')".to_string(),
                pos: start_of_token,
            });
        }
        result
    }

    fn read_numeral(&mut self) -> String {
        let start = self.pos;
        while self.pos < self.input.len() {
            if let Some(c) = self.input[self.pos..].chars().next() {
                if c.is_ascii_digit() {
                    self.pos += 1;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        self.input[start..self.pos].to_string()
    }

    fn read_hex_chars(&mut self) -> String {
        let start = self.pos;
        while self.pos < self.input.len() {
            if let Some(c) = self.input[self.pos..].chars().next() {
                if c.is_ascii_hexdigit() {
                    self.pos += 1;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        self.input[start..self.pos].to_string()
    }

    fn read_binary_chars(&mut self) -> String {
        let start = self.pos;
        while self.pos < self.input.len() {
            if let Some(c) = self.input[self.pos..].chars().next() {
                if c == '0' || c == '1' {
                    self.pos += 1;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        self.input[start..self.pos].to_string()
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.next_token()?;
        if matches!(token.kind, TokenKind::Eof) {
            None
        } else {
            Some(token)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_tokens() {
        let mut lexer = Lexer::new("(+ 1 2)");
        assert!(matches!(
            lexer.next_token().expect("should get lparen token").kind,
            TokenKind::LParen
        ));
        assert!(matches!(
            lexer.next_token().expect("should get plus symbol token").kind,
            TokenKind::Symbol(s) if s == "+"
        ));
        assert!(matches!(
            lexer.next_token().expect("should get numeral 1 token").kind,
            TokenKind::Numeral(n) if n == "1"
        ));
        assert!(matches!(
            lexer.next_token().expect("should get numeral 2 token").kind,
            TokenKind::Numeral(n) if n == "2"
        ));
        assert!(matches!(
            lexer.next_token().expect("should get rparen token").kind,
            TokenKind::RParen
        ));
    }

    #[test]
    fn test_comments() {
        let mut lexer = Lexer::new("; this is a comment\n(test)");
        assert!(matches!(
            lexer
                .next_token()
                .expect("should get lparen token after comment")
                .kind,
            TokenKind::LParen
        ));
        assert!(matches!(
            lexer.next_token().expect("should get test symbol token").kind,
            TokenKind::Symbol(s) if s == "test"
        ));
    }

    #[test]
    fn test_hex_binary() {
        let mut lexer = Lexer::new("#xDEAD #b1010");
        assert!(matches!(
            lexer.next_token().expect("should get hexadecimal token").kind,
            TokenKind::Hexadecimal(h) if h == "DEAD"
        ));
        assert!(matches!(
            lexer.next_token().expect("should get binary token").kind,
            TokenKind::Binary(b) if b == "1010"
        ));
    }

    #[test]
    fn test_string_literal() {
        let mut lexer = Lexer::new("\"hello world\"");
        assert!(matches!(
            lexer.next_token().expect("should get string literal token").kind,
            TokenKind::StringLit(s) if s == "hello world"
        ));
    }

    #[test]
    fn test_keyword() {
        let mut lexer = Lexer::new(":named");
        assert!(matches!(
            lexer.next_token().expect("should get keyword token").kind,
            TokenKind::Keyword(k) if k == "named"
        ));
    }
}
