//! Constant evaluation for the SMT-LIB `UnicodeStrings` comparison and
//! character-code operations.
//!
//! Every function here is a pure, directly unit-testable implementation of one
//! operator's semantics on fully known operands.  Keeping them out of
//! `builder.rs` mirrors the sibling `bv_fold` module and gives the term builder, the
//! rewriter, the model evaluator and the ground string decision procedure a
//! *single* definition to route through, so their edge cases cannot drift
//! apart.
//!
//! Reference: Z3's `seq_rewriter.cpp` (`mk_str_lt`, `mk_str_le`,
//! `mk_str_to_code`, `mk_str_from_code`) folds exactly these operations.
//!
//! The subtleties the SMT-LIB Unicode Strings theory pins down, and that are
//! easy to get wrong:
//!
//! * The order is over **code points**, not over UTF-8 bytes.  The two orders
//!   happen to agree (UTF-8 is an order-preserving prefix code), but
//!   [`str_lt`] compares `chars()` explicitly so the property is not silently
//!   relied upon.
//! * [`str_to_code`] is `-1` for *every* string that is not exactly one
//!   character long – including the empty string.
//! * [`str_from_code`] is `""` outside the alphabet `[0, 0x2FFFF]`, not an
//!   error and not a saturating value.

use core::cmp::Ordering;
use num_bigint::BigInt;

#[allow(unused_imports)]
use crate::prelude::*;

/// The largest code point in the SMT-LIB Unicode Strings alphabet
/// (`0x2FFFF` = 196607, Unicode planes 0-2).
///
/// This is the same bound the lexer enforces on `\u{...}` escapes; it is
/// re-stated here because `ast` must not depend on `smtlib`.
pub const MAX_CODE_POINT: u32 = 0x2_FFFF;

/// Compare two strings in the SMT-LIB lexicographic order.
///
/// The theory defines the order as the lexicographic extension of the
/// numerical `<` on code points, so the comparison runs over `chars()` (Unicode
/// scalar values) rather than over bytes.
#[must_use]
pub fn str_cmp(lhs: &str, rhs: &str) -> Ordering {
    lhs.chars().cmp(rhs.chars())
}

/// `str.<` – strict lexicographic order over code points.
#[must_use]
pub fn str_lt(lhs: &str, rhs: &str) -> bool {
    str_cmp(lhs, rhs) == Ordering::Less
}

/// `str.<=` – the reflexive closure of [`str_lt`].
#[must_use]
pub fn str_le(lhs: &str, rhs: &str) -> bool {
    str_cmp(lhs, rhs) != Ordering::Greater
}

/// `str.to_code` – the code point of the only character of `s` when `s` is a
/// singleton string, and `-1` for every other string (including `""` and any
/// string of two or more characters).
#[must_use]
pub fn str_to_code(s: &str) -> BigInt {
    let mut chars = s.chars();
    match (chars.next(), chars.next()) {
        (Some(c), None) => BigInt::from(u32::from(c)),
        _ => BigInt::from(-1),
    }
}

/// The result of folding `str.from_code`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FromCode {
    /// The operand is a representable code point; the singleton string.
    Char(char),
    /// The operand is outside the theory's alphabet `[0, 0x2FFFF]`; per the
    /// theory the result is the empty string.
    Empty,
    /// The operand is a UTF-16 surrogate (`0xD800..=0xDFFF`).
    ///
    /// The theory *does* include these code points in its alphabet, so the
    /// specified result is a one-character string – but OxiZ's strings are
    /// Rust `String`s (sequences of Unicode scalar values), which cannot hold
    /// a lone surrogate, and the lexer already rejects `\u{d800}` in literals
    /// for the same reason.  Folding to `""` would be a *wrong* answer rather
    /// than a missing one (it has length 0 where the theory says 1), so the
    /// caller must leave the term unevaluated and let the solver report an
    /// honest `unknown`.
    Unrepresentable,
}

/// `str.from_code` – the singleton string whose only character is the code
/// point `n` when `n` lies in `[0, 0x2FFFF]`, and `""` otherwise.
///
/// See [`FromCode::Unrepresentable`] for the surrogate range, which this
/// implementation deliberately declines to fold.
#[must_use]
pub fn str_from_code(n: &BigInt) -> FromCode {
    match u32::try_from(n) {
        Ok(code) if code <= MAX_CODE_POINT => match char::from_u32(code) {
            Some(c) => FromCode::Char(c),
            None => FromCode::Unrepresentable,
        },
        // Negative, or beyond the alphabet: the theory specifies `""`.
        _ => FromCode::Empty,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexicographic_order_is_over_code_points() {
        assert!(str_lt("abc", "abd"));
        assert!(!str_lt("abd", "abc"));
        // A proper prefix is strictly smaller.
        assert!(str_lt("ab", "abc"));
        assert!(!str_lt("abc", "ab"));
        // Irreflexive / reflexive.
        assert!(!str_lt("abc", "abc"));
        assert!(str_le("abc", "abc"));
        // The empty string is the minimum.
        assert!(str_lt("", "a"));
        assert!(!str_lt("a", ""));
        assert!(str_le("", ""));
    }

    /// The three UTF-8 length boundaries: a byte-order implementation that
    /// forgot to decode would still pass these, but a code-unit implementation
    /// over UTF-16 would not (`U+FFFF` vs `U+10000`).
    #[test]
    fn order_agrees_across_encoding_length_boundaries() {
        assert!(str_lt("\u{7f}", "\u{80}"));
        assert!(str_lt("\u{7ff}", "\u{800}"));
        assert!(str_lt("\u{ffff}", "\u{10000}"));
        assert!(str_lt("\u{ff}", "\u{100}"));
    }

    #[test]
    fn to_code_is_minus_one_unless_singleton() {
        assert_eq!(str_to_code("A"), BigInt::from(65));
        assert_eq!(str_to_code(""), BigInt::from(-1));
        assert_eq!(str_to_code("AB"), BigInt::from(-1));
        // A single non-BMP character is still a singleton string.
        assert_eq!(str_to_code("\u{2ffff}"), BigInt::from(0x2_FFFF));
    }

    #[test]
    fn from_code_covers_the_alphabet_and_its_boundaries() {
        assert_eq!(str_from_code(&BigInt::from(0)), FromCode::Char('\0'));
        assert_eq!(str_from_code(&BigInt::from(65)), FromCode::Char('A'));
        assert_eq!(
            str_from_code(&BigInt::from(0x2_FFFF)),
            FromCode::Char('\u{2ffff}')
        );
        // One past the alphabet, and negative.
        assert_eq!(str_from_code(&BigInt::from(0x3_0000)), FromCode::Empty);
        assert_eq!(str_from_code(&BigInt::from(-1)), FromCode::Empty);
        // Surrogates are inside the alphabet but not representable.
        assert_eq!(
            str_from_code(&BigInt::from(0xD800)),
            FromCode::Unrepresentable
        );
        assert_eq!(
            str_from_code(&BigInt::from(0xDFFF)),
            FromCode::Unrepresentable
        );
        assert_eq!(
            str_from_code(&BigInt::from(0xE000)),
            FromCode::Char('\u{e000}')
        );
    }
}
