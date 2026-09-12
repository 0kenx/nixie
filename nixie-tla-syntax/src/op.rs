//! The TLA+ operator table: fixity, precedence **ranges**, and associativity.
//!
//! # Why ranges
//!
//! TLA+ does not give an operator a single precedence level. It gives it an
//! interval `(lo, hi)`. Two operators may be written adjacent without
//! parentheses only when their intervals do **not** overlap; when they do
//! overlap the specification is *in error* and must be rejected with a message
//! naming both operators. That is why this crate uses a Pratt parser and not a
//! generated LR table: `%left` / `%nonassoc` assigns one number per token and
//! cannot express an interval, so an LR encoding necessarily approximates and
//! degrades the diagnostic. See `docs/TLA_FRONTEND_DESIGN.md` §1.0.
//!
//! # Closed symbol set
//!
//! TLA+ does **not** admit new operator glyphs. A specification may supply a
//! definition for a symbol drawn from the fixed table below (`x \oplus y == …`)
//! but cannot invent one, so this table is closed and can live in the lexer.
//!
//! # Provenance and verification status
//!
//! The normative source is the operator table in Lamport's *Specifying
//! Systems* (and SANY's own table, which is what real specifications are
//! checked against).
//!
//! **The common operators here are high-confidence; several rare ones are
//! not.** `=>` 1-1, `<=>` 2-2, `/\` and `\/` 3-3, `~` 4-4, the comparison and
//! set-relation family 5-5, `@@` 6-6, `:>` / `<:` 7-7, `\cup` / `\cap` / `\`
//! 8-8, `..` and `DOMAIN` 9-9, `+` 10-10, `-` 11-11, unary minus 12-12, `*`
//! and `/` 13-13, `^` 14-14, `'` 15-15 and `.` 17-17 are the load-bearing
//! entries and are relied on by the tests. The exotic entries (`\wr`, `\sqcap`,
//! `##`, `$$`, `??`, …) are transcribed with lower confidence.
//!
//! The `precedence_table_is_pinned` test pins the current values so that a
//! correction against the normative table shows up as an explicit, reviewable
//! diff rather than a silent behaviour change. Verify the whole table against
//! SANY before the parser differential suite is declared green.

/// How an operator attaches to its operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Fixity {
    /// Written before its single operand, e.g. `~p`, `SUBSET S`.
    Prefix,
    /// Written between its two operands, e.g. `a \cup b`.
    Infix,
    /// Written after its single operand, e.g. `x'`.
    Postfix,
}

/// Fixity, precedence range and associativity of one operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpInfo {
    /// Canonical ASCII spelling of the operator.
    pub canonical: &'static str,
    /// How it attaches to its operands.
    pub fixity: Fixity,
    /// Low end of the precedence interval, inclusive.
    pub lo: u8,
    /// High end of the precedence interval, inclusive.
    pub hi: u8,
    /// Whether `a op b op c` is legal without parentheses.
    ///
    /// Only ever true for a chain of the *same* operator. TLA+ has no
    /// cross-operator associativity: `a = b < c` is an error regardless.
    pub assoc: bool,
}

impl OpInfo {
    /// Binding power the Pratt loop must already be under to accept this
    /// operator as a continuation.
    #[must_use]
    pub const fn left_bp(&self) -> u8 {
        self.lo
    }

    /// Binding power the right operand is parsed at.
    ///
    /// `hi + 1` makes a strictly tighter-binding operator the only thing that
    /// can extend the right operand. Equal-precedence chaining is then decided
    /// by `assoc` in [`ranges_overlap`], not by the binding power,
    /// which is what lets a non-associative operator produce a *precedence
    /// conflict* diagnostic instead of silently re-associating.
    #[must_use]
    pub const fn right_bp(&self) -> u8 {
        // Saturating: `.` sits at 17-17 and the arithmetic must not wrap.
        self.hi.saturating_add(1)
    }
}

/// Whether two precedence intervals overlap.
///
/// Overlap between adjacent operators is a static error in TLA+ unless the two
/// are the same associative operator.
#[must_use]
pub const fn ranges_overlap(a: &OpInfo, b: &OpInfo) -> bool {
    a.lo <= b.hi && b.lo <= a.hi
}

const fn infix(canonical: &'static str, lo: u8, hi: u8, assoc: bool) -> OpInfo {
    OpInfo {
        canonical,
        fixity: Fixity::Infix,
        lo,
        hi,
        assoc,
    }
}

const fn prefix(canonical: &'static str, lo: u8, hi: u8) -> OpInfo {
    OpInfo {
        canonical,
        fixity: Fixity::Prefix,
        lo,
        hi,
        assoc: false,
    }
}

const fn postfix(canonical: &'static str, lo: u8, hi: u8) -> OpInfo {
    OpInfo {
        canonical,
        fixity: Fixity::Postfix,
        lo,
        hi,
        assoc: false,
    }
}

/// Look up the infix meaning of a canonical operator spelling.
///
/// Returns `None` when the symbol has no infix form, which the parser reads as
/// "this token cannot continue an expression" — never as a reason to guess.
#[must_use]
pub fn infix_info(canonical: &str) -> Option<OpInfo> {
    let info = match canonical {
        "=>" => infix("=>", 1, 1, false),
        "<=>" => infix("<=>", 2, 2, false),
        "~>" => infix("~>", 2, 2, false),
        "-+->" => infix("-+->", 2, 2, false),
        "/\\" => infix("/\\", 3, 3, true),
        "\\/" => infix("\\/", 3, 3, true),
        // The 5-5 comparison / relation family. Non-associative throughout:
        // `a = b = c` is a precedence conflict in TLA+, not a chained test.
        "=" => infix("=", 5, 5, false),
        "/=" => infix("/=", 5, 5, false),
        "<" => infix("<", 5, 5, false),
        ">" => infix(">", 5, 5, false),
        "<=" => infix("<=", 5, 5, false),
        ">=" => infix(">=", 5, 5, false),
        "\\in" => infix("\\in", 5, 5, false),
        "\\notin" => infix("\\notin", 5, 5, false),
        "\\subseteq" => infix("\\subseteq", 5, 5, false),
        "\\subset" => infix("\\subset", 5, 5, false),
        "\\supset" => infix("\\supset", 5, 5, false),
        "\\supseteq" => infix("\\supseteq", 5, 5, false),
        "\\sqsubset" => infix("\\sqsubset", 5, 5, false),
        "\\sqsubseteq" => infix("\\sqsubseteq", 5, 5, false),
        "\\sqsupset" => infix("\\sqsupset", 5, 5, false),
        "\\sqsupseteq" => infix("\\sqsupseteq", 5, 5, false),
        "\\prec" => infix("\\prec", 5, 5, false),
        "\\preceq" => infix("\\preceq", 5, 5, false),
        "\\succ" => infix("\\succ", 5, 5, false),
        "\\succeq" => infix("\\succeq", 5, 5, false),
        "\\approx" => infix("\\approx", 5, 5, false),
        "\\asymp" => infix("\\asymp", 5, 5, false),
        "\\cong" => infix("\\cong", 5, 5, false),
        "\\doteq" => infix("\\doteq", 5, 5, false),
        "\\simeq" => infix("\\simeq", 5, 5, false),
        "\\sim" => infix("\\sim", 5, 5, false),
        "\\propto" => infix("\\propto", 5, 5, false),
        "\\ll" => infix("\\ll", 5, 5, false),
        "\\gg" => infix("\\gg", 5, 5, false),
        "|-" => infix("|-", 5, 5, false),
        "|=" => infix("|=", 5, 5, false),
        "-|" => infix("-|", 5, 5, false),
        "=|" => infix("=|", 5, 5, false),
        // Action composition spans nearly the whole table.
        "\\cdot" => infix("\\cdot", 5, 14, true),
        "@@" => infix("@@", 6, 6, true),
        ":=" => infix(":=", 5, 5, false),
        "::=" => infix("::=", 5, 5, false),
        "!!" => infix("!!", 9, 13, true),
        ":>" => infix(":>", 7, 7, false),
        "<:" => infix("<:", 7, 7, false),
        "\\cup" => infix("\\cup", 8, 8, true),
        "\\union" => infix("\\cup", 8, 8, true),
        "\\cap" => infix("\\cap", 8, 8, true),
        "\\intersect" => infix("\\cap", 8, 8, true),
        "\\" => infix("\\", 8, 8, false),
        ".." => infix("..", 9, 9, false),
        "..." => infix("...", 9, 9, false),
        "##" => infix("##", 9, 13, true),
        "$" => infix("$", 9, 13, true),
        "$$" => infix("$$", 9, 13, true),
        "??" => infix("??", 9, 13, true),
        "\\sqcap" => infix("\\sqcap", 9, 13, true),
        "\\sqcup" => infix("\\sqcup", 9, 13, true),
        "\\uplus" => infix("\\uplus", 9, 13, true),
        "\\wr" => infix("\\wr", 9, 14, false),
        "+" => infix("+", 10, 10, true),
        "++" => infix("++", 10, 10, true),
        "\\oplus" => infix("\\oplus", 10, 10, true),
        "%" => infix("%", 10, 11, false),
        "%%" => infix("%%", 10, 11, true),
        "|" => infix("|", 10, 11, true),
        "||" => infix("||", 10, 11, true),
        // `A \X B \X C` is a legal ternary product in TLA+, so `\X` chains.
        // (It denotes a 3-tuple set, not `(A \X B) \X C`; flattening that
        // nesting is the lowering step's job, not the parser's.)
        "\\X" => infix("\\X", 10, 13, true),
        "-" => infix("-", 11, 11, true),
        "--" => infix("--", 11, 11, true),
        "\\ominus" => infix("\\ominus", 11, 11, true),
        "*" => infix("*", 13, 13, true),
        "**" => infix("**", 13, 13, true),
        "/" => infix("/", 13, 13, false),
        "//" => infix("//", 13, 13, false),
        "\\div" => infix("\\div", 13, 13, false),
        "\\o" => infix("\\o", 13, 13, true),
        "\\circ" => infix("\\o", 13, 13, true),
        "\\bullet" => infix("\\bullet", 13, 13, true),
        "\\star" => infix("\\star", 13, 13, true),
        "\\bigcirc" => infix("\\bigcirc", 13, 13, true),
        "\\odot" => infix("\\odot", 13, 13, true),
        "\\oslash" => infix("\\oslash", 13, 13, false),
        "\\otimes" => infix("\\otimes", 13, 13, true),
        "&" => infix("&", 13, 13, true),
        "&&" => infix("&&", 13, 13, true),
        "^" => infix("^", 14, 14, false),
        "^^" => infix("^^", 14, 14, false),
        "." => infix(".", 17, 17, true),
        _ => return None,
    };
    Some(info)
}

/// Look up the prefix meaning of a canonical operator spelling.
#[must_use]
pub fn prefix_info(canonical: &str) -> Option<OpInfo> {
    let info = match canonical {
        "~" => prefix("~", 4, 4),
        "[]" => prefix("[]", 4, 15),
        "<>" => prefix("<>", 4, 15),
        "ENABLED" => prefix("ENABLED", 4, 15),
        "UNCHANGED" => prefix("UNCHANGED", 4, 15),
        "SUBSET" => prefix("SUBSET", 8, 8),
        "UNION" => prefix("UNION", 8, 8),
        "DOMAIN" => prefix("DOMAIN", 9, 9),
        // Unary minus. The lexer never emits `-.`; it emits `-`, and the
        // parser decides by position. The canonical form is kept distinct so
        // the AST does not conflate `-x` with binary subtraction.
        "-." => prefix("-.", 12, 12),
        _ => return None,
    };
    Some(info)
}

/// Look up the postfix meaning of a canonical operator spelling.
#[must_use]
pub fn postfix_info(canonical: &str) -> Option<OpInfo> {
    let info = match canonical {
        "'" => postfix("'", 15, 15),
        "^+" => postfix("^+", 15, 15),
        "^*" => postfix("^*", 15, 15),
        "^#" => postfix("^#", 15, 15),
        _ => return None,
    };
    Some(info)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pins the load-bearing precedence values.
    ///
    /// See the module docs: this test exists so that correcting the table
    /// against SANY is a visible diff, not a silent behaviour change.
    #[test]
    fn precedence_table_is_pinned() {
        let cases: &[(&str, u8, u8)] = &[
            ("=>", 1, 1),
            ("<=>", 2, 2),
            ("/\\", 3, 3),
            ("\\/", 3, 3),
            ("=", 5, 5),
            ("\\in", 5, 5),
            ("@@", 6, 6),
            (":>", 7, 7),
            ("\\cup", 8, 8),
            ("..", 9, 9),
            ("+", 10, 10),
            ("-", 11, 11),
            ("*", 13, 13),
            ("^", 14, 14),
            (".", 17, 17),
        ];
        for &(sym, lo, hi) in cases {
            let info = infix_info(sym).expect("load-bearing operator must be in the table");
            assert_eq!((info.lo, info.hi), (lo, hi), "precedence drift for {sym}");
        }
        assert_eq!(prefix_info("~").map(|i| (i.lo, i.hi)), Some((4, 4)));
        assert_eq!(prefix_info("-.").map(|i| (i.lo, i.hi)), Some((12, 12)));
        assert_eq!(postfix_info("'").map(|i| (i.lo, i.hi)), Some((15, 15)));
    }

    #[test]
    fn equal_precedence_ranges_overlap() {
        let eq = infix_info("=").expect("= is in the table");
        let lt = infix_info("<").expect("< is in the table");
        assert!(ranges_overlap(&eq, &lt), "a = b < c must be a conflict");

        let plus = infix_info("+").expect("+ is in the table");
        let times = infix_info("*").expect("* is in the table");
        assert!(!ranges_overlap(&plus, &times), "a + b * c is well-formed");
    }

    #[test]
    fn right_bp_does_not_wrap_at_the_top_of_the_table() {
        let dot = infix_info(".").expect(". is in the table");
        assert_eq!(dot.right_bp(), 18);
    }
}
