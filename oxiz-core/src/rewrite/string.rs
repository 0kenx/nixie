//! String Term Rewriter
//!
//! This module provides rewriting rules for string expressions:
//! - String constant folding (concat("a", "b") → "ab")
//! - Length simplification (len("abc") → 3)
//! - Empty string identity (concat("", s) → s)
//! - Substring simplification
//! - Contains/prefix/suffix simplification
//! - String-to-int and int-to-string handling

use super::{RewriteContext, RewriteResult, Rewriter};
use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;

/// String rewriter
#[derive(Debug, Clone)]
pub struct StringRewriter {
    /// Enable aggressive constant folding
    pub aggressive_fold: bool,
    /// Enable substring simplification
    pub simplify_substring: bool,
    /// Cache for string constants
    str_cache: FxHashMap<TermId, String>,
}

impl Default for StringRewriter {
    fn default() -> Self {
        Self::new()
    }
}

impl StringRewriter {
    /// Create a new string rewriter
    pub fn new() -> Self {
        Self {
            aggressive_fold: true,
            simplify_substring: true,
            str_cache: FxHashMap::default(),
        }
    }

    /// Get string constant value
    fn get_str_const(&mut self, term: TermId, manager: &TermManager) -> Option<String> {
        if let Some(cached) = self.str_cache.get(&term) {
            return Some(cached.clone());
        }

        let t = manager.get(term)?;
        if let TermKind::StringLit(s) = &t.kind {
            self.str_cache.insert(term, s.clone());
            return Some(s.clone());
        }
        None
    }

    /// Check if string is empty constant
    fn is_empty_str(&mut self, term: TermId, manager: &TermManager) -> bool {
        self.get_str_const(term, manager)
            .is_some_and(|s| s.is_empty())
    }

    /// Get integer constant
    fn get_int_const(&self, term: TermId, manager: &TermManager) -> Option<i64> {
        let t = manager.get(term)?;
        if let TermKind::IntConst(n) = &t.kind {
            // Try to convert BigInt to i64
            n.try_into().ok()
        } else {
            None
        }
    }

    /// Rewrite string concatenation (binary)
    fn rewrite_concat(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // concat("", s) → s
        if self.is_empty_str(lhs, manager) {
            ctx.stats_mut().record_rule("str_concat_empty_lhs");
            return RewriteResult::Rewritten(rhs);
        }

        // concat(s, "") → s
        if self.is_empty_str(rhs, manager) {
            ctx.stats_mut().record_rule("str_concat_empty_rhs");
            return RewriteResult::Rewritten(lhs);
        }

        // Constant folding: concat("a", "b") → "ab"
        if let (Some(s1), Some(s2)) = (
            self.get_str_const(lhs, manager),
            self.get_str_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("str_concat_const");
            let result = format!("{}{}", s1, s2);
            return RewriteResult::Rewritten(manager.mk_string_lit(&result));
        }

        RewriteResult::Unchanged(manager.mk_str_concat(lhs, rhs))
    }

    /// Rewrite string length
    fn rewrite_length(
        &mut self,
        arg: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // len("abc") → 3. SMT-LIB `str.len` counts codepoints, not UTF-8
        // bytes; `s.len()` (Rust's byte length) is only correct for
        // all-ASCII strings.
        if let Some(s) = self.get_str_const(arg, manager) {
            ctx.stats_mut().record_rule("str_len_const");
            return RewriteResult::Rewritten(manager.mk_int(s.chars().count() as i64));
        }

        // len(concat(s1, s2)) → len(s1) + len(s2)
        if let Some(t) = manager.get(arg).cloned()
            && let TermKind::StrConcat(s1, s2) = &t.kind
        {
            ctx.stats_mut().record_rule("str_len_concat");
            let len1 = manager.mk_str_len(*s1);
            let len2 = manager.mk_str_len(*s2);
            return RewriteResult::Rewritten(manager.mk_add([len1, len2]));
        }

        RewriteResult::Unchanged(manager.mk_str_len(arg))
    }

    /// Rewrite substring/extract
    fn rewrite_substr(
        &mut self,
        str_arg: TermId,
        start: TermId,
        len: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // Constant folding
        if let (Some(s), Some(st), Some(ln)) = (
            self.get_str_const(str_arg, manager),
            self.get_int_const(start, manager),
            self.get_int_const(len, manager),
        ) && st >= 0
            && ln >= 0
        {
            let start_idx = st as usize;
            let length = ln as usize;
            // Bound against the codepoint count, matching the codepoint
            // (not byte) semantics that `.chars().skip()/.take()` below
            // already use — `s.len()` is a byte count and would let a
            // codepoint-out-of-range `start_idx` through for any
            // multi-byte-character string.
            let char_count = s.chars().count();
            if start_idx <= char_count {
                let end_idx = (start_idx + length).min(char_count);
                let result: String = s
                    .chars()
                    .skip(start_idx)
                    .take(end_idx - start_idx)
                    .collect();
                ctx.stats_mut().record_rule("str_substr_const");
                return RewriteResult::Rewritten(manager.mk_string_lit(&result));
            }
        }

        // substr(s, 0, len(s)) → s
        if let Some(0) = self.get_int_const(start, manager)
            && let Some(len_term) = manager.get(len)
            && let TermKind::StrLen(inner) = &len_term.kind
            && *inner == str_arg
        {
            ctx.stats_mut().record_rule("str_substr_identity");
            return RewriteResult::Rewritten(str_arg);
        }

        // substr(s, start, 0) → ""
        if let Some(0) = self.get_int_const(len, manager) {
            ctx.stats_mut().record_rule("str_substr_zero_len");
            return RewriteResult::Rewritten(manager.mk_string_lit(""));
        }

        RewriteResult::Unchanged(manager.mk_str_substr(str_arg, start, len))
    }

    /// Rewrite string contains
    fn rewrite_contains(
        &mut self,
        haystack: TermId,
        needle: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // contains(s, "") → true
        if self.is_empty_str(needle, manager) {
            ctx.stats_mut().record_rule("str_contains_empty");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        // contains(s, s) → true
        if haystack == needle {
            ctx.stats_mut().record_rule("str_contains_self");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        // Constant folding
        if let (Some(h), Some(n)) = (
            self.get_str_const(haystack, manager),
            self.get_str_const(needle, manager),
        ) {
            ctx.stats_mut().record_rule("str_contains_const");
            if h.contains(&n) {
                return RewriteResult::Rewritten(manager.mk_true());
            } else {
                return RewriteResult::Rewritten(manager.mk_false());
            }
        }

        RewriteResult::Unchanged(manager.mk_str_contains(haystack, needle))
    }

    /// Rewrite string prefix check
    fn rewrite_prefixof(
        &mut self,
        prefix: TermId,
        str_arg: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // prefixof("", s) → true
        if self.is_empty_str(prefix, manager) {
            ctx.stats_mut().record_rule("str_prefix_empty");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        // prefixof(s, s) → true
        if prefix == str_arg {
            ctx.stats_mut().record_rule("str_prefix_self");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        // Constant folding
        if let (Some(p), Some(s)) = (
            self.get_str_const(prefix, manager),
            self.get_str_const(str_arg, manager),
        ) {
            ctx.stats_mut().record_rule("str_prefix_const");
            if s.starts_with(&p) {
                return RewriteResult::Rewritten(manager.mk_true());
            } else {
                return RewriteResult::Rewritten(manager.mk_false());
            }
        }

        RewriteResult::Unchanged(manager.mk_str_prefixof(prefix, str_arg))
    }

    /// Rewrite string suffix check
    fn rewrite_suffixof(
        &mut self,
        suffix: TermId,
        str_arg: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // suffixof("", s) → true
        if self.is_empty_str(suffix, manager) {
            ctx.stats_mut().record_rule("str_suffix_empty");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        // suffixof(s, s) → true
        if suffix == str_arg {
            ctx.stats_mut().record_rule("str_suffix_self");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        // Constant folding
        if let (Some(su), Some(s)) = (
            self.get_str_const(suffix, manager),
            self.get_str_const(str_arg, manager),
        ) {
            ctx.stats_mut().record_rule("str_suffix_const");
            if s.ends_with(&su) {
                return RewriteResult::Rewritten(manager.mk_true());
            } else {
                return RewriteResult::Rewritten(manager.mk_false());
            }
        }

        RewriteResult::Unchanged(manager.mk_str_suffixof(suffix, str_arg))
    }

    /// Rewrite string indexof
    fn rewrite_indexof(
        &mut self,
        haystack: TermId,
        needle: TermId,
        start: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // indexof(s, "", i) → i, but only under the SMT-LIB side condition
        // 0 <= i <= len(s); otherwise the result is -1. We must not fire the
        // rewrite unconditionally for symbolic/out-of-range starts.
        if self.is_empty_str(needle, manager) {
            match (
                self.get_int_const(start, manager),
                self.get_str_const(haystack, manager),
            ) {
                (Some(st), Some(h)) => {
                    // Fully constant: decide the side condition directly.
                    // `len(s)` in the SMT-LIB side condition is the
                    // codepoint count, not the Rust (byte) `String::len()`.
                    ctx.stats_mut().record_rule("str_indexof_empty_const");
                    return RewriteResult::Rewritten(
                        if st >= 0 && (st as usize) <= h.chars().count() {
                            start
                        } else {
                            manager.mk_int(-1)
                        },
                    );
                }
                (Some(st), None) if st < 0 => {
                    // Negative start always fails the side condition, regardless
                    // of the (symbolic) haystack.
                    ctx.stats_mut().record_rule("str_indexof_empty_neg");
                    return RewriteResult::Rewritten(manager.mk_int(-1));
                }
                _ => {
                    // Symbolic start and/or haystack length: encode the side
                    // condition explicitly rather than dropping it.
                    let zero = manager.mk_int(0);
                    let len_h = manager.mk_str_len(haystack);
                    let ge_zero = manager.mk_leq(zero, start);
                    let le_len = manager.mk_leq(start, len_h);
                    let cond = manager.mk_and([ge_zero, le_len]);
                    let neg_one = manager.mk_int(-1);
                    ctx.stats_mut().record_rule("str_indexof_empty_ite");
                    return RewriteResult::Rewritten(manager.mk_ite(cond, start, neg_one));
                }
            }
        }

        // Constant folding
        //
        // SMT-LIB `str.indexof` indices are *codepoint* offsets, not byte
        // offsets. `st as usize` naively used as a Rust byte index into
        // `h[start_idx..]` was both wrong for any non-ASCII haystack (a
        // codepoint count generally differs from the byte count) and could
        // outright panic (Rust string slicing requires the index to land on
        // a UTF-8 character boundary, which a codepoint-counted `start_idx`
        // need not do for multi-byte characters). The returned position had
        // the same problem in reverse: `str.find`'s byte offset was reported
        // directly instead of being converted back to a codepoint offset.
        if let (Some(h), Some(n), Some(st)) = (
            self.get_str_const(haystack, manager),
            self.get_str_const(needle, manager),
            self.get_int_const(start, manager),
        ) && st >= 0
        {
            let start_idx = st as usize;
            let h_char_count = h.chars().count();
            if start_idx <= h_char_count {
                ctx.stats_mut().record_rule("str_indexof_const");
                // Byte offset of the `start_idx`-th codepoint (always a
                // valid char boundary); falls back to `h.len()` exactly
                // when `start_idx == h_char_count`.
                let byte_start = h
                    .char_indices()
                    .nth(start_idx)
                    .map(|(b, _)| b)
                    .unwrap_or(h.len());
                if let Some(byte_pos) = h[byte_start..].find(&n) {
                    // Convert the byte offset of the match back to a
                    // codepoint offset relative to the whole haystack.
                    let char_pos = h[..byte_start + byte_pos].chars().count();
                    return RewriteResult::Rewritten(manager.mk_int(char_pos as i64));
                } else {
                    return RewriteResult::Rewritten(manager.mk_int(-1));
                }
            }
        }

        RewriteResult::Unchanged(manager.mk_str_indexof(haystack, needle, start))
    }

    /// Rewrite string replace
    fn rewrite_replace(
        &mut self,
        str_arg: TermId,
        pattern: TermId,
        replacement: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // replace(s, "", r) → concat(r, s)  (replace first occurrence of empty)
        if self.is_empty_str(pattern, manager) {
            ctx.stats_mut().record_rule("str_replace_empty");
            return RewriteResult::Rewritten(manager.mk_str_concat(replacement, str_arg));
        }

        // replace(s, p, p) → s
        if pattern == replacement {
            ctx.stats_mut().record_rule("str_replace_same");
            return RewriteResult::Rewritten(str_arg);
        }

        // Constant folding
        if let (Some(s), Some(p), Some(r)) = (
            self.get_str_const(str_arg, manager),
            self.get_str_const(pattern, manager),
            self.get_str_const(replacement, manager),
        ) {
            ctx.stats_mut().record_rule("str_replace_const");
            let result = s.replacen(&p, &r, 1);
            return RewriteResult::Rewritten(manager.mk_string_lit(&result));
        }

        RewriteResult::Unchanged(manager.mk_str_replace(str_arg, pattern, replacement))
    }

    /// Rewrite string equality
    fn rewrite_str_eq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // s = s → true
        if lhs == rhs {
            ctx.stats_mut().record_rule("str_eq_self");
            return RewriteResult::Rewritten(manager.mk_true());
        }

        // Constant equality
        if let (Some(l), Some(r)) = (
            self.get_str_const(lhs, manager),
            self.get_str_const(rhs, manager),
        ) {
            ctx.stats_mut().record_rule("str_eq_const");
            if l == r {
                return RewriteResult::Rewritten(manager.mk_true());
            } else {
                return RewriteResult::Rewritten(manager.mk_false());
            }
        }

        RewriteResult::Unchanged(manager.mk_eq(lhs, rhs))
    }

    /// Rewrite str.to.int
    fn rewrite_str_to_int(
        &mut self,
        arg: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // str.to.int("123") → 123
        //
        // Per SMT-LIB, `str.to_int s` is the non-negative integer `s`
        // denotes in decimal if `s` consists solely of digit characters
        // (leading zeros allowed), and `-1` otherwise. Two things `s.parse
        // ::<i64>()` got wrong: (1) it accepts a leading `+`/`-` sign,
        // which is not a digit and must make the result `-1` (e.g. `"+5"`
        // is not `5`); (2) it rejects any all-digit string whose value
        // overflows `i64`, folding it to `-1` even though such a string
        // *does* denote a (large but valid) non-negative integer.
        if let Some(s) = self.get_str_const(arg, manager) {
            ctx.stats_mut().record_rule("str_to_int_const");
            if !s.is_empty() && s.chars().all(|c| c.is_ascii_digit()) {
                // All-digit and non-empty: always a valid non-negative
                // integer, arbitrary precision (matches `IntConst`'s
                // `BigInt` representation, so no size limit is imposed
                // here that SMT-LIB itself doesn't impose).
                if let Ok(n) = s.parse::<BigInt>() {
                    return RewriteResult::Rewritten(manager.mk_int(n));
                }
            }
            return RewriteResult::Rewritten(manager.mk_int(-1));
        }

        RewriteResult::Unchanged(manager.mk_str_to_int(arg))
    }

    /// Rewrite int.to.str
    fn rewrite_int_to_str(
        &mut self,
        arg: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        // int.to.str(123) → "123"
        if let Some(n) = self.get_int_const(arg, manager) {
            ctx.stats_mut().record_rule("int_to_str_const");
            if n < 0 {
                return RewriteResult::Rewritten(manager.mk_string_lit(""));
            }
            return RewriteResult::Rewritten(manager.mk_string_lit(&n.to_string()));
        }

        RewriteResult::Unchanged(manager.mk_int_to_str(arg))
    }

    /// Check if a term is a string term
    fn is_str_term(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(t) = manager.get(term) else {
            return false;
        };

        matches!(
            t.kind,
            TermKind::StringLit(_)
                | TermKind::StrConcat(_, _)
                | TermKind::StrSubstr(_, _, _)
                | TermKind::StrReplace(_, _, _)
                | TermKind::IntToStr(_)
        )
    }

    /// Clear the cache
    pub fn clear_cache(&mut self) {
        self.str_cache.clear();
    }
}

impl Rewriter for StringRewriter {
    fn rewrite(
        &mut self,
        term: TermId,
        ctx: &mut RewriteContext,
        manager: &mut TermManager,
    ) -> RewriteResult {
        let Some(t) = manager.get(term).cloned() else {
            return RewriteResult::Unchanged(term);
        };

        match &t.kind {
            TermKind::StrConcat(lhs, rhs) => self.rewrite_concat(*lhs, *rhs, ctx, manager),
            TermKind::StrLen(arg) => self.rewrite_length(*arg, ctx, manager),
            TermKind::StrSubstr(s, start, len) => {
                self.rewrite_substr(*s, *start, *len, ctx, manager)
            }
            TermKind::StrContains(haystack, needle) => {
                self.rewrite_contains(*haystack, *needle, ctx, manager)
            }
            TermKind::StrPrefixOf(prefix, s) => self.rewrite_prefixof(*prefix, *s, ctx, manager),
            TermKind::StrSuffixOf(suffix, s) => self.rewrite_suffixof(*suffix, *s, ctx, manager),
            TermKind::StrIndexOf(haystack, needle, start) => {
                self.rewrite_indexof(*haystack, *needle, *start, ctx, manager)
            }
            TermKind::StrReplace(s, pattern, replacement) => {
                self.rewrite_replace(*s, *pattern, *replacement, ctx, manager)
            }
            TermKind::StrToInt(arg) => self.rewrite_str_to_int(*arg, ctx, manager),
            TermKind::IntToStr(arg) => self.rewrite_int_to_str(*arg, ctx, manager),
            TermKind::Eq(lhs, rhs) => {
                // Check if it's a string equality
                if self.is_str_term(*lhs, manager) || self.is_str_term(*rhs, manager) {
                    self.rewrite_str_eq(*lhs, *rhs, ctx, manager)
                } else {
                    RewriteResult::Unchanged(term)
                }
            }
            _ => RewriteResult::Unchanged(term),
        }
    }

    fn name(&self) -> &str {
        "StringRewriter"
    }

    fn can_handle(&self, term: TermId, manager: &TermManager) -> bool {
        let Some(t) = manager.get(term) else {
            return false;
        };

        matches!(
            t.kind,
            TermKind::StrConcat(_, _)
                | TermKind::StrLen(_)
                | TermKind::StrSubstr(_, _, _)
                | TermKind::StrContains(_, _)
                | TermKind::StrPrefixOf(_, _)
                | TermKind::StrSuffixOf(_, _)
                | TermKind::StrIndexOf(_, _, _)
                | TermKind::StrReplace(_, _, _)
                | TermKind::StrToInt(_)
                | TermKind::IntToStr(_)
                | TermKind::Eq(_, _)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn setup() -> (TermManager, RewriteContext, StringRewriter) {
        (
            TermManager::new(),
            RewriteContext::new(),
            StringRewriter::new(),
        )
    }

    #[test]
    fn test_concat_constants() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s1 = manager.mk_string_lit("hello");
        let s2 = manager.mk_string_lit(" world");
        let concat = manager.mk_str_concat(s1, s2);

        let result = rewriter.rewrite(concat, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        if let TermKind::StringLit(s) = &t.kind {
            assert_eq!(s, "hello world");
        } else {
            panic!("Expected StringLit");
        }
    }

    #[test]
    fn test_concat_empty() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let str_sort = manager.sorts.string_sort();
        let x = manager.mk_var("x", str_sort);
        let empty = manager.mk_string_lit("");
        let concat = manager.mk_str_concat(empty, x);

        let result = rewriter.rewrite(concat, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
        assert_eq!(result.term(), x);
    }

    #[test]
    fn test_len_constant() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s = manager.mk_string_lit("hello");
        let len = manager.mk_str_len(s);

        let result = rewriter.rewrite(len, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(5)));
    }

    #[test]
    fn test_contains_empty() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let str_sort = manager.sorts.string_sort();
        let s = manager.mk_var("s", str_sort);
        let empty = manager.mk_string_lit("");
        let contains = manager.mk_str_contains(s, empty);

        let result = rewriter.rewrite(contains, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::True));
    }

    #[test]
    fn test_contains_constant() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s1 = manager.mk_string_lit("hello world");
        let s2 = manager.mk_string_lit("world");
        let contains = manager.mk_str_contains(s1, s2);

        let result = rewriter.rewrite(contains, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::True));
    }

    #[test]
    fn test_prefix_empty() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let str_sort = manager.sorts.string_sort();
        let s = manager.mk_var("s", str_sort);
        let empty = manager.mk_string_lit("");
        let prefix = manager.mk_str_prefixof(empty, s);

        let result = rewriter.rewrite(prefix, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::True));
    }

    #[test]
    fn test_suffix_constant() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s1 = manager.mk_string_lit("world");
        let s2 = manager.mk_string_lit("hello world");
        let suffix = manager.mk_str_suffixof(s1, s2);

        let result = rewriter.rewrite(suffix, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(t.kind, TermKind::True));
    }

    #[test]
    fn test_indexof_constant() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s1 = manager.mk_string_lit("hello world");
        let s2 = manager.mk_string_lit("world");
        let zero = manager.mk_int(0);
        let indexof = manager.mk_str_indexof(s1, s2, zero);

        let result = rewriter.rewrite(indexof, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(6)));
    }

    #[test]
    fn test_replace_constant() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s = manager.mk_string_lit("hello world");
        let pattern = manager.mk_string_lit("world");
        let replacement = manager.mk_string_lit("rust");
        let replace = manager.mk_str_replace(s, pattern, replacement);

        let result = rewriter.rewrite(replace, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        if let TermKind::StringLit(res) = &t.kind {
            assert_eq!(res, "hello rust");
        } else {
            panic!("Expected StringLit");
        }
    }

    #[test]
    fn test_str_eq_self() {
        let (mut manager, _ctx, _rewriter) = setup();

        // Note: mk_eq already simplifies eq(x, x) -> true at term creation
        let str_sort = manager.sorts.string_sort();
        let s = manager.mk_var("s", str_sort);
        let eq = manager.mk_eq(s, s);

        // Verify the simplification happened at creation time
        let t = manager.get(eq).expect("term should exist");
        assert!(matches!(t.kind, TermKind::True));
    }

    #[test]
    fn test_str_to_int_constant() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s = manager.mk_string_lit("42");
        let to_int = manager.mk_str_to_int(s);

        let result = rewriter.rewrite(to_int, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(42)));
    }

    #[test]
    fn test_int_to_str_constant() {
        let (mut manager, mut ctx, mut rewriter) = setup();

        let n = manager.mk_int(42);
        let to_str = manager.mk_int_to_str(n);

        let result = rewriter.rewrite(to_str, &mut ctx, &mut manager);
        assert!(result.was_rewritten());

        let t = manager.get(result.term()).expect("term should exist");
        if let TermKind::StringLit(s) = &t.kind {
            assert_eq!(s, "42");
        } else {
            panic!("Expected StringLit");
        }
    }

    #[test]
    fn test_indexof_empty_in_range_constant() {
        // indexof("abc", "", 2) -> 2  (0 <= 2 <= len("abc")=3)
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s = manager.mk_string_lit("abc");
        let empty = manager.mk_string_lit("");
        let start = manager.mk_int(2);
        let indexof = manager.mk_str_indexof(s, empty, start);

        let result = rewriter.rewrite(indexof, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(2)));
    }

    #[test]
    fn test_indexof_empty_out_of_range_constant() {
        // Regression: indexof("abc", "", 10) must fold to -1, per SMT-LIB
        // side condition 0 <= i <= len(s), NOT to 10.
        let (mut manager, mut ctx, mut rewriter) = setup();

        let s = manager.mk_string_lit("abc");
        let empty = manager.mk_string_lit("");
        let start = manager.mk_int(10);
        let indexof = manager.mk_str_indexof(s, empty, start);

        let result = rewriter.rewrite(indexof, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
        let t = manager.get(result.term()).expect("term should exist");
        assert!(
            matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(-1)),
            "expected -1 for out-of-range start, got {:?}",
            t.kind
        );
    }

    #[test]
    fn test_indexof_empty_negative_start_constant() {
        // indexof(s, "", -1) must fold to -1 regardless of haystack.
        let (mut manager, mut ctx, mut rewriter) = setup();

        let str_sort = manager.sorts.string_sort();
        let s = manager.mk_var("s", str_sort);
        let empty = manager.mk_string_lit("");
        let start = manager.mk_int(-1);
        let indexof = manager.mk_str_indexof(s, empty, start);

        let result = rewriter.rewrite(indexof, &mut ctx, &mut manager);
        assert!(result.was_rewritten());
        let t = manager.get(result.term()).expect("term should exist");
        assert!(matches!(&t.kind, TermKind::IntConst(n) if n == &BigInt::from(-1)));
    }

    #[test]
    fn test_indexof_empty_symbolic_start_not_unconditional() {
        // Regression: indexof(s, "", i) with symbolic i must NOT
        // unconditionally fold to `i` -- the 0<=i<=len(s) side condition
        // must be encoded (e.g. via ite), never dropped.
        let (mut manager, mut ctx, mut rewriter) = setup();

        let str_sort = manager.sorts.string_sort();
        let int_sort = manager.sorts.int_sort;
        let s = manager.mk_var("s", str_sort);
        let i = manager.mk_var("i", int_sort);
        let empty = manager.mk_string_lit("");
        let indexof = manager.mk_str_indexof(s, empty, i);

        let result = rewriter.rewrite(indexof, &mut ctx, &mut manager);
        let t = manager.get(result.term()).expect("term should exist");
        // Must not be the bare variable `i` (that would drop the side
        // condition entirely, e.g. wrongly folding indexof(s,"",-5) to -5).
        assert_ne!(
            result.term(),
            i,
            "symbolic indexof(s, \"\", i) must not collapse to `i` unconditionally"
        );
        // The side condition must be represented explicitly (an Ite guarding
        // the [0, len(s)] range), not silently dropped.
        assert!(
            matches!(t.kind, TermKind::Ite(_, _, _)),
            "expected an Ite encoding the side condition, got {:?}",
            t.kind
        );
    }
}
