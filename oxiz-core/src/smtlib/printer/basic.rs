//\! Basic SMT-LIB2 printer

use crate::ast::{TermId, TermKind, TermManager};
#[allow(unused_imports)]
use crate::prelude::*;
use crate::sort::{SortId, SortKind};
use core::cell::Cell;
use core::fmt::Write;

/// Maximum `write_term` recursion depth before printing degrades to a
/// truncation marker instead of continuing to descend, mirroring the
/// depth caps applied elsewhere in the crate (e.g.
/// `ast::manager::query::MAX_QUERY_RECURSION_DEPTH`,
/// `simplification`'s `SIMPLIFICATION_MAX_DEPTH`). Terms built directly
/// via the `mk_*` builder API bypass those parser-/rewriter-side caps, so
/// without a bound here, printing a pathologically deep (but validly
/// constructed) term could overflow the native call stack.
const MAX_PRINT_DEPTH: u32 = 2000;

/// Printer for SMT-LIB2 format
pub struct Printer<'a> {
    pub(super) manager: &'a TermManager,
    /// Current `write_term` recursion depth on this printer. `Cell`
    /// because `write_term` takes `&self` (it is called recursively and
    /// re-entrantly from many call sites, all of which stay unchanged —
    /// see `write_term`'s depth-guard wrapper below).
    depth: Cell<u32>,
}

/// RAII guard that decrements a [`Printer`]'s `depth` counter on drop
/// (including on early return), keeping the depth bookkeeping accurate
/// regardless of which path through `write_term_at_depth` returns.
struct PrintDepthGuard<'p, 'a>(&'p Printer<'a>);

impl Drop for PrintDepthGuard<'_, '_> {
    fn drop(&mut self) {
        self.0.depth.set(self.0.depth.get().saturating_sub(1));
    }
}

impl<'a> Printer<'a> {
    /// Create a new printer
    #[must_use]
    pub fn new(manager: &'a TermManager) -> Self {
        Self {
            manager,
            depth: Cell::new(0),
        }
    }

    /// Print a term to a string
    #[must_use]
    pub fn print_term(&self, term_id: TermId) -> String {
        let mut buf = String::new();
        self.write_term(&mut buf, term_id);
        buf
    }

    /// Write a term to a writer.
    ///
    /// Bounds recursion at `MAX_PRINT_DEPTH`: past that depth, printing
    /// degrades gracefully to a truncation marker (`...`) instead of
    /// recursing further and risking a native stack overflow. See
    /// `write_term_at_depth` for the actual
    /// per-`TermKind` printing logic — every recursive call within it
    /// still goes back through this wrapper, so the depth check applies
    /// at every level without needing to touch each call site.
    pub fn write_term(&self, w: &mut impl Write, term_id: TermId) {
        let depth = self.depth.get();
        if depth >= MAX_PRINT_DEPTH {
            let _ = write!(w, "...");
            return;
        }
        self.depth.set(depth + 1);
        let _guard = PrintDepthGuard(self);
        self.write_term_at_depth(w, term_id);
    }

    /// Per-`TermKind` printing logic for [`write_term`](Self::write_term);
    /// see that method's doc comment for the depth-guarding this relies
    /// on.
    fn write_term_at_depth(&self, w: &mut impl Write, term_id: TermId) {
        let Some(term) = self.manager.get(term_id) else {
            let _ = write!(w, "?{}", term_id.0);
            return;
        };

        match &term.kind {
            TermKind::True => {
                let _ = write!(w, "true");
            }
            TermKind::False => {
                let _ = write!(w, "false");
            }
            TermKind::IntConst(n) => {
                let _ = write!(w, "{n}");
            }
            TermKind::RealConst(r) => {
                let _ = write!(w, "{r}");
            }
            TermKind::BitVecConst { value, width } => {
                let _ = write!(
                    w,
                    "#x{:0>width$}",
                    value,
                    width = (*width as usize).div_ceil(4)
                );
            }
            TermKind::StringLit(s) => {
                let _ = write!(w, "\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""));
            }
            TermKind::Var(spur) => {
                let name = self.manager.resolve_str(*spur);
                let _ = write!(w, "{name}");
            }
            TermKind::Not(arg) => {
                let _ = write!(w, "(not ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::And(args) => {
                let _ = write!(w, "(and");
                for arg in args {
                    let _ = write!(w, " ");
                    self.write_term(w, *arg);
                }
                let _ = write!(w, ")");
            }
            TermKind::Or(args) => {
                let _ = write!(w, "(or");
                for arg in args {
                    let _ = write!(w, " ");
                    self.write_term(w, *arg);
                }
                let _ = write!(w, ")");
            }
            TermKind::Xor(lhs, rhs) => {
                let _ = write!(w, "(xor ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Implies(lhs, rhs) => {
                let _ = write!(w, "(=> ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Ite(cond, then_b, else_b) => {
                let _ = write!(w, "(ite ");
                self.write_term(w, *cond);
                let _ = write!(w, " ");
                self.write_term(w, *then_b);
                let _ = write!(w, " ");
                self.write_term(w, *else_b);
                let _ = write!(w, ")");
            }
            TermKind::Eq(lhs, rhs) => {
                let _ = write!(w, "(= ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Distinct(args) => {
                let _ = write!(w, "(distinct");
                for arg in args {
                    let _ = write!(w, " ");
                    self.write_term(w, *arg);
                }
                let _ = write!(w, ")");
            }
            TermKind::Neg(arg) => {
                let _ = write!(w, "(- ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::StrLen(arg) => {
                let _ = write!(w, "(str.len ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::StrToInt(arg) => {
                let _ = write!(w, "(str.to_int ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::IntToStr(arg) => {
                let _ = write!(w, "(int.to_str ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::Add(args) => {
                let _ = write!(w, "(+");
                for arg in args {
                    let _ = write!(w, " ");
                    self.write_term(w, *arg);
                }
                let _ = write!(w, ")");
            }
            TermKind::Sub(lhs, rhs) => {
                let _ = write!(w, "(- ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Mul(args) => {
                let _ = write!(w, "(*");
                for arg in args {
                    let _ = write!(w, " ");
                    self.write_term(w, *arg);
                }
                let _ = write!(w, ")");
            }
            TermKind::Div(lhs, rhs) => {
                let _ = write!(w, "(div ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Mod(lhs, rhs) => {
                let _ = write!(w, "(mod ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Lt(lhs, rhs) => {
                let _ = write!(w, "(< ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Le(lhs, rhs) => {
                let _ = write!(w, "(<= ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Gt(lhs, rhs) => {
                let _ = write!(w, "(> ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Ge(lhs, rhs) => {
                let _ = write!(w, "(>= ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::Select(array, index) => {
                let _ = write!(w, "(select ");
                self.write_term(w, *array);
                let _ = write!(w, " ");
                self.write_term(w, *index);
                let _ = write!(w, ")");
            }
            TermKind::StrConcat(s1, s2) => {
                let _ = write!(w, "(str.++ ");
                self.write_term(w, *s1);
                let _ = write!(w, " ");
                self.write_term(w, *s2);
                let _ = write!(w, ")");
            }
            TermKind::StrAt(s, i) => {
                let _ = write!(w, "(str.at ");
                self.write_term(w, *s);
                let _ = write!(w, " ");
                self.write_term(w, *i);
                let _ = write!(w, ")");
            }
            TermKind::StrContains(s, sub) => {
                let _ = write!(w, "(str.contains ");
                self.write_term(w, *s);
                let _ = write!(w, " ");
                self.write_term(w, *sub);
                let _ = write!(w, ")");
            }
            TermKind::StrPrefixOf(prefix, s) => {
                let _ = write!(w, "(str.prefixof ");
                self.write_term(w, *prefix);
                let _ = write!(w, " ");
                self.write_term(w, *s);
                let _ = write!(w, ")");
            }
            TermKind::StrSuffixOf(suffix, s) => {
                let _ = write!(w, "(str.suffixof ");
                self.write_term(w, *suffix);
                let _ = write!(w, " ");
                self.write_term(w, *s);
                let _ = write!(w, ")");
            }
            TermKind::StrInRe(s, re) => {
                let _ = write!(w, "(str.in_re ");
                self.write_term(w, *s);
                let _ = write!(w, " ");
                self.write_term(w, *re);
                let _ = write!(w, ")");
            }
            TermKind::StrSubstr(s, i, n) => {
                let _ = write!(w, "(str.substr ");
                self.write_term(w, *s);
                let _ = write!(w, " ");
                self.write_term(w, *i);
                let _ = write!(w, " ");
                self.write_term(w, *n);
                let _ = write!(w, ")");
            }
            TermKind::StrIndexOf(s, sub, offset) => {
                let _ = write!(w, "(str.indexof ");
                self.write_term(w, *s);
                let _ = write!(w, " ");
                self.write_term(w, *sub);
                let _ = write!(w, " ");
                self.write_term(w, *offset);
                let _ = write!(w, ")");
            }
            TermKind::StrReplace(s, from, to) => {
                let _ = write!(w, "(str.replace ");
                self.write_term(w, *s);
                let _ = write!(w, " ");
                self.write_term(w, *from);
                let _ = write!(w, " ");
                self.write_term(w, *to);
                let _ = write!(w, ")");
            }
            TermKind::StrReplaceAll(s, from, to) => {
                let _ = write!(w, "(str.replace_all ");
                self.write_term(w, *s);
                let _ = write!(w, " ");
                self.write_term(w, *from);
                let _ = write!(w, " ");
                self.write_term(w, *to);
                let _ = write!(w, ")");
            }
            TermKind::Store(array, index, value) => {
                let _ = write!(w, "(store ");
                self.write_term(w, *array);
                let _ = write!(w, " ");
                self.write_term(w, *index);
                let _ = write!(w, " ");
                self.write_term(w, *value);
                let _ = write!(w, ")");
            }
            TermKind::Apply { func, args } => {
                let name = self.manager.resolve_str(*func);
                let _ = write!(w, "({name}");
                for arg in args {
                    let _ = write!(w, " ");
                    self.write_term(w, *arg);
                }
                let _ = write!(w, ")");
            }
            TermKind::Forall {
                vars,
                body,
                patterns,
            } => {
                let _ = write!(w, "(forall (");
                for (i, (name, sort)) in vars.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(w, " ");
                    }
                    let name_str = self.manager.resolve_str(*name);
                    let _ = write!(w, "({name_str} ");
                    self.write_sort(w, *sort);
                    let _ = write!(w, ")");
                }
                let _ = write!(w, ") ");
                if patterns.is_empty() {
                    self.write_term(w, *body);
                } else {
                    let _ = write!(w, "(! ");
                    self.write_term(w, *body);
                    for pattern in patterns {
                        let _ = write!(w, " :pattern (");
                        for (i, term) in pattern.iter().enumerate() {
                            if i > 0 {
                                let _ = write!(w, " ");
                            }
                            self.write_term(w, *term);
                        }
                        let _ = write!(w, ")");
                    }
                    let _ = write!(w, ")");
                }
                let _ = write!(w, ")");
            }
            TermKind::Exists {
                vars,
                body,
                patterns,
            } => {
                let _ = write!(w, "(exists (");
                for (i, (name, sort)) in vars.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(w, " ");
                    }
                    let name_str = self.manager.resolve_str(*name);
                    let _ = write!(w, "({name_str} ");
                    self.write_sort(w, *sort);
                    let _ = write!(w, ")");
                }
                let _ = write!(w, ") ");
                if patterns.is_empty() {
                    self.write_term(w, *body);
                } else {
                    let _ = write!(w, "(! ");
                    self.write_term(w, *body);
                    for pattern in patterns {
                        let _ = write!(w, " :pattern (");
                        for (i, term) in pattern.iter().enumerate() {
                            if i > 0 {
                                let _ = write!(w, " ");
                            }
                            self.write_term(w, *term);
                        }
                        let _ = write!(w, ")");
                    }
                    let _ = write!(w, ")");
                }
                let _ = write!(w, ")");
            }
            TermKind::Let { bindings, body } => {
                let _ = write!(w, "(let (");
                for (i, (name, term)) in bindings.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(w, " ");
                    }
                    let name_str = self.manager.resolve_str(*name);
                    let _ = write!(w, "({name_str} ");
                    self.write_term(w, *term);
                    let _ = write!(w, ")");
                }
                let _ = write!(w, ") ");
                self.write_term(w, *body);
                let _ = write!(w, ")");
            }
            // BitVector operations
            TermKind::BvConcat(lhs, rhs) => {
                let _ = write!(w, "(concat ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvExtract { high, low, arg } => {
                let _ = write!(w, "((_ extract {high} {low}) ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::BvNot(arg) => {
                let _ = write!(w, "(bvnot ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::BvAnd(lhs, rhs) => {
                let _ = write!(w, "(bvand ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvOr(lhs, rhs) => {
                let _ = write!(w, "(bvor ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvXor(lhs, rhs) => {
                let _ = write!(w, "(bvxor ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvAdd(lhs, rhs) => {
                let _ = write!(w, "(bvadd ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvSub(lhs, rhs) => {
                let _ = write!(w, "(bvsub ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvMul(lhs, rhs) => {
                let _ = write!(w, "(bvmul ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvUdiv(lhs, rhs) => {
                let _ = write!(w, "(bvudiv ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvSdiv(lhs, rhs) => {
                let _ = write!(w, "(bvsdiv ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvUrem(lhs, rhs) => {
                let _ = write!(w, "(bvurem ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvSrem(lhs, rhs) => {
                let _ = write!(w, "(bvsrem ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvShl(lhs, rhs) => {
                let _ = write!(w, "(bvshl ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvLshr(lhs, rhs) => {
                let _ = write!(w, "(bvlshr ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvAshr(lhs, rhs) => {
                let _ = write!(w, "(bvashr ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvUlt(lhs, rhs) => {
                let _ = write!(w, "(bvult ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvUle(lhs, rhs) => {
                let _ = write!(w, "(bvule ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvSlt(lhs, rhs) => {
                let _ = write!(w, "(bvslt ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::BvSle(lhs, rhs) => {
                let _ = write!(w, "(bvsle ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            // Floating-point literals and constants
            TermKind::FpLit { sign, exp, sig, .. } => {
                let _ = write!(
                    w,
                    "(fp #b{} #b{} #b{})",
                    if *sign { "1" } else { "0" },
                    exp,
                    sig
                );
            }
            TermKind::FpPlusInfinity { eb, sb } => {
                let _ = write!(w, "(_ +oo {eb} {sb})");
            }
            TermKind::FpMinusInfinity { eb, sb } => {
                let _ = write!(w, "(_ -oo {eb} {sb})");
            }
            TermKind::FpPlusZero { eb, sb } => {
                let _ = write!(w, "(_ +zero {eb} {sb})");
            }
            TermKind::FpMinusZero { eb, sb } => {
                let _ = write!(w, "(_ -zero {eb} {sb})");
            }
            TermKind::FpNaN { eb, sb } => {
                let _ = write!(w, "(_ NaN {eb} {sb})");
            }
            // Unary FP operations
            TermKind::FpAbs(arg) => {
                let _ = write!(w, "(fp.abs ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpNeg(arg) => {
                let _ = write!(w, "(fp.neg ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpSqrt(rm, arg) => {
                let _ = write!(w, "(fp.sqrt {rm:?} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpRoundToIntegral(rm, arg) => {
                let _ = write!(w, "(fp.roundToIntegral {rm:?} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            // Binary FP operations
            TermKind::FpAdd(rm, lhs, rhs) => {
                let _ = write!(w, "(fp.add {rm:?} ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpSub(rm, lhs, rhs) => {
                let _ = write!(w, "(fp.sub {rm:?} ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpMul(rm, lhs, rhs) => {
                let _ = write!(w, "(fp.mul {rm:?} ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpDiv(rm, lhs, rhs) => {
                let _ = write!(w, "(fp.div {rm:?} ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpRem(lhs, rhs) => {
                let _ = write!(w, "(fp.rem ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpMin(lhs, rhs) => {
                let _ = write!(w, "(fp.min ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpMax(lhs, rhs) => {
                let _ = write!(w, "(fp.max ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpLeq(lhs, rhs) => {
                let _ = write!(w, "(fp.leq ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpLt(lhs, rhs) => {
                let _ = write!(w, "(fp.lt ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpGeq(lhs, rhs) => {
                let _ = write!(w, "(fp.geq ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpGt(lhs, rhs) => {
                let _ = write!(w, "(fp.gt ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            TermKind::FpEq(lhs, rhs) => {
                let _ = write!(w, "(fp.eq ");
                self.write_term(w, *lhs);
                let _ = write!(w, " ");
                self.write_term(w, *rhs);
                let _ = write!(w, ")");
            }
            // Ternary FP operations
            TermKind::FpFma(rm, a, b, c) => {
                let _ = write!(w, "(fp.fma {rm:?} ");
                self.write_term(w, *a);
                let _ = write!(w, " ");
                self.write_term(w, *b);
                let _ = write!(w, " ");
                self.write_term(w, *c);
                let _ = write!(w, ")");
            }
            // FP predicates
            TermKind::FpIsNormal(arg) => {
                let _ = write!(w, "(fp.isNormal ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpIsSubnormal(arg) => {
                let _ = write!(w, "(fp.isSubnormal ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpIsZero(arg) => {
                let _ = write!(w, "(fp.isZero ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpIsInfinite(arg) => {
                let _ = write!(w, "(fp.isInfinite ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpIsNaN(arg) => {
                let _ = write!(w, "(fp.isNaN ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpIsNegative(arg) => {
                let _ = write!(w, "(fp.isNegative ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpIsPositive(arg) => {
                let _ = write!(w, "(fp.isPositive ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            // FP conversions
            TermKind::FpToFp { rm, arg, eb, sb } => {
                let _ = write!(w, "((_ to_fp {eb} {sb}) {rm:?} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpToSBV { rm, arg, width } => {
                let _ = write!(w, "((_ fp.to_sbv {width}) {rm:?} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpToUBV { rm, arg, width } => {
                let _ = write!(w, "((_ fp.to_ubv {width}) {rm:?} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::FpToReal(arg) => {
                let _ = write!(w, "(fp.to_real ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::RealToFp { rm, arg, eb, sb } => {
                let _ = write!(w, "((_ to_fp {eb} {sb}) {rm:?} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::SBVToFp { rm, arg, eb, sb } => {
                let _ = write!(w, "((_ to_fp {eb} {sb}) {rm:?} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::UBVToFp { rm, arg, eb, sb } => {
                let _ = write!(w, "((_ to_fp_unsigned {eb} {sb}) {rm:?} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }

            // Algebraic datatypes
            TermKind::DtConstructor { constructor, args } => {
                let name = self.manager.resolve_str(*constructor);
                let _ = write!(w, "({name}");
                for arg in args {
                    let _ = write!(w, " ");
                    self.write_term(w, *arg);
                }
                let _ = write!(w, ")");
            }
            TermKind::DtTester { constructor, arg } => {
                let name = self.manager.resolve_str(*constructor);
                let _ = write!(w, "(is-{name} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }
            TermKind::DtSelector { selector, arg } => {
                let name = self.manager.resolve_str(*selector);
                let _ = write!(w, "({name} ");
                self.write_term(w, *arg);
                let _ = write!(w, ")");
            }

            // Match expressions
            TermKind::Match { scrutinee, cases } => {
                let _ = write!(w, "(match ");
                self.write_term(w, *scrutinee);
                let _ = write!(w, " (");
                for (i, case) in cases.iter().enumerate() {
                    if i > 0 {
                        let _ = write!(w, " ");
                    }
                    let _ = write!(w, "(");
                    if let Some(constructor) = case.constructor {
                        let _ = write!(w, "(");
                        let name = self.manager.resolve_str(constructor);
                        let _ = write!(w, "{name}");
                        for binding in &case.bindings {
                            let binding_name = self.manager.resolve_str(*binding);
                            let _ = write!(w, " {binding_name}");
                        }
                        let _ = write!(w, ")");
                    } else {
                        // Wildcard pattern
                        let _ = write!(w, "_");
                    }
                    let _ = write!(w, " ");
                    self.write_term(w, case.body);
                    let _ = write!(w, ")");
                }
                let _ = write!(w, "))");
            }
        }
    }

    /// Write a sort to a writer
    pub fn write_sort(&self, w: &mut impl Write, sort_id: SortId) {
        let Some(sort) = self.manager.sorts.get(sort_id) else {
            let _ = write!(w, "?Sort{}", sort_id.0);
            return;
        };

        match &sort.kind {
            SortKind::Bool => {
                let _ = write!(w, "Bool");
            }
            SortKind::Int => {
                let _ = write!(w, "Int");
            }
            SortKind::Real => {
                let _ = write!(w, "Real");
            }
            SortKind::BitVec(width) => {
                let _ = write!(w, "(_ BitVec {width})");
            }
            SortKind::String => {
                let _ = write!(w, "String");
            }
            SortKind::FloatingPoint { eb, sb } => {
                let _ = write!(w, "(_ FloatingPoint {eb} {sb})");
            }
            SortKind::Array { domain, range } => {
                let _ = write!(w, "(Array ");
                self.write_sort(w, *domain);
                let _ = write!(w, " ");
                self.write_sort(w, *range);
                let _ = write!(w, ")");
            }
            SortKind::Uninterpreted(spur) => {
                let name = self.manager.resolve_str(*spur);
                let _ = write!(w, "{name}");
            }
            SortKind::Parameter(spur) => {
                let name = self.manager.resolve_str(*spur);
                let _ = write!(w, "{name}");
            }
            SortKind::Parametric { name, args } => {
                let name_str = self.manager.resolve_str(*name);
                let _ = write!(w, "({name_str}");
                for arg in args {
                    let _ = write!(w, " ");
                    self.write_sort(w, *arg);
                }
                let _ = write!(w, ")");
            }
            SortKind::Datatype(spur) => {
                let name = self.manager.resolve_str(*spur);
                let _ = write!(w, "{name}");
            }
        }
    }

    /// Print a sort to a string
    #[must_use]
    pub fn print_sort(&self, sort_id: SortId) -> String {
        let mut buf = String::new();
        self.write_sort(&mut buf, sort_id);
        buf
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Regression tests for: "Recursive term printers lack an explicit
    // depth cap" — `write_term` must degrade gracefully (truncate) past
    // `MAX_PRINT_DEPTH` instead of recursing without bound.

    #[test]
    fn write_term_truncates_past_max_print_depth_instead_of_overflowing_stack() {
        let mut manager = TermManager::new();
        let bool_sort = manager.sorts.bool_sort;

        // Build a chain of nested `not`s deeper than MAX_PRINT_DEPTH via
        // the crate-internal `intern` (bypassing `mk_not`'s double
        // negation simplification, which would otherwise collapse this
        // chain instead of building it) — exactly the "term constructed
        // directly via the builder API, not routed through a depth-capped
        // parser/rewriter" case MAX_PRINT_DEPTH exists to guard.
        let mut term = manager.mk_true();
        for _ in 0..(MAX_PRINT_DEPTH as usize + 500) {
            term = manager.intern(TermKind::Not(term), bool_sort);
        }

        let printer = Printer::new(&manager);
        let printed = printer.print_term(term);
        assert!(
            printed.contains("..."),
            "expected a truncation marker once MAX_PRINT_DEPTH is exceeded, got a string of len {}",
            printed.len()
        );
    }

    #[test]
    fn write_term_prints_normal_depth_terms_without_truncation() {
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let y = manager.mk_var("y", manager.sorts.bool_sort);
        let and = manager.mk_and([x, y]);

        let printer = Printer::new(&manager);
        let printed = printer.print_term(and);
        assert_eq!(printed, "(and x y)");
        assert!(!printed.contains("..."));
    }

    #[test]
    fn write_term_depth_counter_resets_between_independent_calls() {
        // The depth counter must not leak across independent top-level
        // `write_term` calls on the same `Printer` — verified by printing
        // a normal term successfully more than once in a row.
        let mut manager = TermManager::new();
        let x = manager.mk_var("x", manager.sorts.bool_sort);
        let not_x = manager.mk_not(x);

        let printer = Printer::new(&manager);
        assert_eq!(printer.print_term(not_x), "(not x)");
        assert_eq!(printer.print_term(not_x), "(not x)");
    }
}
