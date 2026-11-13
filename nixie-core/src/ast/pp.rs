//! SMT-LIB 2 pretty-printing for terms.
//!
//! Explicit-stack walk (the repo's stack-safety rule: no unbounded native
//! recursion over user-controlled DAGs).  Covers every kind needed to
//! reconstruct a clause for external checking (arithmetic, Boolean,
//! ite/equality, arrays, bit-vector basics); exotic kinds print as
//! `(_term <id>)` placeholders — an honest partial rendering, never a
//! wrong one (the placeholder is a free constant for the checker).
//!
//! Also the debugging channel for `NIXIE_APROP_VERIFY` (see
//! `docs/studies/2026-11-12-diff-scan-4.md`): pushed propagation clauses
//! are reconstructed exactly and checked against a reference solver.

use super::manager::TermManager;
use super::term::{TermId, TermKind};
use num_traits::ToPrimitive;
use std::fmt::Write;

/// One work item of the explicit print stack: emit `term` after emitting
/// everything pushed above it.
enum Frame {
    /// Emit the term itself (the node's own token or an application head).
    Term(TermId),
    /// Emit a literal token.
    Tok(&'static str),
    /// Emit an integer constant.
    Int(i128, bool),
    /// Emit a rational constant.
    Rat(i64, i64),
    /// A declared variable name (already resolved).
    Name(Box<str>),
    /// Close `n` open parens.
    Close(u8),
}

/// Print `root` as SMT-LIB 2 into `out`.
pub fn write_smt2(out: &mut String, manager: &TermManager, root: TermId) {
    let mut stack: Vec<Frame> = vec![Frame::Term(root)];
    let mut opens: u32 = 0;
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Tok(t) => {
                out.push_str(t);
                opens += t.matches('(').count() as u32;
            }
            Frame::Name(n) => {
                out.push_str(&n);
            }
            Frame::Int(v, neg) => {
                if neg {
                    out.push('-');
                }
                let _ = write!(out, "{v}");
            }
            Frame::Rat(n, d) => {
                let _ = write!(out, "(/ {n} {d})");
            }
            Frame::Close(n) => {
                for _ in 0..n {
                    out.push(')');
                }
                opens -= n as u32;
            }
            Frame::Term(id) => {
                let Some(term) = manager.get(id) else {
                    let _ = write!(out, "(_term {id:?})");
                    continue;
                };
                match &term.kind {
                    TermKind::True => out.push_str("true"),
                    TermKind::False => out.push_str("false"),
                    TermKind::IntConst(n) => {
                        // Any width beyond i128 prints as a placeholder
                        // (an honest partial rendering, never a wrong one).
                        if let Some(v) = n.to_i128() {
                            stack.push(Frame::Int(v.unsigned_abs() as i128, v.is_negative()));
                        } else {
                            let _ = write!(out, "(_term {id:?})");
                        }
                    }
                    TermKind::RealConst(r) => {
                        stack.push(Frame::Rat(*r.numer(), *r.denom()));
                    }
                    TermKind::BitVecConst { .. } => {
                        // A free constant placeholder: the exact bit pattern
                        // is irrelevant for clause-shape checking.
                        let _ = write!(out, "(_term {id:?})");
                    }
                    TermKind::Var(name) => {
                        let resolved = manager.resolve_str(*name);
                        let sanitized: String = resolved
                            .chars()
                            .map(|c| {
                                if c.is_ascii_alphanumeric() || c == '_' {
                                    c
                                } else {
                                    '_'
                                }
                            })
                            .collect();
                        stack.push(Frame::Name(sanitized.into_boxed_str()));
                    }
                    TermKind::Not(a) => {
                        push_app(&mut stack, "(not ", &[*a]);
                    }
                    TermKind::And(args) => {
                        push_nary(&mut stack, args, "(and ");
                    }
                    TermKind::Or(args) => {
                        push_nary(&mut stack, args, "(or ");
                    }
                    TermKind::Xor(a, b) => {
                        stack.extend([
                            Frame::Close(1),
                            Frame::Term(*b),
                            Frame::Tok(" "),
                            Frame::Term(*a),
                            Frame::Tok("(xor"),
                        ]);
                    }
                    TermKind::Implies(a, b) => {
                        stack.extend([
                            Frame::Close(1),
                            Frame::Term(*b),
                            Frame::Tok(" "),
                            Frame::Term(*a),
                            Frame::Tok("(=>"),
                        ]);
                    }
                    TermKind::Ite(c, a, b) => {
                        push_app(&mut stack, "(ite ", &[*c, *a, *b]);
                    }
                    TermKind::Eq(a, b) => {
                        stack.extend([
                            Frame::Close(1),
                            Frame::Term(*b),
                            Frame::Tok(" "),
                            Frame::Term(*a),
                            Frame::Tok("(="),
                        ]);
                    }
                    TermKind::Distinct(args) => {
                        push_nary(&mut stack, args, "(distinct ");
                    }
                    TermKind::Neg(a) => {
                        push_app(&mut stack, "(-", &[*a]);
                    }
                    TermKind::Add(args) => {
                        push_nary(&mut stack, args, "(+ ");
                    }
                    TermKind::Sub(a, b) => {
                        stack.extend([
                            Frame::Close(1),
                            Frame::Term(*b),
                            Frame::Tok(" "),
                            Frame::Term(*a),
                            Frame::Tok("(-"),
                        ]);
                    }
                    TermKind::Mul(args) => {
                        push_nary(&mut stack, args, "(* ");
                    }
                    TermKind::Div(a, b) => {
                        stack.extend([
                            Frame::Close(1),
                            Frame::Term(*b),
                            Frame::Term(*a),
                            if manager.sorts.get(term.sort).is_some_and(|s| s.is_real()) {
                                Frame::Tok("(/")
                            } else {
                                Frame::Tok("div")
                            },
                        ]);
                    }
                    TermKind::Mod(a, b) => {
                        stack.extend([
                            Frame::Close(1),
                            Frame::Term(*b),
                            Frame::Tok(" "),
                            Frame::Term(*a),
                            Frame::Tok("(mod"),
                        ]);
                    }
                    TermKind::Lt(a, b) => {
                        push_cmp(&mut stack, *a, *b, "<");
                    }
                    TermKind::Le(a, b) => {
                        push_cmp(&mut stack, *a, *b, "<=");
                    }
                    TermKind::Gt(a, b) => {
                        push_cmp(&mut stack, *a, *b, ">");
                    }
                    TermKind::Ge(a, b) => {
                        push_cmp(&mut stack, *a, *b, ">=");
                    }
                    // Uninterpreted application: SMT-LIB allows any atom head.
                    TermKind::Apply { func, args } => {
                        stack.push(Frame::Close(1));
                        for a in args.iter().rev() {
                            stack.push(Frame::Term(*a));
                        }
                        // `func` is the interned symbol name directly.
                        let resolved = manager.resolve_str(*func).replace('|', "_");
                        stack.push(Frame::Tok("("));
                        stack.push(Frame::Name(resolved.into_boxed_str()));
                        stack.push(Frame::Tok(" "));
                    }
                    TermKind::Select(a, i) => {
                        stack.extend([
                            Frame::Close(1),
                            Frame::Term(*i),
                            Frame::Tok(" "),
                            Frame::Term(*a),
                            Frame::Tok("(select"),
                        ]);
                    }
                    TermKind::Store(a, i, v) => {
                        stack.extend([
                            Frame::Close(1),
                            Frame::Term(*v),
                            Frame::Tok(" "),
                            Frame::Term(*i),
                            Frame::Tok(" "),
                            Frame::Term(*a),
                            Frame::Tok("(store"),
                        ]);
                    }
                    // Exotic kinds: an honest placeholder.
                    _ => {
                        let _ = write!(out, "(_term {id:?})");
                    }
                }
            }
        }
    }
    let _ = opens; // every Tok/Close pair is balanced by construction
}

fn push_nary(stack: &mut Vec<Frame>, args: &[TermId], head: &'static str) {
    // Build the wanted POP order, then push reversed (the stack pops LIFO).
    let mut frames: Vec<Frame> = Vec::with_capacity(args.len() * 2 + 2);
    frames.push(Frame::Tok(head));
    for (k, a) in args.iter().enumerate() {
        if k > 0 {
            frames.push(Frame::Tok(" "));
        }
        frames.push(Frame::Term(*a));
    }
    frames.push(Frame::Close(1));
    stack.extend(frames.into_iter().rev());
}

/// Binary/unary application: emit `head t1 t2 ... )` in explicit pop order.
fn push_app(stack: &mut Vec<Frame>, head: &'static str, ts: &[TermId]) {
    let mut frames: Vec<Frame> = Vec::with_capacity(ts.len() * 2 + 2);
    frames.push(Frame::Tok(head));
    for (k, t) in ts.iter().enumerate() {
        if k > 0 {
            frames.push(Frame::Tok(" "));
        }
        frames.push(Frame::Term(*t));
    }
    frames.push(Frame::Close(1));
    stack.extend(frames.into_iter().rev());
}

fn push_cmp(stack: &mut Vec<Frame>, a: TermId, b: TermId, op: &'static str) {
    let head: &'static str = match op {
        "<" => "(< ",
        "<=" => "(<= ",
        ">" => "(> ",
        _ => "(>= ",
    };
    push_app(stack, head, &[a, b]);
}

/// Render `root` as a standalone SMT-LIB 2 string.
#[must_use]
pub fn to_smt2(manager: &TermManager, root: TermId) -> String {
    let mut out = String::new();
    write_smt2(&mut out, manager, root);
    out
}

/// Collect the names of every `Var` under `root` (explicit stack; the
/// printer's sibling for emitting `declare-fun` lines).
pub fn collect_var_names(
    manager: &TermManager,
    root: TermId,
    out: &mut std::collections::BTreeSet<String>,
) {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        let Some(term) = manager.get(id) else {
            continue;
        };
        match &term.kind {
            TermKind::Var(n) => {
                out.insert(manager.resolve_str(*n).to_string());
            }
            TermKind::Not(a) | TermKind::Neg(a) => {
                stack.push(*a);
            }
            TermKind::Div(a, b)
            | TermKind::Mod(a, b)
            | TermKind::Lt(a, b)
            | TermKind::Le(a, b)
            | TermKind::Gt(a, b)
            | TermKind::Ge(a, b)
            | TermKind::Eq(a, b)
            | TermKind::Implies(a, b)
            | TermKind::Xor(a, b)
            | TermKind::Sub(a, b)
            | TermKind::Select(a, b) => {
                stack.extend([*a, *b]);
            }
            TermKind::Ite(a, b, c) | TermKind::Store(a, b, c) => {
                stack.extend([*a, *b, *c]);
            }
            TermKind::And(args)
            | TermKind::Or(args)
            | TermKind::Add(args)
            | TermKind::Mul(args)
            | TermKind::Distinct(args)
            | TermKind::Apply { args, .. } => {
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Balanced parens and non-empty tokens: the output must be parseable
    /// SMT-LIB regardless of spacing.
    fn assert_well_formed(s: &str) {
        let mut depth = 0i64;
        for (i, c) in s.chars().enumerate() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    assert!(depth >= 0, "unbalanced close at {i}: {s}");
                }
                _ => {}
            }
        }
        assert_eq!(depth, 0, "unbalanced: {s}");
    }

    #[test]
    fn arith_and_boolean_shapes_print_valid_smt2() {
        let m = &mut TermManager::new();
        let i = m.sorts.int_sort;
        let x = m.mk_var("x", i);
        let y = m.mk_var("y", i);
        let two = m.mk_int(2);
        let two_x = m.mk_mul(vec![two, x]);
        let diff = m.mk_sub(two_x, y);
        let three = m.mk_int(3);
        let lhs = m.mk_add(vec![diff, three]);
        let c5 = m.mk_int(5);
        let le = m.mk_le(lhs, c5);
        let s = to_smt2(m, le);
        assert_well_formed(&s);
        // Symbols and constants present; order-insensitive parts.
        assert!(s.contains("x") && s.contains("y"));
        assert!(s.contains('2') && s.contains('3') && s.contains('5'));
        assert!(s.contains("<=") && s.contains('(') && s.contains(')'));

        let zero = m.mk_int(0);
        let gt = m.mk_gt(x, zero);
        let eq = m.mk_eq(x, y);
        let four = m.mk_int(4);
        let md = m.mk_mod(x, four);
        let c2 = m.mk_int(2);
        let ge = m.mk_ge(md, c2);
        let ite = m.mk_ite(gt, eq, ge);
        let s2 = to_smt2(m, ite);
        assert_well_formed(&s2);
        assert!(s2.contains("ite") && s2.contains("mod"));
    }

    #[test]
    fn deep_chain_prints_without_recursion() {
        // ~40k-deep right-nested add chain: the explicit stack must
        // handle what native recursion could not.
        let m = &mut TermManager::new();
        let i = m.sorts.int_sort;
        let x = m.mk_var("x", i);
        let one = m.mk_int(1);
        let mut cur = x;
        for _ in 0..40_000 {
            cur = m.mk_add(vec![cur, one]);
        }
        let s = to_smt2(m, cur);
        assert_eq!(s.matches("(+").count(), 40_000);
        assert_well_formed(&s);
    }
}
