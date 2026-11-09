//! Constructor equality and datatype ITE lifting with one heap worklist.
//!
//! Constructor injectivity, disjointness and distribution over ITE are exact
//! identities (see Z3's datatype_rewriter::mk_eq_core). A single worklist owns
//! all three rewrites: calling mk_eq recursively from each otherwise iterative
//! helper would still overflow on alternating constructor/ITE nesting.

use super::TermManager;
use crate::ast::{TermId, TermKind};
#[allow(unused_imports)]
use crate::prelude::*;

type Pair = (TermId, TermId);

enum Finish {
    Alias(Pair),
    And(Vec<Pair>),
    Ite(TermId, Pair, Pair),
}

enum Frame {
    Expand(Pair),
    Finish(Pair, Finish),
}

impl TermManager {
    /// Build equality, folding datatype constructors and bounded datatype ITEs.
    /// The rewrite uses a heap stack even for alternating constructor/ITE DAGs.
    pub fn mk_eq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if lhs == rhs {
            return self.true_id;
        }
        // Ordinary equality keeps its allocation-free construction path.
        if !self.eq_needs_worklist(lhs, rhs) {
            return self.mk_eq_basic(lhs, rhs);
        }
        let root = ordered(lhs, rhs);
        let mut values: FxHashMap<Pair, TermId> = FxHashMap::default();
        let mut stack = vec![Frame::Expand(root)];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Expand(pair @ (left, right)) => {
                    if values.contains_key(&pair) {
                        continue;
                    }
                    if left == right {
                        values.insert(pair, self.true_id);
                        continue;
                    }
                    let nodes = self.get(left).zip(self.get(right));
                    let finish = if let Some((l, r)) = nodes {
                        match (&l.kind, &r.kind) {
                            (TermKind::Not(a), TermKind::Not(b)) => {
                                Some(Finish::Alias(ordered(*a, *b)))
                            }
                            (
                                TermKind::DtConstructor {
                                    constructor: a,
                                    args: xs,
                                },
                                TermKind::DtConstructor {
                                    constructor: b,
                                    args: ys,
                                },
                            ) if l.sort == r.sort => {
                                if a != b {
                                    values.insert(pair, self.false_id);
                                    continue;
                                }
                                if xs.len() == ys.len() {
                                    match self.constructor_eq_fields(pair) {
                                        Ok(fields) => Some(Finish::And(fields)),
                                        Err(()) => {
                                            values.insert(pair, self.false_id);
                                            continue;
                                        }
                                    }
                                } else {
                                    None
                                }
                            }
                            _ => self.eq_ite_children(left, right),
                        }
                    } else {
                        None
                    };
                    if let Some(finish) = finish {
                        let children = match &finish {
                            Finish::Alias(child) => vec![*child],
                            Finish::And(children) => children.clone(),
                            Finish::Ite(_, a, b) => vec![*a, *b],
                        };
                        stack.push(Frame::Finish(pair, finish));
                        stack.extend(children.into_iter().rev().map(Frame::Expand));
                    } else {
                        let result = self.mk_eq_basic(left, right);
                        values.insert(pair, result);
                    }
                }
                Frame::Finish(pair, finish) => {
                    // Every child is scheduled before this continuation; a missing
                    // value is an internal error, never a fabricated Boolean.
                    let value = |p: Pair| match values.get(&p) {
                        Some(&term) => term,
                        None => panic!("missing equality rewrite child {p:?}"),
                    };
                    let result = match finish {
                        Finish::Alias(child) => value(child),
                        Finish::And(children) => {
                            let terms: Vec<_> = children.into_iter().map(value).collect();
                            self.mk_eq_conjunction(terms)
                        }
                        Finish::Ite(condition, then_pair, else_pair) => {
                            let then_value = value(then_pair);
                            let else_value = value(else_pair);
                            self.mk_ite(condition, then_value, else_value)
                        }
                    };
                    values.insert(pair, result);
                }
            }
        }
        match values.get(&root) {
            Some(&term) => term,
            None => panic!("missing equality rewrite root"),
        }
    }

    // Flatten a whole constructor component once, before rebuilding any
    // conjunction. Per-level flattening would be quadratic on a list and
    // exponential on a shared binary constructor DAG. ITEs are leaf pairs
    // here; the outer heap worklist resumes their rewrites without recursion.
    fn constructor_eq_fields(&self, root: Pair) -> Result<Vec<Pair>, ()> {
        let mut pending = vec![root];
        let mut seen = FxHashSet::default();
        let mut fields = Vec::new();
        while let Some(pair @ (left, right)) = pending.pop() {
            if left == right || !seen.insert(pair) {
                continue;
            }
            if let Some((l, r)) = self.get(left).zip(self.get(right))
                && l.sort == r.sort
                && let (
                    TermKind::DtConstructor {
                        constructor: a,
                        args: xs,
                    },
                    TermKind::DtConstructor {
                        constructor: b,
                        args: ys,
                    },
                ) = (&l.kind, &r.kind)
            {
                if a != b {
                    return Err(());
                }
                if xs.len() == ys.len() {
                    pending.extend(xs.iter().zip(ys).rev().map(|(&x, &y)| ordered(x, y)));
                    continue;
                }
            }
            fields.push(pair);
        }
        Ok(fields)
    }

    fn mk_eq_conjunction(&mut self, terms: Vec<TermId>) -> TermId {
        let mut pending: Vec<_> = terms.into_iter().rev().collect();
        let mut seen = FxHashSet::default();
        let mut leaves = Vec::new();
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            match self.get(term).map(|node| &node.kind) {
                Some(TermKind::True) => {}
                Some(TermKind::False) => return self.false_id,
                Some(TermKind::And(children)) => pending.extend(children.iter().rev().copied()),
                Some(_) => leaves.push(term),
                None => panic!("invalid equality conjunct: {term:?}"),
            }
        }
        self.mk_and(leaves)
    }

    fn eq_needs_worklist(&self, lhs: TermId, rhs: TermId) -> bool {
        let Some((left, right)) = self.get(lhs).zip(self.get(rhs)) else {
            return false;
        };
        matches!(
            (&left.kind, &right.kind),
            (TermKind::Not(_), TermKind::Not(_))
        ) || (left.sort == right.sort
            && ((matches!(left.kind, TermKind::DtConstructor { .. })
                && matches!(right.kind, TermKind::DtConstructor { .. }))
                || (self.sorts.is_datatype(left.sort)
                    && (matches!(left.kind, TermKind::Ite(..))
                        || matches!(right.kind, TermKind::Ite(..))))))
    }

    fn eq_ite_children(&self, lhs: TermId, rhs: TermId) -> Option<Finish> {
        if self.get(lhs)?.sort != self.get(rhs)?.sort {
            return None;
        }
        let left = self.dt_ite_nodes(lhs).map(|nodes| nodes.len());
        let right = self.dt_ite_nodes(rhs).map(|nodes| nodes.len());
        if let (Some(a), Some(b)) = (left, right)
            && a.saturating_mul(b) > super::MAX_ITE_LIFT_NODES
        {
            return None;
        }
        if left.is_some() {
            let TermKind::Ite(c, a, b) = self.get(lhs)?.kind else {
                return None;
            };
            Some(Finish::Ite(c, ordered(a, rhs), ordered(b, rhs)))
        } else if right.is_some() {
            let TermKind::Ite(c, a, b) = self.get(rhs)?.kind else {
                return None;
            };
            Some(Finish::Ite(c, ordered(lhs, a), ordered(lhs, b)))
        } else {
            None
        }
    }

    /// Build the canonical equality atom without datatype decomposition.
    /// Congruence lemmas need this to merge constructor applications: a folded
    /// conclusion would merely repeat the field equalities in their premise.
    pub fn mk_eq_atom(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        if lhs == rhs {
            return self.true_id;
        }
        let (lhs, rhs) = ordered(lhs, rhs);
        self.intern(TermKind::Eq(lhs, rhs), self.sorts.bool_sort)
    }
}

fn ordered(lhs: TermId, rhs: TermId) -> Pair {
    if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sort::{DataTypeConstructor, SortId};
    use smallvec::smallvec;

    fn list(m: &mut TermManager) -> SortId {
        let sort = m.sorts.mk_datatype_sort("L");
        let nil = DataTypeConstructor {
            name: m.intern_str("nil"),
            selectors: smallvec![],
        };
        let cons = DataTypeConstructor {
            name: m.intern_str("cons"),
            selectors: smallvec![
                (m.intern_str("hd"), m.sorts.int_sort),
                (m.intern_str("tl"), sort)
            ],
        };
        m.declare_datatype("L", vec![nil, cons]);
        sort
    }

    #[test]
    fn constructor_equality_folds_deeply_but_raw_atoms_stay_atoms() {
        let mut m = TermManager::new();
        let sort = list(&mut m);
        let zero = m.mk_int(0);
        let nil = m.mk_dt_constructor("nil", [], sort);
        let mut left = nil;
        let mut right = m.mk_dt_constructor("cons", [zero, nil], sort);
        for _ in 0..20_000 {
            left = m.mk_dt_constructor("cons", [zero, left], sort);
            right = m.mk_dt_constructor("cons", [zero, right], sort);
        }
        let raw = m.mk_eq_atom(left, right);
        assert!(matches!(
            m.get(raw).map(|n| &n.kind),
            Some(TermKind::Eq(..))
        ));
        assert_eq!(m.mk_eq(left, right), m.false_id);
        assert_eq!(m.mk_eq_atom(right, left), raw);
    }

    #[test]
    fn alternating_constructors_and_ites_use_one_worklist() {
        let mut m = TermManager::new();
        let sort = list(&mut m);
        let zero = m.mk_int(0);
        let nil = m.mk_dt_constructor("nil", [], sort);
        let (mut left, mut right) = (m.mk_var("x", sort), m.mk_var("y", sort));
        for i in 0..2_000 {
            let cond = m.mk_var(&format!("p{i}"), m.sorts.bool_sort);
            let a = m.mk_dt_constructor("cons", [zero, left], sort);
            let b = m.mk_dt_constructor("cons", [zero, right], sort);
            left = m.mk_ite(cond, a, nil);
            right = m.mk_ite(cond, b, nil);
        }
        let result = m.mk_eq(left, right);
        assert_ne!(result, m.true_id);
        assert_ne!(result, m.false_id);
        assert_eq!(result, m.mk_eq(right, left));
    }

    #[test]
    fn raw_nested_negations_do_not_recurse() {
        let mut m = TermManager::new();
        let bool_sort = m.sorts.bool_sort;
        let x = m.mk_var("x", bool_sort);
        let y = m.mk_var("y", bool_sort);
        let (mut left, mut right) = (x, y);
        for _ in 0..20_000 {
            left = m.intern_term(TermKind::Not(left), bool_sort);
            right = m.intern_term(TermKind::Not(right), bool_sort);
        }
        assert_eq!(m.mk_eq(left, right), m.mk_eq(x, y));
    }

    #[test]
    fn accessor_pass_has_no_round_limit() {
        let mut m = TermManager::new();
        let sort = list(&mut m);
        let zero = m.mk_int(0);
        let one = m.mk_int(1);
        let nil = m.mk_dt_constructor("nil", [], sort);
        let mut value = m.mk_dt_constructor("cons", [one, nil], sort);
        for _ in 0..1_000 {
            value = m.mk_dt_constructor("cons", [zero, value], sort);
        }
        let tail = m.intern_str("tl");
        let head = m.intern_str("hd");
        for _ in 0..1_000 {
            value = m.intern_term(
                TermKind::DtSelector {
                    selector: tail,
                    arg: value,
                },
                sort,
            );
        }
        let result = m.intern_term(
            TermKind::DtSelector {
                selector: head,
                arg: value,
            },
            m.sorts.int_sort,
        );
        assert_eq!(m.fold_constructor_accessors(result), one);
    }
    #[test]
    fn accessor_pass_preserves_binders_and_patterns() {
        use crate::ast::term::MatchCase;
        let mut m = TermManager::new();
        let sort = list(&mut m);
        let int = m.sorts.int_sort;
        let bool_sort = m.sorts.bool_sort;
        let x = m.mk_var("x", int);
        let name = m.intern_str("x");
        let nil = m.mk_dt_constructor("nil", [], sort);
        let cons = m.mk_dt_constructor("cons", [x, nil], sort);
        let hd = m.intern_str("hd");
        let raw = m.intern_term(
            TermKind::DtSelector {
                selector: hd,
                arg: cons,
            },
            int,
        );
        let body = m.mk_eq_atom(raw, x);
        for exists in [false, true] {
            let vars = smallvec![(name, int)];
            let patterns = smallvec![smallvec![raw]];
            let kind = if exists {
                TermKind::Exists {
                    vars,
                    body,
                    patterns,
                }
            } else {
                TermKind::Forall {
                    vars,
                    body,
                    patterns,
                }
            };
            let root = m.intern_term(kind, bool_sort);
            let folded = m.fold_constructor_accessors(root);
            match &m.get(folded).expect("folded binder").kind {
                TermKind::Forall {
                    vars,
                    body,
                    patterns,
                }
                | TermKind::Exists {
                    vars,
                    body,
                    patterns,
                } => {
                    assert_eq!(vars.as_slice(), &[(name, int)]);
                    assert_eq!(*body, m.true_id);
                    assert_eq!(patterns[0].as_slice(), &[raw]);
                }
                other => panic!("lost binder: {other:?}"),
            }
        }
        let one = m.mk_int(1);
        let root = m.intern_term(
            TermKind::Let {
                bindings: smallvec![(name, one)],
                body: raw,
            },
            int,
        );
        let folded = m.fold_constructor_accessors(root);
        assert!(
            matches!(&m.get(folded).expect("folded let").kind, TermKind::Let { body, .. } if *body == x)
        );
        let root = m.intern_term(
            TermKind::Match {
                scrutinee: nil,
                cases: smallvec![MatchCase {
                    constructor: None,
                    bindings: smallvec![name],
                    body: raw,
                }],
            },
            int,
        );
        let folded = m.fold_constructor_accessors(root);
        assert!(
            matches!(&m.get(folded).expect("folded match").kind, TermKind::Match { cases, .. } if cases[0].body == x && cases[0].bindings[0] == name)
        );
    }
    #[test]
    fn shared_constructor_dags_do_not_expand_exponentially() {
        let mut m = TermManager::new();
        let sort = m.sorts.mk_datatype_sort("Tree");
        let branch = DataTypeConstructor {
            name: m.intern_str("branch"),
            selectors: smallvec![(m.intern_str("left"), sort), (m.intern_str("right"), sort)],
        };
        let leaf = DataTypeConstructor {
            name: m.intern_str("leaf"),
            selectors: smallvec![],
        };
        m.declare_datatype("Tree", vec![branch, leaf]);
        let x = m.mk_var("x", sort);
        let y = m.mk_var("y", sort);
        let (mut left, mut right) = (x, y);
        for _ in 0..1_000 {
            left = m.mk_dt_constructor("branch", [left, left], sort);
            right = m.mk_dt_constructor("branch", [right, right], sort);
        }
        assert_eq!(m.mk_eq(left, right), m.mk_eq(x, y));
    }
}
