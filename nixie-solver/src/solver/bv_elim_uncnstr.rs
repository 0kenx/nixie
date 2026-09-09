//! Elimination of unconstrained variables — the Z3 `elim-uncnstr` port.
//!
//! A variable that occurs in **exactly one** place of a formula is
//! *unconstrained* at that site: whenever the surrounding application is
//! surjective (or a bijection) in that operand, the whole sub-term can be
//! replaced by a fresh variable, because for every value the rest of the
//! formula could want there is an operand value producing it
//! (Brummayer/Biere, MEMICS'09; Z3
//! `src/tactic/core/elim_uncnstr_tactic.cpp`, operator rules in
//! `process_basic_app` / `process_bv_app`).
//!
//! * `x + t -> u`, `x := u - t`            (addition is a bijection in `x`)
//! * `x udiv y -> u`, `x := u`, `y := 1`   (surjective: pick `y = 1`)
//! * `x ++ y -> u`, per-arg extracts       (concat is a bijection pair)
//! * `x <= t -> u or t = MAX`              (two values of `x` satisfy the
//! * `t <= x -> u or t = MIN`               bound; the rest map to `t±1`)
//! * `~x -> u`, `x := ~u`; `and`/`or`/`eq`/`ite` analogues
//!
//! The rewrite is **satisfiability-preserving, not equivalence-preserving**:
//! `F[x]` with `x` occurring nowhere else is equisatisfiable with `F[u]`,
//! because the recorded definition `x := def(u)` is chosen so that `def`
//! reproduces the projection — a model of either side extends to a model of
//! the other (eliminated variable from the fresh one; fresh variable from
//! the original operand value).  Two consequences shape the integration:
//!
//! * an `Unsat` of the rewrite transfers to the original (a model of the
//!   original would extend to one of the rewrite), and
//! * a `Sat` verdict must *reconstruct* values for the eliminated variables
//!   from the fresh ones (`defs` below, defaulted where the model has no
//!   opinion: an unconstrained variable's value is chosen, not searched)
//!   and survive certification against the original assertions — the eager
//!   QF_BV dispatch's [`crate::solver::Solver::model_certifies_assertions`]
//!   gate is exactly that check.
//!
//! This is why the pass runs *only* inside
//! [`crate::solver::dispatch_pure_bv`] where both halves exist.  It must
//! never be asserted "alongside" the originals like the
//! equivalence-preserving preprocessor: a non-implied rewrite would refute
//! satisfiable goals — precisely the ring-elimination lesson of
//! `docs/studies/2026-09-07-bv-dispatch-unification.md`.
//!
//! # Deviations from Z3 (each with its surjectivity argument)
//!
//! Z3's rule set omits `bvand`, `bvxor`, `bvsub` and `bvneg` because its
//! simplifier first normalizes `bvand` to `bvnot (bvor (bvnot …))` and
//! subtraction to addition; nixie's preprocessor deliberately keeps the
//! input's own shapes, so the rules are stated directly:
//!
//! * `bvand x y -> u`, `x := u`, `y := ~0` (`u & ~0 = u`),
//! * `bvxor x y -> u`, `x := u`, `y := 0`  (`u ^ 0 = u`),
//! * `bvsub x t -> u`, `x := u + t`        (`(u + t) - t = u`),
//! * `bvneg x -> u`, `x := -u`             (negation is a bijection).
//!
//! # Algorithm (Z3 shape)
//!
//! Fixpoint of rounds: each round counts variable occurrences over the
//! current assertion set, then rewrites every assertion bottom-up (memoized
//! on the hash-consed DAG) replacing eliminable applications by fresh
//! variables.  A fresh variable of one round occurs exactly once
//! afterwards, so later rounds can eliminate it in turn (`bvnot v -> u1`,
//! `bvor u1 u2 u3 -> u4`, …) until nothing changes.  Definitions are
//! emitted newest-round-first, the topological order of the def DAG (a
//! round's defs reference only vars defined in the same or a later round,
//! or vars the model assigns), so model reconstruction resolves in one
//! forward pass.

use nixie_core::ast::traversal::get_children;
use nixie_core::ast::{TermId, TermKind, TermManager};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};
use rustc_hash::{FxHashMap, FxHashSet};

/// Hard bound on fixpoint rounds.  Every rewriting round strictly removes
/// at least one variable occurrence, so the loop terminates well before
/// this; the cap only guards against a logic error looping forever.
const MAX_ROUNDS: usize = 1000;

/// A takeover (or wide-mul-goal elimination) additionally requires the
/// rewrite to shrink the goal to at most ~75 % of its original distinct-
/// subterm count (`new * 4 <= old * 3`).  Two populations separate cleanly
/// at this threshold: `brummayerbiere4/unconstrained*` collapses to a
/// handful of free atoms (~5 %), while goals where the pass mostly renames
/// existing structure (`tacas07/BBB-32`: 138 eliminations, essentially the
/// same DAG) stay near 1.0 — and those are exactly the goals whose
/// *existing* route (unified general path or eager CEGAR dispatch) already
/// solved them; diverting them measured `sat` verdicts regressing to
/// `unknown`.
pub(super) const TAKEOVER_SHRINK_NUM: usize = 3;
pub(super) const TAKEOVER_SHRINK_DEN: usize = 4;

/// Distinct sub-term count of an assertion set (iterative DAG walk).
pub(super) fn dag_nodes(assertions: &[TermId], manager: &TermManager) -> usize {
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(tid) = stack.pop() {
        if !visited.insert(tid) {
            continue;
        }
        let Some(data) = manager.get(tid) else {
            continue;
        };
        stack.extend(get_children(&data.kind));
    }
    visited.len()
}

/// Result of one [`elim_uncnstr_assertions`] run.
pub(super) struct ElimUncnstrOutcome {
    /// The rewritten assertion list (equisatisfiable with the input).
    pub assertions: Vec<TermId>,
    /// Eliminated-variable definitions `(var, defining term)` in
    /// dependency (topological) order: a definition's body only mentions
    /// variables defined later in the list or assigned by the model.
    pub defs: Vec<(TermId, TermId)>,
    /// Number of fresh variables introduced (Z3's `elim-unconstrained`
    /// statistic); zero means the pass found nothing.
    pub fresh_vars: usize,
}

/// Run the unconstrained-variable elimination fixpoint on `assertions`.
pub(super) fn elim_uncnstr_assertions(
    assertions: &[TermId],
    manager: &mut TermManager,
) -> ElimUncnstrOutcome {
    let mut current: Vec<TermId> = assertions.to_vec();
    // Newest-round-first def list (see the module doc for the order proof).
    let mut defs: Vec<(TermId, TermId)> = Vec::new();
    let mut fresh_vars = 0usize;
    let mut name_counter = 0usize;

    for _round in 0..MAX_ROUNDS {
        let uncnstr = collect_unconstrained(&current, manager);
        if uncnstr.is_empty() {
            break;
        }
        let mut round = Round {
            uncnstr: &uncnstr,
            fresh_for_app: FxHashMap::default(),
            defs: Vec::new(),
            fresh_vars: &mut fresh_vars,
            name_counter: &mut name_counter,
        };
        let mut next: Vec<TermId> = Vec::with_capacity(current.len());
        let mut changed = false;
        for &assertion in &current {
            let rewritten = round.rewrite_assertion(assertion, manager);
            changed |= rewritten != assertion;
            next.push(rewritten);
        }
        // Latest round's defs first (dependency order; module doc).
        let round_defs = std::mem::take(&mut round.defs);
        defs.splice(..0, round_defs);
        if !changed {
            break;
        }
        current = next;
    }

    ElimUncnstrOutcome {
        assertions: current,
        defs,
        fresh_vars,
    }
}

/// Variables occurring exactly once across the assertion set (Z3
/// `collect_occs`): iterative DAG walk with a visited set, occurrence
/// counter per variable.  (Z3 counts *uninterpreted constants* only; in
/// nixie every declared or fresh constant is a `Var`.)
fn collect_unconstrained(assertions: &[TermId], manager: &TermManager) -> FxHashSet<TermId> {
    // Per-pop counting for variables: hash-consing makes every occurrence
    // site of the same variable the same `TermId`, and the DAG walk pushes
    // it once per parent — so each pop is one occurrence (Z3 `collect_occs`
    // marks `more_than_once` on exactly the revisit).  Compound terms are
    // walked once; their occurrence count is irrelevant to the rules.
    let mut occurrences: FxHashMap<TermId, u32> = FxHashMap::default();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(tid) = stack.pop() {
        let is_var = manager
            .get(tid)
            .is_some_and(|data| matches!(data.kind, TermKind::Var(_)));
        if is_var {
            *occurrences.entry(tid).or_insert(0) += 1;
            continue; // variables are leaves
        }
        if !visited.insert(tid) {
            continue;
        }
        let Some(data) = manager.get(tid) else {
            continue;
        };
        stack.extend(get_children(&data.kind));
    }
    occurrences
        .into_iter()
        .filter(|(_, count)| *count == 1)
        .map(|(var, _)| var)
        .collect()
}

/// State of one fixpoint round.
struct Round<'a> {
    uncnstr: &'a FxHashSet<TermId>,
    /// Per-application fresh-variable cache (Z3 `m_cache`): applications
    /// that rebuild to the same term share one fresh variable (and one
    /// definition).
    fresh_for_app: FxHashMap<TermId, TermId>,
    /// Definitions created this round, in creation order.
    defs: Vec<(TermId, TermId)>,
    fresh_vars: &'a mut usize,
    name_counter: &'a mut usize,
}

impl Round<'_> {
    /// Whether `t` is an unconstrained variable of this round with a sort
    /// the rules know how to diagonalize (Bool or bit-vector).
    fn uncnstr(&self, t: TermId, manager: &TermManager) -> bool {
        if !self.uncnstr.contains(&t) {
            return false;
        }
        let Some(data) = manager.get(t) else {
            return false;
        };
        if !matches!(data.kind, TermKind::Var(_)) {
            return false;
        }
        manager
            .sorts
            .get(data.sort)
            .is_some_and(|s| s.is_bool() || s.is_bitvec())
    }

    /// Create a fresh variable of `sort`.
    fn mk_fresh(&mut self, sort: nixie_core::sort::SortId, manager: &mut TermManager) -> TermId {
        let name = format!("__nixie!uncnstr!{}", *self.name_counter);
        *self.name_counter += 1;
        *self.fresh_vars += 1;
        manager.mk_var(&name, sort)
    }

    /// Fresh variable standing for the application `app` (memoized).
    /// Returns `(var, is_new)`.
    fn mk_fresh_for_app(
        &mut self,
        app: TermId,
        sort: nixie_core::sort::SortId,
        manager: &mut TermManager,
    ) -> (TermId, bool) {
        if let Some(&v) = self.fresh_for_app.get(&app) {
            return (v, false);
        }
        let v = self.mk_fresh(sort, manager);
        self.fresh_for_app.insert(app, v);
        if std::env::var("NIXIE_ELIM_UNCNSTR_TRACE").is_ok() {
            let kind = manager
                .get(app)
                .map(|td| format!("{:?}", td.kind))
                .unwrap_or_else(|| "?".into());
            eprintln!("[elim-uncnstr]   rule fired on {app:?}: {kind}");
        }
        (v, true)
    }

    fn add_def(&mut self, var: TermId, def: TermId) {
        self.defs.push((var, def));
    }

    /// One assertion's bottom-up rewrite: iterative post-order over the
    /// hash-consed DAG, memoized per round (shared subterms rewrite once).
    fn rewrite_assertion(&mut self, root: TermId, manager: &mut TermManager) -> TermId {
        let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
        enum Step {
            Enter(TermId),
            Exit(TermId),
        }
        let mut stack = vec![Step::Enter(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(tid) => {
                    if memo.contains_key(&tid) {
                        continue;
                    }
                    let Some(data) = manager.get(tid) else {
                        memo.insert(tid, tid);
                        continue;
                    };
                    let children = get_children(&data.kind);
                    stack.push(Step::Exit(tid));
                    for &child in children.iter().rev() {
                        if !memo.contains_key(&child) {
                            stack.push(Step::Enter(child));
                        }
                    }
                }
                Step::Exit(tid) => {
                    let rewritten = self.rewrite_node(tid, &memo, manager);
                    memo.insert(tid, rewritten);
                }
            }
        }
        memo.get(&root).copied().unwrap_or(root)
    }

    /// Rewrite one node whose children are already rewritten: rebuild the
    /// node through the constant-folding builders, then try the
    /// unconstrained rules on the rebuilt shape (Z3's `reduce_app` sees
    /// the rewritten children as well).
    fn rewrite_node(
        &mut self,
        term: TermId,
        memo: &FxHashMap<TermId, TermId>,
        manager: &mut TermManager,
    ) -> TermId {
        let Some(data) = manager.get(term).cloned() else {
            return term;
        };
        let kid = |id: &TermId| memo.get(id).copied().unwrap_or(*id);

        // Rebuild with rewritten children (the builders fold constants).
        let rebuilt = match data.kind.clone() {
            TermKind::Not(a) => manager.mk_not(kid(&a)),
            TermKind::And(ref args) => manager.mk_and(args.iter().map(kid)),
            TermKind::Or(ref args) => manager.mk_or(args.iter().map(kid)),
            TermKind::Xor(a, b) => manager.mk_xor(kid(&a), kid(&b)),
            TermKind::Implies(a, b) => manager.mk_implies(kid(&a), kid(&b)),
            TermKind::Ite(c, t, e) => manager.mk_ite(kid(&c), kid(&t), kid(&e)),
            TermKind::Eq(a, b) => manager.mk_eq(kid(&a), kid(&b)),
            TermKind::Distinct(ref args) => manager.mk_distinct(args.iter().map(kid)),
            TermKind::BvAdd(a, b) => manager.mk_bv_add(kid(&a), kid(&b)),
            TermKind::BvSub(a, b) => manager.mk_bv_sub(kid(&a), kid(&b)),
            TermKind::BvMul(a, b) => manager.mk_bv_mul(kid(&a), kid(&b)),
            TermKind::BvNot(a) => manager.mk_bv_not(kid(&a)),
            TermKind::BvAnd(a, b) => manager.mk_bv_and(kid(&a), kid(&b)),
            TermKind::BvOr(a, b) => manager.mk_bv_or(kid(&a), kid(&b)),
            TermKind::BvXor(a, b) => manager.mk_bv_xor(kid(&a), kid(&b)),
            TermKind::BvUdiv(a, b) => manager.mk_bv_udiv(kid(&a), kid(&b)),
            TermKind::BvSdiv(a, b) => manager.mk_bv_sdiv(kid(&a), kid(&b)),
            TermKind::BvUrem(a, b) => manager.mk_bv_urem(kid(&a), kid(&b)),
            TermKind::BvSrem(a, b) => manager.mk_bv_srem(kid(&a), kid(&b)),
            TermKind::BvShl(a, b) => manager.mk_bv_shl(kid(&a), kid(&b)),
            TermKind::BvLshr(a, b) => manager.mk_bv_lshr(kid(&a), kid(&b)),
            TermKind::BvAshr(a, b) => manager.mk_bv_ashr(kid(&a), kid(&b)),
            TermKind::BvUle(a, b) => manager.mk_bv_ule(kid(&a), kid(&b)),
            TermKind::BvSle(a, b) => manager.mk_bv_sle(kid(&a), kid(&b)),
            TermKind::BvUlt(a, b) => manager.mk_bv_ult(kid(&a), kid(&b)),
            TermKind::BvSlt(a, b) => manager.mk_bv_slt(kid(&a), kid(&b)),
            TermKind::BvConcat(a, b) => manager.mk_bv_concat(kid(&a), kid(&b)),
            TermKind::BvExtract { high, low, arg } => manager.mk_bv_extract(high, low, kid(&arg)),
            // Leaves, quantifiers, foreign theories: keep the node (for
            // compound kinds without a builder entry above, keeping the
            // original node drops the children's rewrites — always sound:
            // the kept children are the original ones, hash-consed intact,
            // and a dropped rewrite only forfeits an elimination).
            _ => term,
        };

        match self.try_elim(rebuilt, manager) {
            Some(result) => result,
            None => rebuilt,
        }
    }

    /// The operator rules (Z3 `process_basic_app` + `process_bv_app`).
    /// `app` is the rebuilt application; returns the replacement term.
    fn try_elim(&mut self, app: TermId, manager: &mut TermManager) -> Option<TermId> {
        let data = manager.get(app).cloned()?;
        let sort = data.sort;
        let is_bool_sort = manager.sorts.get(sort).is_some_and(|s| s.is_bool());
        let width = manager.sorts.get(sort).and_then(|s| s.bitvec_width());
        match data.kind {
            // ================= Bool core (Z3 process_basic_app) ==========
            TermKind::Ite(c, t, e) => {
                let t_sort = manager.get(t).map(|td| td.sort)?;
                if self.uncnstr(t, manager) && self.uncnstr(e, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, t_sort, manager);
                    if is_new {
                        self.add_def(t, u);
                        self.add_def(e, u);
                    }
                    return Some(u);
                }
                if self.uncnstr(c, manager) && self.uncnstr(t, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, t_sort, manager);
                    if is_new {
                        let tru = manager.mk_true();
                        self.add_def(c, tru);
                        self.add_def(t, u);
                    }
                    return Some(u);
                }
                if self.uncnstr(c, manager) && self.uncnstr(e, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, t_sort, manager);
                    if is_new {
                        let fls = manager.mk_false();
                        self.add_def(c, fls);
                        self.add_def(e, u);
                    }
                    return Some(u);
                }
                None
            }
            TermKind::Not(a) => {
                if self.uncnstr(a, manager) && is_bool_sort {
                    let (u, is_new) = self.mk_fresh_for_app(app, manager.sorts.bool_sort, manager);
                    if is_new {
                        let def = manager.mk_not(u);
                        self.add_def(a, def);
                    }
                    return Some(u);
                }
                None
            }
            TermKind::And(ref args) => {
                if !args.is_empty() && args.iter().all(|&a| self.uncnstr(a, manager)) {
                    let (u, is_new) = self.mk_fresh_for_app(app, manager.sorts.bool_sort, manager);
                    if is_new {
                        let tru = manager.mk_true();
                        for (i, &a) in args.iter().enumerate() {
                            if i == 0 {
                                self.add_def(a, u);
                            } else {
                                self.add_def(a, tru);
                            }
                        }
                    }
                    return Some(u);
                }
                None
            }
            TermKind::Or(ref args) => {
                if !args.is_empty() && args.iter().all(|&a| self.uncnstr(a, manager)) {
                    let (u, is_new) = self.mk_fresh_for_app(app, manager.sorts.bool_sort, manager);
                    if is_new {
                        let fls = manager.mk_false();
                        for (i, &a) in args.iter().enumerate() {
                            if i == 0 {
                                self.add_def(a, u);
                            } else {
                                self.add_def(a, fls);
                            }
                        }
                    }
                    return Some(u);
                }
                None
            }
            // `x = t -> u`, `x := if(u, t, diff(t))` with `diff` a
            // diagonalization (Z3 `process_eq` + `mk_diff`).  Both Bool
            // and BV sorts have >1 element, so `diff(t) != t` always.
            TermKind::Eq(a, b) => {
                let (v, t) = if self.uncnstr(a, manager) && !self.uncnstr(b, manager) {
                    (a, b)
                } else if self.uncnstr(b, manager) && !self.uncnstr(a, manager) {
                    (b, a)
                } else if self.uncnstr(a, manager) {
                    // both unconstrained: pick the first (Z3 order)
                    (a, b)
                } else {
                    return None;
                };
                let v_data = manager.get(v)?;
                let v_sort_data = manager.sorts.get(v_data.sort)?;
                let diff = if v_sort_data.is_bool() {
                    manager.mk_not(t)
                } else if v_sort_data.is_bitvec() {
                    manager.mk_bv_not(t)
                } else {
                    // Uninterpreted/other sorts: Z3 declines (soundness of
                    // the quantifier argument aside, there is no
                    // diagonalizer); so do we.
                    return None;
                };
                let (u, is_new) = self.mk_fresh_for_app(app, manager.sorts.bool_sort, manager);
                if is_new {
                    let def = manager.mk_ite(u, t, diff);
                    self.add_def(v, def);
                }
                Some(u)
            }

            // ================= BV (Z3 process_bv_app) ====================
            // `x + t -> u`, `x := u - t` (Z3 process_add).
            TermKind::BvAdd(a, b) => {
                let w = width?;
                if self.uncnstr(a, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let def = manager.mk_bv_sub(u, b);
                        self.add_def(a, def);
                    }
                    return Some(u);
                }
                if self.uncnstr(b, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let def = manager.mk_bv_sub(u, a);
                        self.add_def(b, def);
                    }
                    return Some(u);
                }
                let _ = w;
                None
            }
            // `x - t -> u`, `x := u + t` (deviation, see module doc).
            TermKind::BvSub(a, b) => {
                if self.uncnstr(a, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let def = manager.mk_bv_add(u, b);
                        self.add_def(a, def);
                    }
                    return Some(u);
                }
                if self.uncnstr(b, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let def = manager.mk_bv_sub(a, u);
                        self.add_def(b, def);
                    }
                    return Some(u);
                }
                None
            }
            // `x * y -> u` (all args), `x := u`, `y := 1`;
            // `c * x -> u` (c odd), `x := c^-1 * u` (Z3 process_bv_mul).
            TermKind::BvMul(a, b) => {
                let w = width?;
                if self.uncnstr(a, manager) && self.uncnstr(b, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let one = manager.mk_bitvec(BigInt::one(), w);
                        self.add_def(a, u);
                        self.add_def(b, one);
                    }
                    return Some(u);
                }
                for (c, x) in [(a, b), (b, a)] {
                    if self.uncnstr(x, manager)
                        && let Some(cval) = const_value(c, manager)
                        && cval.is_odd()
                    {
                        let modulus = BigInt::one() << w as usize;
                        let inv = super::bv_preprocess::mod_inverse_odd(&cval, &modulus);
                        if inv.is_zero() {
                            continue;
                        }
                        let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                        if is_new {
                            let inv_term = manager.mk_bitvec(inv, w);
                            let def = manager.mk_bv_mul(inv_term, u);
                            self.add_def(x, def);
                        }
                        return Some(u);
                    }
                }
                None
            }
            // `x udiv y -> u`, `x := u`, `y := 1` (Z3 process_bv_div).
            TermKind::BvUdiv(a, b) | TermKind::BvSdiv(a, b) => {
                let w = width?;
                if self.uncnstr(a, manager) && self.uncnstr(b, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let one = manager.mk_bitvec(BigInt::one(), w);
                        self.add_def(a, u);
                        self.add_def(b, one);
                    }
                    return Some(u);
                }
                None
            }
            // `x <= t -> u or t = MAX`, `x := if(·, t, t+1)`;
            // `t <= x -> u or t = MIN`, `x := if(·, t, t-1)`
            // (Z3 process_bv_le; signed variants pick the signed extremes).
            TermKind::BvUle(a, b) => Some(self.process_bv_le(app, a, b, false, manager)?),
            TermKind::BvSle(a, b) => Some(self.process_bv_le(app, a, b, true, manager)?),
            // `x ++ y -> u`, extracts per operand (Z3 process_concat).
            TermKind::BvConcat(a, b) => {
                if self.uncnstr(a, manager) && self.uncnstr(b, manager) {
                    let wa = manager
                        .get(a)
                        .and_then(|td| manager.sorts.get(td.sort))
                        .and_then(|s| s.bitvec_width())?;
                    let wb = manager
                        .get(b)
                        .and_then(|td| manager.sorts.get(td.sort))
                        .and_then(|s| s.bitvec_width())?;
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let hi = manager.mk_bv_extract(wa + wb - 1, wb, u);
                        let lo = manager.mk_bv_extract(wb - 1, 0, u);
                        self.add_def(a, hi);
                        self.add_def(b, lo);
                    }
                    return Some(u);
                }
                None
            }
            // `x[hi:lo] -> u`, `x := 0..0 ++ u ++ 0..0` (Z3 process_extract).
            TermKind::BvExtract { high, low, arg } => {
                if !self.uncnstr(arg, manager) {
                    return None;
                }
                let w = manager
                    .get(arg)
                    .and_then(|td| manager.sorts.get(td.sort))
                    .and_then(|s| s.bitvec_width())?;
                let span = high.checked_sub(low).map(|d| d + 1)?;
                let (u, is_new) = self.mk_fresh_for_app(app, manager.sorts.bitvec(span), manager);
                if is_new {
                    let def = if span == w {
                        u
                    } else {
                        let mut pieces: Vec<TermId> = Vec::new();
                        let top_zeros = w - 1 - high;
                        if top_zeros > 0 {
                            pieces.push(manager.mk_bitvec(BigInt::zero(), top_zeros));
                        }
                        pieces.push(u);
                        if low > 0 {
                            pieces.push(manager.mk_bitvec(BigInt::zero(), low));
                        }
                        // concat(high_part, ..., low_part), left = most
                        // significant.
                        let mut acc = pieces.pop().unwrap_or(u);
                        while let Some(p) = pieces.pop() {
                            acc = manager.mk_bv_concat(p, acc);
                        }
                        acc
                    };
                    self.add_def(arg, def);
                }
                Some(u)
            }
            // `~x -> u`, `x := ~u` (Z3 OP_BNOT arm).
            TermKind::BvNot(a) => {
                if self.uncnstr(a, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let def = manager.mk_bv_not(u);
                        self.add_def(a, def);
                    }
                    return Some(u);
                }
                None
            }
            // `x | y -> u`, `x := u`, `y := 0` (Z3 OP_BOR arm).
            TermKind::BvOr(a, b) => {
                let w = width?;
                if self.uncnstr(a, manager) && self.uncnstr(b, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let zero = manager.mk_bitvec(BigInt::zero(), w);
                        self.add_def(a, u);
                        self.add_def(b, zero);
                    }
                    return Some(u);
                }
                None
            }
            // `x & y -> u`, `x := u`, `y := ~0` (deviation: Z3 normalizes
            // AND through NOT/OR first; nixie keeps input shapes).
            TermKind::BvAnd(a, b) => {
                let w = width?;
                if self.uncnstr(a, manager) && self.uncnstr(b, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let ones = (BigInt::one() << w as usize) - BigInt::one();
                        let ones_term = manager.mk_bitvec(ones, w);
                        self.add_def(a, u);
                        self.add_def(b, ones_term);
                    }
                    return Some(u);
                }
                None
            }
            // `x ^ y -> u`, `x := u`, `y := 0` (deviation).
            TermKind::BvXor(a, b) => {
                let w = width?;
                if self.uncnstr(a, manager) && self.uncnstr(b, manager) {
                    let (u, is_new) = self.mk_fresh_for_app(app, sort, manager);
                    if is_new {
                        let zero = manager.mk_bitvec(BigInt::zero(), w);
                        self.add_def(a, u);
                        self.add_def(b, zero);
                    }
                    return Some(u);
                }
                None
            }
            _ => None,
        }
    }

    /// Z3 `process_bv_le`: `v <= t -> (u or t = MAX)` with
    /// `v := if(·, t, t+1)`, and mirrored for `t <= v` with MIN and `t-1`.
    #[allow(clippy::too_many_arguments)]
    fn process_bv_le(
        &mut self,
        app: TermId,
        a: TermId,
        b: TermId,
        is_signed: bool,
        manager: &mut TermManager,
    ) -> Option<TermId> {
        let w = manager
            .get(app)
            .and_then(|td| manager.sorts.get(td.sort))
            .and_then(|s| s.bitvec_width())?;
        let (v, t, is_upper) = if self.uncnstr(a, manager) {
            (a, b, true)
        } else if self.uncnstr(b, manager) {
            (b, a, false)
        } else {
            return None;
        };
        // Extreme value as an unsigned bit pattern.
        let extreme = if is_signed {
            if is_upper {
                (BigInt::one() << (w - 1) as usize) - BigInt::one() // 2^(w-1) - 1
            } else {
                BigInt::one() << (w - 1) as usize // -2^(w-1) as two's complement
            }
        } else if is_upper {
            (BigInt::one() << w as usize) - BigInt::one()
        } else {
            BigInt::zero()
        };
        let extreme_term = manager.mk_bitvec(extreme, w);
        let (u, is_new) = self.mk_fresh_for_app(app, manager.sorts.bool_sort, manager);
        let t_eq_extreme = manager.mk_eq(t, extreme_term);
        let result = manager.mk_or([u, t_eq_extreme]);
        if is_new {
            let delta = manager.mk_bitvec(BigInt::one(), w);
            let def = if is_upper {
                // v := if(result, t, t+1)
                let bumped = manager.mk_bv_add(t, delta);
                manager.mk_ite(result, t, bumped)
            } else {
                // v := if(result, t, t-1)
                let dropped = manager.mk_bv_sub(t, delta);
                manager.mk_ite(result, t, dropped)
            };
            self.add_def(v, def);
        }
        Some(result)
    }
}

/// Unsigned constant value of a bit-vector term.
fn const_value(t: TermId, manager: &TermManager) -> Option<BigInt> {
    match manager.get(t)?.kind {
        TermKind::BitVecConst { ref value, width } => {
            let modulus = BigInt::one() << width as usize;
            Some(value.mod_floor(&modulus))
        }
        _ => None,
    }
}
