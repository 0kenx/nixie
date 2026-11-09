//! Ground axiomatisation of algebraic datatypes.
//!
//! The CDCL(T) core has no dedicated datatype theory: `encode.rs` maps
//! `DtConstructor` / `DtSelector` / `DtTester` terms to plain SAT variables, and
//! `check_dt.rs` only detects a fixed set of *definite* tester conflicts.  Left
//! at that, every structural property of a datatype is invisible to the solver
//! and a formula such as
//!
//! ```smt2
//! (declare-datatype Lst ((nil) (cons (head Int) (tail Lst))))
//! (declare-const l Lst)
//! (assert (= (head l) 10))
//! (assert (= (head l) 11))
//! ```
//!
//! was answered `sat` – `(head l)` is one ground term and cannot hold two
//! values, so the reported model satisfies neither assertion.
//!
//! This module restores the missing meaning the same way
//! [`super::arith_axioms`] does for `div`/`mod`: by asserting the *defining
//! axioms* of every datatype term reachable from the assertion set to the SAT
//! core as ground lemmas.  For a datatype `D` with constructors `C1..Cn`, a
//! term `t : D` and a constructor application `u = Ci(a1..ak)`:
//!
//! | axiom | lemma |
//! |---|---|
//! | exhaustiveness | `is_C1(t) ∨ … ∨ is_Cn(t)` |
//! | mutual exclusivity | `¬is_Ci(t) ∨ ¬is_Cj(t)` for `i < j` |
//! | reconstruction | `is_Ci(t) ⇒ t = Ci(sel_i1(t), …, sel_ik(t))` |
//! | tester correctness | `is_Ci(u)`, and `¬is_Cj(u)` for `j ≠ i` |
//! | selector over constructor | `sel_ij(u) = aj` |
//! | congruence | `x = y ⇒ sel(x) = sel(y)`, `x = y ⇒ (is_C(x) ⇔ is_C(y))`, `⋀ aj = bj ⇒ Ci(a⃗) = Ci(b⃗)` |
//! | acyclicity | see below |
//!
//! Constructor **distinctness** (`Ci(a⃗) ≠ Cj(b⃗)` for `i ≠ j`) follows from
//! tester correctness plus mutual exclusivity, and **injectivity**
//! (`Ci(a⃗) = Ci(b⃗) ⇒ ⋀ aj = bj`) follows from selector-over-constructor plus
//! selector congruence – neither needs a rule of its own.
//!
//! Deliberately *absent*: any constraint on a selector applied to the wrong
//! constructor.  `(head nil)` is underspecified in SMT-LIB and may take any
//! `Int` value, so `(= (head nil) 42)` must stay `sat`; only the two occurrences
//! of one and the same term are forced to agree.
//!
//! # Acyclicity
//!
//! A datatype value is a *finite* tree, so no term may be a proper sub-term of
//! itself: `l = (cons 1 l)` is unsatisfiable.  Congruence alone never sees this
//! – it happily merges `l` with `(cons 1 l)` – which is why the property is so
//! often missing and yields a false `sat`.
//!
//! Rather than an occurs-check over the E-graph (Z3's approach), the measure is
//! reflected into the linear arithmetic solver that is already wired in: a
//! `dt.size!<id>` integer variable measures each datatype term, and
//!
//! * `size(t) ≥ 0` for every datatype term,
//! * `size(Ci(a⃗)) > size(aj)` for every datatype-sorted argument,
//! * `is_Ci(t) ⇒ size(t) > size(sel_ij(t))` for every datatype-sorted field,
//! * `x = y ⇒ size(x) = size(y)` (it is a function),
//!
//! are all theorems of the theory (`size` counts constructor nodes, so
//! `size(Ci(a⃗)) = 1 + Σ size(aj)`).  A structural cycle, however long and
//! however it is routed through intermediate equalities, becomes a cycle of
//! strict `>` in the tableau and is refuted there.
//!
//! # Termination
//!
//! The reconstruction axiom introduces `sel_ij(t)`, which is itself a datatype
//! term for a recursive datatype.  Those introduced terms are deliberately
//! *not* re-axiomatised, so the expansion stops one level below the assertion
//! set – exactly the bound Z3 gets from only expanding a term whose tester the
//! search has already decided.  Omitting an axiom instance is always sound; it
//! can only cost completeness, and the honesty gate below covers the case where
//! the lemma budget itself runs out.
//!
//! Reference: Z3's `smt/theory_datatype.cpp`, which asserts the same
//! `is_Ci ⇒ t = Ci(accessors)` recogniser axiom, the same
//! `accessor(Ci(a⃗)) = aj` reduction, and enforces the same acyclicity
//! condition with an occurs check.

#[allow(unused_imports)]
use crate::prelude::*;
use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_core::sort::{SortId, SortKind};

use super::Solver;
use super::term_walk::collect_structural_children;
use super::trail::TrailOp;

/// Name prefix of the internal well-founded size measure; the term id of the
/// datatype term being measured is appended.
///
/// Shares the reserved namespace with Skolem symbols. Both the mint and
/// model reconstruction use this constant; source text cannot spell it.
pub(super) const DT_SIZE_MEASURE: &str = "\\nixie.dtsize!";

/// Cap on the number of distinct ground datatype lemmas one solver run may
/// assert.  Congruence is expanded Ackermann-style, so the count grows with the
/// square of the number of datatype terms of a single sort; the cap keeps a
/// pathological input from exhausting memory.  Passing it sets
/// [`Solver::dt_axioms_incomplete`], which downgrades a subsequent `Sat` to
/// `Unknown` – the axiomatisation is then a strict subset of the theory, so
/// `Unsat` stays trustworthy but `Sat` does not.
const MAX_DT_AXIOM_LEMMAS: usize = 200_000;

/// One field of a constructor, resolved to owned data so that the emission
/// phase can borrow the [`TermManager`] mutably.
///
/// Shared with [`super::model_builder`], which rebuilds a concrete datatype
/// value out of exactly these resolved declarations.
pub(super) struct FieldInfo {
    /// Selector (accessor) name.
    pub(super) selector: String,
    /// Sort of the field.
    pub(super) sort: SortId,
    /// Whether the field's sort is itself a datatype – the fields that can
    /// close a structural cycle and therefore need the size ordering.
    pub(super) is_datatype: bool,
}

/// One constructor of a datatype.
pub(super) struct ConstructorInfo {
    pub(super) name: String,
    pub(super) fields: Vec<FieldInfo>,
}

/// A datatype declaration, resolved to owned data.
pub(super) struct DeclInfo {
    pub(super) constructors: Vec<ConstructorInfo>,
}

/// Everything the emission phase needs, harvested in one immutable pass over
/// the assertion set.
pub(super) struct DtScan {
    /// Datatype-sorted terms reachable from the assertions, grouped by sort and
    /// ordered by term id so that lemma emission is deterministic.
    pub(super) members: Vec<(SortId, Vec<TermId>)>,
    /// Declarations of every datatype sort that occurs in `members`.
    pub(super) decls: FxHashMap<SortId, DeclInfo>,
}

/// Harvest every datatype-sorted term reachable from `assertions`, together
/// with the declarations of the sorts involved.
///
/// This is a *discovery* walk, not a definite-conflict collector: it records
/// which terms exist, never which facts hold, and every lemma emitted for a
/// discovered term is a theorem of the datatype theory.  Polarity is therefore
/// irrelevant here and the walk deliberately traverses `Or` / `Not` / `Ite` and
/// both operands of an equality – unlike [`super::term_walk::asserted_children`],
/// which exists for the opposite kind of pass.
///
/// Enter binder bodies only to discover subterms independent of every enclosing
/// binder. For example, `tail(l)` is ground in `forall n. n > 0 => is_nil(tail(l))`,
/// whereas `tail(n)` is not. The latter acquires axioms only after instantiation.
/// Memoization includes the lexical scope: a hash-consed variable can occur both
/// free and bound under the same name.
pub(super) fn scan_datatype_terms(assertions: &[TermId], manager: &TermManager) -> Option<DtScan> {
    use nixie_core::interner::Spur;
    enum Frame {
        Visit(TermId, usize),
        Bind(Vec<Spur>, TermId),
        Unbind(Vec<Spur>),
    }
    let mut visited = FxHashSet::default();
    let mut stack: Vec<_> = assertions.iter().map(|&t| Frame::Visit(t, 0)).collect();
    let mut bound: FxHashMap<Spur, usize> = FxHashMap::default();
    let mut free_names: FxHashMap<TermId, Vec<Spur>> = FxHashMap::default();
    let mut scope = 0usize;
    let mut by_sort: FxHashMap<SortId, Vec<TermId>> = FxHashMap::default();
    let mut children: Vec<TermId> = Vec::new();

    while let Some(frame) = stack.pop() {
        let (term, context) = match frame {
            Frame::Bind(names, body) => {
                for &name in &names {
                    *bound.entry(name).or_default() += 1;
                }
                scope += 1;
                stack.push(Frame::Unbind(names));
                stack.push(Frame::Visit(body, scope));
                continue;
            }
            Frame::Unbind(names) => {
                for name in names {
                    if let Some(count) = bound.get_mut(&name) {
                        *count -= 1;
                        if *count == 0 {
                            bound.remove(&name);
                        }
                    }
                }
                continue;
            }
            Frame::Visit(term, context) => (term, context),
        };
        if !visited.insert((term, context)) {
            continue;
        }
        let Some(node) = manager.get(term) else {
            continue;
        };
        if manager.sorts.is_datatype(node.sort) {
            let ground = bound.is_empty()
                || free_names
                    .entry(term)
                    .or_insert_with(|| {
                        manager
                            .free_vars(term)
                            .iter()
                            .filter_map(|&v| match manager.get(v).map(|n| &n.kind) {
                                Some(TermKind::Var(name)) => Some(*name),
                                _ => None,
                            })
                            .collect()
                    })
                    .iter()
                    .all(|name| !bound.contains_key(name));
            if ground {
                by_sort.entry(node.sort).or_default().push(term);
            }
        }
        match &node.kind {
            TermKind::Forall { vars, body, .. } | TermKind::Exists { vars, body, .. } => {
                stack.push(Frame::Bind(
                    vars.iter().map(|(name, _)| *name).collect(),
                    *body,
                ));
            }
            TermKind::Let { bindings, body } => {
                stack.push(Frame::Bind(
                    bindings.iter().map(|(name, _)| *name).collect(),
                    *body,
                ));
                for &(_, value) in bindings {
                    stack.push(Frame::Visit(value, context));
                }
            }
            TermKind::Match { scrutinee, cases } => {
                for case in cases {
                    stack.push(Frame::Bind(case.bindings.to_vec(), case.body));
                }
                stack.push(Frame::Visit(*scrutinee, context));
            }
            kind => {
                children.clear();
                collect_structural_children(kind, &mut children);
                stack.extend(children.iter().map(|&t| Frame::Visit(t, context)));
            }
        }
    }

    if by_sort.is_empty() {
        return None;
    }

    let mut decls: FxHashMap<SortId, DeclInfo> = FxHashMap::default();
    for &sort in by_sort.keys() {
        if let Some(decl) = resolve_decl(sort, manager) {
            decls.insert(sort, decl);
        }
    }
    if decls.is_empty() {
        return None;
    }

    let mut members: Vec<(SortId, Vec<TermId>)> = by_sort
        .into_iter()
        .filter(|(sort, _)| decls.contains_key(sort))
        .map(|(sort, mut terms)| {
            terms.sort_unstable();
            terms.dedup();
            (sort, terms)
        })
        .collect();
    members.sort_unstable_by_key(|(sort, _)| sort.raw());

    Some(DtScan { members, decls })
}

/// Resolve the declaration of the datatype `sort` into owned data, or `None`
/// when the sort was never declared (a forward reference that no
/// `declare-datatype` ever completed).  An unresolved sort simply receives no
/// axioms, which is sound.
pub(super) fn resolve_decl(sort: SortId, manager: &TermManager) -> Option<DeclInfo> {
    let name = manager.sorts.datatype_name(sort)?;
    let def = manager.sorts.get_datatype(name)?;
    if def.constructors.is_empty() {
        return None;
    }
    // Stored declaration names belong to SortManager; AST names belong to
    // TermManager. Resolve declarations before constructing AST terms.
    let constructors = def
        .constructors
        .iter()
        .map(|constructor| ConstructorInfo {
            name: manager.sorts.resolve_spur(constructor.name).to_string(),
            fields: constructor
                .selectors
                .iter()
                .map(|&(selector, field_sort)| FieldInfo {
                    selector: manager.sorts.resolve_spur(selector).to_string(),
                    sort: field_sort,
                    is_datatype: manager.sorts.is_datatype(field_sort),
                })
                .collect(),
        })
        .collect();
    Some(DeclInfo { constructors })
}

/// The index into `decl.constructors` when `term` is an application of one of
/// them, `None` for any other datatype-sorted term (a variable, a selector
/// result, an `ite`, …).
fn applied_constructor(term: TermId, decl: &DeclInfo, manager: &TermManager) -> Option<usize> {
    let node = manager.get(term)?;
    let TermKind::DtConstructor { constructor, .. } = &node.kind else {
        return None;
    };
    let name = manager.resolve_str(*constructor);
    decl.constructors.iter().position(|c| c.name == name)
}

/// The arguments of an applied constructor, cloned out of the term graph so
/// that the manager can be borrowed mutably afterwards.
fn constructor_args(term: TermId, manager: &TermManager) -> Option<Vec<TermId>> {
    let node = manager.get(term)?;
    let TermKind::DtConstructor { args, .. } = &node.kind else {
        return None;
    };
    Some(args.to_vec())
}

/// The internal size measure of a datatype term.
///
/// Deliberately a *variable* keyed by the term id rather than an application of
/// an uninterpreted symbol.  An `Apply` would be interned into EUF, whose
/// congruence closure would then derive `size(x) = size(y)` from `x = y` behind
/// the SAT core's back; the resulting equality reaches the tableau through
/// `TheoryManager::propagate_euf_equalities_to_arith`, which cannot name the
/// literal that justified it, so the conflict clause blames only the arithmetic
/// lemmas and a satisfiable formula is refuted at level 0.  As a variable the
/// measure is opaque to congruence closure and every relation between two sizes
/// is one of the explicitly asserted, literal-justified lemmas below.
fn dt_size(term: TermId, manager: &mut TermManager) -> TermId {
    let int_sort = manager.sorts.int_sort;
    let name = format!("{DT_SIZE_MEASURE}{}", term.raw());
    manager.mk_var(&name, int_sort)
}

impl Solver {
    /// Record only ground portions of source/instance terms. Axiom-generated
    /// recursive selectors are deliberately excluded to keep expansion finite.
    pub(super) fn register_ground_instance_root(&mut self, term: TermId, manager: &TermManager) {
        if self.ground_instance_roots.contains(&term) {
            return;
        }
        let mut stack = vec![term];
        let mut visited = FxHashSet::default();
        let mut has_arrays = false;
        while let Some(current) = stack.pop() {
            if !visited.insert(current) {
                continue;
            }
            if let Some(node) = manager.get(current) {
                if matches!(
                    manager.sorts.get(node.sort).map(|s| &s.kind),
                    Some(SortKind::Array { .. })
                ) {
                    has_arrays = true;
                    break;
                }
                stack.extend(nixie_core::ast::traversal::get_children(&node.kind));
            }
        }
        if has_arrays
            || (manager.sorts.has_datatypes() && scan_datatype_terms(&[term], manager).is_some())
        {
            self.ground_instance_roots.insert(term);
            self.trail.push(TrailOp::GroundInstanceRootAdded { term });
        }
    }

    /// Include ground encodings and instances that the stored binder hides.
    pub(super) fn datatype_scan(&self, manager: &TermManager) -> Option<DtScan> {
        if !manager.sorts.has_datatypes() {
            return None;
        }
        let mut roots = self.assertions.clone();
        roots.extend(self.ground_instance_roots.iter().copied());
        roots.sort_unstable();
        roots.dedup();
        scan_datatype_terms(&roots, manager)
    }

    /// Assert the defining axioms of every datatype term reachable from the
    /// current assertion set.
    ///
    /// Scope: the lemmas enter the SAT core at the *current* assertion level and
    /// each one's dedup entry is journalled on the trail, so a `pop` retracts
    /// the clause and the "already asserted" mark together and a later scope
    /// re-derives whatever it still needs.  Idempotent – re-running it inside
    /// the refinement loop of [`Solver::check`] adds nothing new.
    pub(super) fn instantiate_dt_axioms(&mut self, manager: &mut TermManager) {
        let Some(scan) = self.datatype_scan(manager) else {
            return;
        };

        for (sort, terms) in &scan.members {
            let Some(decl) = scan.decls.get(sort) else {
                continue;
            };
            // Applications of each constructor, indexed as in `decl`.  Holds
            // both the applications found in the assertions and the ones the
            // reconstruction axiom introduces, so that the "equal fields build
            // equal values" direction relates the two.
            let mut pool: Vec<Vec<TermId>> = vec![Vec::new(); decl.constructors.len()];
            for &term in terms {
                self.assert_term_axioms(term, *sort, decl, &mut pool, manager);
                if self.dt_axioms_incomplete {
                    return;
                }
            }
            self.assert_congruence_axioms(terms, decl, manager);
            if self.dt_axioms_incomplete {
                return;
            }
            self.assert_constructor_congruence(&pool, manager);
            if self.dt_axioms_incomplete {
                return;
            }
        }
    }

    /// The structural axioms of a single datatype term.
    fn assert_term_axioms(
        &mut self,
        term: TermId,
        sort: SortId,
        decl: &DeclInfo,
        pool: &mut [Vec<TermId>],
        manager: &mut TermManager,
    ) {
        // Every datatype value is a finite tree, so its node count is a natural
        // number.  Needed even for a nullary constructor, which the strict
        // orderings below never bound from underneath.
        self.assert_size_nonneg(term, manager);

        match applied_constructor(term, decl, manager) {
            Some(index) => {
                pool[index].push(term);
                self.assert_constructor_axioms(term, index, decl, manager);
            }
            None => self.assert_opaque_term_axioms(term, sort, decl, pool, manager),
        }
    }

    /// `is_Ci(u)`, `¬is_Cj(u)` for `j ≠ i`, `sel_ij(u) = aj`, and the size
    /// ordering, for an applied constructor `u = Ci(a1..ak)`.
    ///
    /// Together with the exclusivity axioms these give constructor
    /// *distinctness*; together with selector congruence they give
    /// *injectivity*.
    fn assert_constructor_axioms(
        &mut self,
        term: TermId,
        index: usize,
        decl: &DeclInfo,
        manager: &mut TermManager,
    ) {
        let Some(args) = constructor_args(term, manager) else {
            return;
        };
        for (position, constructor) in decl.constructors.iter().enumerate() {
            let tester = manager.mk_dt_tester(&constructor.name, term);
            let lemma = if position == index {
                tester
            } else {
                manager.mk_not(tester)
            };
            self.assert_dt_lemma(lemma, manager);
        }

        let fields: Vec<(String, SortId, bool)> = decl.constructors[index]
            .fields
            .iter()
            .map(|field| (field.selector.clone(), field.sort, field.is_datatype))
            .collect();
        // An arity mismatch means the term was built against a different
        // declaration than the one in scope; leaving it unaxiomatised is sound.
        if fields.len() != args.len() {
            return;
        }
        for (position, (selector, field_sort, is_datatype)) in fields.into_iter().enumerate() {
            let arg = args[position];
            let applied = manager.mk_dt_selector(&selector, term, field_sort);
            let lemma = manager.mk_eq(applied, arg);
            self.assert_dt_lemma(lemma, manager);
            if is_datatype {
                // A constructor node is strictly larger than each of its
                // datatype-sorted children – the ordering acyclicity rests on.
                self.assert_size_nonneg(arg, manager);
                self.assert_size_nonneg(applied, manager);
                let outer = dt_size(term, manager);
                let inner = dt_size(arg, manager);
                let lemma = manager.mk_gt(outer, inner);
                self.assert_dt_lemma(lemma, manager);
            }
        }
    }

    /// Exhaustiveness, mutual exclusivity, reconstruction and the guarded size
    /// ordering, for a datatype term that is *not* a constructor application.
    fn assert_opaque_term_axioms(
        &mut self,
        term: TermId,
        sort: SortId,
        decl: &DeclInfo,
        pool: &mut [Vec<TermId>],
        manager: &mut TermManager,
    ) {
        // Exhaustiveness: the value was built by *some* constructor.
        let testers: Vec<TermId> = decl
            .constructors
            .iter()
            .map(|constructor| manager.mk_dt_tester(&constructor.name, term))
            .collect();
        let exhaustive = manager.mk_or(testers.iter().copied());
        self.assert_dt_lemma(exhaustive, manager);

        // Mutual exclusivity: and by no more than one.
        for i in 0..testers.len() {
            for j in (i + 1)..testers.len() {
                let left = manager.mk_not(testers[i]);
                let right = manager.mk_not(testers[j]);
                let lemma = manager.mk_or([left, right]);
                self.assert_dt_lemma(lemma, manager);
            }
        }

        // Reconstruction: under its own tester the term *is* the constructor
        // applied to its own accessors.  This is what connects a tester to the
        // term's fields, and what makes `(= p (mk (fst p) (snd p)))` valid.
        for (index, constructor) in decl.constructors.iter().enumerate() {
            let fields: Vec<(String, SortId, bool)> = constructor
                .fields
                .iter()
                .map(|field| (field.selector.clone(), field.sort, field.is_datatype))
                .collect();
            let mut accessors: Vec<TermId> = Vec::with_capacity(fields.len());
            for (selector, field_sort, _) in &fields {
                accessors.push(manager.mk_dt_selector(selector, term, *field_sort));
            }
            let rebuilt = manager.mk_dt_constructor(&constructor.name, accessors.clone(), sort);
            let equality = manager.mk_eq(term, rebuilt);
            let lemma = manager.mk_implies(testers[index], equality);
            self.assert_dt_lemma(lemma, manager);

            // The rebuilt value is a constructor application in its own right,
            // so give it the constructor axioms and enter it into the
            // congruence pool.  Without the latter, `(_ is cons) l` plus
            // `(head l) = 1` could not be closed against a literal
            // `(cons 1 (tail l))` from the formula: nothing said the two
            // `cons` cells with pairwise-equal fields are the same value.
            self.assert_constructor_axioms(rebuilt, index, decl, manager);
            pool[index].push(rebuilt);

            for (position, (_, _, is_datatype)) in fields.iter().enumerate() {
                if !*is_datatype {
                    continue;
                }
                let accessor = accessors[position];
                self.assert_size_nonneg(accessor, manager);
                let outer = dt_size(term, manager);
                let inner = dt_size(accessor, manager);
                let ordering = manager.mk_gt(outer, inner);
                let lemma = manager.mk_implies(testers[index], ordering);
                self.assert_dt_lemma(lemma, manager);
            }
        }
    }

    /// Ackermann-style congruence over the datatype terms of one sort.
    ///
    /// The selectors, the testers and the size measure are *functions*, so
    /// equal arguments force equal results.  There is no datatype theory in the
    /// CDCL(T) loop to run congruence closure for them, so the instances are
    /// expanded explicitly over the finitely many terms of the sort; the SAT
    /// core then relays each consequent to whichever theory owns the result
    /// sort (linear arithmetic for `(head l)`, EUF for `(tail l)`).
    fn assert_congruence_axioms(
        &mut self,
        terms: &[TermId],
        decl: &DeclInfo,
        manager: &mut TermManager,
    ) {
        for i in 0..terms.len() {
            for j in (i + 1)..terms.len() {
                let (left, right) = (terms[i], terms[j]);
                // Two applications of *different* constructors are already kept
                // apart by the tester axioms, so their congruence instances can
                // never fire.
                if let (Some(a), Some(b)) = (
                    applied_constructor(left, decl, manager),
                    applied_constructor(right, decl, manager),
                ) && a != b
                {
                    continue;
                }

                let premise = manager.mk_eq(left, right);
                self.assert_congruence_consequents(premise, left, right, decl, manager);

                if self.dt_axioms_incomplete {
                    return;
                }
            }
        }
    }

    /// `premise ⇒ f(left) = f(right)` for every datatype function `f` of the
    /// sort: the size measure, each tester, and each selector.
    fn assert_congruence_consequents(
        &mut self,
        premise: TermId,
        left: TermId,
        right: TermId,
        decl: &DeclInfo,
        manager: &mut TermManager,
    ) {
        let left_size = dt_size(left, manager);
        let right_size = dt_size(right, manager);
        let size_equal = manager.mk_eq(left_size, right_size);
        let lemma = manager.mk_implies(premise, size_equal);
        self.assert_dt_lemma(lemma, manager);

        for constructor in &decl.constructors {
            let left_tester = manager.mk_dt_tester(&constructor.name, left);
            let right_tester = manager.mk_dt_tester(&constructor.name, right);
            // Both sides are Bool-sorted, so this `Eq` is encoded as an `iff`.
            let equal = manager.mk_eq(left_tester, right_tester);
            let lemma = manager.mk_implies(premise, equal);
            self.assert_dt_lemma(lemma, manager);

            let fields: Vec<(String, SortId, bool)> = constructor
                .fields
                .iter()
                .map(|field| (field.selector.clone(), field.sort, field.is_datatype))
                .collect();
            for (selector, field_sort, is_datatype) in fields {
                let left_field = manager.mk_dt_selector(&selector, left, field_sort);
                let right_field = manager.mk_dt_selector(&selector, right, field_sort);
                let equal = manager.mk_eq(left_field, right_field);
                let lemma = manager.mk_implies(premise, equal);
                self.assert_dt_lemma(lemma, manager);
                if is_datatype {
                    self.assert_size_nonneg(left_field, manager);
                    self.assert_size_nonneg(right_field, manager);
                }
            }
        }
    }

    /// `⋀ aj = bj ⇒ Ci(a⃗) = Ci(b⃗)` over every pair of applications of the same
    /// constructor: equal arguments build equal values.
    ///
    /// This is the converse of injectivity – which needs no rule of its own,
    /// following from selector-over-constructor plus selector congruence – and
    /// it is what closes a reconstructed `Ci(sel(t)…)` against a literal
    /// constructor application appearing in the formula.
    fn assert_constructor_congruence(&mut self, pool: &[Vec<TermId>], manager: &mut TermManager) {
        for applications in pool {
            for i in 0..applications.len() {
                for j in (i + 1)..applications.len() {
                    let (left, right) = (applications[i], applications[j]);
                    // The same application can enter the pool twice (a formula
                    // that literally spells out `Ci(sel(t)…)` also has it
                    // rebuilt); relating a term to itself says nothing.
                    if left == right {
                        continue;
                    }
                    self.assert_constructor_congruence_pair(left, right, manager);
                    if self.dt_axioms_incomplete {
                        return;
                    }
                }
            }
        }
    }

    /// One instance of the "equal arguments build equal values" rule.
    fn assert_constructor_congruence_pair(
        &mut self,
        left: TermId,
        right: TermId,
        manager: &mut TermManager,
    ) {
        let (Some(left_args), Some(right_args)) = (
            constructor_args(left, manager),
            constructor_args(right, manager),
        ) else {
            return;
        };
        if left_args.len() != right_args.len() {
            return;
        }
        // Arguments that are already the *same* hash-consed term contribute no
        // premise.  Emitting `(= x x)` instead would leave a free Boolean atom
        // in the antecedent that the SAT core may set false, silently disabling
        // the rule.
        let premises: Vec<TermId> = left_args
            .iter()
            .zip(right_args.iter())
            .filter(|(a, b)| a != b)
            .map(|(&a, &b)| manager.mk_eq(a, b))
            .collect();
        // Preserve an equality atom: decomposition would repeat the premise.
        let conclusion = manager.mk_eq_atom(left, right);
        let lemma = if premises.is_empty() {
            // Every field is syntactically shared, so the two applications are
            // the same term and `mk_eq` has already folded this to `true`;
            // asserting it is harmless and keeps the branch total.
            conclusion
        } else {
            let premise = manager.mk_and(premises);
            manager.mk_implies(premise, conclusion)
        };
        self.assert_dt_lemma(lemma, manager);
    }

    /// `size(term) >= 0`.
    fn assert_size_nonneg(&mut self, term: TermId, manager: &mut TermManager) {
        let size = dt_size(term, manager);
        let zero = manager.mk_int(0);
        let lemma = manager.mk_ge(size, zero);
        self.assert_dt_lemma(lemma, manager);
    }

    /// Encode `lemma` and force it true with a unit clause at the current
    /// assertion level, at most once per distinct lemma term.
    ///
    /// Deduplication is keyed by the interned lemma id and journalled, mirroring
    /// [`Solver::array_axiom_instances`]: the clause is retracted with the
    /// scope's clauses, so the mark has to go with it or a later scope would
    /// never re-assert an axiom it still needs.
    fn assert_dt_lemma(&mut self, lemma: TermId, manager: &mut TermManager) {
        // The builders fold trivial instances (`(= x x)`, a one-constructor
        // exhaustiveness disjunction under an already-true guard) straight to
        // `true`; asserting those would only burn a lemma slot.
        if manager
            .get(lemma)
            .is_some_and(|node| matches!(node.kind, TermKind::True))
        {
            return;
        }
        if self.dt_axiom_instances.contains(&lemma) {
            return;
        }
        if self.dt_axiom_instances.len() >= MAX_DT_AXIOM_LEMMAS {
            // Out of budget: the axiomatisation is now a strict subset of the
            // theory.  Record it so a later `Sat` is reported as `Unknown`.
            self.dt_axioms_incomplete = true;
            return;
        }
        self.dt_axiom_instances.insert(lemma);
        self.trail
            .push(TrailOp::DtAxiomInstanceAdded { term: lemma });
        let lit = self.encode(lemma, manager);
        let _ = self.sat.add_clause([lit]);
    }
}

#[cfg(test)]
mod upstream034_tests {
    use super::*;
    use crate::Context;

    const DECLS: &str = "(declare-datatype L ((nil) (cons (hd Int) (tl L))))
        (declare-const l L)";

    #[test]
    fn datatype_axioms_and_roots_reset_with_the_clause_database() {
        let mut context = Context::new();
        context
            .execute_script(&format!("{DECLS}(assert ((_ is cons) l))(check-sat)"))
            .expect("script");
        assert!(!context.solver().dt_axiom_instances.is_empty());
        assert!(!context.solver().ground_instance_roots.is_empty());
        // The budget flag must reset even if it is not reached on this tiny goal.
        context.solver_mut().dt_axioms_incomplete = true;
        context.reset();
        assert!(context.solver().dt_axiom_instances.is_empty());
        assert!(context.solver().ground_instance_roots.is_empty());
        assert!(!context.solver().dt_axioms_incomplete);
        let output = context
            .execute_script(&format!("{DECLS}(assert ((_ is cons) l))(check-sat)"))
            .expect("script");
        assert_eq!(output.last().map(String::as_str), Some("sat"));
        assert!(!context.solver().dt_axiom_instances.is_empty());
    }

    #[test]
    fn datatype_root_and_axiom_journals_rollback_together() {
        let mut context = Context::new();
        context
            .execute_script(&format!("{DECLS}(assert ((_ is cons) l))(check-sat)"))
            .expect("script");
        let roots = context.solver().ground_instance_roots.clone();
        let axioms = context.solver().dt_axiom_instances.clone();
        let sort = context.terms.sorts.mk_datatype_sort("L");
        let l = context.terms.mk_var("l", sort);
        let tail = context.terms.mk_dt_selector("tl", l, sort);
        let tester = context.terms.mk_dt_tester("cons", tail);
        for _ in 0..2 {
            context.push();
            context.assert(tester);
            assert_eq!(context.check_sat(), super::super::SolverResult::Sat);
            assert!(context.solver().ground_instance_roots.len() > roots.len());
            context.pop();
            assert_eq!(context.solver().ground_instance_roots, roots);
            assert_eq!(context.solver().dt_axiom_instances, axioms);
        }
    }

    #[test]
    fn datatype_declaration_guard_excludes_forward_references() {
        let mut manager = TermManager::new();
        assert!(!manager.sorts.has_datatypes());
        manager.sorts.mk_datatype_sort("Forward");
        assert!(!manager.sorts.has_datatypes());
    }
}
