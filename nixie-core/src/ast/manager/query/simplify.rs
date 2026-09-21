//! Iterative bottom-up term simplification.
//!
//! Split out of `ast/manager/query.rs`. See `super::substitute`'s module
//! doc comment for the general rationale (an explicit heap stack instead of
//! native recursion, replacing the removed `MAX_QUERY_RECURSION_DEPTH`
//! cap).
//!
//! `simplify`'s conversion is considerably simpler than `substitute`'s:
//! only a small, fixed set of Boolean/arithmetic `TermKind`s ever recurses
//! into its children at all. The prior recursive implementation's catch-all
//! arm was `Some(_) => id`, returning everything else -- bit-vector/string/
//! FP operators, function applications, algebraic datatypes, and every
//! binder (`Forall`/`Exists`/`Let`/`Match`) -- completely untouched,
//! *without even visiting their children*. Since binders are never
//! descended into, there is no capture-avoidance to preserve here, unlike
//! `substitute`.

use super::TermManager;
use crate::ast::term::{TermId, TermKind};
#[allow(unused_imports)]
use crate::prelude::*;
use num_bigint::BigInt;
use smallvec::SmallVec;

/// Fuel for one `ctx_simplify` call: every recursive step decrements;
/// zero means "return unsimplified" — the pass degrades to the identity,
/// never to a wrong answer.
const CTX_FUEL_BUDGET: u32 = 200_000;
/// The growth guard's multiplier: a result beyond this multiple of the
/// input's DAG size is discarded (the input kept).
const CTX_GROWTH_LIMIT: usize = 4;
/// Fuel for one guard-equality solve (`eq_ite_rules`): every worklist
/// step decrements; zero means "stop applying rules, finish with the
/// plain equality" — the solve degrades to the identity, never to a
/// wrong answer.
const SOLVE_EQ_FUEL: u32 = 100_000;

/// The value kinds of [`TermKind`]: constants for which `mk_eq` decides
/// (folds to `true`/`false`) — the "is a value" test of z3's
/// `try_ite_value`.
fn is_value_kind(kind: &TermKind) -> bool {
    matches!(
        kind,
        TermKind::True
            | TermKind::False
            | TermKind::IntConst(_)
            | TermKind::RealConst(_)
            | TermKind::BitVecConst { .. }
            | TermKind::StringLit(_)
    )
}

/// The ctx walk's native-recursion budget: `ctx_walk`/`ctx_walk_inner`
/// are mutually-recursive native code, and the walk's depth is NOT the
/// input's term depth — the Eq arm's solve expands a shallow chain into
/// a deep and/or form and re-enters on it, so a ≤512-deep input (the
/// entry gate's contract) can walk thousands of levels.  Past the
/// budget the walk returns the node unchanged (identity — sound
/// degradation, like the fuel budget).
const CTX_WALK_RECURSION_LIMIT: u32 = 1024;

/// The comparison family of [`TermManager::cmp_ite_rule`]: which
/// operator a distributed residual keeps.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CmpOp {
    Lt,
    Le,
    Gt,
    Ge,
}

impl TermManager {
    /// Re-share a term for PRINTING: the DAG's multiply-referenced
    /// compound subtrees are lifted into `let` bindings, so printing the
    /// body and the bindings (with the stock printer) produces
    /// `let`-shared SMT-LIB text instead of tree-unfolding the sharing —
    /// which is exponential for fan-out chains (the nec-smt residual:
    /// 662 DAG nodes whose tree unfolding never finishes printing;
    /// `2026-09-19-smt-perf-gap-attribution.md`'s printer addendum).
    ///
    /// Returns `(bindings, body)` with `bindings` ordered
    /// children-before-parents (each binding's term may reference the
    /// names bound before it); printing
    /// `(let ((n1 b1)) (let ((n2 b2)) ... body))` is the shared
    /// spelling.  Two safety properties:
    /// * **Name capture is impossible**: candidate names are chosen
    ///   from the term's own symbol vocabulary's complement (every free
    ///   variable and function symbol name in the DAG is collected
    ///   first), so a user variable cannot collide with a binding name.
    /// * **Only compound subtrees bind** (size ≥
    ///   `MIN_SHARED_SUBTREE_SIZE`): shared leaves (variables,
    ///   constants) keep their plain spelling, so small terms print
    ///   exactly as before — the pass engages only where the unfolding
    ///   would actually repeat real content.
    pub fn share_for_printing(&mut self, root: TermId) -> (Vec<(String, TermId)>, TermId) {
        /// A subtree smaller than this is never let-bound: re-printing a
        /// shared leaf or a tiny atom is cheaper than a binding, and the
        /// threshold keeps ordinary terms' printed form unchanged.
        const MIN_SHARED_SUBTREE_SIZE: usize = 2;
        /// Bound on the number of bindings.  The binding count is
        /// naturally DAG-linear (one binding per shared compound node),
        /// so the real bound is the input's DAG size; the previous
        /// hard 1 000 cap truncated the SMALLEST candidates (ascending
        /// size order) and left the largest compounds unbound — their
        /// tree unfolding then exploded the print exponentially (the
        /// large nec-smt members hung in `write_term_at_depth` on a
        /// residual z3 prints with 11 k+ bindings).  100 000 keeps a
        /// hard ceiling for pathological inputs while covering every
        /// real DAG.
        const MAX_SHARED_BINDINGS: usize = 100_000;

        // ---- 1. DAG walk: in-degree-with-multiplicity, subtree size,
        //         and the symbol vocabulary (for capture-free naming). ----
        let mut refs: FxHashMap<TermId, usize> = FxHashMap::default();
        let mut size: FxHashMap<TermId, usize> = FxHashMap::default();
        // Post-order index (the Combine insertion order): a STRICT
        // topological order — every child combines before its parent —
        // used as the sort's tie-break.  Saturating sizes TIE at
        // `usize::MAX` for every huge compound, and a size-only sort can
        // then place a parent BEFORE its saturated child, leaving the
        // child unnamed when the parent's RHS is rebuilt — the inline
        // explosion (376 M printed nodes on one member) this pass
        // exists to prevent.
        let mut post_order: FxHashMap<TermId, usize> = FxHashMap::default();
        let mut vocab: FxHashSet<crate::interner::Spur> = FxHashSet::default();
        // DAG walk, two-phase (Expand/Combine) so sizes combine in TRUE
        // post-order — children's sizes are always inserted before their
        // parents read them.  (A reversed pre-order is NOT post-order:
        // this analysis's first version combined parents first, reading
        // `unwrap_or(1)` for not-yet-sized children — every size was
        // undercounted, the candidate order was not topological, and the
        // bindings' RHS kept un-cut shared subtrees whose printing
        // exploded.  The bug's signature: a 407-DAG-node RHS printing
        // gigabytes.)
        enum Frame {
            Expand(TermId),
            Combine(TermId),
        }
        let mut stack: Vec<Frame> = vec![Frame::Expand(root)];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Expand(t) => {
                    if !seen.insert(t) {
                        continue;
                    }
                    let Some(data) = self.get(t).cloned() else {
                        continue;
                    };
                    if let crate::ast::term::TermKind::Var(name) = &data.kind {
                        vocab.insert(*name);
                    }
                    if let crate::ast::term::TermKind::Apply { func, .. } = &data.kind {
                        vocab.insert(*func);
                    }
                    let children = crate::ast::traversal::get_children(&data.kind);
                    for c in children.iter() {
                        *refs.entry(*c).or_default() += 1;
                    }
                    stack.push(Frame::Combine(t));
                    for c in children.iter().rev() {
                        stack.push(Frame::Expand(*c));
                    }
                }
                Frame::Combine(t) => {
                    let Some(data) = self.get(t) else { continue };
                    let children = crate::ast::traversal::get_children(&data.kind);
                    // Saturating: the TREE size of a shared DAG grows
                    // exponentially with fan-out (the nec-smt large
                    // members exceed 2^64 nodes) — the sizes only gate
                    // the share threshold and binding count, so clamping
                    // at `usize::MAX` is semantically exact ("huge")
                    // where a plain `+` would overflow-panic.
                    let s = children
                        .iter()
                        .map(|c| size.get(c).copied().unwrap_or(1))
                        .fold(1usize, usize::saturating_add);
                    size.insert(t, s);
                    post_order.insert(t, post_order.len());
                }
            }
        }
        let root_size = size.get(&root).copied().unwrap_or(1);

        // ---- 2. Candidates: shared compounds, plus big single-ref
        // compounds.  Sharing alone (refs ≥ 2) is not enough for a
        // bounded print: a SINGLE-reference compound can carry an
        // exponentially-large tree (fan-out chains), and left inline it
        // explodes the printed text (the large nec-smt members' RHS
        // loop hung exactly there).  Binding every compound whose TREE
        // size passes `BIG_INLINE_TREE` makes the binding set a DAG
        // PARTITION — every inline piece is small, so the total printed
        // text is linear in the DAG.
        /// Tree size at (or beyond) which a compound binds even when
        /// referenced only once.
        const BIG_INLINE_TREE: usize = 1024;
        let mut candidates: Vec<TermId> = refs
            .iter()
            .filter(|&(t, &r)| {
                let t_size = size.get(t).copied().unwrap_or(1);
                (r >= 2 && t_size >= MIN_SHARED_SUBTREE_SIZE || t_size >= BIG_INLINE_TREE)
                    && *t != root
            })
            .map(|(&t, _)| t)
            .collect();
        // Children before parents: a candidate's candidate children are
        // strictly smaller, so ascending size is a valid topological
        // order.
        candidates.sort_by_key(|t| {
            (
                size.get(t).copied().unwrap_or(1),
                post_order.get(t).copied().unwrap_or(0),
            )
        });
        candidates.truncate(MAX_SHARED_BINDINGS);
        if candidates.is_empty() || root_size < 2 * MIN_SHARED_SUBTREE_SIZE {
            return (Vec::new(), root);
        }

        // ---- 3. Name minting against the vocabulary's complement. ----
        let mut names: FxHashMap<TermId, TermId> = FxHashMap::default();
        let mut bindings: Vec<(String, TermId)> = Vec::new();
        let mut counter = 1u32;
        for cand in candidates {
            let name = loop {
                let candidate = format!("a!{counter}");
                counter += 1;
                let spur = self.intern_str(&candidate);
                if !vocab.contains(&spur) {
                    break candidate;
                }
            };
            // The binding's RHS: the candidate with its already-named
            // (smaller) candidate children replaced by their names —
            // rebuilt DIRECTLY from the node (children-first candidate
            // order means every shared-compound child is already named,
            // so a one-level child remap is the full substitution).  The
            // previous per-candidate `substitute` call cloned the whole
            // growing `names` map per iteration — O(n²) on the 8k+
            // binding residuals, 43 s on the large nec-smt members.
            let (sort, kind) = match self.get(cand).cloned() {
                Some(data) => (data.sort, data.kind),
                // A missing node cannot be rebuilt; substitute the plain
                // way (the degenerate path — candidates came from get).
                None => {
                    let rhs = self.substitute(cand, &names);
                    let sort = self.sorts.bool_sort;
                    let var = self.mk_var(&name, sort);
                    bindings.push((name, rhs));
                    names.insert(cand, var);
                    continue;
                }
            };
            let rhs =
                self.rebuild_children_with(kind, sort, &|t| names.get(&t).copied().unwrap_or(t));
            let var = self.mk_var(&name, sort);
            bindings.push((name, rhs));
            names.insert(cand, var);
        }
        let body = self.substitute(root, &names);
        (bindings, body)
    }
    /// Simplify a term by applying rewrite rules.
    ///
    /// This performs bottom-up simplification including:
    /// - Constant folding for arithmetic
    /// - Boolean simplifications
    /// - Identity/annihilator rules
    pub fn simplify(&mut self, id: TermId) -> TermId {
        let mut cache = FxHashMap::default();
        self.simplify_cached(id, &mut cache)
    }

    /// Simplify with memoization, using an explicit heap stack instead of
    /// native recursion (see the module doc comment). The two-phase
    /// iterative post-order shape mirrors `size_depth::term_size_cached`;
    /// only the small, explicitly-listed set of kinds in
    /// [`Self::simplifiable_children`] is ever expanded into children --
    /// everything else resolves to itself immediately, matching the prior
    /// recursive catch-all exactly (and, like the prior code, never
    /// memoizes an unvisited node under a fabricated entry -- it simply
    /// isn't pushed).
    fn simplify_cached(&mut self, id: TermId, cache: &mut FxHashMap<TermId, TermId>) -> TermId {
        if let Some(&result) = cache.get(&id) {
            return result;
        }

        let mut stack: Vec<(TermId, bool)> = vec![(id, false)];
        while let Some((current, expanded)) = stack.pop() {
            if cache.contains_key(&current) {
                continue;
            }

            if expanded {
                let result = self.combine_simplified(current, cache);
                cache.insert(current, result);
            } else {
                let children = self.simplifiable_children(current);
                stack.push((current, true));
                for &child in children.iter().rev() {
                    if !cache.contains_key(&child) {
                        stack.push((child, false));
                    }
                }
            }
        }

        cache.get(&id).copied().unwrap_or(id)
    }

    /// `true` when `t` is a value constant ([`is_value_kind`]) — the
    /// "is a value" test of z3's `try_ite_value`.
    fn is_value(&self, t: TermId) -> bool {
        self.get(t).is_some_and(|d| is_value_kind(&d.kind))
    }

    /// z3 `are_equal` for the solve rules: structural identity or value
    /// equality — delegated to `mk_eq`'s constant folding (which decides
    /// every value pair exactly, including mixed `Int`/`Real`).
    fn rw_are_equal(&mut self, a: TermId, b: TermId) -> bool {
        // Structural identity first; then the VALUE pair only — z3's
        // `are_equal` never decides non-value exprs, and gating on
        // `is_value` keeps `mk_eq` on its constant-folding arms (a
        // non-value probe would INTERN an `Eq` node per call — the
        // interning flood that hung the large nec-smt members' walks,
        // 30 % HashMap::insert + 17 % rehash in the profile).
        a == b || (self.is_value(a) && self.is_value(b) && self.mk_eq(a, b) == self.true_id)
    }

    /// z3 `are_distinct`: provably different values.  Only ever true for
    /// a value pair (hash-consing makes distinct ids distinct terms, and
    /// `mk_eq` folds every value pair) — the kind gate is both the z3
    /// semantics and the no-interning guarantee (see `rw_are_equal`).
    fn rw_are_distinct(&mut self, a: TermId, b: TermId) -> bool {
        a != b && self.is_value(a) && self.is_value(b) && self.mk_eq(a, b) == self.false_id
    }

    /// Guard-equality elimination — the `solve_eqs` family proper (z3
    /// `bool_rewriter::mk_eq_core`'s ite rule set: `try_ite_eq`,
    /// `try_ite_value`, and the ite×ite case; the parameter sweep of
    /// `2026-09-19-smt-perf-gap-attribution.md` named this family as one
    /// of the three individually necessary for the nec-smt fold).
    ///
    /// Solves `(= lhs rhs)` when an ite sits on a side into a formula
    /// over the ite's CONDITIONS — the guards are EXTRACTED as literals
    /// (`(= v (ite c t e))` with `t ≠ v` becomes `(and (= e v) ¬c)`),
    /// which the conjunction context then absorbs — instead of being
    /// CASE-SPLIT, which is the measured fuel cost (the ninth session's
    /// memo: distinct split paths carry distinct signatures by
    /// construction, so no memo can catch them).
    ///
    /// Returns `None` when no rule applies.  Every rule is an
    /// unconditional equivalence at the node, so the caller may fall
    /// back to the plain equality.  z3 order: `try_ite_eq` on both
    /// orientations, then `try_ite_value` (one side ite, other a
    /// value), then the ite×ite case.
    fn eq_ite_rules(&mut self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        // Pair memo: the solve is a pure function of the two terms'
        // immutable kinds, so one entry per id-ordered pair serves every
        // later visit (the ctx walk visits the same `(ite, value)` pair
        // under many split signatures; the bottom-up and ctx passes
        // re-visit each other's solved output).  `None` results are
        // cached too — the no-rule probe is the repeated work.
        let key = if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        if let Some(cached) = self.eq_solve_cache.get(&key) {
            return *cached;
        }
        let out = self.eq_ite_rules_uncached(lhs, rhs);
        self.eq_solve_cache.insert(key, out);
        out
    }

    /// [`Self::eq_ite_rules`] before the pair memo — the rule body.
    fn eq_ite_rules_uncached(&mut self, lhs: TermId, rhs: TermId) -> Option<TermId> {
        let l_kind = self.get(lhs).map(|d| d.kind.clone());
        let r_kind = self.get(rhs).map(|d| d.kind.clone());
        if let Some(out) = self.try_ite_eq(lhs, l_kind.as_ref(), rhs) {
            return Some(out);
        }
        if let Some(out) = self.try_ite_eq(rhs, r_kind.as_ref(), lhs) {
            return Some(out);
        }
        match (&l_kind, &r_kind) {
            (Some(TermKind::Ite(..)), Some(k)) if is_value_kind(k) => {
                self.solve_ite_value(lhs, rhs)
            }
            (Some(k), Some(TermKind::Ite(..))) if is_value_kind(k) => {
                self.solve_ite_value(rhs, lhs)
            }
            (Some(TermKind::Ite(..)), Some(TermKind::Ite(..))) => self.solve_ite_ite(lhs, rhs),
            _ => None,
        }
    }

    /// z3 `bool_rewriter::try_ite_eq`: `(= (ite c t e) x)` with the
    /// then-branch equal to `x` and the else-branch provably different
    /// reduces to the condition itself (and symmetrically to `¬c`).
    fn try_ite_eq(
        &mut self,
        ite: TermId,
        ite_kind: Option<&TermKind>,
        other: TermId,
    ) -> Option<TermId> {
        let Some(TermKind::Ite(c, t, e)) = ite_kind else {
            return None;
        };
        let _ = ite;
        if self.rw_are_equal(*t, other) && self.rw_are_distinct(*e, other) {
            return Some(*c);
        }
        if self.rw_are_equal(*e, other) && self.rw_are_distinct(*t, other) {
            return Some(self.mk_not(*c));
        }
        None
    }

    /// z3 `bool_rewriter::try_ite_value` — the guard-extraction core —
    /// as an explicit worklist (z3 re-enters its rewriter via
    /// `BR_REWRITE2`; the worklist is the re-entry, without native
    /// recursion over the chain — the AGENTS.md stack rule).
    ///
    /// Rules on `(= (ite c t e) v)`, `v` a value, in z3's order:
    /// * `try_ite_eq` re-check (the rewriter re-runs it per rewrite);
    /// * R1 `e` a value `≠ v`  → `(and (= t v) c)`;
    /// * R2 `t` a value `≠ v`  → `(and (= e v) ¬c)`;
    /// * R3 `t = v` (and `e = v`) → `true` (else `(or (= e v) c)`);
    /// * R4 `e = v`             → `(or (= t v) ¬c)`;
    /// * R5 `t` an ite with value leaves → `(ite c <solve (= t v)> (= e v))`;
    /// * R6 `e` an ite with value leaves → `(ite c (= t v) <solve (= e v)>)`;
    /// * R7 every leaf of the ite is a value `≠ v` → `false`.
    ///
    /// Fuel-bounded: on exhaustion the pending equality is finished as
    /// the plain (equivalent) `mk_eq` and no further rules fire — the
    /// solve degrades to the identity, never to a wrong answer.
    fn solve_ite_value(&mut self, ite: TermId, val: TermId) -> Option<TermId> {
        // The no-progress guard: when NO rule ever fires, the worklist's
        // terminal is the plain `mk_eq(ite, val)` — which the caller
        // would re-feed to `eq_ite_rules` on its next visit (the ctx
        // walk re-enters on the solved term), an infinite cycle.  Solve
        // only when something was actually rewritten.
        let orig = self.mk_eq(ite, val);
        if matches!(
            self.get(orig).map(|d| &d.kind),
            Some(TermKind::True | TermKind::False)
        ) {
            // Decided outright (a degenerate `mk_eq` fold): progress.
            return Some(orig);
        }
        /// One accumulated combinator: the and/or rules collect their
        /// guard literals and carry exactly one pending equality; the
        /// ite rules (R5/R6) carry two pending equalities (the solved
        /// branch, then the plain sibling — z3's rewriter descends into
        /// the sibling on its next pass, so both are solved here).
        type SolveKey = (TermId, TermId);
        /// The id-ordered cache key for one pending equality.
        fn key_of(x: TermId, v: TermId) -> SolveKey {
            if x.0 <= v.0 { (x, v) } else { (v, x) }
        }
        /// One accumulated combinator: the and/or rules collect their
        /// guard literals and carry exactly one pending equality; the
        /// ite rules (R5/R6) carry two pending equalities (the solved
        /// branch, then the plain sibling — z3's rewriter descends into
        /// the sibling on its next pass, so both are solved here).
        /// Every frame carries its OWNING equality key so the assembled
        /// result memoizes into `eq_solve_cache` — the R5/R6 branch-outs
        /// make the solve TREE exponentially bigger than the DAG unless
        /// intermediate pairs are solved exactly once.
        enum Frame {
            And {
                key: SolveKey,
                parts: SmallVec<[TermId; 4]>,
            },
            Or {
                key: SolveKey,
                parts: SmallVec<[TermId; 4]>,
            },
            Ite {
                key: SolveKey,
                cond: TermId,
                val: TermId,
                else_side: TermId,
                then_res: Option<TermId>,
            },
        }
        let mut frames: Vec<Frame> = Vec::new();
        let mut pending: Option<(TermId, TermId)> = Some((ite, val));
        let mut result: Option<TermId> = None;
        let mut fuel = SOLVE_EQ_FUEL;
        loop {
            if let Some((x, v)) = pending.take() {
                // Sub-solve memo: an intermediate pair already solved
                // (in this call, an earlier call, or the bottom-up pass)
                // resolves without re-descending its whole subtree —
                // this is what keeps the R5/R6 solve TREE linear in the
                // DAG.  A cached `None` (no rule) means the plain
                // equality, which re-interns to the existing id.
                let key = key_of(x, v);
                if let Some(cached) = self.eq_solve_cache.get(&key) {
                    result = Some(match cached {
                        Some(t) => *t,
                        None => self.mk_eq(x, v),
                    });
                    continue;
                }
                if fuel == 0 {
                    let terminal = self.mk_eq(x, v);
                    self.eq_solve_cache.insert(key, Some(terminal));
                    result = Some(terminal);
                    continue;
                }
                fuel -= 1;
                let kind = self.get(x).map(|d| d.kind.clone());
                let Some(TermKind::Ite(c, t, e)) = kind.as_ref() else {
                    // Terminal: a value (folds) or an unsolvable term —
                    // the plain equality IS the solved form.
                    let terminal = self.mk_eq(x, v);
                    self.eq_solve_cache.insert(key, Some(terminal));
                    result = Some(terminal);
                    continue;
                };
                let (c, t, e) = (*c, *t, *e);
                if self.rw_are_equal(t, v) && self.rw_are_distinct(e, v) {
                    self.eq_solve_cache.insert(key, Some(c));
                    result = Some(c);
                } else if self.rw_are_equal(e, v) && self.rw_are_distinct(t, v) {
                    let nc = self.mk_not(c);
                    self.eq_solve_cache.insert(key, Some(nc));
                    result = Some(nc);
                } else if self.is_value(e) && self.rw_are_distinct(e, v) {
                    frames.push(Frame::And {
                        key,
                        parts: SmallVec::from_iter([c]),
                    });
                    pending = Some((t, v));
                } else if self.is_value(t) && self.rw_are_distinct(t, v) {
                    frames.push(Frame::And {
                        key,
                        parts: SmallVec::from_iter([self.mk_not(c)]),
                    });
                    pending = Some((e, v));
                } else if self.is_value(t) && self.rw_are_equal(t, v) {
                    if self.is_value(e) && self.rw_are_equal(e, v) {
                        self.eq_solve_cache.insert(key, Some(self.true_id));
                        result = Some(self.true_id);
                    } else {
                        frames.push(Frame::Or {
                            key,
                            parts: SmallVec::from_iter([c]),
                        });
                        pending = Some((e, v));
                    }
                } else if self.is_value(e) && self.rw_are_equal(e, v) {
                    frames.push(Frame::Or {
                        key,
                        parts: SmallVec::from_iter([self.mk_not(c)]),
                    });
                    pending = Some((t, v));
                } else if self.ite_with_value_leaves(t).is_some() {
                    frames.push(Frame::Ite {
                        key,
                        cond: c,
                        val: v,
                        else_side: e,
                        then_res: None,
                    });
                    pending = Some((t, v));
                } else if self.ite_with_value_leaves(e).is_some() {
                    // R6: `(ite c (= t v) solve(= e v))` — the THEN hole
                    // is the plain t-side, the ELSE hole the solved
                    // e-side (the frame's `else_side` names the ELSE
                    // hole's term — `e`, never `t`: solving the t-side
                    // twice silently dropped the else-branch, a
                    // false-`unsat` shape the equivalence fuzzer
                    // isolated).
                    frames.push(Frame::Ite {
                        key,
                        cond: c,
                        val: v,
                        else_side: e,
                        then_res: None,
                    });
                    pending = Some((t, v));
                } else if self.ite_leaves_all_distinct(x, v) {
                    self.eq_solve_cache.insert(key, Some(self.false_id));
                    result = Some(self.false_id);
                } else {
                    let terminal = self.mk_eq(x, v);
                    self.eq_solve_cache.insert(key, Some(terminal));
                    result = Some(terminal);
                }
            } else if let Some(r) = result.take() {
                match frames.pop() {
                    None => {
                        if r == orig {
                            // Nothing was rewritten anywhere on the
                            // chain: no solve (see the entry guard).
                            return None;
                        }
                        return Some(r);
                    }
                    Some(Frame::And { key, mut parts }) => {
                        // The extracted guards must meet their negations
                        // HERE (z3's mk_and is the REWRITER's absorbing
                        // one): a chain solved down to `(and (= x v) ¬c)`
                        // refutes exactly when some level's condition `c`
                        // reappears against the default's equality — the
                        // member folds only if this conjunction absorbs
                        // complements.
                        parts.push(r);
                        let assembled = self.absorb_literals(parts, true);
                        self.eq_solve_cache.insert(key, Some(assembled));
                        result = Some(assembled);
                    }
                    Some(Frame::Or { key, mut parts }) => {
                        parts.push(r);
                        let assembled = self.absorb_literals(parts, false);
                        self.eq_solve_cache.insert(key, Some(assembled));
                        result = Some(assembled);
                    }
                    Some(Frame::Ite {
                        key,
                        cond,
                        val,
                        else_side,
                        then_res,
                    }) => match then_res {
                        None => {
                            frames.push(Frame::Ite {
                                key,
                                cond,
                                val,
                                else_side,
                                then_res: Some(r),
                            });
                            pending = Some((else_side, val));
                        }
                        Some(then_res) => {
                            let assembled = self.rewrite_ite(cond, then_res, r);
                            self.eq_solve_cache.insert(key, Some(assembled));
                            result = Some(assembled);
                        }
                    },
                }
            } else {
                // Unreachable: the loop starts with `pending` set and
                // every arm re-establishes exactly one of the two.
                return None;
            }
        }
    }

    /// `(c, t, e)` when `t` is an ite whose DIRECT branches are values —
    /// z3's progress guard for the recursive rules R5/R6 (the sub-solve
    /// is guaranteed to fire its first step).
    fn ite_with_value_leaves(&self, t: TermId) -> Option<(TermId, TermId, TermId)> {
        match self.get(t).map(|d| d.kind.clone()) {
            Some(TermKind::Ite(c, a, b)) if self.is_value(a) && self.is_value(b) => Some((c, a, b)),
            _ => None,
        }
    }

    /// z3 `simplify_eq_ite`: every leaf of the ite (recursively through
    /// nested ites, DAG-safe) is a value distinct from `v` — then the
    /// whole `(= ite v)` is `false`.  Iterative with a seen-set.
    fn ite_leaves_all_distinct(&mut self, root: TermId, v: TermId) -> bool {
        /// Budget on the leaf scan: R7 fires at every level whose other
        /// rules stalled, and an unbounded scan over the level's whole
        /// subtree is quadratic on stalling chains (the large nec-smt
        /// members' ~40k-level select spines burned ~90 s in these scans
        /// alone).  Past the budget the rule declines — sound (no
        /// rewrite), and z3's own caller only reaches it after R1–R6
        /// all failed, so deep stalled subtrees lose nothing it would
        /// have decided.
        const R7_SCAN_BUDGET: usize = 8192;
        let mut visited: usize = 0;
        let mut stack: Vec<TermId> = vec![root];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            visited += 1;
            if visited > R7_SCAN_BUDGET {
                return false;
            }
            let kind = self.get(x).map(|d| d.kind.clone());
            match kind {
                Some(TermKind::Ite(_, t, e)) => {
                    stack.push(t);
                    stack.push(e);
                }
                Some(ref k) if is_value_kind(k) => {
                    if self.mk_eq(x, v) != self.false_id {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    /// z3's ite×ite case (`mk_eq_core`'s `m_ite_extra_rules` block): two
    /// ites whose four branches are values cross into a four-clause
    /// conjunction over the conditions (a case-split-free exhaustive
    /// sign matrix — every leaf equality folds, being value-vs-value).
    fn solve_ite_ite(&mut self, l: TermId, r: TermId) -> Option<TermId> {
        let l_kind = self.get(l).map(|d| d.kind.clone());
        let r_kind = self.get(r).map(|d| d.kind.clone());
        let (Some(TermKind::Ite(c1, t1, e1)), Some(TermKind::Ite(c2, t2, e2))) = (&l_kind, &r_kind)
        else {
            return None;
        };
        let (c1, t1, e1, c2, t2, e2) = (*c1, *t1, *e1, *c2, *t2, *e2);
        if !(self.is_value(t1) && self.is_value(e1) && self.is_value(t2) && self.is_value(e2)) {
            return None;
        }
        let e1e2 = self.mk_eq(e1, e2);
        let t1t2 = self.mk_eq(t1, t2);
        let t1e2 = self.mk_eq(t1, e2);
        let e1t2 = self.mk_eq(e1, t2);
        let nc1 = self.mk_not(c1);
        let nc2 = self.mk_not(c2);
        let d1 = self.mk_or([c1, c2, e1e2]);
        let d2 = self.mk_or([nc1, nc2, t1t2]);
        let d3 = self.mk_or([nc1, c2, t1e2]);
        let d4 = self.mk_or([c1, nc2, e1t2]);
        Some(self.mk_and([d1, d2, d3, d4]))
    }

    /// z3 `bool_rewriter::mk_ite_core`, iterative: each rule either
    /// returns a final term or rewrites the `(c, t, e)` triple in place
    /// (z3 re-enters `mk_ite_core` per `BR_REWRITE*`; the loop is the
    /// re-entry, without native recursion).  Every rewrite strictly
    /// shrinks `t`/`e` as DAG terms, so the loop terminates.
    ///
    /// Base rules (unconditional in z3): negated-condition swap,
    /// same-condition merge on either side, constant conditions,
    /// identical branches, and the Boolean connections (a Boolean ite
    /// with constant branches connects to and/or/iff, `m_elim_ite`
    /// default true).  The tail block carries z3's `m_ite_extra_rules`
    /// cross-branch merges (default true) — the structural normal form
    /// that lets two selects with shared leaves fuse into one.
    fn rewrite_ite(&mut self, mut c: TermId, mut t: TermId, mut e: TermId) -> TermId {
        loop {
            // (ite (not c) a b) ==> (ite c b a)
            if let Some(TermKind::Not(inner)) = self.get(c).map(|d| d.kind.clone()) {
                c = inner;
                std::mem::swap(&mut t, &mut e);
            }
            // (ite c (ite c t1 t2) t3) ==> (ite c t1 t3)
            if let Some(TermKind::Ite(c2, t1, _)) = self.get(t).map(|d| d.kind.clone())
                && c2 == c
            {
                t = t1;
            }
            // (ite c t1 (ite c2 t1 t2)) ==> (ite (or c c2) t1 t2)
            if let Some(TermKind::Ite(c2, et, ee)) = self.get(e).map(|d| d.kind.clone()) {
                if et == t {
                    let nc = self.mk_or([c, c2]);
                    c = nc;
                    e = ee;
                    continue;
                }
                // (ite c t1 (ite c t2 t3)) ==> (ite c t1 t3)
                if c2 == c {
                    e = ee;
                }
            }
            if matches!(self.get(c).map(|d| &d.kind), Some(TermKind::True)) {
                return t;
            }
            if matches!(self.get(c).map(|d| &d.kind), Some(TermKind::False)) {
                return e;
            }
            if t == e {
                return t;
            }
            // Boolean connections.
            if self.get(t).is_some_and(|d| d.sort == self.sorts.bool_sort) {
                let t_true = matches!(self.get(t).map(|d| &d.kind), Some(TermKind::True));
                let t_false = matches!(self.get(t).map(|d| &d.kind), Some(TermKind::False));
                let e_true = matches!(self.get(e).map(|d| &d.kind), Some(TermKind::True));
                let e_false = matches!(self.get(e).map(|d| &d.kind), Some(TermKind::False));
                if t_true && e_false {
                    return c;
                }
                if t_false && e_true {
                    return self.mk_not(c);
                }
                if t_true {
                    return self.mk_or([c, e]);
                }
                if t_false {
                    let nc = self.mk_not(c);
                    return self.mk_and([nc, e]);
                }
                if e_true {
                    let nc = self.mk_not(c);
                    return self.mk_or([nc, t]);
                }
                if e_false {
                    return self.mk_and([c, t]);
                }
                if c == e {
                    return self.mk_and([c, t]);
                }
                if c == t {
                    return self.mk_or([c, e]);
                }
                // Complement branches: (ite c p (not p)) ==> (= c p)
                if let Some(TermKind::Not(inner)) = self.get(e).map(|d| d.kind.clone())
                    && inner == t
                {
                    return self.mk_eq(c, t);
                }
                if let Some(TermKind::Not(inner)) = self.get(t).map(|d| d.kind.clone())
                    && inner == e
                {
                    return self.mk_eq(c, t);
                }
            }
            // m_ite_extra_rules cross-branch merges.
            if let Some(TermKind::Ite(c2, tt, te)) = self.get(t).map(|d| d.kind.clone()) {
                // (ite c1 (ite c2 t1 t2) t1) ==> (ite (and c1 (not c2)) t2 t1)
                if e == tt {
                    let nc2 = self.mk_not(c2);
                    let nc = self.mk_and([c, nc2]);
                    c = nc;
                    t = te;
                    continue;
                }
                // (ite c1 (ite c2 t1 t2) t2) ==> (ite (and c1 c2) t1 t2)
                if e == te {
                    let nc = self.mk_and([c, c2]);
                    c = nc;
                    t = tt;
                    continue;
                }
                if let Some(TermKind::Ite(c3, et1, ee1)) = self.get(e).map(|d| d.kind.clone()) {
                    // (ite c1 (ite c2 t1 t2) (ite c3 t1 t2))
                    //   ==> (ite (or (and c1 c2) (and (not c1) c3)) t1 t2)
                    if tt == et1 && te == ee1 {
                        let a1 = self.mk_and([c, c2]);
                        let nc = self.mk_not(c);
                        let a2 = self.mk_and([nc, c3]);
                        let o = self.mk_or([a1, a2]);
                        c = o;
                        t = tt;
                        e = te;
                        continue;
                    }
                    // (ite c1 (ite c2 t1 t2) (ite c3 t2 t1))
                    //   ==> (ite (or (and c1 c2) (and (not c1) (not c3))) t1 t2)
                    if tt == ee1 && te == et1 {
                        let a1 = self.mk_and([c, c2]);
                        let nc = self.mk_not(c);
                        let nc3 = self.mk_not(c3);
                        let a2 = self.mk_and([nc, nc3]);
                        let o = self.mk_or([a1, a2]);
                        c = o;
                        t = tt;
                        e = te;
                        continue;
                    }
                }
            }
            if let Some(TermKind::Ite(c2, et, ee)) = self.get(e).map(|d| d.kind.clone()) {
                // (ite c1 t1 (ite c2 t1 t2)) ==> (ite (or c1 c2) t1 t2)
                if t == et {
                    let nc = self.mk_or([c, c2]);
                    c = nc;
                    e = ee;
                    continue;
                }
                // (ite c1 t1 (ite c2 t2 t1)) ==> (ite (or c1 (not c2)) t1 t2)
                if t == ee {
                    let nc2 = self.mk_not(c2);
                    let nc = self.mk_or([c, nc2]);
                    c = nc;
                    e = et;
                    continue;
                }
            }
            return self.mk_ite(c, t, e);
        }
    }

    /// Context-dependent simplification (z3's `ctx-simplify` shape, the
    /// pass the nec-smt let-chain goals need — see
    /// `2026-09-19-smt-perf-gap-attribution.md`'s parameter-sweep
    /// addendum: `push_ite` + `ite_extra_rules` + `solve_eqs` are each
    /// necessary, and the LOCAL subset alone is a measured dead end; the
    /// closing power comes from carrying a literal context through the
    /// walk).
    ///
    /// The walk is top-down with a context of known-polarity atoms:
    /// * at an `And`, every conjunct contributes its atom polarity (the
    ///   conjunct IS true in this context) and the remaining conjuncts
    ///   simplify under it;
    /// * at an `Or`, a FALSE literal is dropped (modus ponens on the
    ///   path — one disjunct known false removes it);
    /// * at a `Not`, the polarity flips;
    /// * at an `Ite` whose condition the context decides, prune to the
    ///   selected branch; otherwise descend BOTH branches under
    ///   `c` / `¬c` (the case split that reaches through `or`/`not`
    ///   nesting — the piece the one-level And-context prune lacked);
    /// * at `Eq`/comparisons of a constant against an `Ite`, push into
    ///   the branches (fuel-bounded) so constant-vs-constant branches
    ///   decide.
    ///
    /// Every step is an equivalence at its node under the path context
    /// (never a strengthening); the top-level call starts with the empty
    /// context, so the RESULT is unconditionally equivalent to the input.
    /// Fuel-bounded throughout; a growth guard keeps the result when a
    /// rewrite would exceed `CTX_GROWTH_LIMIT` × the input's DAG size.
    pub fn ctx_simplify(&mut self, root: TermId) -> TermId {
        // DEPTH CONTRACT (the assert path's caller-side contract, moved
        // INTO the pass so every caller — the `simplify` command, the
        // tactics, the assert fold — is protected by construction):
        // `ctx_walk` is mutually-recursive NATIVE code, and a deep spine
        // overflows the process stack (the large nec-smt members' ~2500+
        // residuals did, the moment the pair-memo made the walk fast
        // enough to reach their depth).  512 matches the proven envelope
        // (`term_exceeds_encode_depth` gates the same walk on the 128 KiB
        // encode threads); a too-deep input returns UNCHANGED — the
        // identity is sound, the caller keeps the bottom-up result.
        // `term_depth` is itself an explicit-stack walk.
        const CTX_WALK_DEPTH_LIMIT: usize = 512;
        if self.term_depth(root) > CTX_WALK_DEPTH_LIMIT {
            return root;
        }
        let size_in = self.subtree_dag_size(root);
        // The per-subtree Boolean-atom sets (the memo's relevance
        // domains): the walk of `t` can only consult context entries for
        // atoms OCCURRING in `t`'s subtree, so results memoize per
        // (term, relevant-atoms signature) — without this, shared
        // subchains re-walk multiplicatively (the nec-smt member burned
        // the whole 200k-step fuel on a 662-node term).
        let sub_atoms = self.subtree_bool_atoms(root);
        let mut fuel = CTX_FUEL_BUDGET;
        let mut memo: FxHashMap<(TermId, u64), TermId> = FxHashMap::default();
        let out = self.ctx_walk(
            root,
            &mut FxHashMap::default(),
            &mut fuel,
            &sub_atoms,
            &mut memo,
            CTX_WALK_RECURSION_LIMIT,
        );
        let size_out = self.subtree_dag_size(out);
        if size_out > size_in.saturating_mul(CTX_GROWTH_LIMIT) {
            return root;
        }
        out
    }

    /// Boolean-sorted atom sets per subtree, bottom-up over the DAG
    /// (children's sets unioned; a node's own id included when it is
    /// Boolean-sorted — any Boolean node can serve as a context atom
    /// key).  `None` for a node whose set exceeds
    /// [`MAX_MEMO_ATOM_SET`]: such subtrees simply do not memoize (the
    /// walk stays correct, only slower).
    fn subtree_bool_atoms(&self, root: TermId) -> FxHashMap<TermId, Option<FxHashSet<TermId>>> {
        /// Beyond this many distinct atoms a subtree's set is stored as
        /// `None` (no memoization for it) — the set itself would cost
        /// more than the re-walk it saves on typical inputs.
        const MAX_MEMO_ATOM_SET: usize = 1024;
        let mut out: FxHashMap<TermId, Option<FxHashSet<TermId>>> = FxHashMap::default();
        // Two-phase Expand/Combine (children's sets exist before the
        // parent unions them — the post-order trap the share-for-printing
        // pass already recorded once).
        enum Frame {
            Expand(TermId),
            Combine(TermId),
        }
        let mut stack = vec![Frame::Expand(root)];
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        while let Some(f) = stack.pop() {
            match f {
                Frame::Expand(t) => {
                    if !seen.insert(t) {
                        continue;
                    }
                    let Some(data) = self.get(t).cloned() else {
                        continue;
                    };
                    let children = crate::ast::traversal::get_children(&data.kind);
                    stack.push(Frame::Combine(t));
                    for c in children.iter().rev() {
                        stack.push(Frame::Expand(*c));
                    }
                }
                Frame::Combine(t) => {
                    let Some(data) = self.get(t) else { continue };
                    let children = crate::ast::traversal::get_children(&data.kind);
                    let mut set: Option<FxHashSet<TermId>> = if data.sort == self.sorts.bool_sort {
                        let mut s = FxHashSet::default();
                        s.insert(t);
                        Some(s)
                    } else {
                        Some(FxHashSet::default())
                    };
                    for c in children {
                        match (out.get(&c), &mut set) {
                            (Some(Some(cs)), Some(s)) => {
                                for x in cs {
                                    s.insert(*x);
                                }
                            }
                            (Some(None), _) | (None, _) => {
                                set = None;
                            }
                            _ => {}
                        }
                    }
                    if let Some(s) = &set
                        && s.len() > MAX_MEMO_ATOM_SET
                    {
                        set = None;
                    }
                    out.insert(t, set);
                }
            }
        }
        out
    }

    /// The memo signature for walking `t` under `ctx`: a hash of the
    /// context's entries restricted to `t`'s relevant atoms.  Two
    /// contexts agreeing on those entries walk `t` identically — the
    /// walk consults nothing else.
    fn ctx_signature(
        &self,
        t: TermId,
        ctx: &FxHashMap<TermId, bool>,
        sub_atoms: &FxHashMap<TermId, Option<FxHashSet<TermId>>>,
    ) -> Option<u64> {
        let relevant = sub_atoms.get(&t)?;
        let set = relevant.as_ref()?;
        // Iterate the CONTEXT (small: it grows only along the walk's
        // case-split/conjunct path) and test subtree membership — the
        // intersection is what the walk can consult.
        let mut h = std::collections::hash_map::DefaultHasher::new();
        use std::hash::Hash;
        let mut entries: SmallVec<[(TermId, bool); 8]> = SmallVec::new();
        for (&atom, &pol) in ctx.iter() {
            if set.contains(&atom) {
                entries.push((atom, pol));
            }
        }
        entries.sort_unstable_by_key(|(a, _)| a.0);
        for (atom, pol) in entries {
            atom.0.hash(&mut h);
            pol.hash(&mut h);
        }
        Some(std::hash::Hasher::finish(&h))
    }

    /// DAG node count of `t`'s subtree (the growth guard's metric).
    fn subtree_dag_size(&self, t: TermId) -> usize {
        let mut n = 0usize;
        let mut stack = vec![t];
        let mut seen = FxHashSet::default();
        while let Some(x) = stack.pop() {
            if seen.insert(x) {
                n += 1;
                if let Some(d) = self.get(x) {
                    stack.extend(crate::ast::traversal::get_children(&d.kind));
                }
            }
        }
        n
    }

    /// One context step: the polarity `p` assigns to atom `t`, if `t` is
    /// literal-shaped.
    fn atom_polarity(&self, t: TermId) -> Option<(TermId, bool)> {
        match self.get(t).map(|d| &d.kind) {
            Some(TermKind::Not(inner)) => Some((*inner, false)),
            // A Boolean atom in positive position asserts itself.
            Some(_) if self.get(t).is_some_and(|d| d.sort == self.sorts.bool_sort) => {
                Some((t, true))
            }
            _ => None,
        }
    }

    /// The context-decided value of `t`: a literal hit, a constant, or a
    /// comparison the context decides via a known atom's negation
    /// (`(not c)` with `c` known true).
    fn ctx_value(&self, t: TermId, ctx: &FxHashMap<TermId, bool>) -> Option<bool> {
        if let Some(TermKind::True) = self.get(t).map(|d| &d.kind) {
            return Some(true);
        }
        if let Some(TermKind::False) = self.get(t).map(|d| &d.kind) {
            return Some(false);
        }
        let (atom, positive) = self.atom_polarity(t)?;
        let known = *ctx.get(&atom)?;
        Some(if positive { known } else { !known })
    }

    fn ctx_walk(
        &mut self,
        t: TermId,
        ctx: &mut FxHashMap<TermId, bool>,
        fuel: &mut u32,
        sub_atoms: &FxHashMap<TermId, Option<FxHashSet<TermId>>>,
        memo: &mut FxHashMap<(TermId, u64), TermId>,
        depth: u32,
    ) -> TermId {
        if depth == 0 {
            return t;
        }
        let sig = self.ctx_signature(t, ctx, sub_atoms);
        if let Some(s) = sig
            && let Some(&r) = memo.get(&(t, s))
        {
            return r;
        }
        let out = self.ctx_walk_inner(t, ctx, fuel, sub_atoms, memo, depth);
        if let Some(s) = sig {
            memo.insert((t, s), out);
        }
        out
    }

    fn ctx_walk_inner(
        &mut self,
        t: TermId,
        ctx: &mut FxHashMap<TermId, bool>,
        fuel: &mut u32,
        sub_atoms: &FxHashMap<TermId, Option<FxHashSet<TermId>>>,
        memo: &mut FxHashMap<(TermId, u64), TermId>,
        depth: u32,
    ) -> TermId {
        if *fuel == 0 {
            return t;
        }
        *fuel -= 1;
        // Constant or context-decided: replace by the Boolean directly.
        if let Some(v) = self.ctx_value(t, ctx) {
            return if v { self.true_id } else { self.false_id };
        }
        let Some(data) = self.get(t).cloned() else {
            return t;
        };
        match data.kind {
            TermKind::Not(inner) => {
                let s = self.ctx_walk(inner, ctx, fuel, sub_atoms, memo, depth - 1);
                self.mk_not(s)
            }
            TermKind::And(args) => self.ctx_and(args, ctx, fuel, sub_atoms, memo, depth - 1),
            TermKind::Or(args) => {
                // Drop disjuncts the context refutes; recurse the rest.
                let mut kept: SmallVec<[TermId; 4]> = SmallVec::new();
                for a in args {
                    if let Some(false) = self.ctx_value(a, ctx) {
                        continue;
                    }
                    let s = self.ctx_walk(a, ctx, fuel, sub_atoms, memo, depth - 1);
                    kept.push(s);
                }
                self.absorb_literals(kept, false)
            }
            TermKind::Ite(c, a, b) => {
                // Case split: each branch under its own guard.
                let cs = self.ctx_walk(c, ctx, fuel, sub_atoms, memo, depth - 1);
                if let Some(TermKind::True) = self.get(cs).map(|d| &d.kind) {
                    return self.ctx_walk(a, ctx, fuel, sub_atoms, memo, depth - 1);
                }
                if let Some(TermKind::False) = self.get(cs).map(|d| &d.kind) {
                    return self.ctx_walk(b, ctx, fuel, sub_atoms, memo, depth - 1);
                }
                let (as_, bs) = if let Some((atom, pol)) = self.atom_polarity(cs) {
                    let prev = ctx.insert(atom, pol);
                    let as_ = self.ctx_walk(a, ctx, fuel, sub_atoms, memo, depth - 1);
                    ctx.insert(atom, !pol);
                    let bs = self.ctx_walk(b, ctx, fuel, sub_atoms, memo, depth - 1);
                    match prev {
                        Some(p) => {
                            ctx.insert(atom, p);
                        }
                        None => {
                            ctx.remove(&atom);
                        }
                    }
                    (as_, bs)
                } else {
                    (
                        self.ctx_walk(a, ctx, fuel, sub_atoms, memo, depth - 1),
                        self.ctx_walk(b, ctx, fuel, sub_atoms, memo, depth - 1),
                    )
                };
                // The ite-on-Boolean connections (z3's `ite_extra_rules`
                // core): a Boolean ite with a constant branch connects to
                // and/or, where the context's literals absorb it.
                if self
                    .get(as_)
                    .is_some_and(|d| d.sort == self.sorts.bool_sort)
                    && self.get(bs).is_some_and(|d| d.sort == self.sorts.bool_sort)
                {
                    let t_true = matches!(self.get(as_).map(|d| &d.kind), Some(TermKind::True));
                    let t_false = matches!(self.get(as_).map(|d| &d.kind), Some(TermKind::False));
                    let e_true = matches!(self.get(bs).map(|d| &d.kind), Some(TermKind::True));
                    let e_false = matches!(self.get(bs).map(|d| &d.kind), Some(TermKind::False));
                    let not_cs = self.mk_not(cs);
                    if t_true && e_false {
                        return cs;
                    }
                    if t_false && e_true {
                        return not_cs;
                    }
                    if t_true {
                        return self.mk_or([cs, bs]);
                    }
                    if e_true {
                        return self.mk_or([not_cs, as_]);
                    }
                    if t_false {
                        return self.ctx_and(
                            SmallVec::from_iter([not_cs, bs]),
                            ctx,
                            fuel,
                            sub_atoms,
                            memo,
                            depth - 1,
                        );
                    }
                    if e_false {
                        return self.ctx_and(
                            SmallVec::from_iter([cs, as_]),
                            ctx,
                            fuel,
                            sub_atoms,
                            memo,
                            depth - 1,
                        );
                    }
                }
                self.mk_ite(cs, as_, bs)
            }
            TermKind::Eq(l, r) => {
                // Guard-equality elimination FIRST (z3 `mk_eq_core`'s ite
                // rules): the conditions are extracted as literals for
                // the context walk instead of case-split — the memo
                // proved the splits, not sharing, were the fuel cost
                // (the ninth session of the perf-gap study).
                if let Some(solved) = self.eq_ite_rules(l, r) {
                    return self.ctx_walk(solved, ctx, fuel, sub_atoms, memo, depth - 1);
                }
                let ls = self.ctx_walk(l, ctx, fuel, sub_atoms, memo, depth - 1);
                let rs = self.ctx_walk(r, ctx, fuel, sub_atoms, memo, depth - 1);
                self.mk_eq(ls, rs)
            }
            // Every other kind: keep the node (its children were already
            // simplified by the bottom-up pass that runs first).
            _ => t,
        }
    }

    fn ctx_and(
        &mut self,
        args: SmallVec<[TermId; 4]>,
        ctx: &mut FxHashMap<TermId, bool>,
        fuel: &mut u32,
        sub_atoms: &FxHashMap<TermId, Option<FxHashSet<TermId>>>,
        memo: &mut FxHashMap<(TermId, u64), TermId>,
        depth: u32,
    ) -> TermId {
        // Each conjunct asserts its atom's polarity; the REST simplify
        // under it.  The extensions unwind exactly: an entry a parent had
        // set is restored, a FRESH entry is removed — a conjunct's
        // polarity is not valid outside the conjunction.  (The first
        // version of this unwind only restored overwritten entries and
        // skipped fresh ones — the leak survived the conjunction's end
        // and poisoned every later sibling walk in the enclosing scope:
        // the Or arm's next disjunct walked under a conjunct's polarity
        // and `(or (and p q) p)` simplified to `true` — a live
        // false-simplify on main, caught by the solve-rules equivalence
        // fuzzer.)
        /// Unwind one extension: restore the previous polarity, or
        /// remove the entry when this conjunction created it.
        fn unwind_one(ctx: &mut FxHashMap<TermId, bool>, ext: (TermId, Option<bool>)) {
            match ext.1 {
                Some(prev) => {
                    ctx.insert(ext.0, prev);
                }
                None => {
                    ctx.remove(&ext.0);
                }
            }
        }
        let mut simplified: SmallVec<[TermId; 4]> = SmallVec::new();
        let mut unwind: Vec<(TermId, Option<bool>)> = Vec::new();
        for a in args {
            if let Some(false) = self.ctx_value(a, ctx) {
                for ext in unwind.into_iter().rev() {
                    unwind_one(ctx, ext);
                }
                return self.false_id;
            }
            if let Some(true) = self.ctx_value(a, ctx) {
                continue;
            }
            let s = self.ctx_walk(a, ctx, fuel, sub_atoms, memo, depth - 1);
            match self.get(s).map(|d| &d.kind) {
                Some(TermKind::False) => {
                    for ext in unwind.into_iter().rev() {
                        unwind_one(ctx, ext);
                    }
                    return self.false_id;
                }
                Some(TermKind::True) => continue,
                _ => {}
            }
            simplified.push(s);
            if let Some((atom, pol)) = self.atom_polarity(s) {
                let prev = ctx.insert(atom, pol);
                unwind.push((atom, prev));
            }
        }
        for ext in unwind.into_iter().rev() {
            unwind_one(ctx, ext);
        }
        self.absorb_literals(simplified, true)
    }

    /// z3 `bool_rewriter::mk_nflat_and_core`/`mk_nflat_or_core` parity,
    /// at the SIMPLIFIER layer (z3's absorption lives in its rewriter,
    /// never in `ast_manager`'s constructors — builder-level folding here
    /// perturbed the solver's term shapes and broke MBQI's convergence
    /// pins, so the rule is harness-only): over the flattened `args`, a
    /// duplicate literal drops and a literal meeting its negation
    /// decides the connective (`X ∧ ¬X ≡ false`, `X ∨ ¬X ≡ true` —
    /// classical, for ANY `X`).  Returns the folded term.
    fn absorb_literals(&mut self, args: SmallVec<[TermId; 4]>, conjunction: bool) -> TermId {
        // Flatten same-connective children FIRST (z3's
        // `mk_flat_and_core` → `mk_nflat_and_core` pipeline): complements
        // hidden across nested levels (`And(And(X Y) ¬X)`) are visible
        // only in the flattened view — absorbing per level without
        // flattening misses them (the large nec-smt member's top-level
        // and-tree is nested binary).
        let mut flat: SmallVec<[TermId; 4]> = SmallVec::with_capacity(args.len());
        for a in args {
            let inner = if conjunction {
                match self.get(a).map(|d| &d.kind) {
                    Some(TermKind::And(inner)) => Some(inner.clone()),
                    Some(TermKind::True) => {
                        continue;
                    }
                    Some(TermKind::False) => return self.false_id,
                    _ => None,
                }
            } else {
                match self.get(a).map(|d| &d.kind) {
                    Some(TermKind::Or(inner)) => Some(inner.clone()),
                    Some(TermKind::False) => {
                        continue;
                    }
                    Some(TermKind::True) => return self.true_id,
                    _ => None,
                }
            };
            match inner {
                Some(children) => flat.extend(children.iter().copied()),
                None => flat.push(a),
            }
        }
        let args = flat;
        if args.len() < 2 {
            return if conjunction {
                self.mk_and(args)
            } else {
                self.mk_or(args)
            };
        }
        /// Beyond this many args the linear membership scans switch to
        /// hash sets.
        const LINEAR_ABSORB_MAX: usize = 32;
        let n = args.len();
        let mut kept: SmallVec<[TermId; 4]> = SmallVec::with_capacity(n);
        // pos: positive literals kept so far; neg: the inner atoms of
        // negated literals kept so far.  A complement decides the
        // connective outright (false for and, true for or).
        let mut decided: Option<bool> = None;
        if n <= LINEAR_ABSORB_MAX {
            let mut pos: SmallVec<[TermId; 8]> = SmallVec::new();
            let mut neg: SmallVec<[TermId; 8]> = SmallVec::new();
            for &a in args.iter() {
                if let Some(TermKind::Not(x)) = self.get(a).map(|d| &d.kind) {
                    if neg.contains(x) {
                        continue;
                    }
                    if pos.contains(x) {
                        decided = Some(!conjunction);
                        break;
                    }
                    neg.push(*x);
                } else {
                    if pos.contains(&a) {
                        continue;
                    }
                    if neg.contains(&a) {
                        decided = Some(!conjunction);
                        break;
                    }
                    pos.push(a);
                }
                kept.push(a);
            }
        } else {
            let mut pos: FxHashSet<TermId> = FxHashSet::default();
            let mut neg: FxHashSet<TermId> = FxHashSet::default();
            for &a in args.iter() {
                if let Some(TermKind::Not(x)) = self.get(a).map(|d| &d.kind) {
                    if !neg.insert(*x) {
                        continue;
                    }
                    if pos.contains(x) {
                        decided = Some(!conjunction);
                        break;
                    }
                } else {
                    if !pos.insert(a) {
                        continue;
                    }
                    if neg.contains(&a) {
                        decided = Some(!conjunction);
                        break;
                    }
                }
                kept.push(a);
            }
        }
        match decided {
            Some(v) => self.mk_bool(v),
            None => {
                if conjunction {
                    self.mk_and(kept)
                } else {
                    self.mk_or(kept)
                }
            }
        }
    }

    /// The children `simplify_cached` should recurse into for `id`, or none
    /// for a leaf, an unrecognized term, or any kind the simplifier does
    /// not rewrite (matching the prior `Some(_) => id` catch-all, which
    /// never visited such a node's children at all).
    fn simplifiable_children(&self, id: TermId) -> SmallVec<[TermId; 4]> {
        match self.get(id).map(|t| &t.kind) {
            None
            | Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::Var(_),
            ) => SmallVec::new(),
            Some(TermKind::Not(a) | TermKind::Neg(a)) => [*a].into_iter().collect(),
            Some(
                TermKind::And(args)
                | TermKind::Or(args)
                | TermKind::Add(args)
                | TermKind::Mul(args),
            ) => args.iter().copied().collect(),
            Some(
                TermKind::Implies(a, b)
                | TermKind::Eq(a, b)
                | TermKind::Sub(a, b)
                | TermKind::Lt(a, b)
                | TermKind::Le(a, b)
                | TermKind::Gt(a, b)
                | TermKind::Ge(a, b),
            ) => [*a, *b].into_iter().collect(),
            Some(TermKind::Ite(c, t, e)) => [*c, *t, *e].into_iter().collect(),
            Some(_) => SmallVec::new(),
        }
    }

    /// Rebuild `id` from its already-simplified children (see
    /// `simplify_cached`), applying the same rewrite/constant-folding rule
    /// the prior recursive match arm used for each kind.
    fn combine_simplified(&mut self, id: TermId, cache: &FxHashMap<TermId, TermId>) -> TermId {
        let sub =
            |cache: &FxHashMap<TermId, TermId>, t: TermId| cache.get(&t).copied().unwrap_or(t);
        match self.get(id).map(|t| t.kind.clone()) {
            None
            | Some(
                TermKind::True
                | TermKind::False
                | TermKind::IntConst(_)
                | TermKind::RealConst(_)
                | TermKind::BitVecConst { .. }
                | TermKind::Var(_),
            ) => id,

            Some(TermKind::Not(arg)) => {
                let new_arg = sub(cache, arg);
                self.mk_not(new_arg)
            }
            Some(TermKind::And(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.absorb_literals(new_args, true)
            }
            Some(TermKind::Or(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.absorb_literals(new_args, false)
            }
            Some(TermKind::Implies(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.mk_implies(new_lhs, new_rhs)
            }
            Some(TermKind::Eq(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                // Guard-equality elimination (z3 `mk_eq_core`'s ite
                // rules): solve the equality over its ite conditions
                // BEFORE falling back to the plain node.
                if let Some(solved) = self.eq_ite_rules(new_lhs, new_rhs) {
                    return solved;
                }
                self.mk_eq(new_lhs, new_rhs)
            }
            Some(TermKind::Ite(cond, then_br, else_br)) => {
                let new_cond = sub(cache, cond);
                let new_then = sub(cache, then_br);
                let new_else = sub(cache, else_br);
                self.rewrite_ite(new_cond, new_then, new_else)
            }
            Some(TermKind::Add(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.simplify_add(new_args)
            }
            Some(TermKind::Sub(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_sub(new_lhs, new_rhs)
            }
            Some(TermKind::Mul(args)) => {
                let new_args: SmallVec<[TermId; 4]> = args.iter().map(|&a| sub(cache, a)).collect();
                self.simplify_mul(new_args)
            }
            Some(TermKind::Neg(arg)) => {
                let new_arg = sub(cache, arg);
                self.simplify_neg(new_arg)
            }
            Some(TermKind::Lt(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_lt(new_lhs, new_rhs)
            }
            Some(TermKind::Le(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_le(new_lhs, new_rhs)
            }
            Some(TermKind::Gt(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_gt(new_lhs, new_rhs)
            }
            Some(TermKind::Ge(lhs, rhs)) => {
                let new_lhs = sub(cache, lhs);
                let new_rhs = sub(cache, rhs);
                self.simplify_ge(new_lhs, new_rhs)
            }
            // Everything else: left untouched, matching the prior
            // recursive catch-all (its children are never visited, so
            // there is nothing to gather from `cache` for them either).
            Some(_) => id,
        }
    }

    /// Simplify addition with constant folding.
    fn simplify_add(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let mut constant_sum = BigInt::from(0);
        let mut other_args: SmallVec<[TermId; 4]> = SmallVec::new();

        for arg in args {
            if let Some(TermKind::IntConst(n)) = self.get(arg).map(|t| &t.kind) {
                constant_sum += n;
            } else {
                other_args.push(arg);
            }
        }

        let zero = BigInt::from(0);
        if other_args.is_empty() {
            return self.intern(TermKind::IntConst(constant_sum), self.sorts.int_sort);
        }

        if constant_sum != zero {
            other_args.push(self.intern(TermKind::IntConst(constant_sum), self.sorts.int_sort));
        }

        if other_args.len() == 1 {
            return other_args[0];
        }

        self.mk_add(other_args)
    }

    /// Simplify subtraction with constant folding.
    fn simplify_sub(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let zero = BigInt::from(0);
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => {
                self.intern(TermKind::IntConst(a - b), self.sorts.int_sort)
            }
            (_, Some(TermKind::IntConst(n))) if n == zero => lhs,
            (Some(TermKind::IntConst(n)), _) if n == zero => self.simplify_neg(rhs),
            _ => self.mk_sub(lhs, rhs),
        }
    }

    /// Simplify multiplication with constant folding.
    fn simplify_mul(&mut self, args: SmallVec<[TermId; 4]>) -> TermId {
        let mut constant_product = BigInt::from(1);
        let mut other_args: SmallVec<[TermId; 4]> = SmallVec::new();
        let zero = BigInt::from(0);
        let one = BigInt::from(1);

        for arg in args {
            if let Some(TermKind::IntConst(n)) = self.get(arg).map(|t| &t.kind) {
                if *n == zero {
                    return self.mk_int(0);
                }
                constant_product *= n;
            } else {
                other_args.push(arg);
            }
        }

        if other_args.is_empty() {
            return self.intern(TermKind::IntConst(constant_product), self.sorts.int_sort);
        }

        if constant_product == zero {
            return self.mk_int(0);
        }

        if constant_product != one {
            other_args.insert(
                0,
                self.intern(TermKind::IntConst(constant_product), self.sorts.int_sort),
            );
        }

        if other_args.len() == 1 {
            return other_args[0];
        }

        self.mk_mul(other_args)
    }

    /// Simplify negation.
    fn simplify_neg(&mut self, arg: TermId) -> TermId {
        match self.get(arg).map(|t| t.kind.clone()) {
            Some(TermKind::IntConst(n)) => self.intern(TermKind::IntConst(-n), self.sorts.int_sort),
            Some(TermKind::Neg(inner)) => inner,
            _ => {
                let sort = self.get(arg).map_or(self.sorts.int_sort, |t| t.sort);
                self.intern(TermKind::Neg(arg), sort)
            }
        }
    }

    /// Simplify less-than with constant comparison and reflexivity.
    fn simplify_lt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a < a is always False
        if lhs == rhs {
            return self.false_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a < b),
            _ => {
                if let Some(solved) = self.cmp_ite_rule(CmpOp::Lt, lhs, rhs) {
                    return solved;
                }
                self.mk_lt(lhs, rhs)
            }
        }
    }

    /// Simplify less-or-equal with constant comparison and reflexivity.
    fn simplify_le(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a <= a is always True
        if lhs == rhs {
            return self.true_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a <= b),
            _ => {
                if let Some(solved) = self.cmp_ite_rule(CmpOp::Le, lhs, rhs) {
                    return solved;
                }
                self.mk_le(lhs, rhs)
            }
        }
    }

    /// Simplify greater-than with constant comparison and reflexivity.
    fn simplify_gt(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a > a is always False
        if lhs == rhs {
            return self.false_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a > b),
            _ => {
                if let Some(solved) = self.cmp_ite_rule(CmpOp::Gt, lhs, rhs) {
                    return solved;
                }
                self.mk_gt(lhs, rhs)
            }
        }
    }

    /// Simplify greater-or-equal with constant comparison and reflexivity.
    fn simplify_ge(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        // Reflexivity: a >= a is always True
        if lhs == rhs {
            return self.true_id;
        }
        match (
            self.get(lhs).map(|t| t.kind.clone()),
            self.get(rhs).map(|t| t.kind.clone()),
        ) {
            (Some(TermKind::IntConst(a)), Some(TermKind::IntConst(b))) => self.mk_bool(a >= b),
            _ => {
                if let Some(solved) = self.cmp_ite_rule(CmpOp::Ge, lhs, rhs) {
                    return solved;
                }
                self.mk_ge(lhs, rhs)
            }
        }
    }

    /// z3 `arith_rewriter::mk_le_ge_eq_core`'s ite rules, extended to the
    /// strict comparisons (z3 normalizes those through the non-strict
    /// forms; the direct analogue keeps the residual's operator).
    ///
    /// `((ite c t e) ⊙ k)` with `k` a value and a NUMERAL branch decides
    /// that branch against `k`, so the comparison distributes over the
    /// guard instead of nesting under it:
    /// * `t ⊙ k` true  → `(or c (e ⊙ k))`  (the then-path already
    ///   satisfies the comparison);
    /// * `t ⊙ k` false → `(and ¬c (e ⊙ k))` (the then-path is excluded);
    /// * the `e`-numeral case is symmetric (`¬c` / `c`).
    ///
    /// The branches were already simplified bottom-up when this fires
    /// (the residual is built with the plain `mk_*` constructors — no
    /// re-descent, no native recursion over the chain: the 724 KB
    /// nec-smt members nest selects thousands deep).
    /// `None` when no branch is decidable.
    fn cmp_ite_rule(&mut self, op: CmpOp, lhs: TermId, rhs: TermId) -> Option<TermId> {
        let Some(TermKind::Ite(c, t, e)) = self.get(lhs).map(|d| d.kind.clone()) else {
            return None;
        };
        if !self.is_value(rhs) {
            return None;
        }
        let mk_residual = |tm: &mut Self, a: TermId, b: TermId| match op {
            CmpOp::Lt => tm.mk_lt(a, b),
            CmpOp::Le => tm.mk_le(a, b),
            CmpOp::Gt => tm.mk_gt(a, b),
            CmpOp::Ge => tm.mk_ge(a, b),
        };
        // The then-branch decides: t ⊙ k.
        if let Some(true) = self.cmp_decide(op, t, rhs) {
            let rest = mk_residual(self, e, rhs);
            return Some(self.mk_or([c, rest]));
        }
        if let Some(false) = self.cmp_decide(op, t, rhs) {
            let nc = self.mk_not(c);
            let rest = mk_residual(self, e, rhs);
            return Some(self.mk_and([nc, rest]));
        }
        // The else-branch decides: e ⊙ k.
        if let Some(true) = self.cmp_decide(op, e, rhs) {
            let nc = self.mk_not(c);
            let rest = mk_residual(self, t, rhs);
            return Some(self.mk_or([nc, rest]));
        }
        if let Some(false) = self.cmp_decide(op, e, rhs) {
            let rest = mk_residual(self, t, rhs);
            return Some(self.mk_and([c, rest]));
        }
        None
    }

    /// Decide `a ⊙ b` when both sides are integer numerals — the exact
    /// constant fold the comparison simplifiers perform (no descent:
    /// callers pass already-simplified branches).
    fn cmp_decide(&self, op: CmpOp, a: TermId, b: TermId) -> Option<bool> {
        let (Some(TermKind::IntConst(x)), Some(TermKind::IntConst(y))) =
            (self.get(a).map(|d| &d.kind), self.get(b).map(|d| &d.kind))
        else {
            return None;
        };
        Some(match op {
            CmpOp::Lt => x < y,
            CmpOp::Le => x <= y,
            CmpOp::Gt => x > y,
            CmpOp::Ge => x >= y,
        })
    }
}
