//! The transcendental (δ-ICP) dispatch: dReal's dPLL ∘ ICP architecture.
//!
//! [`Solver::dispatch_trans_solver`] owns goals whose arithmetic mentions a
//! transcendental function (`exp`, `log`, `sin`, `cos`, `atan`, `sqrt`):
//!
//! 1. the Boolean skeleton of the assertions is Tseitin-encoded over its
//!    *arithmetic atoms* into a private `nixie-sat` instance;
//! 2. each satisfying atom assignment is compiled to a conjunctive
//!    [`TransProblem`] and decided by interval constraint propagation
//!    (`nixie_theories::trans`); numeric `ite`s are resolved per
//!    assignment (the branch is selected by evaluating the condition
//!    under the assignment);
//! 3. an ICP refutation of an assignment becomes a blocking clause over
//!    the assignment's literals (δ-unsat of a conjunction implies its
//!    unsat, so the clause is a valid theory lemma); a δ-witness ends the
//!    search with `Sat` (published as **delta-sat**); an undecided
//!    assignment ends it with the honest `Unknown`.
//!
//! The whole-goal gate at the top declines anything outside the decidable
//! fragment — quantifiers, uninterpreted functions, arrays, strings, FP,
//! datatypes, integer variables, `distinct` — rather than solving a weaker
//! problem than the one the user posed.
//!
//! Verdict soundness summary (details in `nixie-theories/src/trans/`):
//! * `Unsat` requires every atom assignment refuted by a δ-weakened
//!   emptiness proof, and δ-unsat ⟹ unsat;
//! * `Sat` publishes only re-verified witness values, and is a δ-model (the
//!   CLI prints `delta-sat`), never a claimed exact model;
//! * everything else is `Unknown`.

use nixie_core::ast::{TermId, TermKind, TermManager};
use nixie_sat::{Lit, Solver as SatSolver, Var};
use nixie_theories::trans::{Cmp, TransOptions, TransOutcome, TransProblem};
use num_rational::Rational64;
use num_traits::{ToPrimitive, Zero};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use super::Solver;
use super::types::{Model, SolverResult};

/// Hard round bound for the dPLL loop (deterministic; the wall-clock
/// timeout system still applies above this layer).
const MAX_DPLL_ROUNDS: usize = 20_000;

/// Does the DAG rooted at `term` mention a transcendental function?
/// Explicit stack; `TermId` hash-consing prunes shared subterms.
pub(super) fn term_has_trans(term: TermId, manager: &TermManager) -> bool {
    use rustc_hash::FxHashSet;
    let mut stack: Vec<TermId> = vec![term];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(node) = manager.get(t) else {
            continue;
        };
        match &node.kind {
            TermKind::Exp(_)
            | TermKind::Log(_)
            | TermKind::Sin(_)
            | TermKind::Cos(_)
            | TermKind::Atan(_)
            | TermKind::Sqrt(_) => return true,
            _ => {
                let mut kids = Vec::new();
                super::term_walk::collect_structural_children(&node.kind, &mut kids);
                stack.extend(kids);
            }
        }
    }
    false
}

impl Solver {
    /// Dispatch a transcendental goal to the δ-ICP engine.  `None` = not
    /// ours (no trans terms) or declined fragment — the caller falls
    /// through (the arithmetic honesty gate then answers `Unknown`).
    pub(super) fn dispatch_trans_solver(
        &mut self,
        manager: &mut TermManager,
    ) -> Option<SolverResult> {
        if !self.assertions.iter().any(|&a| term_has_trans(a, manager)) {
            return None;
        }
        // Declared-logics gate: the open logics (`ALL`/unset) and the
        // dedicated `QF_NRT`; a closed logic (e.g. `QF_LRA`) keeps its
        // contract and the honesty gate answers `Unknown` for the trans
        // atoms.
        let logic = self.logic.as_deref().unwrap_or("ALL");
        if logic != "ALL" && logic != "QF_NRT" {
            return None;
        }

        // ---- Boolean abstraction over the arithmetic atoms. ----
        let mut build = TransBuild::new();
        let mut root_units: Vec<i32> = Vec::new();
        for &a in &self.assertions {
            match build.tseitin(a, manager, true) {
                TseitinOut::Lit(l) => root_units.push(l),
                TseitinOut::Const(true) => {}
                TseitinOut::Const(false) => {
                    self.trans_dispatch_answered = true;
                    return Some(SolverResult::Unsat);
                }
                TseitinOut::Declined => return None,
            }
        }
        if build.atoms.is_empty() {
            // Trans terms exist but no arithmetic atom constrains them:
            // nothing for the ICP to decide.  The ordinary search owns the
            // goal (the honesty gate still guards the trans atoms).
            return None;
        }

        let n_atoms = build.atoms.len();
        if n_atoms >= AUX_BASE {
            // Absurd atom count for this fragment; decline honestly.
            return None;
        }
        let n_vars = n_atoms + build.aux;
        let remap = |l: i32| -> i32 {
            let v = (l.unsigned_abs() as usize) - 1;
            let sign = if l < 0 { -1i32 } else { 1 };
            let nv = if v >= AUX_BASE {
                n_atoms + (v - AUX_BASE)
            } else {
                v
            };
            sign * (nv as i32 + 1)
        };
        let mut sat = SatSolver::new();
        for _ in 0..n_vars {
            let _ = sat.new_var();
        }
        let mut trivially_unsat = false;
        for l in &root_units {
            if !sat.add_clause_dimacs(&[remap(*l)]) {
                trivially_unsat = true;
                break;
            }
        }
        if !trivially_unsat {
            for clause in &build.clauses {
                let mapped: SmallVec<[i32; 4]> = clause.iter().map(|&l| remap(l)).collect();
                if !sat.add_clause_dimacs(&mapped) {
                    trivially_unsat = true;
                    break;
                }
            }
        }
        if trivially_unsat {
            self.trans_dispatch_answered = true;
            return Some(SolverResult::Unsat);
        }

        let opts = TransOptions {
            delta: trans_delta_of(&self.config),
            ..TransOptions::default()
        };

        // ---- dPLL ∘ ICP. ----
        for round in 0..MAX_DPLL_ROUNDS {
            let (result, _) = sat.solve_with_assumptions(&[]);
            #[cfg(feature = "std")]
            if std::env::var_os("NIXIE_TRANS_DEBUG").is_some() {
                eprintln!("[trans] sat round {round}: {result:?}");
            }
            match result {
                nixie_sat::SolverResult::Unsat => {
                    // Every atom assignment was refuted by valid theory
                    // lemmas: a sound unsat.
                    self.trans_dispatch_answered = true;
                    return Some(SolverResult::Unsat);
                }
                nixie_sat::SolverResult::Unknown => return Some(SolverResult::Unknown),
                nixie_sat::SolverResult::Sat => {}
            }
            let mut assignment: Vec<bool> = Vec::with_capacity(n_vars);
            let mut all_decided = true;
            for i in 0..n_vars {
                match sat.model_value(Var::new(i as u32)) {
                    nixie_sat::LBool::True => assignment.push(true),
                    nixie_sat::LBool::False => assignment.push(false),
                    _ => {
                        all_decided = false;
                        break;
                    }
                }
            }
            if !all_decided {
                return Some(SolverResult::Unknown);
            }
            // Compile the conjunction for this assignment (ite branches
            // resolved under it).
            let mut ctx = AssignmentCtx {
                build: &build,
                values: &assignment,
                memo: FxHashMap::default(),
            };
            let mut prob = TransProblem::default();
            let mut cache = FxHashMap::default();
            let mut atom_terms: Vec<TermId> = Vec::with_capacity(n_atoms);
            let mut ok = true;
            for (i, &(lhs, rhs, kind)) in build.atoms.iter().enumerate() {
                let positive = assignment[i];
                let cmp = normalize_cmp(kind, positive);
                atom_terms.push(build.atom_key(i));
                let Some((root, rhs_const, cmp)) =
                    ctx.constraint_for(lhs, rhs, cmp, manager, &mut prob, &mut cache)
                else {
                    ok = false;
                    break;
                };
                prob.add_constraint(root, rhs_const, cmp, opts.delta);
            }
            if !ok {
                return Some(SolverResult::Unknown);
            }
            #[cfg(feature = "std")]
            if std::env::var_os("NIXIE_TRANS_DEBUG").is_some() {
                for (i, &(l, r, k)) in build.atoms.iter().enumerate() {
                    let desc = |t: TermId| {
                        manager
                            .get(t)
                            .map(|x| {
                                format!(
                                    "{:?}{}",
                                    x.kind,
                                    if let TermKind::Var(n) = &x.kind {
                                        format!(":{}", manager.resolve_str(*n))
                                    } else {
                                        String::new()
                                    }
                                )
                            })
                            .unwrap_or_else(|| "?".into())
                    };
                    eprintln!(
                        "[trans] atom {i}: {} {} {} (key {:?})",
                        desc(l),
                        match k {
                            0 => "<=",
                            1 => "<",
                            2 => ">=",
                            3 => ">",
                            _ => "=",
                        },
                        desc(r),
                        build.atom_key(i)
                    );
                }
                eprintln!("[trans] assignment={:?}", assignment);
            }
            #[cfg(feature = "std")]
            let stats_t0 = std::time::Instant::now();
            let outcome = nixie_theories::trans::solve_conjunction(&mut prob, &opts);
            #[cfg(feature = "std")]
            if std::env::var_os("NIXIE_TRANS_STATS").is_some() {
                eprintln!(
                    "[trans-stats] round {round}: {:?} in {:?}",
                    nixie_theories::trans::last_stats(),
                    stats_t0.elapsed()
                );
            }
            match outcome {
                TransOutcome::DeltaSat { values } => {
                    self.trans_dispatch_answered = true;
                    self.trans_delta_sat = true;
                    self.install_trans_model(
                        &prob,
                        &values,
                        &assignment,
                        &atom_terms,
                        &build,
                        manager,
                    );
                    return Some(SolverResult::Sat);
                }
                TransOutcome::Unsat { culprits } => {
                    #[cfg(feature = "std")]
                    if std::env::var_os("NIXIE_TRANS_DEBUG").is_some() {
                        eprintln!("[trans] ICP unsat, culprits={culprits:?}");
                    }
                    // Theory lemma: ¬(conjunction of the implicated atoms
                    // under this assignment).  Culprit constraint indices
                    // are atom indices (constraints were added in atom
                    // order).  Without provenance, block the whole
                    // assignment — always valid.
                    let indices: Vec<usize> = if culprits.is_empty() {
                        (0..n_atoms).collect()
                    } else {
                        culprits.iter().map(|&c| c as usize).collect()
                    };
                    let clause: SmallVec<[Lit; 4]> = indices
                        .into_iter()
                        .filter(|&i| i < n_atoms)
                        .map(|i| {
                            if assignment[i] {
                                Lit::neg(Var::new(i as u32))
                            } else {
                                Lit::pos(Var::new(i as u32))
                            }
                        })
                        .collect();
                    let added = !clause.is_empty() && sat.add_clause(clause.iter().copied());
                    #[cfg(feature = "std")]
                    if std::env::var_os("NIXIE_TRANS_DEBUG").is_some() {
                        eprintln!("[trans] blocking clause {clause:?} added={added}");
                    }
                    if !added {
                        self.trans_dispatch_answered = true;
                        return Some(SolverResult::Unsat);
                    }
                }
                TransOutcome::Unknown => return Some(SolverResult::Unknown),
            }
        }
        // Round budget: honest Unknown.
        Some(SolverResult::Unknown)
    }

    /// Publish the δ-witness: Real variables at their re-verified values,
    /// arithmetic atoms (and skeleton Booleans) at the assignment's truth
    /// values.
    fn install_trans_model(
        &mut self,
        prob: &TransProblem,
        values: &[Rational64],
        assignment: &[bool],
        atom_terms: &[TermId],
        build: &TransBuild,
        manager: &mut TermManager,
    ) {
        let mut model = Model::new();
        for (slot, &term) in prob.var_terms().iter().enumerate() {
            let v = values.get(slot).copied().unwrap_or_else(Rational64::zero);
            let value_term = manager.mk_real(v);
            model.set(term, value_term);
        }
        for (i, &atom) in atom_terms.iter().enumerate() {
            let value = if assignment.get(i).copied().unwrap_or(true) {
                manager.mk_true()
            } else {
                manager.mk_false()
            };
            model.set(atom, value);
        }
        // The skeleton's free Boolean variables publish the values the
        // witness actually used — an `ite` condition completed to a
        // default would contradict the branch the Real values verify
        // against (the t6 class: x = ite(b,4,9) with x≈4 must print b =
        // true).
        let n_atoms = atom_terms.len();
        for (&t, &aux) in build.bool_vars.iter() {
            // `aux` is the AUX_BASE-offset encoding index; the assignment
            // vector uses the remapped `n_atoms + k` numbering.
            let k = aux
                .checked_sub(AUX_BASE)
                .map(|k| n_atoms + k)
                .unwrap_or(aux);
            let v = assignment.get(k).copied().unwrap_or(true);
            let value = if v {
                manager.mk_true()
            } else {
                manager.mk_false()
            };
            model.set(t, value);
        }
        self.model = Some(model);
    }
}

/// The configured δ as `f64` (nanos in the config for `Eq`-compatibility).
fn trans_delta_of(config: &super::types::SolverConfig) -> f64 {
    (config.trans_delta_nanos.max(0) as f64) * 1e-9
}

impl Solver {
    /// Whether the last answered `Sat` was a δ-satisfiability witness (for
    /// the context layer's `delta-sat` reporting).
    #[must_use]
    pub fn last_answer_was_delta_sat(&self) -> bool {
        self.trans_delta_sat
    }
}

// ===========================================================================
// Tseitin layer over arithmetic atoms
// ===========================================================================

/// Result of encoding a subformula.
enum TseitinOut {
    /// A literal over the `±(var+1)` protocol; vars index atoms first,
    /// then auxiliaries.
    Lit(i32),
    /// The subformula folded to a constant.
    Const(bool),
    /// Outside the decidable fragment.
    Declined,
}

/// Comparison kinds: 0 = ≤, 1 = <, 2 = ≥, 3 = >, 4 = =.
type AtomKind = u8;

struct TransBuild {
    /// Clauses over the `i32` literal protocol.
    clauses: Vec<SmallVec<[i32; 4]>>,
    /// Canonical comparison term → atom index.
    atom_index: FxHashMap<TermId, usize>,
    /// `(lhs, rhs, kind)` per atom.
    atoms: Vec<(TermId, TermId, AtomKind)>,
    /// The canonical comparison `TermId` per atom (for the model).
    atom_keys: Vec<TermId>,
    /// Free Boolean variables → their aux var index (n_atoms + k).
    bool_vars: FxHashMap<TermId, usize>,
    aux: usize,
}

/// Aux (Tseitin) variables are numbered from this base DURING encoding —
/// atom indices are discovered mid-walk, so any in-band numbering would
/// collide with them (the first version literally fused the or-gate's
/// variable with atom 0 and its root unit forced that atom true at level
/// 0).  The literals are remapped to the contiguous
/// `n_atoms..n_atoms+aux` range when the SAT instance is built.
const AUX_BASE: usize = 1 << 24;

fn lit_of(var: usize, positive: bool) -> i32 {
    if positive {
        (var + 1) as i32
    } else {
        -((var + 1) as i32)
    }
}

/// A literal or one of the two constants.
#[derive(Clone, Copy, PartialEq)]
enum LitOrConst {
    L(i32),
    T,
    F,
}

impl TransBuild {
    fn new() -> Self {
        Self {
            clauses: Vec::new(),
            atom_index: FxHashMap::default(),
            atoms: Vec::new(),
            atom_keys: Vec::new(),
            bool_vars: FxHashMap::default(),
            aux: 0,
        }
    }

    fn atom_key(&self, i: usize) -> TermId {
        self.atom_keys[i]
    }

    fn fresh_aux(&mut self, _n_atoms: usize) -> usize {
        let v = AUX_BASE + self.aux;
        self.aux += 1;
        v
    }

    fn intern_atom(&mut self, lhs: TermId, rhs: TermId, kind: AtomKind, key: TermId) -> usize {
        if let Some(&i) = self.atom_index.get(&key) {
            return i;
        }
        let i = self.atoms.len();
        self.atoms.push((lhs, rhs, kind));
        self.atom_keys.push(key);
        self.atom_index.insert(key, i);
        i
    }

    /// Tseitin-encode `term` under polarity `pos`.  Explicit stack, no
    /// native recursion over user DAGs (AGENTS.md); `pending` carries
    /// child results to the combine frames in argument order.
    #[allow(clippy::too_many_lines)]
    fn tseitin(&mut self, term: TermId, manager: &mut TermManager, pos: bool) -> TseitinOut {
        enum Frame {
            Encode(TermId, bool),
            CombineAnd(bool, usize),
            CombineOr(bool, usize),
            CombineIte(bool),
            CombineEqBool(bool),
            CombineNeg,
        }
        let mut pending: Vec<LitOrConst> = Vec::new();
        let mut stack: Vec<Frame> = vec![Frame::Encode(term, pos)];
        let n_atoms = self.atoms.len();
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Encode(t, p) => {
                    let Some(node) = manager.get(t) else {
                        return TseitinOut::Declined;
                    };
                    let kind = node.kind.clone();
                    match &kind {
                        TermKind::True => pending.push(LitOrConst::T),
                        TermKind::False => pending.push(LitOrConst::F),
                        TermKind::Var(_) if node.sort == manager.sorts.bool_sort => {
                            let v = if let Some(&v) = self.bool_vars.get(&t) {
                                v
                            } else {
                                let v = self.fresh_aux(n_atoms);
                                self.bool_vars.insert(t, v);
                                v
                            };
                            pending.push(LitOrConst::L(lit_of(v, p)));
                        }
                        TermKind::Not(a) => stack.push(Frame::Encode(*a, !p)),
                        TermKind::And(args) => {
                            stack.push(Frame::CombineAnd(p, args.len()));
                            for &a in args.iter().rev() {
                                stack.push(Frame::Encode(a, true));
                            }
                        }
                        TermKind::Or(args) => {
                            stack.push(Frame::CombineOr(p, args.len()));
                            for &a in args.iter().rev() {
                                stack.push(Frame::Encode(a, true));
                            }
                        }
                        TermKind::Implies(a, b) => {
                            // a → b ≡ ¬a ∨ b
                            stack.push(Frame::CombineOr(p, 2));
                            stack.push(Frame::Encode(*b, true));
                            stack.push(Frame::Encode(*a, false));
                        }
                        TermKind::Xor(a, b) => {
                            // a ⊕ b ≡ ¬(a = b)
                            stack.push(Frame::CombineNeg);
                            stack.push(Frame::CombineEqBool(true));
                            stack.push(Frame::Encode(*b, true));
                            stack.push(Frame::Encode(*a, true));
                        }
                        TermKind::Ite(c, a, b) if node.sort == manager.sorts.bool_sort => {
                            stack.push(Frame::CombineIte(p));
                            stack.push(Frame::Encode(*b, true));
                            stack.push(Frame::Encode(*a, true));
                            stack.push(Frame::Encode(*c, true));
                        }
                        TermKind::Eq(a, b) => {
                            let a_bool = manager
                                .get(*a)
                                .is_some_and(|x| x.sort == manager.sorts.bool_sort);
                            if a_bool {
                                stack.push(Frame::CombineEqBool(p));
                                stack.push(Frame::Encode(*b, true));
                                stack.push(Frame::Encode(*a, true));
                            } else {
                                let key = manager.mk_eq(*a, *b);
                                let v = self.intern_atom(*a, *b, 4, key);
                                pending.push(LitOrConst::L(lit_of(v, p)));
                            }
                        }
                        TermKind::Lt(a, b) => {
                            let key = manager.mk_lt(*a, *b);
                            let v = self.intern_atom(*a, *b, 1, key);
                            pending.push(LitOrConst::L(lit_of(v, p)));
                        }
                        TermKind::Le(a, b) => {
                            let key = manager.mk_le(*a, *b);
                            let v = self.intern_atom(*a, *b, 0, key);
                            pending.push(LitOrConst::L(lit_of(v, p)));
                        }
                        TermKind::Gt(a, b) => {
                            let key = manager.mk_gt(*a, *b);
                            let v = self.intern_atom(*a, *b, 3, key);
                            pending.push(LitOrConst::L(lit_of(v, p)));
                        }
                        TermKind::Ge(a, b) => {
                            let key = manager.mk_ge(*a, *b);
                            let v = self.intern_atom(*a, *b, 2, key);
                            pending.push(LitOrConst::L(lit_of(v, p)));
                        }
                        _ => return TseitinOut::Declined,
                    }
                }
                Frame::CombineAnd(p, n) => {
                    let kids = take_pending(&mut pending, n);
                    // Constant filtering: F kills, T drops.
                    if kids.contains(&LitOrConst::F) {
                        pending.push(LitOrConst::F);
                        continue;
                    }
                    let lits: Vec<i32> = kids
                        .into_iter()
                        .filter_map(|k| match k {
                            LitOrConst::L(l) => Some(l),
                            LitOrConst::T => None,
                            LitOrConst::F => unreachable!("filtered above"),
                        })
                        .collect();
                    if lits.is_empty() {
                        pending.push(LitOrConst::T);
                        continue;
                    }
                    if lits.len() == 1 {
                        pending.push(LitOrConst::L(lits[0]));
                        continue;
                    }
                    let phi = self.fresh_aux(n_atoms);
                    // φ ↔ ∧lits:  φ → lᵢ (¬φ ∨ lᵢ) per kid, and
                    // (∧ lits) → φ as the single long clause.
                    for &l in &lits {
                        self.clauses
                            .push(smallvec::smallvec![-lit_of(phi, true), l,]);
                    }
                    let mut long_clause: SmallVec<[i32; 4]> = lits.iter().map(|&l| -l).collect();
                    long_clause.push(lit_of(phi, true));
                    self.clauses.push(long_clause);
                    pending.push(LitOrConst::L(lit_of(phi, p)));
                }
                Frame::CombineOr(p, n) => {
                    let kids = take_pending(&mut pending, n);
                    if kids.contains(&LitOrConst::T) {
                        pending.push(LitOrConst::T);
                        continue;
                    }
                    let lits: Vec<i32> = kids
                        .into_iter()
                        .filter_map(|k| match k {
                            LitOrConst::L(l) => Some(l),
                            LitOrConst::F => None,
                            LitOrConst::T => unreachable!("filtered above"),
                        })
                        .collect();
                    if lits.is_empty() {
                        pending.push(LitOrConst::F);
                        continue;
                    }
                    if lits.len() == 1 {
                        pending.push(LitOrConst::L(lits[0]));
                        continue;
                    }
                    let phi = self.fresh_aux(n_atoms);
                    // φ ↔ ∨lits:  lᵢ → φ (¬lᵢ ∨ φ) per kid, and
                    // φ → (∨ lits) as the single long clause.
                    for &l in &lits {
                        self.clauses
                            .push(smallvec::smallvec![-l, lit_of(phi, true),]);
                    }
                    let mut long_clause: SmallVec<[i32; 4]> = lits.iter().copied().collect();
                    long_clause.push(-lit_of(phi, true));
                    self.clauses.push(long_clause);
                    pending.push(LitOrConst::L(lit_of(phi, p)));
                }
                Frame::CombineIte(p) => {
                    let kids = take_pending(&mut pending, 3);
                    let [c, t, e] = [kids[0], kids[1], kids[2]];
                    let (c, t, e) = match (c, t, e) {
                        (LitOrConst::T, _, _) => {
                            pending.push(t);
                            continue;
                        }
                        (LitOrConst::F, _, _) => {
                            pending.push(e);
                            continue;
                        }
                        (LitOrConst::L(_c), LitOrConst::T, LitOrConst::T) => {
                            pending.push(LitOrConst::T);
                            continue;
                        }
                        (LitOrConst::L(c), LitOrConst::T, LitOrConst::F) => {
                            pending.push(LitOrConst::L(c));
                            continue;
                        }
                        (LitOrConst::L(c), LitOrConst::F, LitOrConst::T) => {
                            pending.push(LitOrConst::L(-c));
                            continue;
                        }
                        (LitOrConst::L(_), LitOrConst::F, LitOrConst::F) => {
                            pending.push(LitOrConst::F);
                            continue;
                        }
                        (LitOrConst::L(c), LitOrConst::L(t), LitOrConst::L(e)) => (c, t, e),
                        // Constant branches with a literal condition
                        // remaining: rare; decline to an aux encoding.
                        (LitOrConst::L(c), LitOrConst::T, LitOrConst::L(e)) => (c, i32::MAX, e),
                        (LitOrConst::L(c), LitOrConst::L(t), LitOrConst::F) => (c, t, i32::MIN),
                        (LitOrConst::L(c), LitOrConst::F, LitOrConst::L(e)) => (c, i32::MIN, e),
                        (LitOrConst::L(c), LitOrConst::L(t), LitOrConst::T) => (c, t, i32::MAX),
                    };
                    if t == i32::MAX || e == i32::MIN {
                        // Mixed constant/literal branches not folded above:
                        // encode via the generic aux (constants handled by
                        // unit clauses on the aux would need more vars than
                        // worth it — decline this exotic shape).
                        return TseitinOut::Declined;
                    }
                    let aux = self.fresh_aux(n_atoms);
                    self.clauses
                        .push(smallvec::smallvec![-lit_of(aux, true), c, t,]);
                    self.clauses
                        .push(smallvec::smallvec![-lit_of(aux, true), -c, e,]);
                    self.clauses
                        .push(smallvec::smallvec![lit_of(aux, true), -c, -t]);
                    self.clauses
                        .push(smallvec::smallvec![lit_of(aux, true), c, -e]);
                    pending.push(LitOrConst::L(lit_of(aux, p)));
                }
                Frame::CombineEqBool(p) => {
                    let kids = take_pending(&mut pending, 2);
                    let (a, b) = (kids[0], kids[1]);
                    let (a, b) = match (a, b) {
                        (LitOrConst::T, other) | (other, LitOrConst::T) => {
                            pending.push(other);
                            continue;
                        }
                        (LitOrConst::F, other) | (other, LitOrConst::F) => match other {
                            LitOrConst::L(l) => {
                                pending.push(LitOrConst::L(-l));
                                continue;
                            }
                            _ => return TseitinOut::Declined,
                        },
                        (LitOrConst::L(a), LitOrConst::L(b)) => (a, b),
                    };
                    if a == b {
                        pending.push(LitOrConst::T);
                        continue;
                    }
                    if a == -b {
                        pending.push(LitOrConst::F);
                        continue;
                    }
                    let aux = self.fresh_aux(n_atoms);
                    self.clauses
                        .push(smallvec::smallvec![-lit_of(aux, true), a, -b]);
                    self.clauses
                        .push(smallvec::smallvec![-lit_of(aux, true), -a, b]);
                    self.clauses
                        .push(smallvec::smallvec![lit_of(aux, true), -a, -b]);
                    self.clauses
                        .push(smallvec::smallvec![lit_of(aux, true), a, b]);
                    pending.push(LitOrConst::L(lit_of(aux, p)));
                }
                Frame::CombineNeg => {
                    let kids = take_pending(&mut pending, 1);
                    match kids[0] {
                        LitOrConst::T => pending.push(LitOrConst::F),
                        LitOrConst::F => pending.push(LitOrConst::T),
                        LitOrConst::L(l) => pending.push(LitOrConst::L(-l)),
                    }
                }
            }
        }
        match pending.pop() {
            Some(LitOrConst::T) => TseitinOut::Const(true),
            Some(LitOrConst::F) => TseitinOut::Const(false),
            Some(LitOrConst::L(l)) => TseitinOut::Lit(l),
            None => TseitinOut::Const(true),
        }
    }
}

fn take_pending(pending: &mut Vec<LitOrConst>, n: usize) -> Vec<LitOrConst> {
    let at = pending.len().saturating_sub(n);
    pending.split_off(at)
}

// ===========================================================================
// Per-assignment constraint compilation
// ===========================================================================

/// Evaluates Boolean structure under a fixed SAT assignment (for `ite`
/// conditions) and interns the constraint terms.
struct AssignmentCtx<'a> {
    build: &'a TransBuild,
    /// SAT truth values: atoms first, then aux (skeleton) vars.
    values: &'a [bool],
    memo: FxHashMap<TermId, bool>,
}

impl<'a> AssignmentCtx<'a> {
    /// Evaluate a Bool-sorted term under the assignment (atoms and free
    /// Bool vars read from `values`; compound structure recursively with a
    /// memo).  `None` = not evaluable — the caller declines the
    /// assignment, which keeps every verdict honest.
    fn eval_bool(&mut self, t: TermId, manager: &TermManager) -> Option<bool> {
        if let Some(&v) = self.memo.get(&t) {
            return Some(v);
        }
        let out = match manager.get(t).map(|x| x.kind.clone())? {
            TermKind::True => true,
            TermKind::False => false,
            TermKind::Var(_) => {
                let v = self.build.bool_vars.get(&t).copied()?;
                return Some(self.values[v]);
            }
            TermKind::Not(a) => !self.eval_bool(a, manager)?,
            TermKind::And(args) => {
                let mut v = true;
                for a in args {
                    v &= self.eval_bool(a, manager)?;
                }
                v
            }
            TermKind::Or(args) => {
                let mut v = false;
                for a in args {
                    v |= self.eval_bool(a, manager)?;
                }
                v
            }
            TermKind::Implies(a, b) => {
                !self.eval_bool(a, manager)? || self.eval_bool(b, manager)?
            }
            TermKind::Ite(c, a, b) => {
                if self.eval_bool(c, manager)? {
                    self.eval_bool(a, manager)?
                } else {
                    self.eval_bool(b, manager)?
                }
            }
            TermKind::Xor(a, b) => self.eval_bool(a, manager)? ^ self.eval_bool(b, manager)?,
            TermKind::Eq(a, b) => {
                let a_bool = manager.get(a)?.sort == manager.sorts.bool_sort;
                if a_bool {
                    self.eval_bool(a, manager)? == self.eval_bool(b, manager)?
                } else if let Some(&i) = self.build.atom_index.get(&t) {
                    self.values[i]
                } else {
                    return None;
                }
            }
            TermKind::Lt(_, _) | TermKind::Le(_, _) | TermKind::Gt(_, _) | TermKind::Ge(_, _) => {
                let i = self.build.atom_index.get(&t).copied()?;
                self.values[i]
            }
            _ => return None,
        };
        self.memo.insert(t, out);
        Some(out)
    }

    /// Intern `(lhs ⋈ rhs)` as a constraint; returns `(root node, rhs
    /// constant, comparison)` — mirroring when the LEFT side is the
    /// constant — with numeric `ite`s resolved via the assignment.
    fn constraint_for(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        cmp: Cmp,
        manager: &mut TermManager,
        prob: &mut TransProblem,
        cache: &mut FxHashMap<TermId, Option<u32>>,
    ) -> Option<(u32, Rational64, Cmp)> {
        let lhs = self.resolve_ite(lhs, manager)?;
        let rhs = self.resolve_ite(rhs, manager)?;
        match const_rational(rhs, manager) {
            Some(c) => {
                let root = prob.intern_term(lhs, manager, cache)?;
                Some((root, c, cmp))
            }
            None => match const_rational(lhs, manager) {
                Some(c) => {
                    let flipped = match cmp {
                        Cmp::Le => Cmp::Ge,
                        Cmp::Ge => Cmp::Le,
                        other => other,
                    };
                    let root = prob.intern_term(rhs, manager, cache)?;
                    Some((root, c, flipped))
                }
                None => {
                    let sub = manager.mk_sub(lhs, rhs);
                    let root = prob.intern_term(sub, manager, cache)?;
                    Some((root, Rational64::zero(), cmp))
                }
            },
        }
    }

    /// Resolve numeric `ite`s inside an arithmetic term by rewriting to the
    /// selected branch.  Recursion depth is bounded by the encoder's depth
    /// cap on asserted terms; the walk is memo-free because rebuilds
    /// produce fresh terms (the no-ite fast path keeps this rare).
    fn resolve_ite(&mut self, t: TermId, manager: &mut TermManager) -> Option<TermId> {
        if !term_has_numeric_ite(t, manager) {
            return Some(t);
        }
        match manager.get(t).map(|x| x.kind.clone())? {
            TermKind::Ite(c, a, b) => {
                let cond = self.eval_bool(c, manager)?;
                let branch = if cond { a } else { b };
                self.resolve_ite(branch, manager)
            }
            TermKind::Neg(a) => {
                let a = self.resolve_ite(a, manager)?;
                Some(manager.mk_neg(a))
            }
            TermKind::Add(args) => {
                let mut new_args = Vec::with_capacity(args.len());
                for a in args {
                    new_args.push(self.resolve_ite(a, manager)?);
                }
                Some(manager.mk_add(new_args))
            }
            TermKind::Sub(a, b) => {
                let a = self.resolve_ite(a, manager)?;
                let b = self.resolve_ite(b, manager)?;
                Some(manager.mk_sub(a, b))
            }
            TermKind::Mul(args) => {
                let mut new_args = Vec::with_capacity(args.len());
                for a in args {
                    new_args.push(self.resolve_ite(a, manager)?);
                }
                Some(manager.mk_mul(new_args))
            }
            TermKind::Div(a, b) => {
                let a = self.resolve_ite(a, manager)?;
                let b = self.resolve_ite(b, manager)?;
                Some(manager.mk_rdiv(a, b))
            }
            TermKind::Exp(a) => {
                let r = self.resolve_ite(a, manager)?;
                Some(manager.mk_exp(r))
            }
            TermKind::Log(a) => {
                let r = self.resolve_ite(a, manager)?;
                Some(manager.mk_log(r))
            }
            TermKind::Sin(a) => {
                let r = self.resolve_ite(a, manager)?;
                Some(manager.mk_sin(r))
            }
            TermKind::Cos(a) => {
                let r = self.resolve_ite(a, manager)?;
                Some(manager.mk_cos(r))
            }
            TermKind::Atan(a) => {
                let r = self.resolve_ite(a, manager)?;
                Some(manager.mk_atan(r))
            }
            TermKind::Sqrt(a) => {
                let r = self.resolve_ite(a, manager)?;
                Some(manager.mk_sqrt(r))
            }
            _ => Some(t),
        }
    }
}

/// Whether an arithmetic term contains a numeric `ite` (explicit stack).
fn term_has_numeric_ite(term: TermId, manager: &TermManager) -> bool {
    use rustc_hash::FxHashSet;
    let mut stack: Vec<TermId> = vec![term];
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        let Some(node) = manager.get(t) else {
            continue;
        };
        match &node.kind {
            TermKind::Ite(_, _, _) => {
                let numeric =
                    node.sort == manager.sorts.int_sort || node.sort == manager.sorts.real_sort;
                if numeric {
                    return true;
                }
                let mut kids = Vec::new();
                super::term_walk::collect_structural_children(&node.kind, &mut kids);
                stack.extend(kids);
            }
            _ => {
                let mut kids = Vec::new();
                super::term_walk::collect_structural_children(&node.kind, &mut kids);
                stack.extend(kids);
            }
        }
    }
    false
}

/// Normalize an atom's kind under the polarity into the ICP comparison.
/// Strict comparisons weaken to their non-strict forms — sound in both
/// directions under δ-semantics (see docs/TRANS.md): for refutation,
/// `¬(a < b)` is exactly `a ≥ b`, and `a < b` weakened to `a ≤ b` only
/// ever makes the pruned problem MORE satisfiable, so an emptiness proof
/// still refutes the strict original.
fn normalize_cmp(kind: AtomKind, positive: bool) -> Cmp {
    match (kind, positive) {
        (0, true) | (1, true) => Cmp::Le,
        (0, false) | (1, false) => Cmp::Ge,
        (2, true) | (3, true) => Cmp::Ge,
        (2, false) | (3, false) => Cmp::Le,
        (4, true) => Cmp::Eq,
        (4, false) => Cmp::Ne,
        _ => Cmp::Eq,
    }
}

/// The exact rational of an arithmetic constant term, if it is one.
fn const_rational(t: TermId, manager: &TermManager) -> Option<Rational64> {
    match manager.get(t).map(|x| &x.kind) {
        Some(TermKind::RealConst(r)) => Some(*r),
        Some(TermKind::IntConst(n)) => n.to_i64().map(Rational64::from_integer),
        _ => None,
    }
}
