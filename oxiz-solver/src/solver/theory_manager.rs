//! Theory manager that bridges the SAT solver with theory solvers

#[allow(unused_imports)]
use crate::prelude::*;
use num_rational::Rational64;
use num_traits::ToPrimitive;
use oxiz_core::ast::{TermId, TermKind, TermManager};
use oxiz_sat::{Lit, TheoryCallback, TheoryCheckResult, Var};
use oxiz_theories::arithmetic::ArithSolver;
use oxiz_theories::bv::BvSolver;
use oxiz_theories::euf::EufSolver;
use oxiz_theories::{EqualityNotification, Theory, TheoryCombination};
use smallvec::SmallVec;

use super::theory_bv_encode::{debug_verify_bv_circuits, encode_bv_term_recursive};
use super::types::{
    ArithConstraintType, Constraint, ParsedArithConstraint, Statistics, TheoryMode,
};

/// Whether theory-conflict tracing is enabled (`OXIZ_TRACE_DECISIONS`, shared
/// with the SAT-side decision/conflict tracer). Read once and cached. Used by
/// `diff_primary_check` to tag each DL (difference-logic) conflict so the
/// SAT-side `oxiz-conflict` lines (which report the detection *point* but not
/// the theory) can be attributed to a theory.
#[cfg(feature = "std")]
fn theory_trace_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("OXIZ_TRACE_DECISIONS")
            .is_ok_and(|v| !v.is_empty() && v != "0" && !v.eq_ignore_ascii_case("false"))
    })
}

/// Incremental arithmetic bound-propagation mode, set from `OXIZ_BOUND_PROP`
/// (read once and cached).  The z3 `:arith-bound-prop` analogue – see
/// [`TheoryManager::derive_arith_bound_propagations`].
///
/// **Default-on for QF_UFIDL** (validated net-positive: closes the vhard
/// family, +1 on the differential suite).  The mode only takes effect where
/// the `is_dl_family` (QF_UFIDL) gate and the matching `set_branching_vsids`
/// gate fire, so non-QF_UFIDL logics are unaffected by the default.
///
/// * unset (default) – `Tighten` (on; the recommended mode for QF_UFIDL).
/// * `"0"` / `"off"` / `"false"` – `Off` (escape hatch: disables even for
///   QF_UFIDL).
/// * `"tight"` – `Tighten` (explicit; same as default).
/// * any other non-empty value (e.g. `"1"`, `"on"`) – `Direct` (cheaper;
///   catches only the first propagation level).
#[cfg(feature = "std")]
pub(crate) fn arith_bound_prop_mode() -> BoundPropMode {
    use std::sync::OnceLock;
    static FLAG: OnceLock<BoundPropMode> = OnceLock::new();
    *FLAG.get_or_init(|| {
        match std::env::var("OXIZ_BOUND_PROP") {
            Ok(v)
                if v.eq_ignore_ascii_case("off") || v == "0" || v.eq_ignore_ascii_case("false") =>
            {
                BoundPropMode::Off
            }
            Ok(v) if v.eq_ignore_ascii_case("tight") => BoundPropMode::Tighten,
            Ok(v) if !v.is_empty() => BoundPropMode::Direct,
            _ => BoundPropMode::Tighten, // default-on
        }
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoundPropMode {
    Off,
    Direct,
    Tighten,
}

mod conflict_clause;
#[cfg(debug_assertions)]
mod debug_scan;
mod derived_reasons;
mod euf_propagate;
pub(crate) use derived_reasons::DerivedReasons;

/// One entry of the theory manager's own deduplicated assignment trail.
///
/// The SAT core drives theory state incrementally through `on_assignment` /
/// `on_new_level` / `on_backtrack`, but its conflict analysis can (on some
/// formulas) compute a wrong backtrack level and *overwrite* a variable's
/// assignment in place – flipping a decision literal's polarity without ever
/// popping the theory scope that recorded the old polarity.  The incremental
/// EUF / arith / BV solvers only support level-scoped `pop`, not point removal
/// of a single mid-level assertion, so a flipped literal would otherwise leave
/// the theory state permanently reflecting the stale polarity and manufacture a
/// spurious conflict (observed as a wrong top-level UNSAT on satisfiable
/// disjunctive LIA chains).  We therefore shadow every theory-relevant
/// assignment here, keyed so a flip is detected in O(1), and rebuild theory
/// state from the corrected trail when one occurs.
#[derive(Debug, Clone, Copy)]
struct TrailAtom {
    /// The SAT variable that was assigned.
    var: Var,
    /// `true` when the atom was assigned true, `false` when assigned false.
    is_positive: bool,
    /// The SAT decision level at which the assignment currently holds.
    level: u32,
}

/// One difference-logic atom extracted from the arithmetic vocabulary.
struct DlAtom {
    var: Var,
    x: TermId,
    y: TermId,
    c: Rational64,
    is_eq: bool,
    ctype: ArithConstraintType,
}

/// A dense-core feeding plan for one DL atom at one polarity: the atom's
/// watch orientation (its TRUE-polarity integer reading `t − s ≤ k`) and the
/// edges to assert for the polarity being fed.
struct DenseFeed {
    /// Watch edge source (the subtrahend of `t − s ≤ k`).
    watch_s: TermId,
    /// Watch edge target (the minuend).
    watch_t: TermId,
    /// Watch bound `k` (already integer-tightened for strict atoms).
    watch_k: i64,
    /// Whether the atom is an equality.
    is_eq: bool,
    /// `(src, dst, weight)` edges to assert at the fed polarity.
    edges: Vec<(TermId, TermId, i64)>,
}

/// The TRUE-polarity integer watch of a difference atom, shared by the
/// assignment-time feed ([`DenseFeed`]) and the eager pre-search interning
/// ([`TheoryManager::intern_pure_dl_atoms`]): reading `t − s ≤ k`.
struct DlWatch {
    watch_s: TermId,
    watch_t: TermId,
    watch_k: i64,
    is_eq: bool,
}
/// Parsed arithmetic atom considered for SAT-level bound propagation.
type ArithPropCandidate = (Var, Vec<(TermId, Rational64)>, Rational64, bool, bool);

/// Outcome of feeding one arithmetic atom to the difference-logic engines.
/// `Consistent` means the atom was exactly representable as DL and the
/// updated graph/closure has no negative cycle; it is therefore safe to
/// defer the more expensive simplex feasibility pass until a non-DL atom or
/// final check.  `Propagated` additionally carries closure-derived theory
/// propagations from the dense core (Z3 `propagate_using_cell`).
enum DlPrimaryResult {
    /// The atom is outside the exact difference-logic fragment.
    NotApplicable,
    /// The atom was added and the complete incremental DL check accepted it.
    Consistent,
    /// Adding the atom produced a justified negative-cycle conflict.
    Conflict(TheoryCheckResult),
    /// The atom was added; the dense core derived new implied atoms.
    Propagated(Vec<(Lit, SmallVec<[Lit; 8]>)>),
}

/// Feed a DL atom using the INCREMENTAL add+check API (`add_*_check`, seeded
/// SPFA – O(affected) per edge), returning a conflict if the edge creates a
/// negative cycle.  This is the cheap DL-primary path (vs the on-demand
/// rebuild which was 97% of theory time).
fn feed_dl_atom_inc(
    dl: &mut oxiz_theories::DiffLogicSolver,
    dla: &DlAtom,
    pol: bool,
    origin: TermId,
) -> oxiz_theories::DiffLogicResult {
    use ArithConstraintType::*;
    use oxiz_theories::DiffLogicResult;
    let (x, y, c) = (dla.x, dla.y, dla.c);
    if dla.is_eq {
        if pol {
            // x - y = c  <=>  two edges; the second may complete a cycle.
            if let r @ DiffLogicResult::Conflict(_) = dl.add_leq_check(x, y, c, origin) {
                return r;
            }
            return dl.add_leq_check(y, x, -c, origin);
        }
        return DiffLogicResult::Ok; // disequality: not representable
    }
    match (dla.ctype, pol) {
        (Le, true) => dl.add_leq_check(x, y, c, origin),
        (Lt, true) => dl.add_lt_check(x, y, c, origin),
        (Ge, true) => dl.add_leq_check(y, x, -c, origin),
        (Gt, true) => dl.add_lt_check(y, x, -c, origin),
        (Le, false) => dl.add_lt_check(y, x, -c, origin),
        (Lt, false) => dl.add_leq_check(y, x, -c, origin),
        (Ge, false) => dl.add_lt_check(x, y, c, origin),
        (Gt, false) => dl.add_leq_check(x, y, c, origin),
    }
}

/// True iff `t` is a plain numeric leaf (Var/IntConst/RealConst).  Difference
/// logic is complete only over plain numeric variables; compound/UF terms are
/// excluded so DL propagations never steer the search across a theory boundary
/// the DL fragment cannot model (defect 3).
fn is_plain_numeric_term(td: &oxiz_core::ast::Term) -> bool {
    matches!(
        td.kind,
        TermKind::Var(_) | TermKind::IntConst(_) | TermKind::RealConst(_)
    )
}

/// Numeric value of a bare constant term (`IntConst`/`RealConst`), else `None`.
/// Used by the DL-primary path to fold constants out of an atom's linear form.
fn direct_const_value(manager: &oxiz_core::ast::TermManager, t: TermId) -> Option<Rational64> {
    let td = manager.get(t)?;
    match &td.kind {
        TermKind::IntConst(n) => n.to_i64().map(Rational64::from_integer),
        TermKind::RealConst(r) => Some(Rational64::new(*r.numer(), *r.denom())),
        _ => None,
    }
}

/// If `(= lhs rhs)` is a GENUINE `term = constant` equality – `rhs` a numeric
/// constant and `lhs` a non-constant Int/Real-sorted term (a plain variable,
/// an uninterpreted-function application like `(Succ 0)`, an array select, an
/// `ite`, … – anything the linear parser treats as ONE opaque arithmetic
/// variable) – return the constant's value.  Such a bound is a direct,
/// unconditional consequence of the single asserted equality, so its
/// single-atom reason is sufficient and the cheap derived-reason propagator
/// stays sound.  Equalities whose `rhs` is itself a term (e.g. `(= a b)`, or
/// a term whose linear parse folded to a constant) record no bound – their
/// real justification may be an EUF/tableau chain the prop tracker cannot
/// summarize.
fn genuine_fixed_var(lhs: TermId, rhs: TermId, manager: &TermManager) -> Option<Rational64> {
    let rhs_td = manager.get(rhs)?;
    let value = match &rhs_td.kind {
        TermKind::IntConst(n) => Rational64::from_integer(n.to_i64()?),
        TermKind::RealConst(r) => *r,
        _ => return None, // rhs is not a numeric constant
    };
    let lhs_td = manager.get(lhs)?;
    // lhs must be a non-constant arithmetic term (so the equality pins one
    // opaque arithmetic variable to `value`).
    if matches!(
        lhs_td.kind,
        TermKind::IntConst(_) | TermKind::RealConst(_) | TermKind::BitVecConst { .. }
    ) {
        return None;
    }
    let sort = manager.sorts.get(lhs_td.sort)?;
    if !sort.is_int() && !sort.is_real() {
        return None;
    }
    Some(value)
}

/// One pending application of an iterative EUF interning walk
/// ([`TheoryManager::intern_term_deep`] and
/// [`TheoryManager::intern_term_for_congruence`]).
///
/// The frame owns the application's operand list and the EUF nodes of the
/// operands already interned, so the walk never needs the native call stack
/// and never needs to re-borrow a half-finished parent.
struct InternFrame {
    /// The application term whose operands are being interned.
    term: TermId,
    /// EUF function symbol of the application (`SELECT_FUNC_ID` for `select`).
    func_id: u32,
    /// The application's operands, in order.
    operands: SmallVec<[TermId; 4]>,
    /// Index of the next operand to descend into.
    next: usize,
    /// EUF nodes of the operands interned so far, in order.
    nodes: SmallVec<[u32; 4]>,
}

/// Theory manager that bridges the SAT solver with theory solvers
pub(crate) struct TheoryManager<'a> {
    /// Reference to the term manager
    manager: &'a TermManager,
    /// Reference to the EUF solver
    euf: &'a mut EufSolver,
    /// Reference to the arithmetic solver
    arith: &'a mut ArithSolver,
    /// Reference to the bitvector solver
    bv: &'a mut BvSolver,
    diff: &'a mut oxiz_theories::DiffLogicSolver,
    /// Bitvector terms (for identifying BV variables)
    bv_terms: &'a FxHashSet<TermId>,
    /// Mapping from SAT variables to constraints
    var_to_constraint: &'a FxHashMap<Var, Constraint>,
    /// Mapping from SAT variables to parsed arithmetic constraints
    var_to_parsed_arith: &'a FxHashMap<Var, ParsedArithConstraint>,
    /// Mapping from terms to SAT variables (for conflict clause generation)
    term_to_var: &'a FxHashMap<TermId, Var>,
    /// Reverse mapping from SAT variables to terms (for EUF merge reasons)
    var_to_term: &'a Vec<TermId>,
    /// `const TermId -> proxy TermId` map from `purify_numeric_uf_args`.  Because
    /// that pass uses a *global* substitute, a constant abstracted out of one
    /// UF application is replaced *everywhere* – including in arithmetic like
    /// `(+ x 1)` -> `(+ x __oxiz_numarg)`, which destroys difference-logic
    /// shape.  Inverting this map lets the DL-primary path fold those proxies
    /// back into the atom's constant, restoring DL shape.
    numarg_proxies: &'a FxHashMap<TermId, TermId>,
    /// Canonical `IntConst(0)` term – the DL solver's zero reference for
    /// absolute single-variable bounds (`x ≤ k` is fed as the edge
    /// `zero → x` of weight `k`).  Registered as an ordinary DL variable; a
    /// free zero gives correct feasibility (bounds `x ≤ k`, `x ≥ k'` form a
    /// `zero→x→zero` cycle of weight `k − k'`, infeasible iff `k < k'`) and
    /// never introduces spurious infeasibility.  Used as the second endpoint
    /// of single-variable bounds on the dense-core path (`x ≤ k` ≡ edge
    /// `zero → x`, weight `k` — Z3's dense solver internalises numerals the
    /// same way).  The sparse engine still defers 1-var bounds to the simplex
    /// (the zero hub inflated the seeded-SPFA check; see `diff_primary_check`).
    zero_term: TermId,
    /// Fresh `ite`-result constants (`__oxiz_ite_*`) axiomatized against
    /// constants (z3-style triangle).  Used by `final_check` to theory-propagate
    /// the `le`/`ge` atoms deterministically when arithmetic fixes such a term
    /// to a constant, so the equality is shared to EUF without CDCL search and
    /// without fragile model-based merging.
    ite_result_terms: &'a FxHashSet<TermId>,
    /// `(ite-result term, constant value) → (le_var, ge_var)` for the z3-style
    /// triangle axioms added at encode time.  Built once in [`new`] by scanning
    /// `var_to_constraint`; used by `final_check` to theory-propagate the `le`/
    /// `ge` atoms when arithmetic fixes an ite-result to a constant.
    ite_const_axioms: FxHashMap<(TermId, i64), (Var, Var)>,
    /// Current decision level stack for backtracking
    level_stack: Vec<usize>,
    /// EUF-derived equalities already asserted into the arithmetic tableau
    /// at the *current* theory scope.
    ///
    /// [`Self::propagate_euf_equalities_to_arith`] re-runs on every Nelson-
    /// Oppen round and every `final_check`, and without this memo it would
    /// re-`add_eq` every same-class term pair as *fresh tableau rows* each
    /// time – the tableau bloated from ~56 rows to 14k+ rows on
    /// QF_AUFLIA/swap, and every subsequent `Simplex::check`/pivot paid
    /// O(rows) over duplicated constraints.  A pair asserted at a scope is
    /// still implied at that scope (its EUF merge is popped by the same
    /// scope pop that removes the rows), so skipping the re-assertion is
    /// sound: it removes a redundant restatement of a fact the tableau
    /// already holds.
    ///
    /// Trail discipline: `asserted_arith_eqs` gives O(1) membership; the
    /// `asserted_arith_eq_trail` vector records insertion order so a scope
    /// pop can retract exactly the pairs asserted inside it.  Cleared by
    /// [`Self::resync_theory_state`], which resets the arithmetic solver and
    /// therefore wipes the rows this memo claims exist.
    asserted_arith_eqs: FxHashSet<(TermId, TermId)>,
    /// Constraint literals already processed at the *current* theory scope.
    ///
    /// [`Self::process_constraint`] applies each asserted literal to every
    /// theory solver (EUF merge, tableau rows, DL edges, BV encodings).
    /// EUF merging is idempotent, but the arithmetic/DL/BV sides are
    /// *additive*: the SAT core re-sends an already-assigned literal (the
    /// documented same-polarity idempotent re-send, and propagation
    /// replays), and every re-send used to add a fresh pair of tableau
    /// rows for an equality whose rows were still live.  On
    /// QF_AUFLIA/swap that ballooned a ~100-row tableau past 13,000 rows,
    /// and every subsequent simplex check/pivot/pop paid for the
    /// duplicates.
    ///
    /// A literal processed at a scope is *still in effect* at that scope
    /// (the scope pop that removes its rows also removes its guard entry),
    /// so skipping the re-process is sound: it suppresses a duplicate of
    /// work whose effect is already present.
    processed_lit_trail: Vec<(Var, bool)>,
    /// Scope markers into `processed_lit_trail`, parallel to `level_stack`.
    processed_lit_marks: Vec<usize>,
    /// O(1) membership mirror of `processed_lit_trail`.
    processed_lits: FxHashSet<(Var, bool)>,
    /// Insertion-ordered trail backing `asserted_arith_eqs`; entry `i` is
    /// the scope marker (number of live pairs) when the trail had `i`
    /// entries at `push_theory_scope` time.
    asserted_arith_eq_trail: Vec<(TermId, TermId)>,
    /// Scope markers into `asserted_arith_eq_trail`, parallel to
    /// `level_stack`.
    asserted_arith_eq_marks: Vec<usize>,
    /// Number of processed assignments
    processed_count: usize,
    /// Theory checking mode
    theory_mode: TheoryMode,
    /// Pending equality notifications for Nelson-Oppen
    pending_equalities: Vec<EqualityNotification>,
    /// Processed equalities (to avoid duplicates)
    processed_equalities: FxHashMap<(TermId, TermId), bool>,
    /// Reference to solver statistics (for tracking)
    statistics: &'a mut Statistics,
    /// Maximum conflicts allowed (0 = unlimited)
    max_conflicts: u64,
    /// Maximum decisions allowed (0 = unlimited)
    #[allow(dead_code)]
    max_decisions: u64,
    /// Whether formula contains BV arithmetic operations (division/remainder)
    #[allow(dead_code)]
    has_bv_arith_ops: bool,
    /// Whether the problem's logic is the difference-logic family
    /// (QF_IDL/QF_UFIDL), for which the cheap derived-reason bound propagator
    /// is SOUND (validated: 0 differential disagreements on the IDL/UFIDL
    /// sample).  On denser logics the derived reason can be an insufficient
    /// subset of the true Farkas proof, so bound propagation is gated to this
    /// family.
    is_dl_family: bool,
    /// Pairs whose tentative arrangement merge was refuted during the last
    /// [`Self::model_based_combination`] round (`C ⊢ x ≠ y` for then-true
    /// facts C).  Drained by `Solver::refine_arrangement_splits`, which
    /// internalizes `(= x y)` atoms for them so the next search can *decide*
    /// the arrangement (the refutation itself lives on search facts, so no
    /// clause can be asserted — only the branching dimension is added).
    arrangement_splits: Vec<(TermId, TermId)>,
    /// Pure integer difference logic end-to-end: every arithmetic atom is
    /// difference-shaped (Z3's structural `is_in_diff_logic(st)` gate, see
    /// `solver::static_features`) and integer-sorted without UF.  While this
    /// holds, the dense DL core is the ONLY arithmetic engine — atoms are not
    /// duplicated into the simplex tableau (Z3's `setup_QF_IDL` installs
    /// `theory_dense_diff_logic` in exactly this shape).  The first atom the
    /// DL engines reject (`NotApplicable`) breaks purity and replays every
    /// live arith assignment into the simplex, restoring the general path.
    dl_pure: bool,
    /// Whether the sparse difference engine may feed at all: the declared
    /// logic is a difference-logic family the dense core does not cover
    /// (QF_RDL / QF_UFIDL), or the pure integer route is still active.
    sparse_dl: bool,
    /// Canonical EUF node for each distinct integer constant value.
    ///
    /// Maps an integer literal value (i64) to the canonical EUF node that
    /// represents it.  When a new `IntConst(v)` term is first encountered for a
    /// value `v`, we create its EUF node, assert pairwise disequalities against
    /// every canonical node of a different value, and record it here.
    ///
    /// If the same value `v` appears again (e.g., as a fresh TermId created
    /// during MBQI instantiation), we merge the new node with the existing
    /// canonical node rather than appending another entry.  This keeps the
    /// number of distinct entries – and therefore the number of pairwise
    /// disequality edges – bounded by the number of *distinct* integer literal
    /// values in the original formula, not by the total number of term IDs
    /// created across all MBQI iterations (which grows without bound).
    interned_int_constants: FxHashMap<i64, u32>,
    /// Canonical EUF nodes for distinct bit-vector constant *values*, keyed by
    /// `(value, width)`.  Mirrors `interned_int_constants` but for the BV theory:
    /// EUF has no notion that `#x00 != #x01`, so without explicit disequality
    /// edges a congruence chain merging `g(a)` (= `#x00`) with `g(b)` (= `#x01`)
    /// when `a = b` would not produce a conflict.  We track one canonical node
    /// per distinct `(value, width)` pair and assert pairwise disequalities
    /// between same-width constants, bounding the edge count by the number of
    /// distinct BV literals in the formula.
    ///
    /// The value half of the key is the constant's *full* little-endian limb
    /// sequence, not a `u64` digest of it.  Keying on the low 64 bits merged
    /// two genuinely different wide constants – `0` and `2^64` at width 128
    /// share those bits – into one EUF class, which turned a satisfiable
    /// `(distinct (g a) (g b))` into `unsat`.
    interned_bv_constants: FxHashMap<(SmallVec<[u64; 2]>, u32), u32>,
    /// Canonical EUF nodes for Boolean true and false values.
    /// Used to track Bool-valued function applications in EUF:
    /// when `f(x)` is assigned true by the SAT solver, we merge its EUF node
    /// with `bool_true_node`; when assigned false, with `bool_false_node`.
    /// A disequality `true != false` is asserted so that congruence closure
    /// detects conflicts (e.g., f(a)=true, f(b)=false, but a=b).
    bool_true_node: Option<u32>,
    bool_false_node: Option<u32>,
    /// Set to `true` when a genuine theory conflict was detected but suppressed
    /// because the conflict limit (`max_conflicts`) had been reached.  On
    /// exhaustion the manager returns `TheoryCheckResult::Sat` to make the SAT
    /// solver stop searching; that `Sat` is a resource signal, not a model.
    /// The owning `Solver` reads this flag after `solve_with_theory` and, when
    /// set, answers `Unknown` instead of trusting the `Sat` – so a dropped
    /// conflict never turns into a fabricated satisfiability result.
    resource_exhausted: bool,
    /// Set to `true` when a theory reported a conflict whose justification this
    /// manager could not account for, so that no conflict clause could be built
    /// (see [`Self::conflict_from_terms`]).
    ///
    /// Read like [`Self::resource_exhausted`], and for the same reason: the
    /// conflict was *dropped*, so a subsequent `Sat` rests on an assignment the
    /// theories may already have refuted and the owning `Solver` must answer
    /// `Unknown`.  An `Unsat` reached from other conflicts stays sound –
    /// dropping a lemma only ever removes refutations.
    ///
    /// This is a bug channel, not a resource one: every path that sets it is
    /// guarded by a `debug_assert!` that fails the build's tests first.  It
    /// exists so that the *release* build degrades to `Unknown` instead of
    /// emitting the empty clause, which claims an unconditional refutation.
    unjustified_conflict: bool,
    /// Wall-clock deadline for this solve, derived from `timeout_ms`.  `None`
    /// means no timeout.  Checked in the theory callbacks so a single
    /// uninterruptible `solve_with_theory` call cannot run past the budget:
    /// once the deadline passes we set `resource_exhausted` and stop reporting
    /// conflicts, forcing the search to terminate; the owning `Solver` then
    /// answers `Unknown`.
    #[cfg(feature = "std")]
    deadline: Option<std::time::Instant>,
    /// Latest SAT-assignment polarity of each theory-atom variable
    /// (`true` = atom assigned true, `false` = assigned false).  Recorded in
    /// `on_assignment` / lazy `final_check` so that `terms_to_conflict_clause`
    /// can emit, for each reason atom, the literal that is currently *false*
    /// (the negation of its assignment).  Without this a negatively-assigned
    /// atom would contribute a currently-*true* literal, violating the
    /// all-literals-false convention `analyze_theory_conflict` relies on and
    /// yielding an unsound lemma.
    ///
    /// Stored as two generation-stamped `Vec`s indexed by `Var` rather than a
    /// `HashMap`: `on_assignment` fires per atom-assignment during SAT
    /// propagation, and the per-access hashing was a measurable cost.  This
    /// map is deliberately *not* pruned on backtrack (`assigned_level` is the
    /// liveness authority), so `assigned_pol_cur` never changes within a
    /// manager's lifetime and the stamp check reduces to "was this var ever
    /// set" -- identical to the previous `HashMap::get` semantics.  A fresh
    /// `TheoryManager` per `Solver::check` re-initialises all three.
    assigned_pol_gen: Vec<u32>,
    assigned_pol_val: Vec<bool>,
    assigned_pol_cur: u32,
    /// Current SAT decision level, mirrored from `on_new_level` / `on_backtrack`.
    /// Used to stamp shadow-trail entries with the level they hold at.
    current_level: u32,
    /// Deduplicated shadow of every theory-relevant SAT assignment, in the
    /// order asserted.  Each variable appears at most once.  See [`TrailAtom`]
    /// for why this exists: it lets us detect an in-place polarity flip by the
    /// SAT core and rebuild theory state soundly rather than trust the stale
    /// incremental state.
    assignment_trail: Vec<TrailAtom>,
    /// Map from a theory variable to its index in `assignment_trail`, for O(1)
    /// flip detection.  Rebuilt whenever the trail is truncated on backtrack.
    ///
    /// Stored as a dense `Vec<u32>` indexed by `Var::index()` (sentinel
    /// `u32::MAX` = absent) rather than a `HashMap`: `on_assignment` fires per
    /// atom-assignment during SAT propagation and the per-access hashing was a
    /// measurable cost on QF_UF.  Grown lazily to cover the variable seen.
    trail_index: Vec<u32>,
    /// Decision level at which each entry of the polarity map currently
    /// holds, pruned on backtrack.  Unlike `assignment_trail` this is
    /// maintained in *both* eager and lazy theory modes, because it backs
    /// [`Self::full_assignment_conflict_clause`] – the sound fallback used
    /// when a theory reason cannot be justified.
    ///
    /// Dense `Vec<u32>` indexed by `Var::index()` storing `level + 1` (so `0`
    /// means "unassigned"): same rationale as [`Self::trail_index`].  Pruned
    /// on backtrack by walking only the shadow-trail entries above the
    /// rollback level (its key set is exactly the set of trail vars), which is
    /// O(pruned) instead of a full `HashMap::retain`.
    assigned_level: Vec<u32>,
    /// Reason terms that are theory *tautologies*: facts the theory layer
    /// injects itself, true in every model and justified by no literal.
    ///
    /// The interned-constant machinery asserts `10 ≠ 20`, `#x00 ≠ #x01` and
    /// `true ≠ false`, and merges two term ids that denote the same constant.
    /// Those assertions carry the constant's own term id as their reason, and
    /// that term id has no SAT variable.  Registering them here is what lets
    /// [`Self::terms_to_conflict_clause`] tell "correctly contributes nothing
    /// to the clause" apart from "justification silently lost".
    tautological_reasons: FxHashSet<TermId>,
    /// Constant numeric args of quantified (un-purified) functions to pin
    /// into arithmetic each combine round; see the Solver field of the same
    /// name for why these exist and why the pin is re-asserted here.
    quant_uf_const_pins: &'a FxHashMap<TermId, num_rational::Rational64>,
    /// Explanations for reason terms that stand for a *derived* equality
    /// propagated between theories.
    ///
    /// `ArithSolver` records a single `TermId` per assertion, so an equality
    /// propagated out of congruence closure (`f(a) = f(b)` because `a = b`) can
    /// only be tagged with one of its own operands – a term that names no
    /// literal.  The EUF explanation of that equality is kept here, keyed by the
    /// tag, and [`Self::terms_to_conflict_clause`] expands the tag into those
    /// literals.  Without this the conflict clause would blame only the
    /// arithmetic atoms and refute a satisfiable formula at level 0.
    ///
    /// The table is **owned by the `Solver`**, not by this manager, because the
    /// arithmetic solver it explains is: `Solver::check` builds a fresh manager
    /// for every MBQI round while deliberately keeping the theory solvers'
    /// state.  A per-manager map started empty in front of a tableau that still
    /// held the previous round's derived equalities.  See
    /// [`DerivedReasons`] for the scope-depth pruning rule.
    derived_reasons: &'a mut DerivedReasons,
    /// Incremental array-theory index (Stage 5).  Solver-owned, so it persists
    /// across the per-round `TheoryManager` rebuilds; the event-driven stages
    /// query it to react to reads/writes during search.
    array_theory: &'a mut super::array_theory::ArrayTheory,
    euf_eq_atoms: Vec<(Var, TermId, TermId, bool)>,
    euf_bool_atoms: Vec<(Var, TermId)>,
    eager_interned: bool,
    /// Whether e-graph watches were registered for the equality atoms (the
    /// watch-based successor of the old `euf_eq_atoms.len() <= 6000` rescan
    /// gate: above that size, equality-atom propagation is disabled).
    eq_atom_watches: bool,
}

impl<'a> TheoryManager<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        manager: &'a TermManager,
        euf: &'a mut EufSolver,
        arith: &'a mut ArithSolver,
        bv: &'a mut BvSolver,
        diff: &'a mut oxiz_theories::DiffLogicSolver,
        array_theory: &'a mut super::array_theory::ArrayTheory,
        bv_terms: &'a FxHashSet<TermId>,
        var_to_constraint: &'a FxHashMap<Var, Constraint>,
        var_to_parsed_arith: &'a FxHashMap<Var, ParsedArithConstraint>,
        term_to_var: &'a FxHashMap<TermId, Var>,
        var_to_term: &'a Vec<TermId>,
        numarg_proxies: &'a FxHashMap<TermId, TermId>,
        quant_uf_const_pins: &'a FxHashMap<TermId, num_rational::Rational64>,
        zero_term: TermId,
        ite_result_terms: &'a FxHashSet<TermId>,
        derived_reasons: &'a mut DerivedReasons,
        theory_mode: TheoryMode,
        statistics: &'a mut Statistics,
        max_conflicts: u64,
        max_decisions: u64,
        has_bv_arith_ops: bool,
        timeout_ms: u64,
        logic: Option<&str>,
        pure_dl: bool,
        sparse_dl: bool,
    ) -> Self {
        #[cfg(feature = "std")]
        let deadline = if timeout_ms > 0 {
            std::time::Instant::now().checked_add(core::time::Duration::from_millis(timeout_ms))
        } else {
            None
        };
        #[cfg(not(feature = "std"))]
        let _ = timeout_ms;
        let mut this = Self {
            manager,
            euf,
            arith,
            bv,
            diff,
            bv_terms,
            var_to_constraint,
            var_to_parsed_arith,
            term_to_var,
            var_to_term,
            numarg_proxies,
            zero_term,
            ite_result_terms,
            derived_reasons,
            level_stack: vec![0],
            asserted_arith_eqs: FxHashSet::default(),
            asserted_arith_eq_trail: Vec::new(),
            asserted_arith_eq_marks: vec![0],
            processed_lit_trail: Vec::new(),
            processed_lit_marks: vec![0],
            processed_lits: FxHashSet::default(),
            processed_count: 0,
            theory_mode,
            pending_equalities: Vec::new(),
            processed_equalities: FxHashMap::default(),
            statistics,
            max_conflicts,
            max_decisions,
            has_bv_arith_ops,
            arrangement_splits: Vec::new(),
            is_dl_family: logic
                .map(|l| matches!(l, "QF_UFIDL" | "UFIDL"))
                .unwrap_or(false),
            dl_pure: pure_dl,
            sparse_dl: sparse_dl || pure_dl,
            interned_int_constants: FxHashMap::default(),
            interned_bv_constants: FxHashMap::default(),
            ite_const_axioms: Self::build_ite_const_axioms(
                var_to_constraint,
                ite_result_terms,
                manager,
            ),
            bool_true_node: None,
            bool_false_node: None,
            resource_exhausted: false,
            unjustified_conflict: false,
            array_theory,
            #[cfg(feature = "std")]
            deadline,
            assigned_pol_gen: Vec::new(),
            assigned_pol_val: Vec::new(),
            assigned_pol_cur: 1,
            current_level: 0,
            assignment_trail: Vec::new(),
            trail_index: Vec::new(),
            assigned_level: Vec::new(),
            tautological_reasons: FxHashSet::default(),
            quant_uf_const_pins,
            euf_eq_atoms: var_to_constraint
                .iter()
                .filter_map(|(&v, c)| match c {
                    Constraint::Eq(l, r) => Some((v, *l, *r, true)),
                    Constraint::Diseq(l, r) => Some((v, *l, *r, false)),
                    _ => None,
                })
                .collect(),
            euf_bool_atoms: var_to_constraint
                .iter()
                .filter_map(|(&v, c)| match c {
                    Constraint::BoolApp(t) => Some((v, *t)),
                    _ => None,
                })
                .collect(),
            eager_interned: false,
            eq_atom_watches: false,
        };
        if this.unique_uf_func_count() <= 32 {
            this.intern_all_euf_terms();
            this.eager_interned = true;
        }
        // Register the watch-based equality-atom propagation index once all
        // endpoints are interned.  The cap mirrors the old rescan gate: past
        // it, propagation is off (search guidance only, never required for a
        // verdict).
        if this.eager_interned && this.euf_eq_atoms.len() <= 6000 {
            this.register_eq_atom_watches();
            this.eq_atom_watches = true;
        }
        // Every TheoryManager construction follows (or starts) a search round;
        // if the BV solver was reset for the round, re-blast its vocabulary at
        // the base scope before any scoped assertion happens (memo no-op when
        // the circuits are already there).
        this.blast_bv_vocabulary_at_base_scope();
        // Pure-DL route: intern every difference atom's watch into the active
        // difference engine BEFORE the search, so closure improvements can
        // propagate not-yet-assigned atoms (Z3 `internalize_atom` timing).
        // See [`Self::intern_pure_dl_atoms`].
        if this.dl_pure {
            this.intern_pure_dl_atoms();
        }
        this
    }

    /// Build the `(ite-result, const) → (le_var, ge_var)` map for the z3-style
    /// triangle axioms by scanning the encoded comparison atoms.
    ///
    /// For every `le`/`ge` atom whose left operand is an axiomatized
    /// `ite`-result term and whose right operand is an integer constant, record
    /// the atom's SAT variable keyed by `(term, const_value)`.  `final_check`
    /// then theory-propagates both variables when arithmetic fixes the term to
    /// that constant, so the triangle clause `(eq ∨ ¬le ∨ ¬ge)` forces the
    /// equality deterministically.
    fn build_ite_const_axioms(
        var_to_constraint: &FxHashMap<Var, Constraint>,
        ite_result_terms: &FxHashSet<TermId>,
        manager: &TermManager,
    ) -> FxHashMap<(TermId, i64), (Var, Var)> {
        let int_const_value = |t: TermId| -> Option<i64> {
            manager.get(t).and_then(|tm| match &tm.kind {
                TermKind::IntConst(n) => n.to_i64(),
                _ => None,
            })
        };
        let mut map: FxHashMap<(TermId, i64), (Option<Var>, Option<Var>)> = FxHashMap::default();
        for (&var, constraint) in var_to_constraint {
            let (lhs, rhs, is_le) = match constraint {
                Constraint::Le(l, r) => (*l, *r, true),
                Constraint::Ge(l, r) => (*l, *r, false),
                _ => continue,
            };
            if !ite_result_terms.contains(&lhs) {
                continue;
            }
            let Some(c) = int_const_value(rhs) else {
                continue;
            };
            let entry = map.entry((lhs, c)).or_insert((None, None));
            if is_le {
                entry.0 = Some(var);
            } else {
                entry.1 = Some(var);
            }
        }
        map.into_iter()
            .filter_map(|(k, (le, ge))| Some((k, (le?, ge?))))
            .collect()
    }

    /// The polarity a theory variable is currently assigned, or `None` if it is
    /// unassigned (not yet decided/propagated by the SAT core).
    #[inline]
    fn assigned_pol_of(&self, var: Var) -> Option<bool> {
        let idx = var.index();
        // `assigned_pol_cur` is constant within a manager (this map is never
        // cleared -- `assigned_level` is the liveness authority), so a stamp
        // equal to `cur` simply means "this var was set at some point".
        let stamp = *self.assigned_pol_gen.get(idx)?;
        if stamp == self.assigned_pol_cur {
            Some(self.assigned_pol_val[idx])
        } else {
            None
        }
    }

    /// Record `var`'s current polarity (direct-indexed, generation-stamped).
    #[inline]
    fn set_assigned_polarity(&mut self, var: Var, polarity: bool) {
        let idx = var.index();
        if idx >= self.assigned_pol_gen.len() {
            self.assigned_pol_gen.resize(idx + 1, 0);
            self.assigned_pol_val.resize(idx + 1, false);
        }
        self.assigned_pol_gen[idx] = self.assigned_pol_cur;
        self.assigned_pol_val[idx] = polarity;
    }

    /// Index of `var` in `assignment_trail`, or `None` if it is not on it.
    #[inline]
    fn trail_idx_of(&self, var: Var) -> Option<usize> {
        match self.trail_index.get(var.index()) {
            Some(&idx) if idx != u32::MAX => Some(idx as usize),
            _ => None,
        }
    }

    /// Record `var -> idx` in the shadow-trail index (direct-indexed).
    #[inline]
    fn trail_idx_set(&mut self, var: Var, idx: usize) {
        let slot = var.index();
        if slot >= self.trail_index.len() {
            self.trail_index.resize(slot + 1, u32::MAX);
        }
        self.trail_index[slot] = idx as u32;
    }

    /// Whether `var` is currently assigned at some decision level (the
    /// liveness authority for shadow-trail entries and propagations).
    #[inline]
    fn is_level_assigned(&self, var: Var) -> bool {
        self.assigned_level
            .get(var.index())
            .is_some_and(|&l| l != 0)
    }

    /// Record `var` as assigned at `level` (direct-indexed, `level + 1`).
    #[inline]
    fn set_assigned_level(&mut self, var: Var, level: u32) {
        let slot = var.index();
        if slot >= self.assigned_level.len() {
            self.assigned_level.resize(slot + 1, 0);
        }
        self.assigned_level[slot] = level + 1;
    }

    /// Returns `true` once the configured wall-clock deadline has passed.
    /// Always `false` when no timeout was set or in `no_std` builds (no clock).
    #[inline]
    fn timed_out(&self) -> bool {
        #[cfg(feature = "std")]
        {
            match self.deadline {
                Some(d) => std::time::Instant::now() >= d,
                None => false,
            }
        }
        #[cfg(not(feature = "std"))]
        {
            false
        }
    }

    /// Returns `true` if a real theory conflict was suppressed because the
    /// conflict limit was reached during this solve.  When set, the caller must
    /// treat any subsequent `Sat` as `Unknown`: the dropped conflict means the
    /// current assignment is not a verified model.
    pub(crate) fn resource_exhausted(&self) -> bool {
        self.resource_exhausted
    }

    /// Returns `true` if a theory conflict was dropped because its justification
    /// could not be accounted for.  Like [`Self::resource_exhausted`], the
    /// caller must then treat a `Sat` as `Unknown`.
    pub(crate) fn unjustified_conflict(&self) -> bool {
        self.unjustified_conflict
    }

    /// The single seam from "a theory refuted these reason terms" to a
    /// [`TheoryCheckResult`].
    ///
    /// Builds the conflict clause with [`Self::terms_to_conflict_clause`] and,
    /// when that cannot justify the conflict, **aborts the conflict** rather
    /// than emitting a clause: it flags [`Self::unjustified_conflict`] and
    /// reports `Sat`, which stops the SAT core from learning anything and makes
    /// the owning `Solver` answer `Unknown`.
    ///
    /// Routing every call site through here is what keeps the empty clause
    /// unrepresentable.  The alternative – returning "the negation of the empty
    /// assignment" – is the empty clause, i.e. a claim that the input is
    /// refuted unconditionally, produced by a code path whose whole premise is
    /// that it does not know why anything is refuted.  Answering `Unknown`
    /// loses a verdict; emitting that clause invents one.
    fn conflict_from_terms(&mut self, terms: &[TermId]) -> TheoryCheckResult {
        match self.terms_to_conflict_clause(terms) {
            Some(conflict) => TheoryCheckResult::Conflict(conflict),
            None => {
                self.unjustified_conflict = true;
                TheoryCheckResult::Sat
            }
        }
    }

    /// Array read-over-write theory propagation (Stage 5 of
    /// `docs/ARRAY_THEORY_PLAN.md`): for every indexed
    /// `select(store(b, i, v), j)`:
    ///   * read-over-write-SAME: if `i = j` in EUF, the axiom forces
    ///     `select = v`;
    ///   * read-over-write-DIFFERENT: if `i ≠ j` is a *proven* disequality, the
    ///     axiom forces `select = select(b, j)` (the `select(b, j)` term is
    ///     pre-created at encode time – see `ArrayTheory::add_row_target` –
    ///     because this pass holds `&TermManager` and cannot `mk_select`).
    ///
    /// Merge the consequence in EUF; if that exposes a contradiction with an
    /// asserted disequality, return the conflict.  SOUND: it only ever merges
    /// a term with the value the array axiom *proves* it equals, so it can
    /// only strengthen, never fabricate.  Two-phase (collect with shared EUF
    /// reads, then merge) so the `&mut check_conflicts` does not alias the
    /// index iteration.
    fn propagate_array_read_over_write(&mut self) -> Option<TheoryCheckResult> {
        let mut to_merge: Vec<(TermId, TermId)> = Vec::new();
        for (_array, select_term) in self.array_theory.select_entries() {
            let Some((store_idx, read_idx, store_val, base_read)) =
                self.array_theory.row_target(select_term)
            else {
                continue;
            };
            let (Some(ni), Some(nj)) = (
                self.euf.term_to_node(store_idx),
                self.euf.term_to_node(read_idx),
            ) else {
                continue;
            };
            if self.euf.are_equal_immutable(ni, nj) {
                to_merge.push((select_term, store_val));
            } else if self.euf.are_proven_disequal(ni, nj) {
                to_merge.push((select_term, base_read));
            }
        }
        for (lhs, rhs) in to_merge {
            let (Some(nl), Some(nr)) = (self.euf.term_to_node(lhs), self.euf.term_to_node(rhs))
            else {
                continue;
            };
            if self.euf.are_equal_immutable(nl, nr) {
                continue;
            }
            let _ = self.euf.merge(nl, nr, lhs);
            if let Some(conflict_terms) = self.euf.check_conflicts() {
                return Some(self.conflict_from_terms(&conflict_terms));
            }
        }
        None
    }

    /// Array extensionality theory propagation (Stage 5): for each array
    /// equality atom `(= a b)` whose operands are PROVEN disequal (`a ≠ b`)
    /// while the witness reads `select(a, k)` and `select(b, k)` are EUF-equal,
    /// extensionality forces `a = b` – a contradiction.  Return the conflict.
    /// SOUND: fires only on a real `a = b` derivation (reads equal at the
    /// witness) contradicting an asserted `a ≠ b`.
    fn check_array_extensionality(&mut self) -> Option<TheoryCheckResult> {
        for &(a, b, _k, sa, sb) in self.array_theory.ext_witnesses() {
            let (Some(na), Some(nb)) = (self.euf.term_to_node(a), self.euf.term_to_node(b)) else {
                continue;
            };
            if !self.euf.are_proven_disequal(na, nb) {
                continue;
            }
            let (Some(nsa), Some(nsb)) = (self.euf.term_to_node(sa), self.euf.term_to_node(sb))
            else {
                continue;
            };
            if !self.euf.are_equal_immutable(nsa, nsb) {
                continue;
            }
            // `a ≠ b` (asserted) but `select(a, k) = select(b, k)` (EUF), so by
            // extensionality `a = b`: contradiction.  The conflict clause is
            // the explanation of `select(a, k) = select(b, k)`.
            let terms = self.euf.explain_eq(nsa, nsb);
            return Some(self.conflict_from_terms(&terms));
        }
        None
    }

    /// Open one theory scope on the EUF, arithmetic and bit-vector solvers.
    ///
    /// Every push of the three solvers goes through here (and every pop through
    /// [`Self::pop_theory_scope`]) so that `derived_reasons` – which outlives
    /// this manager – tracks their true depth.  Counting scopes from
    /// `level_stack` instead would restart at zero for every manager, while a
    /// CDCL(T) search that ends in `Sat` never backtracks and therefore hands
    /// the next manager solvers that are still several scopes deep.
    fn push_theory_scope(&mut self) {
        use oxiz_theories::Theory;

        self.level_stack.push(self.processed_count);
        self.asserted_arith_eq_marks
            .push(self.asserted_arith_eq_trail.len());
        self.processed_lit_marks
            .push(self.processed_lit_trail.len());
        self.euf.push();
        self.arith.push();
        self.bv.push();
        self.diff.push();
        self.derived_reasons.push_scope();
    }

    /// Close one theory scope on the EUF, arithmetic and bit-vector solvers,
    /// dropping the derived-equality explanations that belonged to it.
    fn pop_theory_scope(&mut self) {
        use oxiz_theories::Theory;

        self.level_stack.pop();
        // Retract the EUF-derived equality rows asserted inside this scope,
        // mirroring the arithmetic solver's own scope pop (which removed the
        // rows themselves).  Without this the memo would keep claiming rows
        // exist after a backtrack removed them, permanently suppressing
        // re-assertion of equalities whose rows are gone.
        if let Some(mark) = self.asserted_arith_eq_marks.pop() {
            while self.asserted_arith_eq_trail.len() > mark {
                if let Some(pair) = self.asserted_arith_eq_trail.pop() {
                    self.asserted_arith_eqs.remove(&pair);
                }
            }
        }
        // Same discipline for the per-literal processed guards: the scope pop
        // just rolled the theory solvers back, so literals processed inside
        // it must become processable again.
        if let Some(mark) = self.processed_lit_marks.pop() {
            while self.processed_lit_trail.len() > mark {
                if let Some(lit) = self.processed_lit_trail.pop() {
                    self.processed_lits.remove(&lit);
                }
            }
        }
        self.euf.pop();
        self.arith.pop();
        self.bv.pop();
        self.diff.pop(1);
        self.derived_reasons.pop_scope();
    }

    /// Rebuild all incremental theory state from the deduplicated shadow trail.
    ///
    /// Invoked when the SAT core overwrites a variable's assignment in place
    /// (flips a decision literal's polarity without a matching backtrack – a
    /// wrong assertion-level result from its conflict analysis).  The
    /// incremental EUF / arith / BV solvers still reflect the stale polarity and,
    /// because they support only level-scoped `pop` (not point removal of a
    /// single mid-level assertion), the stale fact cannot be surgically undone.
    /// We therefore reset the theory solvers and replay the corrected
    /// trail level by level, re-establishing exactly one push scope per decision
    /// level so subsequent `on_backtrack` pops stay aligned with `level_stack`.
    ///
    /// Replay continues through every level even after a conflict is found, so
    /// that `level_stack` ends fully populated (`current_level + 1` entries) and
    /// any later backtrack – to any level – pops a matching number of scopes.
    /// The first conflict encountered is remembered and returned; a returned
    /// `Conflict` triggers the SAT core to backtrack, which the now-consistent
    /// scope stack handles correctly.
    /// Re-run the assert-time eager bit-blasting after the embedded BV solver
    /// was reset (see [`Self::resync_theory_state`] and
    /// [`crate::solver::Solver::blast_bv_circuits_at_base_scope`]).  A reset
    /// wipes the clause database *and* the term→bits registry together –
    /// consistent – but the replay that follows re-interns atoms at scoped
    /// levels, and any circuit first wired there is popped by the next
    /// backtrack while its registry entry survives: the encode memo then skips
    /// rebuilding it and the atom is asserted against unwired bits (false
    /// `sat`, see `bv_soundness_integration::issue_17`).  Blasting the whole
    /// constraint vocabulary right after the reset, while no scope is open,
    /// makes the circuits permanent before the replay touches anything.
    fn blast_bv_vocabulary_at_base_scope(&mut self) {
        if !self.bv.at_base_scope() {
            return;
        }
        let mut roots: Vec<TermId> = Vec::new();
        for c in self.var_to_constraint.values() {
            match c {
                Constraint::Eq(l, r)
                | Constraint::Diseq(l, r)
                | Constraint::Lt(l, r)
                | Constraint::Le(l, r)
                | Constraint::Gt(l, r)
                | Constraint::Ge(l, r) => {
                    roots.push(*l);
                    roots.push(*r);
                }
                Constraint::BoolApp(t) => roots.push(*t),
            }
        }
        let mut encoded = rustc_hash::FxHashSet::default();
        for root in roots {
            super::encode::blast_bv_term(self.bv, root, self.manager, &mut encoded);
        }
    }

    fn resync_theory_state(&mut self) -> TheoryCheckResult {
        use oxiz_theories::Theory;
        // Drop all incremental theory state and derived caches.
        //
        // EUF/BV/DL/arith are rebuilt wholesale (the congruence-loss backstop
        // this function exists for).
        //
        // NOTE: an earlier attempt replaced `arith.reset()` with a pop to the
        // base scope (keeping the interned rows so the replay below hits the
        // row cache) and had to be reverted: with rows surviving, the replay
        // is NOT equivalent to a fresh assert path – measured as read6 going
        // 0.18 s -> 22 s and fb_var_5_12 1.6 s -> timeout.  Root cause not
        // yet isolated (candidates: the Diophantine `int_equalities`
        // bookkeeping that `assert_eq` records per replay, or the
        // propagation-bound undo trail).  Do not re-apply without profiling
        // those paths.
        self.euf.reset();
        self.arith.reset();
        self.bv.reset();
        self.diff.reset();
        self.interned_int_constants.clear();
        self.interned_bv_constants.clear();
        self.bool_true_node = None;
        self.bool_false_node = None;
        self.processed_equalities.clear();
        self.pending_equalities.clear();
        // The proof forest these explanations were read out of is gone; the
        // equalities they justified are gone from the tableau with it.
        self.derived_reasons.clear();
        // The pops above undid every EUF-derived equality bound (they are
        // scoped), so the memo that claims they are asserted must go with
        // them; the replay re-asserts each surviving equality against its
        // (still cached) row.
        self.asserted_arith_eqs.clear();
        self.asserted_arith_eq_trail.clear();
        self.asserted_arith_eq_marks = vec![0];
        self.processed_lits.clear();
        self.processed_lit_trail.clear();
        self.processed_lit_marks = vec![0];
        if self.eager_interned {
            self.intern_all_euf_terms();
        }
        // Make the bit-vector circuits permanent again before the level-by-level
        // replay re-interns anything (see the method's docs).
        self.blast_bv_vocabulary_at_base_scope();

        // Rebuild the level-scope bookkeeping to match the current level.
        self.level_stack = vec![0];
        self.processed_count = 0;

        let max_level = self.current_level;
        // Snapshot the trail so we can call `&mut self` methods while iterating.
        let trail = self.assignment_trail.clone();
        let mut first_conflict: Option<TheoryCheckResult> = None;

        for lvl in 0..=max_level {
            if lvl > 0 {
                self.push_theory_scope();
            }
            for atom in trail.iter().filter(|a| a.level == lvl) {
                // `reset()` also clears the BV solver's mirror of outer
                // Boolean assignments.  Lazy-mode shadow trails contain every
                // SAT variable (not only theory atoms), so restore that mirror
                // before replaying the associated theory constraint.
                if let Some(term) = self.var_to_term.get(atom.var.index()).copied() {
                    self.bv.assert_bool_value(term, atom.is_positive);
                }
                let Some(constraint) = self.var_to_constraint.get(&atom.var).cloned() else {
                    continue;
                };
                self.processed_count += 1;
                let result =
                    self.process_constraint(atom.var, constraint, atom.is_positive, self.manager);
                if first_conflict.is_none() && matches!(result, TheoryCheckResult::Conflict(_)) {
                    first_conflict = Some(result);
                }
            }
        }

        first_conflict.unwrap_or(TheoryCheckResult::Sat)
    }

    /// Process Nelson-Oppen equality sharing
    /// Propagates equalities between theories until a fixed point is reached
    #[allow(dead_code)]
    fn propagate_equalities(&mut self) -> TheoryCheckResult {
        // Process all pending equalities
        while let Some(eq) = self.pending_equalities.pop() {
            // Avoid processing the same equality twice
            let key = if eq.lhs < eq.rhs {
                (eq.lhs, eq.rhs)
            } else {
                (eq.rhs, eq.lhs)
            };

            if self.processed_equalities.contains_key(&key) {
                continue;
            }
            self.processed_equalities.insert(key, true);

            // Notify EUF theory
            let lhs_node = self.euf.intern(eq.lhs);
            let rhs_node = self.euf.intern(eq.rhs);
            if let Err(_e) = self
                .euf
                .merge(lhs_node, rhs_node, eq.reason.unwrap_or(eq.lhs))
            {
                // Merge failed - should not happen
                continue;
            }

            // Check for conflicts after merging
            if let Some(conflict_terms) = self.euf.check_conflicts() {
                return self.conflict_from_terms(&conflict_terms);
            }

            // Notify arithmetic theory
            self.arith.notify_equality(eq);
        }

        TheoryCheckResult::Sat
    }

    /// Propagate EUF-derived equalities to the arithmetic solver.
    ///
    /// When EUF fires congruence closure and derives `f(x) = f(y)` because
    /// `x = y` was asserted, the arithmetic solver is unaware of this equality.
    /// This method gathers all arithmetic terms from `var_to_parsed_arith`,
    /// looks each one up in EUF (via `term_to_node`), and for any pair whose
    /// EUF nodes are in the same equivalence class asserts `t1 - t2 = 0` into
    /// the arithmetic solver.
    ///
    /// Note: `euf.intern(t)` uses the `term_to_node` map first, so it correctly
    /// returns the shared node index even when two distinct term IDs (e.g.
    /// `f_x_term` and `f_y_term`) were mapped to the same node via congruence
    /// during `intern_app`.
    ///
    /// The equality crosses a theory boundary, so it must arrive at the tableau
    /// with an **explanation**: `ArithSolver` stores one `TermId` per assertion
    /// and the only term ids available here – `t1`, `t2` – name no literal, so a
    /// conflict resting on the equality would be blamed on the arithmetic atoms
    /// alone.  We therefore ask congruence closure why `t1 = t2` holds
    /// ([`EufSolver::explain_eq`]) and record that answer under the tag `t1` in
    /// `derived_reason_justifications`, where `terms_to_conflict_clause` expands
    /// it back into literals.  An equality congruence closure cannot explain is
    /// not propagated at all: losing a propagation costs completeness, asserting
    /// an unexplainable fact costs soundness.
    fn propagate_euf_equalities_to_arith(
        &mut self,
        dedup: &mut FxHashSet<(TermId, TermId)>,
    ) -> TheoryCheckResult {
        // Collect every unique term ID that appears in any parsed arithmetic
        // constraint.  These are the terms the arithmetic solver knows about.
        let mut arith_terms: Vec<TermId> = Vec::new();
        for parsed in self.var_to_parsed_arith.values() {
            for &(term, _coef) in &parsed.terms {
                if !arith_terms.contains(&term) {
                    arith_terms.push(term);
                }
            }
        }

        // Incremental: group arith terms by EUF equivalence-class root and only
        // consider pairs *within* a class.  The old O(n^2) all-pairs scan (most
        // pairs are in different EUF classes and can never be equal) dominated
        // runtime on QF_UFLIA, where this runs once per full SAT assignment.
        // The class index skips the cross-class pairs for free; `dedup` avoids
        // re-asserting a pair already sent to Arith this call.
        let mut classes: FxHashMap<u32, Vec<TermId>> = FxHashMap::default();
        for term in &arith_terms {
            let Some(node) = self.euf.term_to_node(*term) else {
                continue;
            };
            let root = self.euf.find(node);
            classes.entry(root).or_default().push(*term);
        }

        for members in classes.values() {
            if members.len() < 2 {
                continue;
            }
            // Representative chain, not all pairs: every member is asserted
            // equal to the FIRST member, which transitively equates the whole
            // class in the tableau (t_i − t_0 = 0 pins every t_i to t_0).
            // Asserting all C(k,2) pairs instead built C(k,2) permanent rows
            // per class – on class-heavy inputs (bofill/cmodels scheduling,
            // where one EUF class can hold hundreds of arith terms) that
            // ballooned the tableau past 100k rows for a ~250-constraint
            // problem and every pivot/check walked it all.
            let rep = members[0];
            for &member in &members[1..] {
                let (mut t1, mut t2) = (rep, member);
                if t1 > t2 {
                    std::mem::swap(&mut t1, &mut t2);
                }
                if !dedup.insert((t1, t2)) {
                    continue;
                }
                // EUF has derived t1 = t2 (same class). Assert the equality
                // into the arithmetic solver.  (Batched: no per-equality
                // solve; the caller runs one check after this pass, and
                // the row's reason ids carry precise attribution.)
                self.assert_explained_equality(t1, t2);
            }
        }

        TheoryCheckResult::Sat
    }

    /// Assert an EUF-derived equality `t1 = t2` into the arithmetic solver,
    /// carrying the explanation that justifies it.
    ///
    /// This is the single crossing point between congruence closure and the
    /// tableau, and the only place allowed to tag an arithmetic assertion with a
    /// term that names no literal.  It upholds two invariants:
    ///
    /// * an equality congruence closure cannot explain is **not propagated** –
    ///   skipping it only costs completeness, whereas asserting an unexplainable
    ///   fact makes every conflict that uses it unsound;
    /// * an equality that *is* propagated has its explanation recorded under the
    ///   tag `t1`, so [`Self::terms_to_conflict_clause`] can expand the tag back
    ///   into the literals it stands for.
    ///
    /// Idempotent per theory scope: a pair already asserted at this scope is
    /// skipped (see `asserted_arith_eqs`), so the repeated Nelson-Oppen rounds
    /// and `final_check` calls that rediscover the same EUF merge never
    /// duplicate its tableau rows.
    ///
    /// Does **not** run `arith.check()` itself: every caller batch-asserts a
    /// set of equalities and then runs one check for the whole batch
    /// (the row's own reason ids carry the precise conflict attribution, so
    /// batching loses no core minimality).
    fn assert_explained_equality(&mut self, t1: TermId, t2: TermId) {
        let key = if t1 < t2 { (t1, t2) } else { (t2, t1) };
        if self.asserted_arith_eqs.contains(&key) {
            return;
        }

        let (Some(n1), Some(n2)) = (self.euf.term_to_node(t1), self.euf.term_to_node(t2)) else {
            return;
        };

        // `n1 == n2` means the two term ids were hash-consed onto one node, so
        // the equality is structural and rests on no assertion.  An empty
        // explanation for *distinct* nodes means no proof path was found, and
        // propagating then would re-create exactly the unjustified equality this
        // whole path exists to prevent.
        let justification = self.euf.explain_eq(n1, n2);
        if n1 != n2 && justification.is_empty() {
            return;
        }
        self.derived_reasons.record(t1, justification);

        self.arith.assert_eq(
            &[
                (t1, Rational64::from_integer(1)),
                (t2, Rational64::from_integer(-1)),
            ],
            Rational64::from_integer(0),
            t1,
        );
        self.asserted_arith_eqs.insert(key);
        self.asserted_arith_eq_trail.push(key);
    }

    /// Model-based theory combination.
    ///
    /// Finds shared terms that congruence closure has put in one equivalence
    /// class while the tableau's current model gives them different values.
    /// Two terms can only disagree inside a class, so instead of the naive O(n²)
    /// all-pairs scan we bucket each shared term by its EUF representative node
    /// in a single O(n) pass and compare each later class member against the
    /// first witness.
    ///
    /// A disagreement is a *model* disagreement, not a refutation: the tableau
    /// is free to pick another model that honours the equality.  The previous
    /// implementation reported it as a conflict and built the clause from the
    /// two disagreeing terms, which asserts that those two atoms are jointly
    /// contradictory – nothing entails that.  We instead resolve the
    /// disagreement the Nelson-Oppen way: hand the (explained) equality to the
    /// tableau via [`Self::assert_explained_equality`] and let it decide, so a
    /// conflict is reported only when arithmetic really is refuted and comes
    /// with arithmetic's own core.
    fn model_based_combination(&mut self) -> TheoryCheckResult {
        // Sound bound propagation: resolve forced comparison atoms before the
        // model-based disagreement check.
        if let Some(props) = self.derive_arith_propagations() {
            self.statistics.theory_propagations += props.len() as u64;
            return TheoryCheckResult::Propagated(props);
        }
        // Map EUF representative node -> (witness term, its arith value) for the
        // first class member that carries a concrete arithmetic value.  Terms
        // without an arith value cannot participate in an arith disagreement and
        // are simply skipped (mirroring the old `if let (Some, Some)` guard).
        let mut witness: FxHashMap<u32, (TermId, Rational64)> = FxHashMap::default();
        let mut asserted_any = false;

        // `term_to_var` is a hash map, so iterate in term-id order: which member
        // of a class becomes the witness – and hence which equality is asserted
        // – must not depend on hash iteration order.
        let mut shared_terms: Vec<TermId> = self.term_to_var.keys().copied().collect();
        shared_terms.sort_unstable_by_key(|t| t.raw());
        for term in shared_terms {
            let Some(value) = self.arith.value(term) else {
                continue;
            };
            // `intern` returns the existing node (or creates one, matching the
            // previous behaviour), and `find` yields its equivalence-class root.
            let node = self.euf.intern(term);
            let rep = self.euf.find(node);

            match witness.get(&rep) {
                Some(&(prev_term, prev_value)) => {
                    if prev_value != value {
                        self.assert_explained_equality(prev_term, term);
                        asserted_any = true;
                    }
                }
                None => {
                    witness.insert(rep, (term, value));
                }
            }
        }

        // One batched feasibility check for every equality asserted above.
        if asserted_any {
            use oxiz_theories::Theory;
            if let Ok(oxiz_theories::TheoryCheckResult::Unsat(conflict_terms)) = self.arith.check()
            {
                return self.conflict_from_terms(&conflict_terms);
            }
        }

        // ===== arith → EUF: tentative arrangement (non-convex combination) =====
        //
        // The entailed-equality pass in `nelson_oppen_combine` merges only
        // pairs arithmetic *proves* equal.  When a refutation instead needs
        // the model-suggested arrangement – two interface terms the tableau
        // merely co-locates (equal UF arguments whose congruent results a
        // negated `=` atom keeps apart) – that merge never happens,
        // congruence never fires, and a full assignment whose arrangement was
        // never jointly checked gets accepted: the pete false-SATs (see
        // `docs/studies/2026-08-arithmetic-negated-atoms-false-sat.md`).
        //
        // For each model-equal, EUF-distinct interface pair, merge
        // tentatively inside a scope.  A conflict proves `C ⊢ x ≠ y` for the
        // currently-true facts C (the conflict core minus the tentative
        // edge's own tag); that **derived disequality** is asserted at the
        // current scope with C recorded as its justification, so congruence
        // stops re-proposing the refuted arrangement and any later conflict
        // citing the edge expands back to C.  Sound because C is exactly the
        // proof's other premises (see the tag-collision note in the helper);
        // incomplete because refutations needing several merges at once are
        // not explored.
        self.arrange_model_equal_pairs();

        TheoryCheckResult::Sat
    }

    /// The tentative-arrangement round described on
    /// [`Self::model_based_combination`].  Best-effort and scoped: every
    /// tentative merge lives in its own EUF scope and is popped before the
    /// next pair, so the round never leaves partial merges behind.
    fn arrange_model_equal_pairs(&mut self) {
        use oxiz_theories::Theory;

        // Scoped to the validated family (QF_UFIDL/UFIDL), mirroring the
        // `is_dl_family` gate on bound propagation: on wider inputs the
        // refinement loop can move a search that main answers correctly onto
        // a trajectory that reaches a *different* unchecked arrangement
        // (QF_UFLIA wisas: main `unsat`, with the round `sat` — the round
        // found no refutation for wisas's shape, so it only perturbed the
        // search).  Widen only after that shape is covered.
        if !self.is_dl_family {
            return;
        }

        // Candidate set: interface terms that are UF arguments, grouped by
        // their current arithmetic model value (the same grouping
        // `nelson_oppen_combine`'s model-equal probe uses).
        let uf_args = self.euf.app_argument_terms();
        let mut by_val: FxHashMap<(Rational64, oxiz_core::SortId), Vec<TermId>> =
            FxHashMap::default();
        for &t in self.arith.interface_terms() {
            if uf_args.contains(&t)
                && let Some(v) = self.arith.value(t)
                && let Some(sort) = self.manager.get(t).map(|tm| tm.sort)
            {
                let e = by_val.entry((v, sort)).or_default();
                if !e.contains(&t) {
                    e.push(t);
                }
            }
        }

        const MAX_PAIRS: usize = 64;
        let mut probed = 0usize;
        'groups: for terms in by_val.values() {
            if terms.len() < 2 {
                continue;
            }
            for i in 0..terms.len() {
                for j in (i + 1)..terms.len() {
                    if probed >= MAX_PAIRS {
                        break 'groups;
                    }
                    probed += 1;
                    let (x, y) = (terms[i], terms[j]);

                    // Existing nodes only: interning here would perturb node
                    // creation order (explanation iteration order → conflict
                    // clause tie-breaking → search trajectory) even when the
                    // round derives nothing, flipping unrelated verdicts
                    // (wisas).  A pair without EUF presence is skipped.
                    let (Some(nx), Some(ny)) = (self.euf.term_to_node(x), self.euf.term_to_node(y))
                    else {
                        continue;
                    };
                    if self.euf.are_equal_immutable(nx, ny) || self.euf.are_proven_disequal(nx, ny)
                    {
                        continue;
                    }

                    // Tag for the tentative edge (and, on refutation, for the
                    // derived disequality).  It must name no *existing*
                    // derived-equality justification: filtering the tag back
                    // out of the conflict core assumes every occurrence is
                    // this edge's, so a tag that also justifies another edge
                    // would silently drop that premise from C and let the
                    // asserted diseq claim more than was derived.
                    let tag = [x, y, self.zero_term]
                        .into_iter()
                        .find(|t| self.derived_reasons.literals(*t).is_none());
                    let Some(tag) = tag else { continue };

                    self.euf.push();
                    let _ = self.euf.merge(nx, ny, tag);
                    let conflict = self.euf.check_conflicts();
                    self.euf.pop();

                    let Some(core) = conflict else {
                        continue; // arrangement-consistent; not kept (v1)
                    };
                    // C = the proof's premises minus the tentative edge
                    // itself: `C ⊢ x ≠ y` with every C premise currently
                    // true, so the derived diseq holds for exactly as long
                    // as the scope it is asserted at.
                    let justification: Vec<TermId> =
                        core.into_iter().filter(|t| *t != tag).collect();
                    self.derived_reasons.record(tag, justification);
                    self.euf.assert_diseq(nx, ny, tag);
                    self.arrangement_splits.push((x, y));
                    self.statistics.theory_propagations += 1;
                }
            }
        }
        // ===== Phase 2: the full model arrangement. =====
        //
        // Phase 1 refutes pairs one merge at a time and misses refutations
        // that need several merges simultaneously (congruence fires only
        // once a whole group of model-equal arguments is merged).  So also
        // accumulate ALL candidate merges in one scope and check once.  A
        // conflict there proves the *conjunction* of the merged equalities
        // is incompatible with the current facts — no per-pair diseq is
        // derivable (soundness), but requesting `(= x y)` atoms for the
        // merged pairs lets the next search DECIDE the arrangement, where a
        // true polarity merges through `process_constraint` and the conflict
        // becomes an ordinary learned clause over existing atoms.
        //
        // The requested set is a superset of the proof's actual needs (we
        // cannot attribute the conflict to individual merges without
        // per-edge tags); over-approximating is sound — an internalized
        // equality atom is a pure branching dimension, never a constraint —
        // and bounded by the cap.
        {
            // COMPLETE arrangement: per value-group, merge a spanning
            // CHAIN (consecutive terms) instead of enumerating pairs.
            // A chain realizes the same partition as all-pairs merging at
            // O(group) cost, so there is no cap and no truncation.  The
            // previous 64-pair / 32-merge caps left the arrangement
            // dependent on FxHashMap group order: the fatal pair of a
            // false candidate was probed only against other partners and
            // never against each other, its split atom was never
            // internalized, and the candidate escaped as `sat` — reachable
            // by any clause-DB perturbation that shifted term ids (measured
            // on pete/cxs-bp under trie-vivify; root cause of the
            // trajectory-dependent false-SAT class).
            let mut merged: Vec<(TermId, TermId)> = Vec::new();
            self.euf.push();
            for terms in by_val.values() {
                let mut prev: Option<TermId> = None;
                for &t in terms.iter() {
                    let Some(pt) = prev else {
                        prev = Some(t);
                        continue;
                    };
                    let (Some(np), Some(nt)) =
                        (self.euf.term_to_node(pt), self.euf.term_to_node(t))
                    else {
                        prev = Some(t);
                        continue;
                    };
                    if self.euf.are_equal_immutable(np, nt) || self.euf.are_proven_disequal(np, nt)
                    {
                        prev = Some(t);
                        continue;
                    }
                    let _ = self.euf.merge(np, nt, pt);
                    merged.push((pt, t));
                    prev = Some(t);
                }
            }
            let mut conflicted = self.euf.check_conflicts().is_some();
            if !conflicted && !merged.is_empty() {
                // Cross-theory joint check: congruence may have collapsed
                // applications whose PINNED values (equalities with
                // constants) disagree only in arithmetic — invisible to
                // `check_conflicts`, which sees no EUF disequality between
                // the constants.  Group the arith-valued shared terms by
                // their (now merged) EUF class and let a scoped tableau
                // check refute the arrangement (wisas shape).
                conflicted = self.arrangement_cross_check_arith();
            }
            self.euf.pop();
            if conflicted {
                self.arrangement_splits.extend(merged);
            }
        }
    }

    /// Cross-theory joint check for the tentative arrangement: group every
    /// arith-valued shared term by its current EUF class and assert one
    /// equality per class-disagreement into a scoped tableau; `Unsat` proves
    /// the arrangement is jointly inconsistent (congruence + arithmetic).
    /// Runs INSIDE the arrangement scope: the caller pops the EUF side, this
    /// helper pops its own arith scope.
    fn arrangement_cross_check_arith(&mut self) -> bool {
        use oxiz_theories::Theory;
        let mut witness: FxHashMap<u32, (TermId, Rational64)> = FxHashMap::default();
        let mut pending: Vec<(TermId, TermId)> = Vec::new();
        // Deterministic order (see `model_based_combination`'s note).
        let mut shared_terms: Vec<TermId> = self.term_to_var.keys().copied().collect();
        shared_terms.sort_unstable_by_key(|t| t.raw());
        for term in shared_terms {
            let Some(value) = self.arith.value(term) else {
                continue;
            };
            let Some(node) = self.euf.term_to_node(term) else {
                continue;
            };
            let rep = self.euf.find(node);
            match witness.get(&rep) {
                Some(&(prev, prev_value)) => {
                    if prev_value != value {
                        pending.push((prev, term));
                    }
                }
                None => {
                    witness.insert(rep, (term, value));
                }
            }
        }
        if pending.is_empty() {
            return false;
        }
        self.arith.push();
        for (a, b) in pending {
            self.arith.assert_eq(
                &[
                    (a, Rational64::from_integer(1)),
                    (b, Rational64::from_integer(-1)),
                ],
                Rational64::from_integer(0),
                a,
            );
        }
        let unsat = matches!(
            self.arith.check(),
            Ok(oxiz_theories::TheoryCheckResult::Unsat(_))
        );
        self.arith.pop();
        unsat
    }

    /// Drain the arrangement-split requests collected by the last
    /// [`Self::model_based_combination`] round (see `arrangement_splits`).
    #[must_use]
    pub fn take_arrangement_splits(&mut self) -> Vec<(TermId, TermId)> {
        core::mem::take(&mut self.arrangement_splits)
    }

    /// Bidirectional Nelson–Oppen combination to a fixpoint.
    ///
    /// tip's [`Self::model_based_combination`] is one direction of the equality
    /// exchange – it propagates EUF-derived equalities *into* arithmetic (two
    /// shared terms in one EUF class with different arithmetic values must be
    /// equal, so assert the equality and let the tableau refute it).  The other
    /// direction – arithmetic-**entailed** equalities propagated *into* EUF –
    /// was missing, and its absence is the source of the non-convex
    /// QF_UFLIA/QF_UFIDL false-SAT: arithmetic can force `x = y` (e.g. two
    /// `ite`-result terms both pinned to `2·t`) while EUF holds them distinct
    /// under a `distinct`/disequality, and without propagating that entailed
    /// equality the `distinct` conflict is never seen.
    ///
    /// This closes the loop: alternate the two directions until neither produces
    /// new information (bounded, since each round strictly grows the EUF merge
    /// set or the asserted-equality set), then fall back to the model-based
    /// disagreement check.  Arithmetic-entailed equalities come with their
    /// Farkas reason ([`ArithSolver::entailed_equal_reason`]) and are
    /// recorded under their tag in [`derived_reasons`], so a conflict that cites
    /// the resulting EUF merge expands back to the arithmetic atoms that forced
    /// it – the merge is a *deduction*, never a guess, so it cannot cause a
    /// false `unsat`.
    /// Model value of `t` for interface grouping: pinned constants report
    /// their pin value (true by construction; the tableau assignment may be
    /// stale between the re-pin and the next solve), everything else the
    /// arithmetic solver's current value.
    fn arith_value_with_pins(&self, t: TermId) -> Option<num_rational::Rational64> {
        self.quant_uf_const_pins
            .get(&t)
            .copied()
            .or_else(|| self.arith.value(t))
    }

    fn nelson_oppen_combine(&mut self) -> TheoryCheckResult {
        use oxiz_theories::Theory;
        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;

        // Re-pin the constant numeric arguments of quantified (un-purified)
        // functions into arithmetic.  UNCONDITIONALLY: `term_to_var` survives
        // `pop` while the bounds do not, so `is_interned` cannot distinguish a
        // live pin from a popped one — and the rows are cached per linear
        // form, so re-asserting is a bound re-set on an existing row.  Each
        // pin is a tautology (`c = c`) whose reason tag names no literal; the
        // empty `DerivedReasons` explanation keeps a certificate citing it
        // contributing nothing instead of losing justification.  Without the
        // pin, no interface-equality mechanism can pair `3` with an
        // equal-valued shared `y`, congruence `f(y) = f(3)` never fires, and
        // a refutable input answers `sat` (pr30#3 class).
        for (&t, &v) in self.quant_uf_const_pins.iter() {
            self.arith
                .assert_eq(&[(t, num_rational::Rational64::from_integer(1))], v, t);
            self.derived_reasons.record(t, Vec::new());
        }

        const NO_MAX_ROUNDS: usize = 8;
        for _ in 0..NO_MAX_ROUNDS {
            // ======== arithmetic → EUF: propagate entailed equalities. ========
            //
            // Care graph (cvc5-style watched differences): difference-constraint
            // pairs (x − y ≤ c) + live EUF disequality operands.  No model-equal
            // filter – the probe is sound regardless and catches chain-derived
            // equalities the model-equal filter misses.
            let mut candidates: rustc_hash::FxHashSet<(TermId, TermId)> =
                rustc_hash::FxHashSet::default();
            for parsed in self.var_to_parsed_arith.values() {
                if parsed.terms.len() == 2 {
                    let (t0, c0) = (parsed.terms[0].0, parsed.terms[0].1);
                    let (t1, c1) = (parsed.terms[1].0, parsed.terms[1].1);
                    let is_diff = (c0 == Rational64::from_integer(1)
                        && c1 == Rational64::from_integer(-1))
                        || (c0 == Rational64::from_integer(-1)
                            && c1 == Rational64::from_integer(1));
                    if is_diff {
                        candidates.insert(if t0 < t1 { (t0, t1) } else { (t1, t0) });
                    }
                }
            }
            for (a, b) in self.euf.live_diseq_pairs() {
                candidates.insert(if a < b { (a, b) } else { (b, a) });
            }
            // Model-equal shared-term pairs: arithmetic terms the simplex
            // currently assigns the *same* value are candidates for an entailed
            // equality (e.g. two purified UF-argument proxies `v1`, `v2` both
            // pinned to `3`).  Difference-constraint pairs alone miss these, so
            // without this the congruence `f(v1) = f(v2)` never fires.  Group
            // the shared interface by arith value and add same-valued pairs
            // (capped) for the probe.  Sound: `entailed_equal_reason`
            // re-verifies entailment per pair.
            const MAX_MODEL_EQ_PAIRS: usize = 256;
            let mut by_val: rustc_hash::FxHashMap<Rational64, Vec<TermId>> =
                rustc_hash::FxHashMap::default();
            // Only UF-ARGUMENT terms can enable a congruence `f(x)=f(y)` when
            // merged, so restrict the model-equal probe set to them (the
            // purification proxies are UF arguments; UF *results*, plain
            // variables, and other arith terms are not, and probing their
            // model-equal pairs is pure overhead that times out satisfiable
            // instances).  This is the `shared` set used by the care graph.
            let uf_args = self.euf.app_argument_terms();
            for &t in self.arith.interface_terms() {
                if uf_args.contains(&t) {
                    if let Some(v) = self.arith_value_with_pins(t) {
                        by_val.entry(v).or_default().push(t);
                    }
                }
            }
            let mut added_pairs = 0usize;
            for terms in by_val.values() {
                if added_pairs >= MAX_MODEL_EQ_PAIRS {
                    break;
                }
                if terms.len() < 2 {
                    continue;
                }
                'pair: for i in 0..terms.len() {
                    for j in (i + 1)..terms.len() {
                        if added_pairs >= MAX_MODEL_EQ_PAIRS {
                            break 'pair;
                        }
                        let (a, b) = (terms[i], terms[j]);
                        candidates.insert(if a < b { (a, b) } else { (b, a) });
                        added_pairs += 1;
                    }
                }
            }
            let mut merged_any = false;
            for &(x, y) in &candidates {
                let l_node = self.euf.intern(x);
                let r_node = self.euf.intern(y);
                if self.euf.are_equal(l_node, r_node) {
                    continue;
                }
                // Cheap sound pre-filter: if the current arithmetic model
                // assigns x and y *different* values, then arithmetic does NOT
                // entail x = y -- a satisfying model exists with x != y, so the
                // equal-entailment probe (two simplex feasibility checks)
                // would return None.  Skip it.  On SAT instances nearly every
                // spurious difference-constraint / live-diseq candidate pair
                // has distinct model values, so this prunes the hundreds of
                // wasted probes per call to the handful that are model-equal.
                if let (Some(a), Some(b)) =
                    (self.arith_value_with_pins(x), self.arith_value_with_pins(y))
                {
                    if a != b {
                        continue;
                    }
                }
                let Some(reason) = self.arith.entailed_equal_reason(x, y) else {
                    continue;
                };
                self.derived_reasons.record(x, reason);
                let _ = self.euf.merge(l_node, r_node, x);
                merged_any = true;
            }
            // cvc5 watchedVariableCannotBeZero: propagate arith-entailed
            // DISEQUALITIES.  For candidate pairs now EUF-merged (by the
            // equality loop above or by congruence), if arith forces x≠y,
            // assert the disequality in EUF → immediate conflict.
            for &(x, y) in &candidates {
                let lx = self.euf.intern(x);
                let ly = self.euf.intern(y);
                if !self.euf.are_equal(lx, ly) {
                    continue;
                }
                let Some(reason) = self.arith.entailed_disequal_reason(x, y) else {
                    continue;
                };
                self.derived_reasons.record(x, reason);
                self.euf.assert_diseq(lx, ly, x);
                if let Some(conflict_terms) = self.euf.check_conflicts() {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                    return self.conflict_from_terms(&conflict_terms);
                }
                merged_any = true;
            }
            if merged_any {
                if let Some(conflict_terms) = self.euf.check_conflicts() {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                    return self.conflict_from_terms(&conflict_terms);
                }
            }
            if !merged_any {
                break;
            }

            // ---- EUF → arithmetic: the new merges may put two terms in one
            //       class with different arithmetic values; assert the equality
            //       and let the tableau refute it. ----
            let mut dedup: FxHashSet<(TermId, TermId)> = FxHashSet::default();
            let eu = self.propagate_euf_equalities_to_arith(&mut dedup);
            if let TheoryCheckResult::Conflict(_) = eu {
                self.statistics.theory_conflicts += 1;
                self.statistics.conflicts += 1;
                if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
                return eu;
            }
            // `eu == Sat` here; any other variant would be terminal and is
            // covered by returning it directly.
            if !matches!(eu, TheoryCheckResult::Sat) {
                return eu;
            }
            match self.arith.check() {
                Ok(TheoryCheckResultEnum::Sat) => {
                    // continue to the next arith→EUF round
                }
                Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) => {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                    return self.conflict_from_terms(&conflict_terms);
                }
                Ok(_) => {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
                Err(_) => {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
            }
        }
        // Fixpoint reached (or round bound hit): final model-based
        // disagreement check covers any residual EUF-class/arithmetic-value
        // disagreement the entailed-equality pass did not force.
        self.model_based_combination()
    }

    /// Sound forward theory propagation of comparison atoms (bound propagation).
    ///
    /// Scans every UNASSIGNED comparison atom and, for each whose truth is
    /// forced by the current arithmetic bounds, emits a propagation with a
    /// sound all-true-atom reason.  Resolves `ite` side-conditions
    /// deductively from decided values instead of letting CDCL branch on them.
    fn derive_arith_propagations(&mut self) -> Option<Vec<(Lit, SmallVec<[Lit; 8]>)>> {
        const MAX_ATOMS: usize = 1024;
        if self.var_to_constraint.len() > MAX_ATOMS {
            return None;
        }
        let candidates: Vec<ArithPropCandidate> = self
            .var_to_constraint
            .iter()
            .filter_map(|(&var, _)| {
                if self.assigned_pol_of(var).is_some() {
                    return None;
                }
                // Skip equality-constrained atoms: `var_to_parsed_arith` carries
                // an `Le` placeholder for them, so probing `x <= y` and
                // propagating the equality `x = y` would be unsound (`x <= y`
                // does not force `x = y`; `x != y` is the disjunction `x<y ∨
                // x>y`, not a single comparison). See encode.rs `TermKind::Eq`.
                if matches!(self.var_to_constraint.get(&var), Some(Constraint::Eq(..))) {
                    return None;
                }
                let parsed = self.var_to_parsed_arith.get(&var)?;
                let (less, strict) = match parsed.constraint_type {
                    ArithConstraintType::Lt => (true, true),
                    ArithConstraintType::Le => (true, false),
                    ArithConstraintType::Gt => (false, true),
                    ArithConstraintType::Ge => (false, false),
                };
                Some((var, parsed.terms.to_vec(), parsed.constant, less, strict))
            })
            .collect();
        let mut props: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
        for (var, terms, constant, less, strict) in candidates {
            let Some((truth, reasons)) = self
                .arith
                .comparison_entailed_reason(&terms, constant, less, strict)
            else {
                continue;
            };
            let mut reason_lits: SmallVec<[Lit; 8]> = SmallVec::new();
            let mut ok = true;
            for &r in &reasons {
                match self.term_to_var.get(&r) {
                    Some(&rv) if self.assigned_pol_of(rv) == Some(true) => {
                        reason_lits.push(Lit::pos(rv));
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                props.push((
                    if truth { Lit::pos(var) } else { Lit::neg(var) },
                    reason_lits,
                ));
            }
        }
        if props.is_empty() { None } else { Some(props) }
    }

    /// Incremental bound propagation: forward-propagate arithmetic atoms
    /// whose polarity is *forced* by the simplex's current variable bounds.
    ///
    /// For each UNASSIGNED `Le`/`Lt`/`Ge`/`Gt` atom `e ◦ c`, derive a SOUND
    /// bound on `e` from the variable bounds (the Dutertre–de Oliveira
    /// relaxation – never tighter than the true bound), and if that bound
    /// already forces the comparison, emit the atom's literal with the
    /// bound's antecedent atoms as the reason.
    ///
    /// This is the z3 `:arith-bound-prop` analogue: cheap (`O(atoms)`, no LP
    /// solve), sound (a looser bound that still forces ⇒ genuinely forced),
    /// and the single mechanism that closes finite-domain QF_UFIDL (vhard*) –
    /// asserting `(= x k)` pins `x ∈ [k,k]`, which forces every `x ◦ c` ite
    /// condition at the *current* (low) decision level, so conflicts that the
    /// recurrence eventually triggers are detected shallowly (level ~2, like
    /// z3) instead of deep (level ~96).
    ///
    /// `tighten = true` runs [`Simplex::propagate_bounds`] first so transitive
    /// bounds (through tableau rows, e.g. the recurrence) feed the derivation;
    /// `tighten = false` uses only directly-asserted bounds (cheaper, catches
    /// the first propagation level).
    ///
    /// Equality atoms are EXCLUDED (the `Le`-placeholder landmine: a `not(=)`
    /// disequality is the disjunction `x<y ∨ x>y`, never a single comparison –
    /// see `encode.rs`).
    fn derive_arith_bound_propagations(
        &mut self,
        tighten: bool,
    ) -> Option<Vec<(Lit, SmallVec<[Lit; 8]>)>> {
        use oxiz_theories::arithmetic::DeltaRational;
        // Collect candidate atoms as a flat `(var, constant, less, strict)` list –
        // all `Copy`, so no per-candidate allocation.  The atom's term vector is
        // fetched lazily into a single reused buffer below, which removes the
        // `Vec<(Var, Vec<terms>, …)>` allocation that dominated this
        // propagator (it inlined into the SAT loop as `extend`/`spec_extend`).
        let candidates: Vec<(Var, Rational64, bool, bool)> = self
            .var_to_constraint
            .iter()
            .filter_map(|(&var, constraint)| {
                if self.assigned_pol_of(var).is_some() {
                    return None; // already decided
                }
                // Skip equality-constrained atoms: `var_to_parsed_arith`
                // carries an `Le` placeholder for them, so probing the bound
                // and propagating would treat a disequality as a single
                // comparison (unsound). See `encode.rs` `TermKind::Eq`.
                if matches!(constraint, Constraint::Eq(..)) {
                    return None;
                }
                let parsed = self.var_to_parsed_arith.get(&var)?;
                let (less, strict) = match parsed.constraint_type {
                    ArithConstraintType::Lt => (true, true),
                    ArithConstraintType::Le => (true, false),
                    ArithConstraintType::Gt => (false, true),
                    ArithConstraintType::Ge => (false, false),
                };
                Some((var, parsed.constant, less, strict))
            })
            .collect();
        if candidates.is_empty() {
            return None;
        }
        // Tighten the tableau's variable bounds ONCE (to a fixpoint) so the
        // per-atom derivation below sees transitive (recurrence-derived)
        // bounds cheaply.  Done here rather than inside `derive_expr_bound_reasons`
        // (which runs per atom) so the O(tableau) cost is paid once per
        // assertion, not per atom × per assertion.
        if tighten {
            self.arith.tighten_tableau_bounds();
        }
        let mut props: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
        // One reused term buffer for every candidate (DL atoms have ≤2 terms,
        // so capacity stabilises immediately): the immutable borrow of
        // `var_to_parsed_arith` is scoped to the refill and ends before the
        // `&mut self.arith` derivation call.
        let mut terms_buf: Vec<(TermId, Rational64)> = Vec::new();
        for (var, constant, less, strict) in candidates {
            {
                let Some(parsed) = self.var_to_parsed_arith.get(&var) else {
                    continue;
                };
                terms_buf.clear();
                terms_buf.extend(parsed.terms.iter().copied());
            }
            let c_dr = DeltaRational::from_rational(constant);
            // Derive the bound on `e := Σ coefᵢ·termᵢ` (the atom's LHS) by
            // passing constant = 0; `constant` is the atom's RHS THRESHOLD,
            // compared below, NOT part of the expression.  (Passing `constant`
            // here would fold the threshold into the expression and make the
            // check read `e + c ◦ c` ≡ `e ◦ 0` – a soundness bug for any atom
            // with a non-zero threshold.)
            let (lo, hi) = self.arith.derive_expr_bound_reasons(
                &terms_buf,
                Rational64::from_integer(0),
                tighten,
            );
            // Determine whether the atom `e ◦ c` is forced TRUE or FALSE.
            //
            //   less (e ≤ c / e < c): TRUE ⇔ upper(e) ≤/< c ;  FALSE ⇔ lower(e) >/≥ c
            //   !less (e ≥ c / e > c): TRUE ⇔ lower(e) ≥/> c ;  FALSE ⇔ upper(e) </≤ c
            let forced: Option<(bool, Vec<TermId>)> = if less {
                let true_forced = hi
                    .as_ref()
                    .map(|(v, _)| if strict { *v < c_dr } else { *v <= c_dr });
                if true_forced == Some(true) {
                    hi.map(|(_, r)| (true, r))
                } else {
                    let false_forced = lo
                        .as_ref()
                        .map(|(v, _)| if strict { *v >= c_dr } else { *v > c_dr });
                    if false_forced == Some(true) {
                        lo.map(|(_, r)| (false, r))
                    } else {
                        None
                    }
                }
            } else {
                let true_forced = lo
                    .as_ref()
                    .map(|(v, _)| if strict { *v > c_dr } else { *v >= c_dr });
                if true_forced == Some(true) {
                    lo.map(|(_, r)| (true, r))
                } else {
                    let false_forced = hi
                        .as_ref()
                        .map(|(v, _)| if strict { *v <= c_dr } else { *v < c_dr });
                    if false_forced == Some(true) {
                        hi.map(|(_, r)| (false, r))
                    } else {
                        None
                    }
                }
            };
            let Some((truth, derived_reason)) = forced else {
                continue;
            };
            // Build the reason-literal set from the derived bound's antecedent
            // atoms (the cheap, derived-reason path).  SOUND only on the
            // difference-logic family (QF_IDL/QF_UFIDL): the caller gates this
            // propagator to those logics, where the prop tracker's single-atom
            // bounds are sufficient justifications.  On denser logics
            // (QF_LIA/UFLIA/ANIA) the derived reason can be an insufficient
            // subset of the true Farkas proof (the bound's real justification
            // combines many atoms the prop tracker cannot summarize), so the
            // gate excludes them.
            let reason_terms = derived_reason;
            let mut reason_lits: SmallVec<[Lit; 8]> = SmallVec::new();
            let mut ok = true;
            for &r in &reason_terms {
                let Some(&rv) = self.term_to_var.get(&r) else {
                    ok = false;
                    break;
                };
                if rv == var {
                    continue;
                }
                match self.assigned_pol_of(rv) {
                    Some(true) => reason_lits.push(Lit::pos(rv)),
                    Some(false) => reason_lits.push(Lit::neg(rv)),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok && !reason_lits.is_empty() {
                props.push((
                    if truth { Lit::pos(var) } else { Lit::neg(var) },
                    reason_lits,
                ));
            }
        }
        if props.is_empty() { None } else { Some(props) }
    }

    /// If `t` is a `__oxiz_numarg` proxy (a fresh variable that
    /// `purify_numeric_uf_args` substituted for a numeric constant), return the
    /// constant's value.  Linear scan of `numarg_proxies` (the map is small –
    /// one entry per distinct numeric UF-arg constant, e.g. ~28 on vhard7).
    fn proxy_const_value(&self, t: TermId) -> Option<Rational64> {
        for (const_t, proxy_t) in self.numarg_proxies.iter() {
            if *proxy_t == t {
                return direct_const_value(self.manager, *const_t);
            }
        }
        None
    }

    /// Feed one asserted atom to the incremental DL solver and report whether
    /// it was exactly handled, was outside the fragment, or created a negative
    /// cycle.  Uses the seeded-SPFA
    /// `add_*_check` (O(affected) per edge), the cheap DL-primary path.
    /// Folds `__oxiz_numarg` proxies and bare constants into the atom's RHS so
    /// exact two-variable differences feed the graph; single-variable bounds
    /// deliberately remain on the simplex path.  SOUND: a DL negative cycle
    /// is a valid refutation.
    ///
    /// Normalise an atom's linear form to a difference pair `(x, y, c)`
    /// reading `x − y ○ c` per the caller's constraint type: folds every
    /// constant sub-term — whether a `purify_numeric_uf_args` proxy
    /// (`__oxiz_numarg`, recoverable via `numarg_proxies`) or a bare
    /// `IntConst`/`RealConst` — into the RHS constant `c` (restoring the
    /// difference-logic shape the global purification substitute destroyed),
    /// maps a single-variable bound through the canonical zero term
    /// (`x ≤ k` ≡ `x − 0 ≤ k` — Z3's dense-solver numeral internalization),
    /// and rejects every non-unit-difference shape (3+ variables, non-unit
    /// coefficients, pure constants).  `None` = not difference-logic-shaped.
    fn dl_normalized_pair(
        &self,
        terms: &[(TermId, Rational64)],
        constant: Rational64,
    ) -> Option<(TermId, TermId, Rational64)> {
        let mut adj_constant = constant;
        let mut real_terms: SmallVec<[(TermId, Rational64); 4]> = SmallVec::new();
        for &(t, c) in terms {
            let folded = self
                .proxy_const_value(t)
                .or_else(|| direct_const_value(self.manager, t));
            if let Some(v) = folded {
                adj_constant -= c * v;
            } else {
                real_terms.push((t, c));
            }
        }
        let one = Rational64::from_integer(1);
        match real_terms.as_slice() {
            // Pure constant atom (e.g. `0 ≤ k`): nothing for the DL engines.
            [] => None,
            [(v, coef)] => {
                // Single-variable bound `coef·v ≤ adj_constant`: only unit
                // coefficients are difference-logic-shaped.
                if *coef == one {
                    Some((*v, self.zero_term, adj_constant))
                } else if *coef == -one {
                    Some((self.zero_term, *v, adj_constant))
                } else {
                    None
                }
            }
            [(a, ca), (b, cb)] => {
                // Difference `x − y`: one +1 coefficient, one −1.
                if *ca == one && *cb == -one {
                    Some((*a, *b, adj_constant))
                } else if *cb == one && *ca == -one {
                    Some((*b, *a, adj_constant))
                } else {
                    None // not a unit difference
                }
            }
            // 3+ real variables: genuinely non-difference.
            _ => None,
        }
    }

    fn diff_primary_check(
        &mut self,
        var: Var,
        terms: &[(TermId, Rational64)],
        constant: Rational64,
        ctype: ArithConstraintType,
        is_eq: bool,
        is_positive: bool,
    ) -> DlPrimaryResult {
        use oxiz_theories::DiffLogicResult;
        let Some((xt, yt, c)) = self.dl_normalized_pair(terms, constant) else {
            return DlPrimaryResult::NotApplicable;
        };
        let dla = DlAtom {
            var,
            x: xt,
            y: yt,
            c,
            is_eq,
            ctype,
        };
        // Dense integer path (Z3 `theory_dense_diff_logic`): exact i64
        // weights over integer-sorted plain numeric terms, incremental
        // closure with occurrence-list propagation.  Serves the PURE
        // difference-logic route only — a vocabulary that mixes in UF,
        // `ite`s or quantifiers keeps the seeded-SPFA sparse engine below,
        // matching Z3 (the dense solver is installed by `setup_QF_IDL`
        // alone) and keeping mixed problems' conflict, unsat-core and
        // clause-budget behaviour byte-identical to the general path.
        if self.dl_pure
            && let Some(feed) = self.dense_feed(&dla, is_positive)
        {
            return self.feed_dense_edges(dla.var, &feed, is_positive);
        }
        // Sparse path — the dedicated difference engine for the *declared*
        // difference-logic logics that the dense integer core does not cover
        // (QF_RDL's reals; QF_UFIDL's UF combination), mirroring Z3, which
        // installs a difference solver per logic and never for the general
        // LIA mix.  Feeding it from arbitrary logics interleaves a second
        // conflict source with the simplex's explanations on shared atoms
        // and perturbs the trail-consistency invariants the conflict-clause
        // builder checks (`repro_disjunctive_lia`).
        if !self.sparse_dl {
            return DlPrimaryResult::NotApplicable;
        }
        // 2-var differences only — feeding single-var bounds through the
        // sparse zero-node hub was measured net-negative (the zero vertex
        // inflates the seeded SPFA per-edge check), so those defer to the
        // simplex here.  Both endpoints must be plain numeric Int/Real-sorted
        // terms (the dense eligibility above additionally requires Int and an
        // i64 weight).
        if yt == self.zero_term || xt == self.zero_term {
            return DlPrimaryResult::NotApplicable;
        }
        for t in [xt, yt] {
            let Some(td) = self.manager.get(t) else {
                return DlPrimaryResult::NotApplicable;
            };
            if !is_plain_numeric_term(td) {
                return DlPrimaryResult::NotApplicable;
            }
            let Some(sort) = self.manager.sorts.get(td.sort) else {
                return DlPrimaryResult::NotApplicable;
            };
            if !sort.is_int() && !sort.is_real() {
                return DlPrimaryResult::NotApplicable;
            }
        }
        let origin = self.term_for_var(var);
        if let DiffLogicResult::Conflict(cycle_terms) =
            feed_dl_atom_inc(&mut *self.diff, &dla, is_positive, origin)
        {
            #[cfg(feature = "std")]
            if theory_trace_enabled() {
                eprintln!("oxiz-tconf\tdiff");
            }
            return DlPrimaryResult::Conflict(self.conflict_from_terms(&cycle_terms));
        }
        DlPrimaryResult::Consistent
    }

    /// Dense-core eligibility for one DL atom: the **watch orientation**
    /// `(s, t, k)` — the exact integer reading `t − s ≤ k` of the atom's
    /// TRUE polarity, with strict bounds tightened over ℤ — plus the edges
    /// to assert at the given polarity (Z3 `internalize_atom`: the positive
    /// edge is `(s→t, k)`, the negative edge is `(t→s, −k−1)`; an equality
    /// asserts both directions when positive and nothing when negative).
    ///
    /// `None` when the dense integer core does not apply: non-integer solver,
    /// an endpoint that is not a plain numeric Int-sorted term, or a derived
    /// weight outside the exactness envelope.
    fn dense_feed(&self, dla: &DlAtom, pol: bool) -> Option<DenseFeed> {
        let watch = self.dl_watch_of(dla, &dla.c)?;
        let edges = if watch.is_eq {
            if pol {
                vec![
                    (watch.watch_s, watch.watch_t, watch.watch_k),
                    (watch.watch_t, watch.watch_s, -watch.watch_k),
                ]
            } else {
                Vec::new() // disequality: not DL-representable
            }
        } else if pol {
            vec![(watch.watch_s, watch.watch_t, watch.watch_k)]
        } else {
            // ¬(t − s ≤ k) ⟺ t − s ≥ k+1 ⟺ s − t ≤ −k−1
            vec![(watch.watch_t, watch.watch_s, -watch.watch_k - 1)]
        };
        Some(DenseFeed {
            watch_s: watch.watch_s,
            watch_t: watch.watch_t,
            watch_k: watch.watch_k,
            is_eq: watch.is_eq,
            edges,
        })
    }

    /// The TRUE-polarity integer watch `(s, t, k)` of a difference atom
    /// (shared by [`Self::dense_feed`] and the eager
    /// [`Self::intern_pure_dl_atoms`] pass):
    ///
    /// - `Le: x−y ≤ c` → `(s, t, k) = (y, x, c)`
    /// - `Lt: x−y < c` → `x−y ≤ c−1` → `(y, x, c−1)`
    /// - `Ge: x−y ≥ c` → `y−x ≤ −c` → `(x, y, −c)`
    /// - `Gt: x−y > c` → `y−x ≤ −c−1` → `(x, y, −c−1)`
    /// - `Eq: x = y` → both directions ≤ `c` (and `−c`)
    ///
    /// `None` when an endpoint is not a plain numeric Int-sorted term or the
    /// tightened weight leaves the dense core's exact i64 envelope.
    fn dl_watch_of(&self, dla: &DlAtom, c: &Rational64) -> Option<DlWatch> {
        use ArithConstraintType::*;
        if !self.diff.is_integer() {
            return None;
        }
        for t in [dla.x, dla.y] {
            let td = self.manager.get(t)?;
            if !is_plain_numeric_term(td) {
                return None;
            }
            let sort = self.manager.sorts.get(td.sort)?;
            if !sort.is_int() {
                return None;
            }
        }
        let (x, y) = (dla.x, dla.y);
        let one = Rational64::from_integer(1);
        let k_of = |r: &Rational64| oxiz_theories::DiffLogicSolver::dense_fit(r);
        if dla.is_eq {
            let ck = k_of(c)?;
            return Some(DlWatch {
                watch_s: y,
                watch_t: x,
                watch_k: ck,
                is_eq: true,
            });
        }
        // The TRUE-polarity reading `t − s ≤ k`:
        //   Le: x−y ≤ c       →  (s, t, k) = (y, x, c)
        //   Lt: x−y < c       →  x−y ≤ c−1 →  (y, x, c−1)
        //   Ge: x−y ≥ c       →  y−x ≤ −c  →  (x, y, −c)
        //   Gt: x−y > c       →  y−x ≤ −c−1 → (x, y, −c−1)
        let (s, t, k) = match dla.ctype {
            Le => (y, x, k_of(c)?),
            Lt => (y, x, k_of(&(c - one))?),
            Ge => (x, y, k_of(&(-*c))?),
            Gt => (x, y, k_of(&(-*c - one))?),
        };
        Some(DlWatch {
            watch_s: s,
            watch_t: t,
            watch_k: k,
            is_eq: false,
        })
    }

    /// Feed a dense-core plan: interns the atom into the closure's occurrence
    /// lists (once per SAT variable), asserts the polarity's edges, and
    /// converts conflicts / propagations back into theory results.
    fn feed_dense_edges(&mut self, var: Var, feed: &DenseFeed, pol: bool) -> DlPrimaryResult {
        use oxiz_theories::DlAssert;
        let key = var.index() as u32;
        let (s, t) = match (
            self.diff.dense_intern_term(feed.watch_s),
            self.diff.dense_intern_term(feed.watch_t),
        ) {
            (Some(s), Some(t)) => (s, t),
            _ => {
                // Node budget exceeded: the dense core degrades to a partial
                // propagator; this atom defers to the sparse/simplex path.
                return DlPrimaryResult::NotApplicable;
            }
        };
        if let Some(core) = self.diff.dense() {
            if !core.has_atom(key) {
                core.intern_atom(key, s, t, feed.watch_k, feed.is_eq);
            }
        }
        for &(src_term, dst_term, w) in &feed.edges {
            let (Some(src), Some(dst)) = (
                self.diff.dense_intern_term(src_term),
                self.diff.dense_intern_term(dst_term),
            ) else {
                return DlPrimaryResult::NotApplicable;
            };
            let outcome = self
                .diff
                .dense()
                .map(|core| core.assert_edge(src, dst, w, key, pol));
            match outcome {
                Some(DlAssert::Conflict(reason)) => {
                    #[cfg(feature = "std")]
                    if theory_trace_enabled() {
                        eprintln!("oxiz-tconf\tdiff-dense");
                    }
                    return match self.dense_reason_to_conflict(&reason) {
                        Some(c) => DlPrimaryResult::Conflict(c),
                        // A reason atom without a matching live assignment
                        // cannot form a valid conflict clause — refuse to
                        // fabricate one and defer to the simplex.
                        None => DlPrimaryResult::NotApplicable,
                    };
                }
                Some(DlAssert::Ok) => {}
                None => return DlPrimaryResult::NotApplicable,
            }
        }
        // Drain closure-derived propagations (may be empty).  Propagating is
        // a pure-difference-logic behaviour (Z3's occurrence lists belong to
        // the dense solver, which `setup_QF_IDL` installs only for a
        // difference-logic vocabulary): on the general path the closure stays
        // a conflict engine only, so mixed problems keep their clause budget.
        if self.dl_pure
            && let Some(props) = self.dense_take_propagations()
        {
            return DlPrimaryResult::Propagated(props);
        }
        // Discard anything queued (unreachable when pure: drained above).
        let _ = self.diff.dense_take_propagations();
        DlPrimaryResult::Consistent
    }

    /// Pre-search, eager dense-core atom interning for the pure-DL route (Z3
    /// `internalize_atom`, which runs at clause-assertion time — before any
    /// decision): register every difference-shaped arithmetic atom's watch in
    /// the closure's occurrence lists up front, so closure improvements can
    /// propagate atoms the search has not yet assigned.  Without this, a
    /// watch exists only after the atom's first assignment, the closure can
    /// propagate nothing new, and CDCL must decide every atom by hand
    /// (super_queen37-1: 35k decisions / 1.9k conflicts where Z3's eagerly
    /// internalized closure needs 66).
    ///
    /// Asserts nothing — edges still flow only through assignments (the
    /// occurrence lists are watch-only).  Idempotent: `intern_atom` keys on
    /// the SAT variable, and re-constructions of the manager over the same
    /// vocabulary re-register nothing.  Stops early if the node budget
    /// degrades the core (assignment-time feeding then degrades exactly as
    /// before this pass existed).
    fn intern_pure_dl_atoms(&mut self) {
        let atoms: Vec<(Var, ParsedArithConstraint, bool)> = self
            .var_to_parsed_arith
            .iter()
            .map(|(var, parsed)| {
                let is_eq = matches!(self.var_to_constraint.get(var), Some(Constraint::Eq(_, _)));
                (*var, parsed.clone(), is_eq)
            })
            .collect();
        for (var, parsed, is_eq) in atoms {
            let Some((x, y, c)) = self.dl_normalized_pair(&parsed.terms, parsed.constant) else {
                continue;
            };
            let dla = DlAtom {
                var,
                x,
                y,
                c,
                is_eq,
                ctype: parsed.constraint_type,
            };
            let Some(watch) = self.dl_watch_of(&dla, &dla.c) else {
                continue;
            };
            if !self.diff.dense_exact() {
                return;
            }
            let (Some(s), Some(t)) = (
                self.diff.dense_intern_term(watch.watch_s),
                self.diff.dense_intern_term(watch.watch_t),
            ) else {
                continue;
            };
            let key = var.index() as u32;
            if let Some(core) = self.diff.dense()
                && !core.has_atom(key)
            {
                core.intern_atom(key, s, t, watch.watch_k, watch.is_eq);
            }
        }
    }

    /// Break pure-DL routing: the DL engines rejected an atom, so the
    /// simplex must take over arithmetic.  Every live arith assignment on
    /// the shadow trail is replayed into the simplex (in trail order), after
    /// which the caller asserts the rejected atom through the general path.
    /// Idempotent: once `dl_pure` is false this is a no-op.
    fn break_dl_purity(&mut self) {
        if !self.dl_pure {
            return;
        }
        self.dl_pure = false;
        let trail: Vec<(Var, bool)> = self
            .assignment_trail
            .iter()
            .map(|a| (a.var, a.is_positive))
            .collect();
        for (var, is_positive) in trail {
            let Some(parsed) = self.var_to_parsed_arith.get(&var).cloned() else {
                continue;
            };
            self.arith_assert_parsed(var, &parsed, is_positive);
        }
    }

    /// Assert one parsed arithmetic atom into the simplex at the current
    /// polarity (the shared body of the `process_constraint` assert arms and
    /// the [`Self::break_dl_purity`] replay).
    fn arith_assert_parsed(&mut self, var: Var, parsed: &ParsedArithConstraint, is_positive: bool) {
        let terms: Vec<(TermId, Rational64)> = parsed.terms.iter().copied().collect();
        let reason = parsed.reason_term;
        let constant = parsed.constant;
        use super::types::ArithConstraintType::{Ge, Gt, Le, Lt};
        // Equalities: the positive polarity is the tableau row (`assert_eq`);
        // the negative polarity (a disequality) never reached the simplex in
        // `process_constraint` either (the trichotomy clauses carry the
        // split), so the replay mirrors that.
        if matches!(self.var_to_constraint.get(&var), Some(Constraint::Eq(_, _))) {
            if is_positive {
                self.arith.assert_eq(&terms, constant, reason);
            }
            return;
        }
        match (parsed.constraint_type, is_positive) {
            (Lt, true) | (Ge, false) => self.arith.assert_lt(&terms, constant, reason),
            (Le, true) | (Gt, false) => self.arith.assert_le(&terms, constant, reason),
            (Gt, true) | (Le, false) => self.arith.assert_gt(&terms, constant, reason),
            (Ge, true) | (Lt, false) => self.arith.assert_ge(&terms, constant, reason),
        }
    }

    /// Convert dense-core propagations into `(literal, reason literals)`
    /// pairs, dropping every propagation whose head is already assigned or
    /// whose reasons are not all currently assigned with the justifying
    /// polarity (a stale edge from a mid-level flip).  Returns `None` when
    /// nothing survives.
    fn dense_take_propagations(&mut self) -> Option<Vec<(Lit, SmallVec<[Lit; 8]>)>> {
        let pending = self.diff.dense_take_propagations();
        if pending.is_empty() {
            return None;
        }
        let mut out: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
        for prop in pending {
            let head = Var::new(prop.key);
            if self.trail_idx_of(head).is_some() {
                continue; // already assigned — nothing to propagate
            }
            let mut reason: SmallVec<[Lit; 8]> = SmallVec::new();
            let mut ok = true;
            for &(rkey, rpol) in &prop.reason {
                let rvar = Var::new(rkey);
                let Some(idx) = self.trail_idx_of(rvar) else {
                    ok = false;
                    break;
                };
                // Use the *currently assigned* polarity; it must match the
                // justification's (edges pop in sync with scopes).  A
                // mismatch means the trail diverged — drop the propagation
                // rather than risk an invalid reason clause.
                if self.assignment_trail[idx].is_positive != rpol {
                    ok = false;
                    break;
                }
                reason.push(if rpol { Lit::pos(rvar) } else { Lit::neg(rvar) });
            }
            if ok && !reason.is_empty() {
                out.push((
                    if prop.pol {
                        Lit::pos(head)
                    } else {
                        Lit::neg(head)
                    },
                    reason,
                ));
            }
        }
        if out.is_empty() { None } else { Some(out) }
    }

    /// Convert a dense-core conflict reason into a `TheoryCheckResult`
    /// conflict clause.  `None` when a reason atom has no matching live
    /// assignment (cannot happen in a scope-consistent trail; guards
    /// against flips).
    fn dense_reason_to_conflict(&mut self, reason: &[(u32, bool)]) -> Option<TheoryCheckResult> {
        let mut lits: SmallVec<[Lit; 8]> = SmallVec::new();
        for &(rkey, rpol) in reason {
            let rvar = Var::new(rkey);
            let idx = self.trail_idx_of(rvar)?;
            if self.assignment_trail[idx].is_positive != rpol {
                return None;
            }
            lits.push(if rpol { Lit::pos(rvar) } else { Lit::neg(rvar) });
        }
        // The conflict clause refutes the conjunction of the justifying
        // atoms: negate every reason literal.
        let conflict: SmallVec<[Lit; 8]> = lits.iter().map(|l| l.negate()).collect();
        Some(TheoryCheckResult::Conflict(conflict))
    }

    /// Add an equality to be shared between theories
    #[allow(dead_code)]
    fn add_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: Option<TermId>) {
        self.pending_equalities
            .push(EqualityNotification { lhs, rhs, reason });
    }

    /// Sentinel function ID used for array `select(array, index)` in EUF.
    ///
    /// `Spur::into_inner()` always returns a `NonZeroU32` (>= 1), so 0 is safe
    /// to use as a special, collision-free function ID for the built-in select
    /// operation.  By interning `select(a, i)` as `intern_app(term, SELECT_FUNC_ID,
    /// [a_node, i_node])`, the EUF congruence closure engine treats select like any
    /// other binary function application and will automatically derive
    /// `select(a, x) = select(a, y)` whenever `x = y` is merged.
    const SELECT_FUNC_ID: u32 = 0;

    /// Intern a term into EUF, using `intern_app` for Apply terms and
    /// `TermKind::Select` terms so that congruence closure works correctly.
    ///
    /// Plain `intern` creates opaque nodes with no function-symbol or argument
    /// information, which prevents the congruence closure algorithm from firing
    /// when argument classes are merged.
    ///
    /// `Select(array, index)` is treated as a binary function application with
    /// the special function ID `SELECT_FUNC_ID` (0).  This ensures that when
    /// `x = y` causes their EUF nodes to merge, congruence automatically
    /// derives `select(a, x) = select(a, y)`, which in turn allows further
    /// congruence steps (e.g., `f(select(a,x)) = f(select(a,y))`).
    ///
    /// Iterative: `Apply` arguments and `Select` operands are interned through
    /// an explicit frame stack (post-order, left to right – the recursive
    /// order), so operand nesting depth cannot overflow the native call
    /// stack.  `euf.term_to_node` remains the cross-call memo, so shared
    /// sub-terms of the hash-consed DAG are interned once.
    #[allow(dead_code)]
    fn intern_term_deep(&mut self, term: TermId, manager: &TermManager) -> u32 {
        let mut frames: Vec<InternFrame> = Vec::new();
        let mut current = term;
        'open: loop {
            // Intern `current`, descending into application operands first.
            let mut value: u32 = loop {
                if let Some(idx) = self.euf.term_to_node(current) {
                    break idx;
                }
                match Self::intern_operands(current, manager) {
                    Some((func_id, operands)) => match operands.first().copied() {
                        Some(first) => {
                            frames.push(InternFrame {
                                term: current,
                                func_id,
                                operands,
                                next: 1,
                                nodes: SmallVec::new(),
                            });
                            current = first;
                        }
                        None => {
                            break self.euf.intern_app(
                                current,
                                func_id,
                                SmallVec::<[u32; 4]>::new(),
                            );
                        }
                    },
                    None => break self.intern_leaf_deep(current, manager),
                }
            };

            // Hand the finished operand node to the innermost application.
            loop {
                let Some(mut frame) = frames.pop() else {
                    return value;
                };
                frame.nodes.push(value);
                if let Some(&child) = frame.operands.get(frame.next) {
                    frame.next += 1;
                    frames.push(frame);
                    current = child;
                    continue 'open;
                }
                value = self.euf.intern_app(frame.term, frame.func_id, frame.nodes);
            }
        }
    }

    /// The application structure of `term` for EUF interning: `Apply` uses its
    /// function symbol, `Select(array, index)` is a binary application of the
    /// sentinel [`Self::SELECT_FUNC_ID`] so that congruence closure fires when
    /// the index (or array) arguments become equal.  Everything else is a leaf.
    fn intern_operands(
        term: TermId,
        manager: &TermManager,
    ) -> Option<(u32, SmallVec<[TermId; 4]>)> {
        match manager.get(term).map(|t| &t.kind) {
            Some(TermKind::Apply { func, args, .. }) => {
                Some((func.into_inner().get(), args.clone()))
            }
            Some(TermKind::Select(array, index)) => Some((
                Self::SELECT_FUNC_ID,
                SmallVec::from_slice(&[*array, *index]),
            )),
            _ => None,
        }
    }

    /// Intern a non-application term for [`Self::intern_term_deep`]: integer
    /// constants get a canonical node plus pairwise disequalities, everything
    /// else a plain opaque node.
    fn intern_leaf_deep(&mut self, term: TermId, manager: &TermManager) -> u32 {
        if let Some(t) = manager.get(term) {
            if let TermKind::IntConst(n) = &t.kind {
                // Intern the integer constant as an EUF node and maintain
                // pairwise disequalities between *distinct* integer values.
                //
                // EUF has no built-in notion of numeric inequality.  Without
                // explicit disequality edges, a congruence chain equating a
                // node merged with `10` and one merged with `20` would not
                // produce a conflict.  We therefore assert `10 ≠ 20` etc.
                //
                // Performance: we track one *canonical* EUF node per unique
                // integer value.  When the same value appears again (e.g. as a
                // fresh TermId created during MBQI instantiation) we merge the
                // new node into the canonical one.  This bounds the number of
                // entries – and therefore of pairwise disequality edges – to the
                // number of *distinct* literal values in the formula, preventing
                // the O(n²) blowup that arises when MBQI creates many fresh
                // TermIds for the same integer literal across iterations.
                if let Some(val) = n.to_i64() {
                    let new_node = self.euf.intern(term);
                    // Both the merge and the disequalities below carry `term`
                    // as their reason and `term` names no literal; they are
                    // true in every model.  Declaring that keeps
                    // `terms_to_conflict_clause` able to distinguish "omitted
                    // because tautological" from "justification lost".
                    self.tautological_reasons.insert(term);
                    if let Some(&canonical) = self.interned_int_constants.get(&val) {
                        // This value already has a canonical node.  Merge the
                        // new term's node into it so that congruence closure
                        // treats them as equal (they represent the same number).
                        // Ignore merge errors: the nodes may already be in the
                        // same class if this term was interned before.
                        let _ = self.euf.merge(new_node, canonical, term);
                        return canonical;
                    }
                    // First time we see this value: register the canonical node
                    // and assert disequality against every other distinct value.
                    let diseq_targets: Vec<u32> =
                        self.interned_int_constants.values().copied().collect();
                    for other_node in diseq_targets {
                        self.euf.assert_diseq(new_node, other_node, term);
                    }
                    self.interned_int_constants.insert(val, new_node);
                    return new_node;
                }
                // BigInt too large for i64 -- fall through to plain intern.
            }
        }
        self.euf.intern(term)
    }

    /// Intern a term into EUF for congruence closure, using `intern_app` for
    /// Apply and Select terms so that congruence fires correctly.
    ///
    /// Unlike `intern_term_deep`, this variant does NOT add IntConst pairwise
    /// disequality edges.  Those edges are necessary for conflict detection when
    /// numeric constants are compared via the EUF layer, but they cause spurious
    /// UNSAT in SAT cases where the ArithSolver is the one tracking numeric
    /// inequalities.  This function is used exclusively inside
    /// `process_constraint` for equality/disequality assertions so that
    /// `f(a)=f(b)` congruence works while arithmetic stays in the ArithSolver.
    ///
    /// Iterative: `Apply` arguments and `Select` operands are interned through
    /// an explicit [`InternFrame`] stack in post-order, left to right – exactly
    /// the order the recursive version used, which matters because
    /// `intern_app` assigns node indices in creation order.  Operand nesting
    /// depth is therefore bounded by memory rather than by the native call
    /// stack.  `euf.term_to_node` remains the memo, so shared sub-terms of the
    /// hash-consed DAG are interned once.
    fn intern_term_for_congruence(&mut self, term: TermId, manager: &TermManager) -> u32 {
        let mut frames: Vec<InternFrame> = Vec::new();
        let mut current = term;
        'open: loop {
            // Intern `current`, descending into application operands first.
            let mut value: u32 = loop {
                if let Some(idx) = self.euf.term_to_node(current) {
                    break idx;
                }
                match Self::intern_operands(current, manager) {
                    Some((func_id, operands)) => match operands.first().copied() {
                        Some(first) => {
                            frames.push(InternFrame {
                                term: current,
                                func_id,
                                operands,
                                next: 1,
                                nodes: SmallVec::new(),
                            });
                            current = first;
                        }
                        None => {
                            break self.euf.intern_app(
                                current,
                                func_id,
                                SmallVec::<[u32; 4]>::new(),
                            );
                        }
                    },
                    None => break self.intern_leaf_for_congruence(current, manager),
                }
            };

            // Hand the finished operand node to the innermost application.
            loop {
                let Some(mut frame) = frames.pop() else {
                    return value;
                };
                frame.nodes.push(value);
                if let Some(&child) = frame.operands.get(frame.next) {
                    frame.next += 1;
                    frames.push(frame);
                    current = child;
                    continue 'open;
                }
                value = self.euf.intern_app(frame.term, frame.func_id, frame.nodes);
            }
        }
    }

    /// Intern a non-application term for [`Self::intern_term_for_congruence`]:
    /// bit-vector constants get a canonical node plus pairwise disequalities
    /// against the other distinct constants of the same width, everything else
    /// a plain opaque node.  Unlike [`Self::intern_leaf_deep`], integer
    /// constants get **no** disequality edges (see the caller's docs).
    fn intern_leaf_for_congruence(&mut self, term: TermId, manager: &TermManager) -> u32 {
        if let Some(t) = manager.get(term) {
            if let TermKind::BitVecConst { value, width } = &t.kind {
                // Register the BV constant as an EUF node and maintain pairwise
                // disequalities between *distinct* same-width constant values.
                //
                // EUF has no built-in notion that two different bit-vector
                // literals are unequal.  Without explicit disequality edges, a
                // congruence chain that equates a node merged with `#x00` and one
                // merged with `#x01` (e.g. `g(a)=#x00`, `g(b)=#x01`, `a=b`) would
                // not produce a conflict.  We therefore assert `#x00 ≠ #x01` etc.
                //
                // As with `interned_int_constants`, we keep one canonical EUF
                // node per distinct `(value, width)` pair: when the same value
                // reappears (a fresh TermId) we merge it into the canonical node,
                // bounding the number of pairwise edges by the count of distinct
                // BV literals rather than the total number of term IDs.
                //
                // The key carries every limb of the value.  Truncating it to
                // the low 64 bits made `0` and `2^64` the *same* key at width
                // 128, so the two constants were merged into one EUF class –
                // and the merge was recorded as tautological, which is exactly
                // what it was not.  `(distinct (g a) (g b))` over those two
                // constants was then reported `unsat`.
                let key = (
                    value.iter_u64_digits().collect::<SmallVec<[u64; 2]>>(),
                    *width,
                );
                let new_node = self.euf.intern(term);
                // Every edge asserted from here carries `term` as its reason
                // and `term` names no literal: two ids for the same constant
                // really are equal and two distinct constants really are
                // unequal, in every model.  Declare that so a conflict clause
                // can omit it *knowingly*.
                self.tautological_reasons.insert(term);
                if let Some(&canonical) = self.interned_bv_constants.get(&key) {
                    let _ = self.euf.merge(new_node, canonical, term);
                    return canonical;
                }
                // First time we see this value: assert disequality against every
                // other distinct constant of the SAME width (different widths are
                // different sorts and are never merged), then register it.
                let diseq_targets: Vec<u32> = self
                    .interned_bv_constants
                    .iter()
                    .filter_map(|(&(_, w), &node)| (w == *width).then_some(node))
                    .collect();
                for other_node in diseq_targets {
                    self.euf.assert_diseq(new_node, other_node, term);
                }
                self.interned_bv_constants.insert(key, new_node);
                return new_node;
            }
        }
        self.euf.intern(term)
    }

    /// Ensure canonical EUF nodes for Boolean true/false exist, with a
    /// disequality between them.  Returns `(true_node, false_node)`.
    fn ensure_bool_nodes(&mut self) -> (u32, u32) {
        if let (Some(t), Some(f)) = (self.bool_true_node, self.bool_false_node) {
            return (t, f);
        }
        // Use sentinel TermIds that will never collide with real terms.
        // TermId(u32::MAX) and TermId(u32::MAX - 1) are reserved for this.
        let true_term = TermId::new(u32::MAX);
        let false_term = TermId::new(u32::MAX - 1);
        let t = self.euf.intern(true_term);
        let f = self.euf.intern(false_term);
        // `true ≠ false` holds in every model and rests on no literal.
        self.tautological_reasons.insert(true_term);
        self.euf.assert_diseq(t, f, true_term);
        self.bool_true_node = Some(t);
        self.bool_false_node = Some(f);
        (t, f)
    }

    /// Look up the term ID for a SAT variable.
    /// Returns a sentinel zero TermId if not found.
    #[inline]
    fn term_for_var(&self, var: Var) -> TermId {
        self.var_to_term
            .get(var.index())
            .copied()
            .unwrap_or_else(|| TermId::new(0))
    }

    /// Register every shared term of a parsed arithmetic constraint in EUF.
    ///
    /// `intern_term_for_congruence` descends only through the *arguments* of an
    /// application, so an application buried inside an arithmetic expression –
    /// the `f(a)` of `(+ (f a) b)` – never reached congruence closure at all.
    /// With `a = b` asserted, `f(a) = f(b)` was therefore never derived and
    /// `(= a b) ∧ (> (+ (f a) b) (+ (f b) a))` came back `sat`, a model that
    /// does not exist.  The same hole swallowed `(select arr i)` under `(+ …)`.
    ///
    /// The linear parser has already reduced the expression to exactly the
    /// opaque terms the tableau reasons about, so interning those – and only
    /// those – is both necessary and sufficient: after it, the two solvers share
    /// the same atoms and every congruence the tableau could use is available.
    fn intern_arith_shared_terms(&mut self, var: Var, manager: &TermManager) {
        let Some(parsed) = self.var_to_parsed_arith.get(&var) else {
            return;
        };
        // Copy the term ids out so the map borrow ends before the `&mut self`
        // interning calls below.
        let shared: SmallVec<[TermId; 4]> = parsed.terms.iter().map(|&(t, _c)| t).collect();
        for term in shared {
            self.intern_term_for_congruence(term, manager);
        }
    }

    /// Look up the BV bit-width of a term from its sort, if it has a BV sort.
    fn bv_width_of(&self, term: TermId, manager: &TermManager) -> Option<u32> {
        manager
            .get(term)
            .and_then(|t| manager.sorts.get(t.sort))
            .and_then(|s| s.bitvec_width())
    }

    /// Bit-blast both operands of a BV constraint into the embedded SAT solver.
    ///
    /// Each side is encoded recursively; a bare leaf that the recursive encoder
    /// cannot handle falls back to a fresh BV variable of the operand's width.
    /// Returns `true` if both operands are BV-sorted with equal width (so that
    /// `assert_eq` / `assert_neq` may be called safely), `false` otherwise.
    fn bit_blast_bv_pair(&mut self, lhs: TermId, rhs: TermId, manager: &TermManager) -> bool {
        let (lw, rw) = match (
            self.bv_width_of(lhs, manager),
            self.bv_width_of(rhs, manager),
        ) {
            (Some(lw), Some(rw)) if lw == rw => (lw, rw),
            _ => return false,
        };
        let mut encoded: FxHashSet<TermId> = FxHashSet::default();
        if !encode_bv_term_recursive(self.bv, lhs, manager, &mut encoded) {
            self.bv.new_bv(lhs, lw);
        }
        if !encode_bv_term_recursive(self.bv, rhs, manager, &mut encoded) {
            self.bv.new_bv(rhs, rw);
        }
        true
    }

    /// Run the embedded BV SAT check after the caller has asserted a constraint.
    ///
    /// Records `constraint_term` so the conflict clause is non-empty, then
    /// returns `Some(Conflict(..))` if the embedded solver reports UNSAT and
    /// `None` otherwise (so the caller falls through to its conservative path).
    ///
    /// `operands` are the two sides of the atom just asserted.  When the check
    /// comes back SAT they are handed to [`debug_verify_bv_circuits`], the
    /// debug-only model-validity net: every bit-blasted node under them must
    /// reproduce its own operation concretely on the model the solver just
    /// found.  That is the check which distinguishes "the search is right" from
    /// "the circuit is wrong", and it costs nothing in release builds.
    fn bv_run_check(
        &mut self,
        constraint_term: TermId,
        operands: (TermId, TermId),
        manager: &TermManager,
    ) -> Option<TheoryCheckResult> {
        use oxiz_theories::Theory;
        use oxiz_theories::TheoryCheckResult as TheoryCheckResultEnum;
        self.bv.record_constraint_term(constraint_term);
        match self.bv.check() {
            Ok(TheoryCheckResultEnum::Unsat(conflict_terms)) => {
                Some(self.conflict_from_terms(&conflict_terms))
            }
            Ok(TheoryCheckResultEnum::Sat) => {
                debug_verify_bv_circuits(self.bv, operands.0, manager);
                debug_verify_bv_circuits(self.bv, operands.1, manager);
                None
            }
            _ => None,
        }
    }

    /// Bit-blast `lhs`/`rhs`, assert `lhs != b` at the bit level, and check.
    ///
    /// Returns `Some(Conflict(..))` on a detected BV theory conflict, `None`
    /// otherwise (including when the operands are not equal-width BV terms).
    fn bv_check_neq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        constraint_term: TermId,
        manager: &TermManager,
    ) -> Option<TheoryCheckResult> {
        if !self.bit_blast_bv_pair(lhs, rhs, manager) {
            return None;
        }
        self.bv.assert_neq(lhs, rhs);
        self.bv_run_check(constraint_term, (lhs, rhs), manager)
    }

    /// Bit-blast `lhs`/`rhs`, assert `lhs = b` at the bit level, and check.
    ///
    /// Returns `Some(Conflict(..))` on a detected BV theory conflict, `None`
    /// otherwise (including when the operands are not equal-width BV terms).
    fn bv_check_eq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        constraint_term: TermId,
        manager: &TermManager,
    ) -> Option<TheoryCheckResult> {
        if !self.bit_blast_bv_pair(lhs, rhs, manager) {
            return None;
        }
        self.bv.assert_eq(lhs, rhs);
        self.bv_run_check(constraint_term, (lhs, rhs), manager)
    }

    /// Process a theory constraint
    fn process_constraint(
        &mut self,
        var: Var,
        constraint: Constraint,
        is_positive: bool,
        manager: &TermManager,
    ) -> TheoryCheckResult {
        // Idempotence guard (see `processed_lits`): the SAT core re-sends
        // already-assigned literals (same-polarity re-send after a backtrack
        // that did not pop this literal's scope, propagation replays).  Every
        // effect of this literal is still live at the current scope in that
        // case, so re-processing would only duplicate tableau rows / DL edges
        // / BV encodings.  A literal whose scope WAS popped had its guard
        // entry popped with it and re-processes normally.
        let lit_key = (var, is_positive);
        if self.processed_lits.contains(&lit_key) {
            // Same-polarity re-send whose effects are still live (see the
            // comment above): idempotently a no-op.  Skipping here is what
            // keeps the sparse DL engine from re-adding duplicate edges and
            // re-running an O(affected) SPFA per re-sent literal — measured
            // 350k feeds for a ~7k-atom problem on gryzzles.37, with the
            // re-feeds dominating the whole run.
            return TheoryCheckResult::Sat;
        }
        self.processed_lit_trail.push(lit_key);
        match constraint {
            Constraint::Eq(lhs, rhs) => {
                if is_positive {
                    // Positive assignment: a = b, tell EUF to merge.
                    // Use the constraint term (which has a SAT variable) as the
                    // merge reason so that conflict clause generation can find it
                    // in term_to_var.
                    let constraint_term = self.term_for_var(var);
                    // Use intern_term_for_congruence so that Apply/Select terms are
                    // registered with intern_app, enabling EUF congruence closure
                    // (e.g., a=b → f(a)=f(b)).  This variant does NOT add IntConst
                    // pairwise disequality edges, keeping arithmetic reasoning in the
                    // ArithSolver and avoiding spurious UNSAT in SAT cases.
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    if let Err(_e) = self.euf.merge(lhs_node, rhs_node, constraint_term) {
                        // Merge failed - should not happen in normal operation
                        return TheoryCheckResult::Sat;
                    }

                    // Check for immediate conflicts
                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        // Convert term IDs to literals for conflict clause
                        return self.conflict_from_terms(&conflict_terms);
                    }

                    // For arithmetic equalities, also send to ArithSolver
                    self.intern_arith_shared_terms(var, manager);
                    if let Some(parsed) = self.var_to_parsed_arith.get(&var).cloned() {
                        // Pure-DL fast path: the dense core owns arithmetic
                        // (conflicts + propagation); the simplex never sees
                        // the atom (Z3 `setup_QF_IDL`'s dense solver).
                        if self.dl_pure {
                            match self.diff_primary_check(
                                var,
                                &parsed.terms,
                                parsed.constant,
                                ArithConstraintType::Le,
                                true,
                                is_positive,
                            ) {
                                DlPrimaryResult::Conflict(dl_conflict) => return dl_conflict,
                                DlPrimaryResult::Propagated(props) => {
                                    return TheoryCheckResult::Propagated(props);
                                }
                                DlPrimaryResult::Consistent => return TheoryCheckResult::Sat,
                                DlPrimaryResult::NotApplicable => {
                                    self.break_dl_purity();
                                }
                            }
                        }
                        self.arith.assert_eq(
                            &parsed.terms.iter().copied().collect::<Vec<_>>(),
                            parsed.constant,
                            parsed.reason_term,
                        );
                        // Record a propagation bound ONLY for a GENUINE
                        // `var = constant` equality (plain variable directly
                        // equated to a numeric constant).  Such a bound's
                        // single-atom reason is sufficient (no EUF chain), so
                        // the cheap derived-reason propagator stays sound.
                        // Other equalities (EUF-mediated, or whose linear parse
                        // dropped an operand) are skipped – their bound's
                        // reason would be incomplete.
                        if let Some(fv) = genuine_fixed_var(lhs, rhs, manager) {
                            self.arith.note_fixed_var(lhs, fv, parsed.reason_term);
                        }
                        // Incremental DL conflict check for equalities (the
                        // pure path returned above; sparse engine, HEAD order).
                        if let DlPrimaryResult::Conflict(dl_conflict) = self.diff_primary_check(
                            var,
                            &parsed.terms,
                            parsed.constant,
                            ArithConstraintType::Le,
                            true,
                            is_positive,
                        ) {
                            return dl_conflict;
                        }
                        // Eager detection of the CHEAP conflict class only
                        // (crossed bounds, O(vars), no pivoting / B&B).
                        // The full LP + integer feasibility solve runs at
                        // `final_check`: a full simplex + branch-and-bound
                        // per literal assignment made every SAT step pay
                        // O(tableau) over a tableau that carries one row per
                        // assigned atom (QF_AUFLIA/swap: thousands of full
                        // solves, none of which the reference solvers run).
                        if let Ok(oxiz_theories::TheoryCheckResult::Unsat(conflict_terms)) =
                            self.arith.check_bound_conflicts()
                        {
                            return self.conflict_from_terms(&conflict_terms);
                        }
                    }

                    // For bitvector equalities, also send to BvSolver
                    // Handle variables, constants, and BV operations
                    // Check if terms have BV sort (not just if they're in bv_terms)
                    let lhs_is_bv = manager
                        .get(lhs)
                        .and_then(|t| manager.sorts.get(t.sort))
                        .is_some_and(|s| s.is_bitvec());
                    let rhs_is_bv = manager
                        .get(rhs)
                        .and_then(|t| manager.sorts.get(t.sort))
                        .is_some_and(|s| s.is_bitvec());

                    // Bit-blast the equality through the *general* recursive
                    // encoder rather than a hand-rolled case analysis over
                    // operand shapes.
                    //
                    // The previous implementation dispatched on a whitelist of
                    // "BV operation" kinds that listed only the arithmetic and
                    // bitwise ops (`bvadd`/`bvmul`/`bvand`/`bvudiv`/...).  Every
                    // BV term whose head was outside that list – `concat`,
                    // `extract`, the shifts `bvshl`/`bvlshr`/`bvashr`, and any
                    // BV-sorted `ite` (which is what `bvsmod`, `bvcomp`,
                    // `rotate_*`, `zero_extend`/`sign_extend` lower to) – matched
                    // none of the cases, left `did_assert` false, and so was
                    // never asserted into the embedded SAT solver at all.  The
                    // atom then survived as a *free boolean*, and the solver
                    // happily reported `sat` with a model that does not satisfy
                    // it (`(= (concat #b000000 w) #x10)` answered `sat, w = #b00`
                    // where every model is impossible).
                    //
                    // `bv_check_eq` bit-blasts both sides with
                    // `encode_bv_term_recursive` – which handles the full BV
                    // TermKind set and pins `BitVecConst` leaves to their concrete
                    // bits – asserts the bit-level equality and consults the
                    // embedded SAT solver.  It is the same path the negative-`Eq`
                    // and `Diseq` branches already take, so the four polarities of
                    // a BV (dis)equality now share one encoding.
                    if lhs_is_bv
                        && rhs_is_bv
                        && let Some(result) = self.bv_check_eq(lhs, rhs, constraint_term, manager)
                    {
                        return result;
                    }
                } else {
                    // Negative assignment: a != b, tell EUF about disequality.
                    // Use the constraint term as the reason (it has a SAT variable).
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    self.euf.assert_diseq(lhs_node, rhs_node, constraint_term);

                    // Check for immediate conflicts (if a = b was already derived)
                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        return self.conflict_from_terms(&conflict_terms);
                    }

                    // For bit-vector operands also send the disequality to the BV
                    // solver.  Mirrors the positive branch: fully bit-blast both
                    // operands, assert `a != b` at the bit level, then consult the
                    // embedded SAT solver.  This catches e.g. `not(= x x)` and
                    // `not(= (bvadd x y) (bvadd y x))`, which the EUF layer alone
                    // cannot refute (it has no bit-level arithmetic semantics).
                    if let Some(result) = self.bv_check_neq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                }
            }
            Constraint::Diseq(lhs, rhs) => {
                if is_positive {
                    // Positive assignment: a != b.
                    // Use the constraint term as the reason for EUF disequality.
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    self.euf.assert_diseq(lhs_node, rhs_node, constraint_term);

                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        return self.conflict_from_terms(&conflict_terms);
                    }

                    // BV disequality (e.g. `(distinct x x)`): bit-blast and assert
                    // `a != b`, mirroring the negative-Eq branch.
                    if let Some(result) = self.bv_check_neq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                } else {
                    // Negative assignment: ~(a != b) means a = b.
                    // Use the constraint term as the merge reason.
                    let constraint_term = self.term_for_var(var);
                    let lhs_node = self.intern_term_for_congruence(lhs, manager);
                    let rhs_node = self.intern_term_for_congruence(rhs, manager);
                    if let Err(_e) = self.euf.merge(lhs_node, rhs_node, constraint_term) {
                        return TheoryCheckResult::Sat;
                    }

                    if let Some(conflict_terms) = self.euf.check_conflicts() {
                        return self.conflict_from_terms(&conflict_terms);
                    }

                    // BV equality forced by `~(a != b)`: bit-blast and assert `a = b`.
                    if let Some(result) = self.bv_check_eq(lhs, rhs, constraint_term, manager) {
                        return result;
                    }
                }
            }
            // Arithmetic constraints - use parsed linear expressions
            Constraint::Lt(lhs, rhs)
            | Constraint::Le(lhs, rhs)
            | Constraint::Gt(lhs, rhs)
            | Constraint::Ge(lhs, rhs) => {
                // Intern both sides into EUF with congruence support so that
                // Apply/Select terms are registered for congruence closure.
                // Deferred until after the difference-engine feed below: an
                // atom the dense core accepted wholesale (plain numeric
                // endpoints — no Apply/Select structure congruence could
                // close over) needs no EUF presence on the pure-DL path,
                // while every other atom still interns (its operands may be
                // shared function applications whose equality the comparison
                // depends on).

                // Check if this is a BV comparison.  Detect it from the operand
                // *sorts*, exactly as the `Eq` arm above does – `bv_terms` only
                // holds BV-sorted *variables*, so keying off it silently skipped
                // every comparison whose sides are both compound, such as
                // `(bvugt (bvxor x x) (bvand #xff x))`, leaving the atom as a
                // free boolean and answering a spurious `sat`.
                let is_bv_sorted = |tid: TermId| -> bool {
                    manager
                        .get(tid)
                        .and_then(|t| manager.sorts.get(t.sort))
                        .is_some_and(|s| s.is_bitvec())
                };
                let lhs_is_bv = is_bv_sorted(lhs);
                let rhs_is_bv = is_bv_sorted(rhs);

                // Handle BV comparisons
                if lhs_is_bv || rhs_is_bv {
                    // Get BV width.  Both operands must agree: `BvSolver`'s
                    // comparison asserts require equal-width operands, and
                    // bit-blasting each side at its *own* declared width (which
                    // `encode_bv_term_recursive` does) would otherwise hand it a
                    // mismatched pair for an ill-sorted input term.  A
                    // width-mismatched comparison is not a well-sorted SMT-LIB
                    // atom, so leaving it to the remaining (boolean) handling is
                    // the correct conservative response.
                    let bv_width_of = |tid: TermId| -> Option<u32> {
                        manager
                            .get(tid)
                            .and_then(|t| manager.sorts.get(t.sort).and_then(|s| s.bitvec_width()))
                    };
                    let width = match (bv_width_of(lhs), bv_width_of(rhs)) {
                        (Some(lw), Some(rw)) if lw == rw => Some(lw),
                        _ => None,
                    };

                    if let Some(width) = width {
                        // Bit-blast both operands *with constant bits pinned*.
                        //
                        // `new_bv` alone allocates a fresh, completely
                        // unconstrained bit-vector for whatever term it is
                        // handed – including `BitVecConst` operands.  A
                        // comparison such as `(bvult x #b00000000)` then reads
                        // as `x <u c` for an arbitrary `c`, which is trivially
                        // satisfiable, so the BV solver could never refute the
                        // always-false strict comparisons (`t <u 0`,
                        // `t <s INT_MIN`, `MAX <u t`, ...).  Reference: Z3's
                        // bv_rewriter.cpp folds those atoms to `false`; here the
                        // equivalent refutation comes from the bit-blasted
                        // circuit, which only works once the literal operand is
                        // pinned to its concrete bits.
                        //
                        // `encode_bv_term_recursive` pins `BitVecConst` leaves
                        // and bit-blasts compound BV structure (`bvadd`,
                        // `bvand`, extract, ...) that appears under a
                        // comparison; `new_bv` remains the fallback for term
                        // shapes it does not model (e.g. an `Apply` of an
                        // uninterpreted function returning a bit-vector), where
                        // a free bit-vector is the correct abstraction.
                        let mut bv_encoded: FxHashSet<TermId> = FxHashSet::default();
                        if !encode_bv_term_recursive(self.bv, lhs, manager, &mut bv_encoded) {
                            self.bv.new_bv(lhs, width);
                        }
                        if !encode_bv_term_recursive(self.bv, rhs, manager, &mut bv_encoded) {
                            self.bv.new_bv(rhs, width);
                        }

                        // Derive signedness from the original TermKind stored for
                        // the SAT variable.  Both BvSlt and BvUlt encode to
                        // Constraint::Lt(lhs, rhs) during formula encoding (encode.rs),
                        // so the distinction is only recoverable by inspecting the term
                        // that the SAT variable was created for.
                        let constraint_term_id = self.term_for_var(var);
                        let is_signed = manager.get(constraint_term_id).is_some_and(|t| {
                            matches!(t.kind, TermKind::BvSlt(_, _) | TermKind::BvSle(_, _))
                        });

                        if is_positive {
                            // Positive assignment: constraint holds
                            match constraint {
                                Constraint::Lt(a, b) => {
                                    if is_signed {
                                        self.bv.assert_slt(a, b);
                                    } else {
                                        self.bv.assert_ult(a, b);
                                    }
                                }
                                Constraint::Le(a, b) if is_signed => {
                                    self.bv.assert_sle(a, b);
                                }
                                Constraint::Le(a, b) => {
                                    // Unsigned a <= b ≡ NOT(b <u a).
                                    self.bv.assert_ule(a, b);
                                }
                                _ => {}
                            }
                        } else {
                            // Negated assignment: the negation of the comparator
                            // holds.  By totality of BV orders the negation is the
                            // swapped non-strict / strict comparator:
                            //   ¬(a <u  b) ≡ b <=u a   ¬(a <=u b) ≡ b <u  a
                            //   ¬(a <s  b) ≡ b <=s a   ¬(a <=s b) ≡ b <s  a
                            match constraint {
                                Constraint::Lt(a, b) => {
                                    if is_signed {
                                        self.bv.assert_sle(b, a);
                                    } else {
                                        self.bv.assert_ule(b, a);
                                    }
                                }
                                Constraint::Le(a, b) => {
                                    if is_signed {
                                        self.bv.assert_slt(b, a);
                                    } else {
                                        self.bv.assert_ult(b, a);
                                    }
                                }
                                _ => {}
                            }
                        }

                        // Check BV solver for conflicts.  Routed through
                        // `bv_run_check` so the comparison path shares the
                        // (dis)equality path's debug-only model-validity net.
                        let constraint_term = self.term_for_var(var);
                        if let Some(result) =
                            self.bv_run_check(constraint_term, (lhs, rhs), manager)
                        {
                            return result;
                        }
                    }
                }

                // Look up the pre-parsed linear constraint for arithmetic.
                // Clone out so the immutable borrow ends before the `&mut self`
                // DL/arith conflict checks below.
                let Some(parsed) = self.var_to_parsed_arith.get(&var).cloned() else {
                    return TheoryCheckResult::Sat;
                };
                {
                    let terms: Vec<(TermId, Rational64)> = parsed.terms.iter().copied().collect();
                    let reason = parsed.reason_term;
                    let constant = parsed.constant;
                    let _ = (terms.as_slice(), reason, constant);

                    // Pure-DL fast path: the difference engines run BEFORE
                    // the simplex assert, and a `Consistent` verdict finishes
                    // the atom — the simplex never sees it (Z3
                    // `setup_QF_IDL`'s dense solver).  The general path keeps
                    // the historical order (simplex assert first, difference
                    // check after): the sparse conflict explanations are
                    // validated against that interleaving, and changing it
                    // perturbs conflict-clause bookkeeping (see
                    // `repro_disjunctive_lia`).
                    if self.dl_pure {
                        let dl_res = self.diff_primary_check(
                            var,
                            &parsed.terms,
                            parsed.constant,
                            parsed.constraint_type,
                            false,
                            is_positive,
                        );
                        match dl_res {
                            DlPrimaryResult::Conflict(dl_conflict) => return dl_conflict,
                            DlPrimaryResult::Propagated(props) => {
                                return TheoryCheckResult::Propagated(props);
                            }
                            DlPrimaryResult::Consistent => return TheoryCheckResult::Sat,
                            DlPrimaryResult::NotApplicable => {
                                self.break_dl_purity();
                            }
                        }
                    }

                    self.intern_term_for_congruence(lhs, manager);
                    self.intern_term_for_congruence(rhs, manager);
                    self.intern_arith_shared_terms(var, manager);

                    if is_positive {
                        // Positive assignment: constraint holds
                        match parsed.constraint_type {
                            ArithConstraintType::Lt => {
                                // lhs - rhs < 0, i.e., sum of terms < constant
                                self.arith.assert_lt(&terms, constant, reason);
                            }
                            ArithConstraintType::Le => {
                                // lhs - rhs <= 0
                                self.arith.assert_le(&terms, constant, reason);
                            }
                            ArithConstraintType::Gt => {
                                // lhs - rhs > 0, i.e., sum of terms > constant
                                self.arith.assert_gt(&terms, constant, reason);
                            }
                            ArithConstraintType::Ge => {
                                // lhs - rhs >= 0
                                self.arith.assert_ge(&terms, constant, reason);
                            }
                        }
                    } else {
                        // Negative assignment: negation of constraint holds
                        // ~(a < b) => a >= b
                        // ~(a <= b) => a > b
                        // ~(a > b) => a <= b
                        // ~(a >= b) => a < b
                        match parsed.constraint_type {
                            ArithConstraintType::Lt => {
                                // ~(lhs < rhs) => lhs >= rhs
                                self.arith.assert_ge(&terms, constant, reason);
                            }
                            ArithConstraintType::Le => {
                                // ~(lhs <= rhs) => lhs > rhs
                                self.arith.assert_gt(&terms, constant, reason);
                            }
                            ArithConstraintType::Gt => {
                                // ~(lhs > rhs) => lhs <= rhs
                                self.arith.assert_le(&terms, constant, reason);
                            }
                            ArithConstraintType::Ge => {
                                // ~(lhs >= rhs) => lhs < rhs
                                self.arith.assert_lt(&terms, constant, reason);
                            }
                        }
                    }

                    // Incremental DL conflict check (sparse engine; the
                    // pure path returned above).  DL-representable
                    // comparisons were already checked by the exact
                    // incremental graph; keep their constraints in the
                    // simplex tableau for mixed-fragment interaction and
                    // model construction, but defer its global feasibility
                    // pass until a non-DL atom or `final_check`.  Running
                    // the full tableau after every edge makes dense
                    // all-different cliques quadratic checks over a
                    // quadratically growing tableau.
                    let dl_exact = match self.diff_primary_check(
                        var,
                        &parsed.terms,
                        parsed.constant,
                        parsed.constraint_type,
                        false,
                        is_positive,
                    ) {
                        DlPrimaryResult::Conflict(dl_conflict) => return dl_conflict,
                        DlPrimaryResult::Propagated(props) => {
                            return TheoryCheckResult::Propagated(props);
                        }
                        DlPrimaryResult::Consistent => true,
                        DlPrimaryResult::NotApplicable => false,
                    };
                    if !dl_exact {
                        // See the equality branch above: cheap crossed-bound
                        // probe here, full LP solve at `final_check`.  (The
                        // probe call matters: a full `arith.check()` here
                        // re-solved the LP from a stale assignment on every
                        // arith literal – 50%+ of runtime on the SVC `dlx` /
                        // `pp-*` processor-verification goals, whose searches
                        // assign thousands of literals.)
                        if let Ok(oxiz_theories::TheoryCheckResult::Unsat(conflict_terms)) =
                            self.arith.check_bound_conflicts()
                        {
                            return self.conflict_from_terms(&conflict_terms);
                        }
                    }
                }
            }
            Constraint::BoolApp(app_term) => {
                // Bool-valued function application (e.g., `t(m)`).
                // Intern the application in EUF so that congruence closure
                // can fire.  Then merge its EUF node with the canonical
                // true or false node depending on the SAT assignment.
                let app_node = self.intern_term_for_congruence(app_term, manager);
                let (true_node, false_node) = self.ensure_bool_nodes();
                let merge_target = if is_positive { true_node } else { false_node };
                let constraint_term = self.term_for_var(var);
                if let Err(_e) = self.euf.merge(app_node, merge_target, constraint_term) {
                    // Merge error (should not happen in normal operation)
                    return TheoryCheckResult::Sat;
                }

                // Check for immediate conflicts
                if let Some(conflict_terms) = self.euf.check_conflicts() {
                    return self.conflict_from_terms(&conflict_terms);
                }
            }
        }
        TheoryCheckResult::Sat
    }
}

impl TheoryCallback for TheoryManager<'_> {
    /// A real theory is attached: inprocessing must skip its pure-literal pass
    /// (see `TheoryCallback::is_real_theory` in oxiz-sat for the soundness
    /// argument).
    fn is_real_theory(&self) -> bool {
        true
    }

    fn on_assignment(&mut self, lit: Lit) -> TheoryCheckResult {
        let var = lit.var();
        let is_positive = !lit.is_neg();

        if self.timed_out() {
            self.resource_exhausted = true;
            return TheoryCheckResult::Sat;
        }

        if !self.var_to_constraint.contains_key(&var) {
            return TheoryCheckResult::Sat;
        }

        self.set_assigned_polarity(var, is_positive);
        self.set_assigned_level(var, self.current_level);

        if !self.bv_terms.is_empty()
            && let Some(term) = self.var_to_term.get(var.index()).copied()
        {
            self.bv.assert_bool_value(term, is_positive);
        }

        // Track propagation
        self.statistics.propagations += 1;

        // Lazy mode keeps a deduplicated, level-stamped shadow of the complete
        // SAT trail and rebuilds the theory solvers from it in `final_check`.
        // Merely queueing atoms and asserting them at the *current* (deepest)
        // scope is unsound: after a theory conflict, a backtrack pops that
        // scope and loses even the queued facts whose SAT assignments survived
        // at lower levels.  The next candidate can then be accepted against a
        // strict subset of its theory atoms (the array-incompleteness false-SAT
        // was one such case).
        if self.theory_mode == TheoryMode::Lazy {
            match self.trail_idx_of(var) {
                Some(idx) => {
                    self.assignment_trail[idx] = TrailAtom {
                        var,
                        is_positive,
                        level: self.current_level,
                    };
                }
                None => {
                    let idx = self.assignment_trail.len();
                    self.assignment_trail.push(TrailAtom {
                        var,
                        is_positive,
                        level: self.current_level,
                    });
                    self.trail_idx_set(var, idx);
                }
            }
            return TheoryCheckResult::Sat;
        }

        // Eager mode: process immediately
        // Check if this variable has a theory constraint
        let Some(constraint) = self.var_to_constraint.get(&var).cloned() else {
            return TheoryCheckResult::Sat;
        };

        // Shadow-trail bookkeeping + in-place-flip detection.
        //
        // If the SAT core has assigned this variable before (and not yet
        // backtracked past it) with the OPPOSITE polarity, it has overwritten
        // its own trail – a wrong assertion-level bug in conflict analysis.  The
        // incremental theory state still holds the old polarity's assertions and
        // cannot be surgically undone, so we replace the trail entry and rebuild
        // theory state from the corrected trail.  A re-assignment with the SAME
        // polarity is an idempotent re-send after a backtrack; it falls through
        // to the normal (re)processing path, preserving pre-existing behaviour.
        match self.trail_idx_of(var) {
            // In-place polarity flip by the SAT core (a wrong assertion-level
            // result from its conflict analysis).  Rebuild theory state from the
            // corrected, deduplicated trail so no stale over-constraint from the
            // old polarity manufactures a spurious conflict (the wrong-UNSAT on
            // satisfiable disjunctive LIA chains).  Any residual unsoundness the
            // corrupted SAT trail could still produce (a full assignment
            // violating a Boolean clause the theory cannot see) is caught
            // downstream by the model-verification gate in `Solver::check`.
            //
            // Scope: the rebuild covers the EUF and arithmetic solvers, so we
            // engage it only when the problem has no bit-vector content.  The BV
            // solver's bit-blasted circuits are rebuilt from scratch on every
            // `check` (see `mod.rs`) and its incremental push/pop already handles
            // flips soundly; resetting and replaying it mid-search would instead
            // corrupt its embedded SAT state.  BV problems therefore retain the
            // existing (correct) incremental behaviour.
            Some(idx)
                if self.assignment_trail[idx].is_positive != is_positive
                    && self.bv_terms.is_empty() =>
            {
                self.assignment_trail[idx] = TrailAtom {
                    var,
                    is_positive,
                    level: self.current_level,
                };
                self.processed_count += 1;
                self.statistics.theory_propagations += 1;

                // Process the flipped literal against the current (stale) state
                // first.  If it stays consistent, keep that result – the extra
                // over-constraint from the not-yet-popped old polarity is
                // harmless here and preserves the existing search trajectory.
                // Only when it manufactures a conflict do we pay for a full
                // rebuild from the corrected, deduplicated trail: that conflict
                // may be spurious (a stale artefact of the SAT core's wrong
                // backtrack level, the wrong-UNSAT cause) so we must re-derive
                // the authoritative verdict – `Conflict` if genuinely
                // inconsistent, `Sat` if the stale state fabricated it.
                let direct = if self.dl_pure {
                    // The dense closure cannot surgically remove the flipped
                    // literal's old edges (it retracts by scope pops only), so
                    // processing the flip directly would leave BOTH
                    // polarities asserted and over-constrain it into bogus
                    // conflicts.  Rebuild from the corrected trail first.
                    self.resync_theory_state()
                } else {
                    let d = self.process_constraint(var, constraint, is_positive, self.manager);
                    if matches!(d, TheoryCheckResult::Conflict(_)) {
                        self.resync_theory_state()
                    } else {
                        d
                    }
                };
                let result = direct;
                if matches!(result, TheoryCheckResult::Conflict(_)) {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                }
                return result;
            }
            Some(_) => {
                // Either an idempotent same-polarity re-send after a backtrack,
                // or a flip in a problem that contains bit-vector terms (handled
                // by the BV solver's own incremental push/pop).  Both fall
                // through to normal processing, preserving pre-existing behaviour.
            }
            None => {
                let idx = self.assignment_trail.len();
                self.assignment_trail.push(TrailAtom {
                    var,
                    is_positive,
                    level: self.current_level,
                });
                self.trail_idx_set(var, idx);
            }
        }

        self.processed_count += 1;
        self.statistics.theory_propagations += 1;

        let result = self.process_constraint(var, constraint, is_positive, self.manager);

        // Track theory conflicts
        if matches!(result, TheoryCheckResult::Conflict(_)) {
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;

            // Check conflict limit
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                // Resource exhaustion: we are dropping a real conflict to stop
                // the search.  Flag it so the solver answers Unknown, not Sat.
                self.resource_exhausted = true;
                return TheoryCheckResult::Sat; // Return Sat to signal resource exhaustion
            }
        }

        // Incremental arithmetic bound propagation (the z3 `:arith-bound-prop`
        // analogue).  Env-gated (`OXIZ_BOUND_PROP`); validated sound before
        // default-enabling.  Fires after a successful arith assertion so that
        // asserting `(= x k)` (which pins `x ∈ [k,k]`) immediately forces every
        // `x ◦ c` ite condition at the current decision level – the mechanism
        // that shallows conflicts on finite-domain QF_UFIDL from ~96 to ~2.
        #[cfg(feature = "std")]
        if matches!(result, TheoryCheckResult::Sat) && self.var_to_parsed_arith.contains_key(&var) {
            let mode = arith_bound_prop_mode();
            if mode != BoundPropMode::Off
                && self.is_dl_family
                && let Some(props) =
                    self.derive_arith_bound_propagations(mode == BoundPropMode::Tighten)
            {
                self.statistics.theory_propagations += props.len() as u64;
                return TheoryCheckResult::Propagated(props);
            }
        }

        if matches!(result, TheoryCheckResult::Sat)
            && self.eq_atom_watches
            && let Some(props) = self.drain_forced_eq_atoms()
        {
            self.statistics.theory_propagations += props.len() as u64;
            return TheoryCheckResult::Propagated(props);
        }

        result
    }

    fn final_check(&mut self) -> TheoryCheckResult {
        if self.timed_out() {
            self.resource_exhausted = true;
            return TheoryCheckResult::Sat;
        }

        // Lazy checking is a from-scratch check of the *current* complete SAT
        // assignment.  Replay each shadow-trail atom at its original decision
        // level so a conflict-driven backtrack can pop exactly the facts that
        // ceased to hold, while retaining every surviving lower-level fact.
        // This also ensures the DL check below sees the current assignment,
        // rather than the stale/empty graph that existed before the old pending
        // batch was processed.
        if self.theory_mode == TheoryMode::Lazy {
            let replay = self.resync_theory_state();
            if let TheoryCheckResult::Conflict(conflict) = replay {
                self.statistics.theory_conflicts += 1;
                self.statistics.conflicts += 1;
                if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
                return TheoryCheckResult::Conflict(conflict);
            }
        }

        // DL conflict backstop at full assignment using the incrementally-
        // maintained solver (one full `check()` here is cheap – once per final
        // check, not per atom).  A negative cycle is a sound refutation.
        if !self.var_to_parsed_arith.is_empty()
            && let oxiz_theories::DiffLogicResult::Conflict(cycle_terms) = self.diff.check()
        {
            return self.conflict_from_terms(&cycle_terms);
        }

        // Check EUF for conflicts
        if let Some(conflict_terms) = self.euf.check_conflicts() {
            // Convert TermIds to Lits for the conflict clause
            let conflict = self.conflict_from_terms(&conflict_terms);
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;

            // Check conflict limit
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                // Dropping a real EUF conflict at the limit: flag it so the
                // solver reports Unknown rather than trusting Sat.
                self.resource_exhausted = true;
                return TheoryCheckResult::Sat; // Signal resource exhaustion
            }

            return conflict;
        }

        if self.array_theory.is_empty()
            && self.var_to_parsed_arith.is_empty()
            && self.bv_terms.is_empty()
        {
            if !self.eager_interned
                && self.theory_mode != TheoryMode::Lazy
                && self.euf.has_app_nodes()
            {
                let replay = self.resync_theory_state();
                if let TheoryCheckResult::Conflict(conflict_lits) = replay {
                    self.statistics.theory_conflicts += 1;
                    self.statistics.conflicts += 1;
                    if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                        self.resource_exhausted = true;
                        return TheoryCheckResult::Sat;
                    }
                    return TheoryCheckResult::Conflict(conflict_lits);
                }
            }
            return TheoryCheckResult::Sat;
        }

        // Array-theory read-over-write propagation (Stage 5 of
        // `docs/ARRAY_THEORY_PLAN.md`): for each `select(store(b,i,v), j)`
        // whose `i = j` is already in EUF, the read-over-write axiom forces
        // `select = v`; merge the two in EUF so congruence / `check_conflicts`
        // and the arithmetic pass below observe the consequence.  Additive to
        // the lazy lemma instantiator (kept as a fallback); single pass per
        // final_check for now (a fixpoint loop arrives with the incremental
        // stages).  SOUND: only ever merges a term with the value the array
        // axiom *proves* it equals, so it can only strengthen, never fabricate.
        if let Some(r) = self.propagate_array_read_over_write() {
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                self.resource_exhausted = true;
                return TheoryCheckResult::Sat;
            }
            return r;
        }
        // Array extensionality (Stage 5): catch `a ≠ b` while the witness reads
        // `select(a, k)` / `select(b, k)` are EUF-equal (extensionality then
        // forces `a = b`).
        if let Some(r) = self.check_array_extensionality() {
            self.statistics.theory_conflicts += 1;
            self.statistics.conflicts += 1;
            if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                self.resource_exhausted = true;
                return TheoryCheckResult::Sat;
            }
            return r;
        }

        // Soundness backstop: the incremental EUF state, built up across CDCL
        // push/pop, can lose a congruence or disequality, so the live
        // `check_conflicts` above can report a spurious "consistent" on a
        // genuinely-unsatisfiable, *function-bearing* assignment (the live
        // e-graph diverges from a fresh replay of the same asserted equalities).
        // Rebuild the theory state from the deduplicated shadow trail and
        // re-check; honor any conflict the rebuild finds that the incremental
        // state missed. Gated on `has_app_nodes` because the divergence is
        // specific to function-bearing EUF, and pure-equality problems would be
        // unfairly penalized by the per-final_check rebuild cost.
        // Eager mode only: lazy mode has already rebuilt all theory state from
        // this shadow trail at the start of `final_check`, so replaying it a
        // second time here would be redundant.
        if self.theory_mode != TheoryMode::Lazy && self.euf.has_app_nodes() {
            let replay = self.resync_theory_state();
            if let TheoryCheckResult::Conflict(conflict_lits) = replay {
                self.statistics.theory_conflicts += 1;
                self.statistics.conflicts += 1;
                if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts {
                    self.resource_exhausted = true;
                    return TheoryCheckResult::Sat;
                }
                return TheoryCheckResult::Conflict(conflict_lits);
            }
        }

        // Propagate EUF-derived equalities into the arithmetic solver.
        // When EUF fires congruence closure and derives f(x) = f(y) because
        // x = y was asserted, the arithmetic solver is unaware of this equality.
        // We must propagate it so the arithmetic solver can detect contradictions.
        //
        // Skipped on the pure-DL path: without UF the only merges come from
        // the asserted `Eq` atoms themselves, which the dense closure already
        // carries as edges — re-asserting them into the (otherwise empty)
        // simplex only re-runs its integer search over rows the DL core has
        // already decided (observed degrading SAL bakery/lpsat to Unknown
        // through that solver's B&B budget).
        if !self.dl_pure {
            let mut propagate_dedup: FxHashSet<(TermId, TermId)> = FxHashSet::default();
            let eq_result = self.propagate_euf_equalities_to_arith(&mut propagate_dedup);
            if let TheoryCheckResult::Conflict(_) = eq_result {
                self.statistics.theory_conflicts += 1;
                self.statistics.conflicts += 1;
                return eq_result;
            }
        }

        // Check arithmetic
        match self.arith.check() {
            Ok(result) => {
                match result {
                    oxiz_theories::TheoryCheckResult::Sat => {
                        // z3-style theory propagation: for every axiomatized
                        // `ite`-result term `t`, read its current arithmetic
                        // value `v`; if arithmetic provably fixes `t = v` (with
                        // an all-atom explanation), propagate the triangle's
                        // `le`/`ge` atoms.  The clause `(eq ∨ ¬le ∨ ¬ge)` then
                        // forces `eq`, EUF merges `t` with `v` using the `eq`
                        // atom (SAT-backed reason), and congruence closure
                        // collapses the nested chain – deterministically.
                        // Cost: O(#ite-terms) – one value lookup + at most one
                        // probe per term (only the constant it's assigned).
                        let mut theory_props: Vec<(Lit, SmallVec<[Lit; 8]>)> = Vec::new();
                        for &term in self.ite_result_terms {
                            let Some(val) = self.arith.value(term) else {
                                continue;
                            };
                            let Some(v) = (if val.is_integer() { val.to_i64() } else { None })
                            else {
                                continue;
                            };
                            let Some(&(le_var, ge_var)) = self.ite_const_axioms.get(&(term, v))
                            else {
                                continue;
                            };
                            // Skip if both already assigned (avoids re-emitting
                            // a no-op Propagated on a fully-assigned trail).
                            if self.assigned_pol_of(le_var).is_some()
                                && self.assigned_pol_of(ge_var).is_some()
                            {
                                continue;
                            }
                            let Some(reasons) = self.arith.fixed_to_const_reason(term, v) else {
                                continue;
                            };
                            let mut reason_lits: SmallVec<[Lit; 8]> = SmallVec::new();
                            let mut ok = true;
                            for &r in &reasons {
                                match self.term_to_var.get(&r) {
                                    Some(&var) if self.assigned_pol_of(var) == Some(true) => {
                                        reason_lits.push(Lit::pos(var));
                                    }
                                    _ => {
                                        ok = false;
                                        break;
                                    }
                                }
                            }
                            if !ok {
                                continue;
                            }
                            if self.assigned_pol_of(le_var).is_none() {
                                theory_props.push((Lit::pos(le_var), reason_lits.clone()));
                            }
                            if self.assigned_pol_of(ge_var).is_none() {
                                theory_props.push((Lit::pos(ge_var), reason_lits));
                            }
                        }
                        if !theory_props.is_empty() {
                            self.statistics.theory_propagations += theory_props.len() as u64;
                            return TheoryCheckResult::Propagated(theory_props);
                        }
                        // Arithmetic is consistent, now check model-based theory combination
                        // This ensures that different theories agree on shared terms
                        self.nelson_oppen_combine()
                    }
                    oxiz_theories::TheoryCheckResult::Unsat(conflict_terms) => {
                        // Arithmetic conflict detected - convert to SAT conflict clause
                        let conflict = self.conflict_from_terms(&conflict_terms);
                        self.statistics.theory_conflicts += 1;
                        self.statistics.conflicts += 1;

                        // Check conflict limit
                        if self.max_conflicts > 0 && self.statistics.conflicts >= self.max_conflicts
                        {
                            // Dropping a real arithmetic conflict at the limit:
                            // flag it so the solver reports Unknown, not Sat.
                            self.resource_exhausted = true;
                            return TheoryCheckResult::Sat; // Signal resource exhaustion
                        }

                        conflict
                    }
                    oxiz_theories::TheoryCheckResult::Propagate(_) => {
                        // Propagations should be handled in on_assignment
                        self.model_based_combination()
                    }
                    oxiz_theories::TheoryCheckResult::Unknown => {
                        // The arithmetic solver could not decide this state
                        // (e.g. LIA branch-and-bound / LP budget exhausted).
                        // Returning a plain `Sat` here would fabricate a model
                        // the solver never verified – an unsound `Sat`.  Flag
                        // resource exhaustion so the owning solver answers
                        // `Unknown`, and stop the search by reporting Sat.
                        self.resource_exhausted = true;
                        TheoryCheckResult::Sat
                    }
                }
            }
            Err(_error) => {
                // Internal error in the arithmetic solver.  We have no verified
                // model, so we must not claim `Sat`.  Flag resource exhaustion
                // (→ solver answers `Unknown`) and stop the search.
                self.resource_exhausted = true;
                TheoryCheckResult::Sat
            }
        }
    }

    fn on_new_level(&mut self, level: u32) {
        // Track the current SAT decision level for the shadow trail.
        self.current_level = level;
        // Push theory state when a new decision level is created
        // Ensure we have enough levels in the stack
        while self.level_stack.len() < (level as usize + 1) {
            self.push_theory_scope();
        }
    }

    fn on_backtrack(&mut self, level: u32) {
        // Track the current SAT decision level and prune the shadow trail of
        // every assignment made above `level` (they have been undone by the SAT
        // core's backtrack).  Prune with swap-removal so both the trail and its
        // dense var->index map stay exact without re-hashing anything, and
        // clear the corresponding `assigned_level` slots in the same pass
        // (their key set is exactly the set of shadow-trail vars).
        self.current_level = level;
        if self.assignment_trail.iter().any(|a| a.level > level) {
            let mut i = 0;
            while i < self.assignment_trail.len() {
                if self.assignment_trail[i].level > level {
                    let removed_var = self.assignment_trail[i].var;
                    let last = self.assignment_trail.pop();
                    if let Some(t) = last
                        && i < self.assignment_trail.len()
                    {
                        // The popped tail entry moved into slot `i`; fix its index.
                        self.assignment_trail[i] = t;
                        self.trail_idx_set(t.var, i);
                    }
                    // Invalidate the removed var's own index unconditionally –
                    // it is stale whether the removed entry was the tail (slot
                    // gone) or was backfilled (slot now belongs to `t`).
                    if let Some(slot) = self.trail_index.get_mut(removed_var.index()) {
                        *slot = u32::MAX;
                    }
                    if let Some(slot) = self.assigned_level.get_mut(removed_var.index()) {
                        *slot = 0;
                    }
                } else {
                    i += 1;
                }
            }
        }

        // Pop EUF, Arith, and BV states if needed.  Each pop also drops the
        // derived-equality explanations recorded in the scope it retracts –
        // and, just as importantly, keeps the ones recorded at or below the
        // surviving depth: those assertions are still in the tableau, and
        // forgetting their explanation leaves a later conflict citing one of
        // them unable to name the literals it rests on.
        while self.level_stack.len() > (level as usize + 1) {
            self.pop_theory_scope();
        }
        self.processed_count = *self.level_stack.last().unwrap_or(&0);

        // Evict stale integer-constant canonicals whose EUF nodes were removed
        // by the preceding pop().  After truncation, any node index >=
        // euf.node_count() is invalid; keeping such entries would cause an
        // out-of-bounds access in `intern_term_deep` when `merge` is called
        // against the stale canonical.  Evicting them forces re-registration
        // (and fresh disequality assertions) the next time those values appear.
        let live_nodes = self.euf.node_count();
        self.interned_int_constants
            .retain(|_val, &mut canonical| (canonical as usize) < live_nodes);

        // Evict stale bit-vector-constant canonicals for the same reason.
        self.interned_bv_constants
            .retain(|_key, &mut canonical| (canonical as usize) < live_nodes);

        // Evict stale Boolean canonical nodes
        if let Some(t) = self.bool_true_node {
            if (t as usize) >= live_nodes {
                self.bool_true_node = None;
            }
        }
        if let Some(f) = self.bool_false_node {
            if (f as usize) >= live_nodes {
                self.bool_false_node = None;
            }
        }
    }
}

/// Result from parallel theory checking
#[cfg(feature = "parallel-theories")]
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum ParallelTheoryResult {
    /// All theories report SAT
    AllSat,
    /// At least one theory found a conflict
    Conflict(SmallVec<[Lit; 8]>),
}

/// Parallel theory checking support.
#[cfg(feature = "parallel-theories")]
#[allow(dead_code)]
pub struct ParallelTheoryChecker;

#[cfg(feature = "parallel-theories")]
impl ParallelTheoryChecker {
    /// Check multiple independent theory assertions in parallel.
    #[allow(dead_code)]
    pub fn check_parallel(
        assertions: &[(Var, Constraint, bool)],
        _term_to_var: &FxHashMap<TermId, Var>,
    ) -> ParallelTheoryResult {
        use rayon::prelude::*;

        let mut euf_assertions = Vec::new();
        let mut arith_assertions = Vec::new();
        let bv_assertions = Vec::new();

        for (var, constraint, is_positive) in assertions {
            match constraint {
                Constraint::Eq(_, _) | Constraint::Diseq(_, _) => {
                    euf_assertions.push((*var, constraint.clone(), *is_positive));
                }
                Constraint::Le(_, _)
                | Constraint::Lt(_, _)
                | Constraint::Ge(_, _)
                | Constraint::Gt(_, _) => {
                    arith_assertions.push((*var, constraint.clone(), *is_positive));
                }
                Constraint::BoolApp(_) => {
                    euf_assertions.push((*var, constraint.clone(), *is_positive));
                }
            }
        }

        let results: Vec<Option<SmallVec<[Lit; 8]>>> =
            [&euf_assertions, &arith_assertions, &bv_assertions]
                .par_iter()
                .map(|domain| Self::check_domain_contradictions(domain))
                .collect();

        if let Some(conflict) = results.into_iter().flatten().next() {
            return ParallelTheoryResult::Conflict(conflict);
        }

        ParallelTheoryResult::AllSat
    }

    #[allow(dead_code)]
    fn check_domain_contradictions(
        assertions: &[(Var, Constraint, bool)],
    ) -> Option<SmallVec<[Lit; 8]>> {
        for i in 0..assertions.len() {
            for j in (i + 1)..assertions.len() {
                let (var_i, constraint_i, pos_i) = &assertions[i];
                let (var_j, constraint_j, pos_j) = &assertions[j];
                if Self::are_contradictory(constraint_i, *pos_i, constraint_j, *pos_j) {
                    let mut conflict = SmallVec::new();
                    conflict.push(Lit::neg(*var_i));
                    conflict.push(Lit::neg(*var_j));
                    return Some(conflict);
                }
            }
        }
        None
    }

    #[allow(dead_code)]
    fn are_contradictory(c1: &Constraint, pos1: bool, c2: &Constraint, pos2: bool) -> bool {
        match (c1, c2) {
            (Constraint::Eq(a1, b1), Constraint::Eq(a2, b2)) => {
                a1 == a2 && b1 == b2 && pos1 != pos2
            }
            (Constraint::Eq(a1, b1), Constraint::Diseq(a2, b2))
            | (Constraint::Diseq(a2, b2), Constraint::Eq(a1, b1)) => {
                a1 == a2 && b1 == b2 && pos1 && pos2
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod s8_iterative_tests;
