//! Mod-2 parity lemmas: lift the parity signature of the asserted
//! integer-equality system into Boolean xor lemmas for the SAT core.
//!
//! # The gap this closes
//!
//! Graph-parity obligations realized across theories (obligation-grammar
//! fuzzer, `bench/obligation` parity family) put the *same* parity argument
//! half in the Bool view (xor chains over `b_e`) and half in the Int view
//! (vertex equations `Σ i_e − 2·k_v = c_v`), linking the two with
//! `i_e = (ite b_e 1 0)` or an exact `div`/`mod` chain over such an `ite`.
//! The theory side is leaf-complete — with every `b_e` fixed at level 0 the
//! Hermite view refutes instantly — but during search the Int view's parity
//! constraint never reaches the CDCL core as learnable structure, so the
//! mixed instances stall at `unknown`/timeout where z3 answers in seconds.
//!
//! # The derivation (and why it is sound)
//!
//! Every ingredient below is a *logical consequence of the input*; the
//! emitted lemma is therefore a consequence, never an extra assumption.
//!
//! 1. **Rows.** Walk the (preprocessed, level-0) assertions and collect every
//!    Int-sorted linear equality `Σ a_i·x_i = b` (integral `i64` coefficients
//!    only; [`Solver::extract_linear_terms`] treats `div`/`mod`/`ite` terms
//!    as opaque columns).  Each row *is* an asserted formula, so it holds in
//!    every model.
//! 2. **Mod-2 consequences.** A GF(2) Gaussian elimination over the rows'
//!    parity reductions (each row `Σ a_i·x_i = b` implies
//!    `Σ_{a_i odd} x_i ≡ b (mod 2)`) yields row combinations
//!    `Σ x_j ≡ r (mod 2)` — integer summation followed by reduction mod 2.
//! 3. **Literal images.** A column `T` is *image-determined* when its value
//!    is fixed under both phases of a single Boolean condition `c`: `T` is
//!    (or chains, through exact Euclidean `div`/`mod` by constants, down to)
//!    the fresh variable of a non-Bool `ite` over two constant branches
//!    `C1`/`C0`.  The `ite` side-conditions (`c → v = C1`, `¬c → v = C0`)
//!    are asserted formulas, and `div`/`mod` have fixed SMT-LIB semantics,
//!    so `T ≡ (C1 mod 2)` under `c` and `T ≡ (C0 mod 2)` under `¬c` are
//!    consequences.  Evaluating both branch images exactly in Rust (checked
//!    `i128`, Euclidean `div_euclid`/`rem_euclid`, zero divisor bails) gives
//!    either a literal (`T ≡ c` or `T ≡ ¬c`, when the parities differ) or a
//!    constant (when they agree).  A column needing two distinct conditions,
//!    or any non-evaluable term, is not image-determined and is *eliminated*
//!    in step 2 instead of interpreted — a derivation that cannot reach
//!    image-determined columns simply emits nothing.
//! 4. **Lemma.** Substitute the images into a mod-2 consequence: the result
//!    `xor(l_1 … l_k) = c` is a consequence of the input.  Assert it as a
//!    ground unit lemma through the same channel as
//!    [`super::arith_axioms`]' defining axioms (`encode` + unit clause), at
//!    the current assertion level; the SAT core's scoped clause store
//!    retracts it on `pop`, and the trail retracts the bookkeeping.
//!
//! For the fuzzer's mixed instances the vertex rows sum to
//! `Σ_{cross} i_e ≡ Σ_I c_v (mod 2)` (interior edges and `2·k_v` slack have
//! even coefficients and vanish mod 2), the link rows and image evaluation
//! turn `i_e` into `b_e`, and the lemma handed to CDCL is exactly
//! `xor(Σ_{cross} b_e) = Σ_I c_v (mod 2)` — the missing half of the parity
//! argument, which the Bool side's xor chains then contradict.
//!
//! # Timing
//!
//! Derived once per *assertion generation* (bumped by `assert` /
//! `assert_named` / `pop`), consumed at the next `check_core` entry — never
//! per theory check.  Per-check recomputation is the measured failure mode
//! (see `docs/studies/2026-09-06-mixed-parity-lia-equality-gap.md`).
//!
//! Every quantity is bounded (row/column/lemma/width caps, evaluation depth
//! cap); exceeding a cap emits nothing — a missed lemma is the status quo,
//! never a wrong answer.

use nixie_core::ast::{TermId, TermKind, TermManager};
use num_rational::Rational64;
use num_traits::{One, ToPrimitive, Zero};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use super::Solver;

/// Cap on recorded integer-equality rows.  Beyond this the derivation is
/// skipped (the parity family sits at ~100; large Gaussian workloads gain
/// nothing and would pay quadratic elimination).
pub(crate) const MAX_PARITY_ROWS: usize = 1024;
/// Cap on distinct columns across the recorded rows.
pub(crate) const MAX_PARITY_COLS: usize = 1024;
/// Cap on lemmas emitted by one derivation (each is a Tseitin chain).
pub(crate) const MAX_PARITY_LEMMAS: usize = 256;
/// Cap on literals in one emitted xor chain.
pub(crate) const MAX_PARITY_WIDTH: usize = 256;
/// Depth cap for the two-phase image evaluation (the div/mod chains are
/// shallow; the cap bounds native recursion on user-shaped input the same
/// way `arith_axioms::MAX_CONST_EVAL_DEPTH` bounds constant folding).
const MAX_IMAGE_EVAL_DEPTH: u32 = 64;

/// One recorded integer equality: `Σ coeff_i · term_i = rhs`, all integral.
/// Stored verbatim (even coefficients included); the mod-2 reduction happens
/// at derivation time.
#[derive(Debug, Clone)]
pub(crate) struct ParityRow {
    pub(super) terms: Vec<(TermId, i64)>,
    pub(super) rhs: i64,
}

/// Definition of a non-Bool `ite` fresh variable, recorded by
/// [`Solver::eliminate_nonbool_ite`]: the variable stands for
/// `ite(cond, then_b, else_b)` with both branches already substituted.
pub(crate) type IteDef = (TermId, TermId, TermId);

/// One GF(2) row: `⊕ support = rhs` over column indices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Gf2Row {
    /// Column indices in increasing order (a set, not a multiset).
    pub(crate) support: Vec<usize>,
    pub(crate) rhs: bool,
}

/// `row ^= other` (symmetric difference of sorted supports, rhs toggle).
fn gf2_xor(row: &mut Gf2Row, other: &Gf2Row) {
    let mut merged: Vec<usize> = Vec::with_capacity(row.support.len() + other.support.len());
    let (mut i, mut j) = (0usize, 0usize);
    while i < row.support.len() && j < other.support.len() {
        match row.support[i].cmp(&other.support[j]) {
            std::cmp::Ordering::Less => {
                merged.push(row.support[i]);
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                merged.push(other.support[j]);
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                // present in both: cancels
                i += 1;
                j += 1;
            }
        }
    }
    merged.extend_from_slice(&row.support[i..]);
    merged.extend_from_slice(&other.support[j..]);
    row.support = merged;
    row.rhs ^= other.rhs;
}

/// Eliminate every *bad* column from the row space and return a spanning
/// set of the surviving rows: those rows of the spanned space whose support
/// contains no bad column.  Each returned row is a GF(2) consequence of the
/// input rows (row XOR is integer summation mod 2, which preserves every
/// integer solution).
///
/// Method: forward elimination pivoting on bad columns only.  A row is
/// first reduced against every existing pivot whose column it contains,
/// then — if a bad column remains — installed as that column's pivot
/// (echelon position); otherwise it is emitted.  The emitted rows therefore
/// have zero bad support, and together with the echelon pivot rows they
/// span the original space, so every zero-bad-support vector of the space
/// is a combination of emitted rows alone (the pivot rows' bad coordinates
/// are triangular, forcing their coefficients to zero).
pub(crate) fn gf2_eliminate_bad_columns(rows: Vec<Gf2Row>, bad: &[bool]) -> Vec<Gf2Row> {
    let mut pivots: Vec<Option<Gf2Row>> = vec![None; bad.len()];
    let mut out = Vec::new();
    for mut row in rows {
        loop {
            // Reduce against the first bad column that already has a pivot.
            let reducible = row
                .support
                .iter()
                .copied()
                .find(|&c| bad[c] && pivots[c].is_some());
            match reducible {
                Some(col) => {
                    let pivot = pivots[col].as_ref().expect("col selected with pivot");
                    gf2_xor(&mut row, pivot);
                }
                None => {
                    // Fully reduced: install on the first remaining bad
                    // column, or emit as a consequence over good columns.
                    let install = row.support.iter().copied().find(|&c| bad[c]);
                    match install {
                        Some(col) => {
                            pivots[col] = Some(row);
                            break;
                        }
                        None => {
                            if !row.support.is_empty() || row.rhs {
                                out.push(row);
                            }
                            break;
                        }
                    }
                }
            }
        }
    }
    out
}

/// The mod-2 parity of one column, as fixed by its two-phase image.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ColumnParity {
    /// Both phase images agree mod 2: the column is that constant bit.
    Const(bool),
    /// Parity equals the truth of the literal term.
    Literal(TermId),
    /// Parity equals the negation of the literal term.
    NegLiteral(TermId),
}

/// Two-phase exact evaluation context (see [`classify_column`]).
struct ImageEval<'a> {
    manager: &'a TermManager,
    ite_defs: &'a FxHashMap<TermId, IteDef>,
    /// The single Boolean condition all visited `ite` definitions share.
    cond: Option<TermId>,
    /// Set when two distinct conditions were needed: the column's parity is
    /// then not a function of one literal and the classification fails.
    conflict: bool,
}

impl<'a> ImageEval<'a> {
    /// Exact value of `term` under `phase` (the truth value assigned to the
    /// single recorded condition).  `None` = not exactly evaluable (bail —
    /// the caller treats the column as bad and eliminates it instead).
    fn value(&mut self, term: TermId, phase: bool, depth: u32) -> Option<i128> {
        if depth > MAX_IMAGE_EVAL_DEPTH {
            return None;
        }
        if let Some(&(cond, then_b, else_b)) = self.ite_defs.get(&term) {
            match self.cond {
                None => self.cond = Some(cond),
                Some(c) if c == cond => {}
                Some(_) => {
                    self.conflict = true;
                    return None;
                }
            }
            return self.value(if phase { then_b } else { else_b }, phase, depth + 1);
        }
        let node = self.manager.get(term)?;
        let int_sort = self.manager.sorts.int_sort;
        let v =
            match &node.kind {
                TermKind::IntConst(n) => n.to_i128()?,
                TermKind::Neg(a) => self.value(*a, phase, depth + 1)?.checked_neg()?,
                TermKind::Add(args) => {
                    let mut sum: i128 = 0;
                    for &a in args.iter() {
                        sum = sum.checked_add(self.value(a, phase, depth + 1)?)?;
                    }
                    sum
                }
                TermKind::Sub(a, b) => self
                    .value(*a, phase, depth + 1)?
                    .checked_sub(self.value(*b, phase, depth + 1)?)?,
                TermKind::Mul(args) => {
                    let mut product: i128 = 1;
                    for &a in args.iter() {
                        product = product.checked_mul(self.value(a, phase, depth + 1)?)?;
                    }
                    product
                }
                // SMT-LIB Int `div`/`mod` are Euclidean (Rust's `div_euclid` /
                // `rem_euclid` match exactly).  A zero divisor is uninterpreted
                // per SMT-LIB, so no value exists to evaluate to — bail.  The
                // Real-sorted `Div` (true division) never occurs under an
                // Int-sorted equality but is excluded by sort as well.
                TermKind::Div(m, n) if node.sort == int_sort => {
                    let m = self.value(*m, phase, depth + 1)?;
                    let n = self.value(*n, phase, depth + 1)?;
                    if n == 0 {
                        return None;
                    }
                    m.checked_div_euclid(n)?
                }
                TermKind::Mod(m, n) if node.sort == int_sort => {
                    let m = self.value(*m, phase, depth + 1)?;
                    let n = self.value(*n, phase, depth + 1)?;
                    if n == 0 {
                        return None;
                    }
                    m.checked_rem_euclid(n)?
                }
                _ => return None,
            };
        Some(v)
    }
}

/// Classify one column: does its mod-2 parity equal a constant, a single
/// literal, or the negation of one?
///
/// SOUND only when the returned parity is a consequence: the evaluation
/// uses exclusively (a) the asserted `ite` side-conditions (via the recorded
/// definition choosing branch values per phase) and (b) the fixed semantics
/// of `div`/`mod`/constant arithmetic, each applied to exact `i128` values.
pub(crate) fn classify_column(
    term: TermId,
    manager: &TermManager,
    ite_defs: &FxHashMap<TermId, IteDef>,
) -> Option<ColumnParity> {
    let mut ev = ImageEval {
        manager,
        ite_defs,
        cond: None,
        conflict: false,
    };
    let then_val = ev.value(term, true, 0)?;
    let else_val = ev.value(term, false, 0)?;
    if ev.conflict {
        return None;
    }
    let then_odd = then_val.rem_euclid(2) == 1;
    let else_odd = else_val.rem_euclid(2) == 1;
    match (then_odd, else_odd) {
        (true, true) | (false, false) => Some(ColumnParity::Const(then_odd)),
        // then-branch odd, else-branch even: parity = the condition itself.
        (true, false) => Some(ColumnParity::Literal(ev.cond?)),
        // then-branch even, else-branch odd: parity = ¬condition.
        (false, true) => Some(ColumnParity::NegLiteral(ev.cond?)),
    }
}

/// Try to record the Int-sorted linear equality `lhs = rhs` as a
/// [`ParityRow`].  Returns `None` (and records nothing) unless the equation
/// is linear with purely integral coefficients and constant — a non-integral
/// row has no well-defined mod-2 reduction, and silently dropping it only
/// forfeits lemmas.
fn parity_row_of(
    solver: &Solver,
    lhs: TermId,
    rhs: TermId,
    manager: &TermManager,
) -> Option<ParityRow> {
    let mut lterms: SmallVec<[(TermId, Rational64); 4]> = SmallVec::new();
    let mut lconst = Rational64::zero();
    let mut rterms: SmallVec<[(TermId, Rational64); 4]> = SmallVec::new();
    let mut rconst = Rational64::zero();
    solver.extract_linear_terms(lhs, Rational64::one(), &mut lterms, &mut lconst, manager)?;
    solver.extract_linear_terms(rhs, -Rational64::one(), &mut rterms, &mut rconst, manager)?;
    // Merge both sides into one coefficient map keyed by TermId.
    let mut combined: Vec<(TermId, Rational64)> = lterms.into_iter().collect();
    combined.extend(rterms);
    combined.sort_unstable_by_key(|&(t, _)| t);
    let mut merged: Vec<(TermId, Rational64)> = Vec::with_capacity(combined.len());
    for (term, coef) in combined {
        if let Some((last_t, last_c)) = merged.last_mut() {
            if *last_t == term {
                *last_c += coef;
                continue;
            }
        }
        merged.push((term, coef));
    }
    let rhs_val = lconst - rconst;
    if rhs_val.denom() != &1 {
        return None;
    }
    let rhs = rhs_val.numer().to_i64()?;
    let mut terms: Vec<(TermId, i64)> = Vec::with_capacity(merged.len());
    for (term, coef) in merged {
        if coef == Rational64::zero() {
            continue;
        }
        if coef.denom() != &1 {
            // Non-integral coefficient: the row has no mod-2 image.  Bail
            // on the whole row — keeping the integral part would fabricate
            // a consequence the equation does not state.
            return None;
        }
        terms.push((term, coef.numer().to_i64()?));
    }
    if terms.is_empty() {
        return None;
    }
    Some(ParityRow { terms, rhs })
}

impl Solver {
    /// Derive and assert mod-2 parity lemmas, if the assertion basis changed
    /// since the last derivation.  Called once per `check_core` entry (the
    /// generation guard makes repeated entries free); see the module doc for
    /// the derivation and its soundness argument.
    pub(super) fn derive_parity_lemmas(&mut self, manager: &mut TermManager) {
        if self.parity_generation == self.parity_last_derived {
            return;
        }
        self.parity_last_derived = self.parity_generation;
        // Mod-2 reasoning needs integer semantics; without an `ite` over
        // constant branches no column can be image-determined, so there is
        // no lemma to find.
        if !self.arith.is_integer() || self.ite_defs.is_empty() {
            return;
        }

        // ---- 1. Harvest new rows from the un-walked assertions. ----
        // Conjuncts of top-level `and`s count (ite elimination packs the
        // link equalities and side conditions into one conjunction);
        // everything else (implications, negations, quantifiers, …) does
        // not: only an *asserted equality* is a row.
        let mut new_rows: Vec<ParityRow> = Vec::new();
        if self.parity_rows.len() < MAX_PARITY_ROWS {
            let mut stack: Vec<TermId> = self.assertions
                [self.parity_watermark.min(self.assertions.len())..]
                .iter()
                .rev()
                .copied()
                .collect();
            while let Some(term) = stack.pop() {
                let Some(node) = manager.get(term) else {
                    continue;
                };
                match &node.kind {
                    TermKind::And(args) => {
                        stack.extend(args.iter().rev().copied());
                    }
                    TermKind::Eq(a, b)
                        if manager
                            .get(*a)
                            .is_some_and(|n| n.sort == manager.sorts.int_sort) =>
                    {
                        if self.parity_rows.len() + new_rows.len() >= MAX_PARITY_ROWS {
                            break;
                        }
                        if let Some(row) = parity_row_of(self, *a, *b, manager) {
                            new_rows.push(row);
                        }
                    }
                    _ => {}
                }
            }
        }
        if !new_rows.is_empty() {
            let op = super::trail::TrailOp::ParityScanAdded {
                rows_len: self.parity_rows.len(),
                watermark: self.parity_watermark,
            };
            self.trail.push(op);
            self.parity_rows.append(&mut new_rows);
        }
        self.parity_watermark = self.assertions.len();
        if self.parity_rows.is_empty() {
            return;
        }

        // ---- 2. Build the GF(2) system (deterministic column order). ----
        let mut col_ids: Vec<TermId> = self
            .parity_rows
            .iter()
            .flat_map(|r| r.terms.iter().map(|&(t, _)| t))
            .collect();
        col_ids.sort_unstable();
        col_ids.dedup();
        if col_ids.is_empty() || col_ids.len() > MAX_PARITY_COLS {
            return;
        }
        let col_of: FxHashMap<TermId, usize> =
            col_ids.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let mut bad = vec![false; col_ids.len()];
        let mut parity: Vec<Option<ColumnParity>> = vec![None; col_ids.len()];
        let mut good = 0usize;
        for (i, &term) in col_ids.iter().enumerate() {
            let classified = classify_column(term, manager, &self.ite_defs);
            if let Some(p) = classified {
                parity[i] = Some(p);
                good += 1;
            } else {
                bad[i] = true;
            }
        }
        if good == 0 {
            return; // no literal-linked column: nothing to translate into
        }
        let mut rows: Vec<Gf2Row> = Vec::with_capacity(self.parity_rows.len());
        for stored in &self.parity_rows {
            let mut support: Vec<usize> = stored
                .terms
                .iter()
                .filter(|(_, c)| c % 2 != 0)
                .filter_map(|&(t, _)| col_of.get(&t).copied())
                .collect();
            support.sort_unstable();
            support.dedup();
            rows.push(Gf2Row {
                support,
                rhs: stored.rhs % 2 != 0,
            });
        }

        // ---- 3. Eliminate non-image-determined columns. ----
        let derived = gf2_eliminate_bad_columns(rows, &bad);
        if derived.is_empty() {
            return;
        }

        // ---- 4. Translate each consequence into a ground xor lemma. ----
        let mut emitted = 0usize;
        'row: for row in derived {
            if emitted >= MAX_PARITY_LEMMAS {
                break;
            }
            // Substitute the column images: constants fold into the rhs,
            // literals collect.  A support column whose classification was
            // consumed above is guaranteed present (only good columns
            // survive elimination), but a defensive `continue` keeps this
            // total: an unclassifiable column can never produce a lemma.
            let mut c = row.rhs;
            let mut lits: Vec<(TermId, bool)> = Vec::new();
            for col in row.support {
                match parity[col] {
                    Some(ColumnParity::Const(b)) => c ^= b,
                    Some(ColumnParity::Literal(t)) => lits.push((t, false)),
                    Some(ColumnParity::NegLiteral(t)) => lits.push((t, true)),
                    None => continue 'row,
                }
            }
            // Fold duplicate literals: l ⊕ l cancels, l ⊕ ¬l is constantly
            // true (both fold into the rhs).
            lits.sort_unstable();
            let mut folded: Vec<(TermId, bool)> = Vec::with_capacity(lits.len());
            let mut it = lits.into_iter().peekable();
            while let Some((t, neg)) = it.next() {
                if it.peek().is_some_and(|&(t2, _)| t2 == t) {
                    let (_, neg2) = it.next().expect("peeked just above");
                    if neg != neg2 {
                        c ^= true;
                    }
                    // same polarity twice: both cancel
                } else {
                    folded.push((t, neg));
                }
            }
            if folded.len() > MAX_PARITY_WIDTH {
                continue;
            }
            let lemma = build_xor_lemma(&folded, c, manager);
            if self.parity_lemmas.contains(&lemma) {
                continue;
            }
            self.trail
                .push(super::trail::TrailOp::ParityLemmaAdded { term: lemma });
            self.parity_lemmas.insert(lemma);
            self.assert_ground_lemma(lemma, manager);
            emitted += 1;
        }
    }
}

/// Build the Bool term `xor(l_1, …, l_k) = c` (or the constant `c` when no
/// literal survives folding).  `lits` carries `(term, negate)` pairs.
fn build_xor_lemma(lits: &[(TermId, bool)], c: bool, manager: &mut TermManager) -> TermId {
    let mut acc: Option<TermId> = None;
    for &(term, neg) in lits {
        let lit = if neg { manager.mk_not(term) } else { term };
        acc = Some(match acc {
            None => lit,
            Some(prev) => manager.mk_xor(prev, lit),
        });
    }
    let value = manager.mk_bool(c);
    match acc {
        None => value,
        Some(chain) => manager.mk_eq(chain, value),
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;

    // ---- GF(2) elimination --------------------------------------------

    #[test]
    fn gf2_elimination_recovers_the_parity_row() {
        // Two vertex rows over interior edge i2 and cross edges i0, i1:
        //   V1: i0 + i2     = 1     -> {i0, i2} = 1
        //   V2: i1 + i2 + 2 = 0     -> {i1, i2} = 0
        // Link rows i0 = v0, i1 = v1 (v's good, i's bad, i2 bad).
        // Sum of everything: v0 + v1 = 1 (i2 cancels).
        // columns: [i0, i1, i2, v0, v1]
        let bad = [true, true, true, false, false];
        let rows = vec![
            Gf2Row {
                support: vec![0, 3],
                rhs: false,
            }, // i0 = v0
            Gf2Row {
                support: vec![1, 4],
                rhs: false,
            }, // i1 = v1
            Gf2Row {
                support: vec![0, 2],
                rhs: true,
            }, // V1
            Gf2Row {
                support: vec![1, 2],
                rhs: false,
            }, // V2
        ];
        let out = gf2_eliminate_bad_columns(rows, &bad);
        assert_eq!(
            out,
            vec![Gf2Row {
                support: vec![3, 4],
                rhs: true
            }],
            "expected xor(v0, v1) = 1"
        );
    }

    #[test]
    fn gf2_elimination_reports_mod2_contradiction() {
        // x = 2y  ∧  x = 2z + 1 : mod 2 both rows pin x, rhs disagrees.
        let bad = [true, true, true]; // [x, y, z]
        let rows = vec![
            Gf2Row {
                support: vec![0],
                rhs: false,
            }, // x ≡ 0
            Gf2Row {
                support: vec![0],
                rhs: true,
            }, // x ≡ 1
        ];
        let out = gf2_eliminate_bad_columns(rows, &bad);
        assert_eq!(
            out,
            vec![Gf2Row {
                support: vec![],
                rhs: true
            }]
        );
    }

    #[test]
    fn gf2_elimination_all_bad_consumes_everything() {
        // With no good columns there is no emittable row (the span lives on
        // bad columns), except a contradiction.
        let bad = [true, true];
        let rows = vec![Gf2Row {
            support: vec![0, 1],
            rhs: false,
        }];
        assert!(gf2_eliminate_bad_columns(rows, &bad).is_empty());
    }

    // ---- column classification ----------------------------------------

    fn test_manager() -> TermManager {
        TermManager::new()
    }

    /// Build `v` as an ite fresh variable over two constant branches and
    /// register its definition, mirroring `eliminate_nonbool_ite`.
    fn ite_var(
        manager: &mut TermManager,
        name: &str,
        cond: TermId,
        c1: i64,
        c0: i64,
        defs: &mut FxHashMap<TermId, IteDef>,
    ) -> TermId {
        let int = manager.sorts.int_sort;
        let v = manager.mk_var(name, int);
        defs.insert(v, (cond, manager.mk_int(c1), manager.mk_int(c0)));
        v
    }

    #[test]
    fn classify_plain_ite_link() {
        let mut m = test_manager();
        let b = m.mk_var("b", m.sorts.bool_sort);
        let mut defs = FxHashMap::default();
        let v = ite_var(&mut m, "v", b, 1, 0, &mut defs);
        // images 1 (b) / 0 (¬b): parity = b
        assert_eq!(
            classify_column(v, &m, &defs),
            Some(ColumnParity::Literal(b))
        );
        // swapped branches: parity = ¬b
        let mut defs2 = FxHashMap::default();
        let w = ite_var(&mut m, "w", b, 0, 1, &mut defs2);
        assert_eq!(
            classify_column(w, &m, &defs2),
            Some(ColumnParity::NegLiteral(b))
        );
    }

    #[test]
    fn classify_div_mod_chain_link() {
        // The mixed-boundary link shape: t = (mod (div v 4) 2) with
        // v = ite(b, 4, 24): images (1, 0) -> parity = b.
        let mut m = test_manager();
        let b = m.mk_var("b", m.sorts.bool_sort);
        let mut defs = FxHashMap::default();
        let v = ite_var(&mut m, "v", b, 4, 24, &mut defs);
        let four = m.mk_int(4);
        let two = m.mk_int(2);
        let q = m.mk_div(v, four);
        let t = m.mk_mod(q, two);
        assert_eq!(
            classify_column(t, &m, &defs),
            Some(ColumnParity::Literal(b))
        );
        // A chain whose two images agree mod 2 contributes a constant:
        // (mod (div v 4) 2) with v = ite(b, 8, 24): (2, 6) -> both even.
        let mut defs2 = FxHashMap::default();
        let v2 = ite_var(&mut m, "v2", b, 8, 24, &mut defs2);
        let q2 = m.mk_div(v2, four);
        let t2 = m.mk_mod(q2, two);
        assert_eq!(
            classify_column(t2, &m, &defs2),
            Some(ColumnParity::Const(false))
        );
    }

    #[test]
    fn classify_two_conditions_bails() {
        // A column whose evaluation needs two distinct Booleans is not a
        // function of one literal: must return None, never a guess.
        let mut m = test_manager();
        let b1 = m.mk_var("b1", m.sorts.bool_sort);
        let b2 = m.mk_var("b2", m.sorts.bool_sort);
        let mut defs = FxHashMap::default();
        let v1 = ite_var(&mut m, "v1", b1, 1, 0, &mut defs);
        let v2 = ite_var(&mut m, "v2", b2, 1, 0, &mut defs);
        let sum = m.mk_add([v1, v2]);
        assert_eq!(classify_column(sum, &m, &defs), None);
    }

    #[test]
    fn classify_constant_and_zero_divisor() {
        let mut m = test_manager();
        let mut defs = FxHashMap::default();
        // A pure constant column: images agree (no condition needed).
        let seven = m.mk_int(7);
        assert_eq!(
            classify_column(seven, &m, &defs),
            Some(ColumnParity::Const(true))
        );
        // Division by zero is uninterpreted: no exact image, must bail.
        let b = m.mk_var("b", m.sorts.bool_sort);
        let v = ite_var(&mut m, "v", b, 4, 24, &mut defs);
        let zero = m.mk_int(0);
        let t = m.mk_div(v, zero);
        assert_eq!(classify_column(t, &m, &defs), None);
    }

    #[test]
    fn classify_negative_branch_constants_euclidean() {
        // Euclidean semantics with negative dividends: v = ite(b, -1, -2);
        // (mod (div v 2) 2): b: div(-1,2) = -1 (Euclidean), mod 2 -> 1;
        // ¬b: div(-2,2) = -1, mod 2 -> 1.  Both odd -> constant true.
        let mut m = test_manager();
        let b = m.mk_var("b", m.sorts.bool_sort);
        let mut defs = FxHashMap::default();
        let v = ite_var(&mut m, "v", b, -1, -2, &mut defs);
        let d = m.mk_int(2);
        let q = m.mk_div(v, d);
        let t = m.mk_mod(q, d);
        assert_eq!(
            classify_column(t, &m, &defs),
            Some(ColumnParity::Const(true))
        );
    }

    // ---- lemma construction --------------------------------------------

    #[test]
    fn xor_lemma_folds_duplicates_and_polarity() {
        let mut m = test_manager();
        let c = m.mk_var("c", m.sorts.bool_sort);
        // b ⊕ b cancels; c ⊕ ¬c is true: xor(c) = rhs ⊕ true.
        let folded = vec![(c, false)]; // after folding b,b and c,¬c
        let lemma = build_xor_lemma(&folded, true, &mut m);
        let expect = m.mk_eq(c, m.mk_bool(true));
        assert_eq!(lemma, expect);
        // Empty fold: the lemma is the constant itself.
        assert_eq!(build_xor_lemma(&[], false, &mut m), m.mk_false());
    }

    // ---- solver-level: the fuzzer's mixed-parity shapes ----------------

    use super::super::Solver;

    /// Build one mixed Bool+LIA parity graph, the obligation fuzzer's
    /// `parity-mixedboolint` shape (small): two Int vertices joined by an
    /// interior edge, two Bool-linked cross edges, one Bool vertex.
    ///
    /// ```text
    ///   V_I1: i0 + i2 = 0 + 2·k1      V_B1: b0 ⊕ b3 = false
    ///   V_I2: i2 + i3 = charge + 2·k2
    ///   links: i0 = ite(b0 1 0),  i3 = ite(b3 1 0)
    /// ```
    ///
    /// Odd total Int charge contradicts the Bool side's even xor; even
    /// charge is satisfiable.
    fn mixed_boolint_graph(charge: i64) -> (Solver, TermManager) {
        let mut solver = Solver::new();
        solver.set_logic("QF_LIA");
        let mut m = TermManager::new();
        let bool_sort = m.sorts.bool_sort;
        let int_sort = m.sorts.int_sort;
        let b0 = m.mk_var("b0", bool_sort);
        let b3 = m.mk_var("b3", bool_sort);
        let i0 = m.mk_var("i0", int_sort);
        let i2 = m.mk_var("i2", int_sort);
        let i3 = m.mk_var("i3", int_sort);
        let k1 = m.mk_var("k1", int_sort);
        let k2 = m.mk_var("k2", int_sort);
        let zero = m.mk_int(0);
        let one = m.mk_int(1);
        let two = m.mk_int(2);

        // links
        let l0 = m.mk_ite(b0, one, zero);
        let e0 = m.mk_eq(i0, l0);
        solver.assert(e0, &mut m);
        let l3 = m.mk_ite(b3, one, zero);
        let e3 = m.mk_eq(i3, l3);
        solver.assert(e3, &mut m);
        // Bool vertex: b0 xor b3 = false
        let x03 = m.mk_xor(b0, b3);
        let bx = m.mk_eq(x03, m.mk_false());
        solver.assert(bx, &mut m);
        // Int vertices
        let s1 = m.mk_add([i0, i2]);
        let m2k1 = m.mk_mul([two, k1]);
        let v1_rhs = m.mk_add([zero, m2k1]);
        let v1 = m.mk_eq(s1, v1_rhs);
        solver.assert(v1, &mut m);
        let s2 = m.mk_add([i2, i3]);
        let m2k2 = m.mk_mul([two, k2]);
        let ch = m.mk_int(charge);
        let v2_rhs = m.mk_add([ch, m2k2]);
        let v2 = m.mk_eq(s2, v2_rhs);
        solver.assert(v2, &mut m);
        (solver, m)
    }

    #[test]
    fn mixed_boolint_odd_charge_unsat_with_parity_lemma() {
        let (mut solver, mut m) = mixed_boolint_graph(1);
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Unsat
        );
        // The derivation must actually have fired: at least one ground xor
        // lemma was asserted (without it the obstruction needs the full
        // mixed search and stalls on the medium instances).
        assert!(!solver.parity_lemmas.is_empty());
    }

    #[test]
    fn mixed_boolint_even_charge_sat() {
        let (mut solver, mut m) = mixed_boolint_graph(0);
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Sat
        );
        assert!(!solver.parity_lemmas.is_empty());
    }

    #[test]
    fn mixed_boolint_parity_lemma_is_a_consequence() {
        // SOUNDNESS pin: a consequence of the assertions can never flip a
        // Sat verdict, so re-asserting every emitted lemma as an ordinary
        // constraint must leave the (satisfiable) even-charge instance Sat.
        let (mut solver, mut m) = mixed_boolint_graph(0);
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Sat
        );
        let lemmas: Vec<TermId> = solver.parity_lemmas.iter().copied().collect();
        assert!(!lemmas.is_empty());
        for lemma in lemmas {
            solver.assert(lemma, &mut m);
        }
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Sat
        );
    }

    /// The fuzzer's `parity-mixedboundary` shape: cross edges linked through
    /// an exact Euclidean div/mod chain (`(mod (div (ite b 4 24) 4) 2)`),
    /// so the link variable reaches the Boolean through term structure the
    /// image evaluation must walk exactly.
    fn mixed_boundary_graph(charge: i64) -> (Solver, TermManager) {
        let mut solver = Solver::new();
        solver.set_logic("QF_LIA");
        let mut m = TermManager::new();
        let bool_sort = m.sorts.bool_sort;
        let int_sort = m.sorts.int_sort;
        let b0 = m.mk_var("b0", bool_sort);
        let b3 = m.mk_var("b3", bool_sort);
        let i0 = m.mk_var("i0", int_sort);
        let i2 = m.mk_var("i2", int_sort);
        let i3 = m.mk_var("i3", int_sort);
        let k1 = m.mk_var("k1", int_sort);
        let k2 = m.mk_var("k2", int_sort);
        let four = m.mk_int(4);
        let c24 = m.mk_int(24);
        let two = m.mk_int(2);

        // links: i = (mod (div (ite b 4 24) 4) 2); images (1, 0)
        let mk_link = |b: TermId, m: &mut TermManager| {
            let it = m.mk_ite(b, four, c24);
            let q = m.mk_div(it, four);
            m.mk_mod(q, two)
        };
        let link0 = mk_link(b0, &mut m);
        let e0 = m.mk_eq(i0, link0);
        solver.assert(e0, &mut m);
        let link3 = mk_link(b3, &mut m);
        let e3 = m.mk_eq(i3, link3);
        solver.assert(e3, &mut m);
        // Bool vertex
        let x03 = m.mk_xor(b0, b3);
        let bx = m.mk_eq(x03, m.mk_false());
        solver.assert(bx, &mut m);
        // Int vertices
        let s1 = m.mk_add([i0, i2]);
        let m2k1 = m.mk_mul([two, k1]);
        let z0 = m.mk_int(0);
        let v1_rhs = m.mk_add([z0, m2k1]);
        let v1 = m.mk_eq(s1, v1_rhs);
        solver.assert(v1, &mut m);
        let s2 = m.mk_add([i2, i3]);
        let m2k2 = m.mk_mul([two, k2]);
        let ch = m.mk_int(charge);
        let v2_rhs = m.mk_add([ch, m2k2]);
        let v2 = m.mk_eq(s2, v2_rhs);
        solver.assert(v2, &mut m);
        (solver, m)
    }

    #[test]
    fn mixed_boundary_odd_charge_unsat() {
        let (mut solver, mut m) = mixed_boundary_graph(1);
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Unsat
        );
        assert!(!solver.parity_lemmas.is_empty());
    }

    #[test]
    fn mixed_boundary_even_charge_sat_and_lemmas_hold() {
        let (mut solver, mut m) = mixed_boundary_graph(0);
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Sat
        );
        assert!(!solver.parity_lemmas.is_empty());
        let lemmas: Vec<TermId> = solver.parity_lemmas.iter().copied().collect();
        for lemma in lemmas {
            solver.assert(lemma, &mut m);
        }
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Sat
        );
    }

    #[test]
    fn parity_lemmas_retreat_with_pop() {
        // Scoped correctness: a lemma derived inside a push-scope must go
        // with the scope, or a later check would inherit a refuted basis.
        let (mut solver, mut m) = mixed_boolint_graph(0);
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Sat
        );
        let before = solver.parity_lemmas.len();
        solver.push();
        // Flip the parity inside the scope: the base rows sum to
        // i0 + i3 = even; asserting the same sum odd contradicts the
        // Bool side (b0 xor b3 = false) once the parity lemma of the
        // *scope's* row set is derived.
        let int_sort = m.sorts.int_sort;
        let i0 = m.mk_var("i0", int_sort);
        let i3 = m.mk_var("i3", int_sort);
        let k3 = m.mk_var("k3", int_sort);
        let two = m.mk_int(2);
        let m2k3 = m.mk_mul([two, k3]);
        let c1 = m.mk_int(1);
        let rhs = m.mk_add([c1, m2k3]);
        let sum = m.mk_add([i0, i3]);
        let row = m.mk_eq(sum, rhs);
        solver.assert(row, &mut m);
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Unsat
        );
        solver.pop();
        // The scope's rows and lemmas are gone: even charge again.
        assert_eq!(
            solver.check(&mut m),
            crate::solver::types::SolverResult::Sat
        );
        assert_eq!(solver.parity_lemmas.len(), before);
    }
}
