//! Hermite Normal Form and complete integer-equality solving.
//!
//! # What this module computes
//!
//! [`HermiteNormalForm::try_compute`] reduces an integer matrix `A` by
//! **column operations only**, returning `H` and a unimodular `U` with
//!
//! ```text
//! A · U = H
//! ```
//!
//! where `H` is in column-echelon (Hermite) form:
//!
//! * the pivot columns are exactly the first `r` columns (`r` = rank),
//!   each pivot row carrying zeros to the right of its pivot;
//! * pivot entries are strictly positive;
//! * among pivot rows the form is lower-triangular, and the canonical
//!   reduction pass leaves every below-diagonal entry `H[i][j]` (of pivot
//!   row `i`, column `j < i`) reduced modulo the row's own pivot
//!   (`0 ≤ H[i][j] < H[i][i]`);
//! * `U` is unimodular (`|det U| = 1`), so `x ↦ U·x` is a bijection of
//!   `ℤⁿ` and the columns of `H` generate exactly the lattice generated
//!   by the columns of `A`.
//!
//! `pivot_rows` lists the row of each pivot in order. For full-row-rank
//! inputs this is the textbook HNF (`[L | 0]` with `L` lower triangular,
//! zero rows at the bottom); for rank-deficient inputs, zero rows may be
//! interleaved — pure column operations cannot reorder rows — and
//! `pivot_rows` is the authoritative echelon ordering.
//!
//! # Why this file was rewritten
//!
//! The previous implementation was not a Hermite Normal Form: its pivot
//! search mis-indexed (`col + idx` over an already-absolute `idx`) and
//! could panic out of bounds on common inputs; its sign normalization
//! negated a *row* of `H` while updating a *column* of `U`, permanently
//! breaking the documented `A·U = H` invariant (measured: for
//! `A = [[-2, 5], [0, 3]]` it returned `H = [[2, 1], [0, 3]]`,
//! `U = [[-1, 0], [-3, 1]]` with `A·U = [[-13, 5], [-9, 3]]`); it never
//! eliminated entries below pivots; and all arithmetic was unchecked
//! `i64`. It had no callers and no tests. See
//! `docs/studies/2026-09-06-mixed-parity-lia-equality-gap.md`.
//!
//! # Arithmetic contract
//!
//! All elimination runs in `i128` with a magnitude guard
//! ([`MAG_BOUND`]): every stored intermediate must satisfy `|v| ≤
//! MAG_BOUND`, under which the products and sums of the update rules
//! cannot overflow `i128`. Any violation — or a system larger than the
//! entry budget — makes the API return `None` / [`EqSolution::GiveUp`]:
//! callers fall back to their search path. A wrapped answer is never
//! returned (the same honest-skip policy as the rest of the arithmetic
//! stack).

/// Magnitude bound for every stored intermediate during elimination.
/// Update rules multiply at most two stored values (plus a gcd cofactor
/// of similar size), so `|v| ≤ 2^40` keeps every product below `2^82`,
/// far inside `i128`.
const MAG_BOUND: i128 = 1 << 40;

/// Entry budget: systems larger than this defer to the caller's search.
const MAX_ENTRIES: usize = 200_000;

/// Result of [`solve_integer_eq_system`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EqSolution {
    /// The system `A·x = b` has no integer solution, with the indices of
    /// the input rows responsible (the lineage of the reduced row whose
    /// exact-divisibility failed, or the failing consistency row).  This
    /// is the small infeasibility core CDCL(T) needs: a full-core clause
    /// teaches the SAT solver nothing it can resolve usefully.
    Infeasible(Vec<usize>),
    /// An integer solution (free variables set to zero). The witness is
    /// indexed by the matrix's column order.
    Feasible(Vec<i128>),
    /// A guard tripped (magnitude or size): no verdict, defer.
    GiveUp,
}

/// Hermite (column-echelon) normal form with its unimodular transform.
#[derive(Debug, Clone)]
pub struct HermiteNormalForm {
    /// `H` with `A · U = H`.
    pub matrix: Vec<Vec<i64>>,
    /// Unimodular `U` with `A · U = H`.
    pub transform: Vec<Vec<i64>>,
    /// Row of the pivot in each pivot column `0..rank`, in order.
    pub pivot_rows: Vec<usize>,
}

/// Iterative extended GCD over `i128`: returns `(g, s, t)` with
/// `g = gcd(|a|, |b|) ≥ 0`, `s·a + t·b = g`, and `|s| ≤ |b|/(2g)`,
/// `|t| ≤ |a|/(2g)` for nonzero `g` (the classic Bézout bounds).
fn ext_gcd(a: i128, b: i128) -> (i128, i128, i128) {
    let (mut old_r, mut r) = (a, b);
    let (mut old_s, mut s) = (1i128, 0i128);
    let (mut old_t, mut t) = (0i128, 1i128);
    while r != 0 {
        let q = old_r / r;
        let nr = old_r - q * r;
        old_r = r;
        r = nr;
        let ns = old_s - q * s;
        old_s = s;
        s = ns;
        let nt = old_t - q * t;
        old_t = t;
        t = nt;
    }
    // Normalize the gcd to be non-negative (flipping the sign of a
    // Bézout pair together with it keeps `s·a + t·b = g`).
    if old_r < 0 {
        (-old_r, -old_s, -old_t)
    } else {
        (old_r, old_s, old_t)
    }
}

/// Checked magnitude guard.
fn fits(v: i128) -> bool {
    (-MAG_BOUND..=MAG_BOUND).contains(&v)
}

/// Column-echelon reduction state (shared by HNF computation and the
/// equality solver).
struct ColEchelon {
    h: Vec<Vec<i128>>,
    u: Vec<Vec<i128>>,
    pivot_rows: Vec<usize>,
    rank: usize,
}

/// Reduce `a` (rows × cols, row-major) to column-echelon form with the
/// unimodular column transform tracked in `u` (starts as the identity).
///
/// Invariant maintained: `orig_a · U_current = H_current`.
///
/// After the call: pivot columns are `0..rank`; pivot row `pivot_rows[i]`
/// has zeros right of column `i` and a positive pivot at column `i`.
/// Returns `None` when a magnitude/size guard trips.
fn column_echelon(a: &[Vec<i128>]) -> Option<ColEchelon> {
    let rows = a.len();
    let cols = a.first().map_or(0, |r| r.len());
    if rows * cols > MAX_ENTRIES {
        return None;
    }
    let mut h: Vec<Vec<i128>> = a.to_vec();
    let mut u: Vec<Vec<i128>> = vec![vec![0i128; cols]; cols];
    for (i, row) in u.iter_mut().enumerate() {
        row[i] = 1;
    }
    let mut pivot_rows: Vec<usize> = Vec::new();

    for r in 0..rows {
        let cs = pivot_rows.len(); // pivot columns found so far
        // Euclid-reduce row r over the open columns cs..cols until at
        // most one nonzero entry remains, then install it as a pivot.
        loop {
            let mut nz = [usize::MAX, usize::MAX];
            for (i, &v) in h[r][cs..cols].iter().enumerate() {
                if v != 0 {
                    if nz[0] == usize::MAX {
                        nz[0] = cs + i;
                    } else {
                        nz[1] = cs + i;
                        break;
                    }
                }
            }
            if nz[1] == usize::MAX {
                break;
            }
            let (p, q) = (nz[0], nz[1]);
            let (a0, b0) = (h[r][p], h[r][q]);
            let (g, s, t) = ext_gcd(a0, b0);
            if g == 0 {
                // Both entries zero cannot happen here (nz only lists
                // nonzeros); defensive, keeps arithmetic total.
                break;
            }
            // Unimodular pair update (det = s·(a0/g) − t·(−b0/g) = 1):
            //   c_p' =  s·c_p + t·c_q
            //   c_q' = -(b0/g)·c_p + (a0/g)·c_q     (zeroes h[r][q])
            let (m11, m12) = (s, t);
            let (m21, m22) = (-b0 / g, a0 / g);
            for row in h.iter_mut() {
                let (hp, hq) = (row[p], row[q]);
                row[p] = m11 * hp + m12 * hq;
                row[q] = m21 * hp + m22 * hq;
                if !fits(row[p]) || !fits(row[q]) {
                    return None;
                }
            }
            for row in u.iter_mut() {
                let (up, uq) = (row[p], row[q]);
                row[p] = m11 * up + m12 * uq;
                row[q] = m21 * up + m22 * uq;
                if !fits(row[p]) || !fits(row[q]) {
                    return None;
                }
            }
        }
        // Install the (at most one) remaining nonzero as the pivot at the
        // next column slot, swapping it into position.
        if let Some(p) = (cs..cols).find(|&c| h[r][c] != 0) {
            if p != cs {
                for row in h.iter_mut() {
                    row.swap(p, cs);
                }
                for row in u.iter_mut() {
                    row.swap(p, cs);
                }
            }
            if h[r][cs] < 0 {
                for row in h.iter_mut() {
                    row[cs] = -row[cs];
                }
                for row in u.iter_mut() {
                    row[cs] = -row[cs];
                }
            }
            pivot_rows.push(r);
        }
    }
    Some(ColEchelon {
        rank: pivot_rows.len(),
        h,
        u,
        pivot_rows,
    })
}

/// Decide the integer system `A·x = b` completely.
///
/// Soundness and completeness both hold for the returned verdicts:
/// `Infeasible` is a proof (forward substitution found an indivisible
/// pivot row, or a consistency row fails); `Feasible` is a witness (with
/// free variables set to zero, which is lossless: in column-echelon form
/// the pivot variables are *uniquely determined* by the earlier ones, so
/// either every choice of free variables works or none does — unlike
/// row-Gaussian elimination with free variables, where integrality can
/// depend on the free choice, this substitution order never consults
/// them).
pub fn solve_integer_eq_system(a: &[Vec<i128>], b: &[i128]) -> EqSolution {
    let rows = a.len();
    if rows != b.len() {
        return EqSolution::GiveUp;
    }
    let Some(e) = column_echelon(a) else {
        return EqSolution::GiveUp;
    };
    let cols = e.u.len();
    // Forward substitution over pivot rows in pivot order: pivot row i
    // reads sum_{j<=i} H[pr_i][j]·y_j = b[pr_i]; y_i is uniquely
    // determined by y_0..y_{i-1}.
    let mut z = vec![0i128; e.rank];
    for (i, &pr) in e.pivot_rows.iter().enumerate() {
        let mut val = b[pr];
        if !fits(val) {
            return EqSolution::GiveUp;
        }
        for (j, &zj) in z.iter().enumerate() {
            let term = match e.h[pr][j].checked_mul(zj) {
                Some(t) => t,
                None => return EqSolution::GiveUp,
            };
            val = match val.checked_sub(term) {
                Some(v) => v,
                None => return EqSolution::GiveUp,
            };
            if !fits(val) {
                return EqSolution::GiveUp;
            }
        }
        let d = e.h[pr][i];
        if d == 0 {
            return EqSolution::GiveUp;
        }
        if val % d != 0 {
            // Lineage: the failing effective row is `pr` after
            // substituting the earlier pivots, so every pivot row that
            // fed a z value (transitively) is responsible.
            let mut core: Vec<usize> = Vec::new();
            for j in 0..=i {
                core.push(e.pivot_rows[j]);
            }
            core.sort_unstable();
            core.dedup();
            return EqSolution::Infeasible(core);
        }
        z[i] = val / d;
        if !fits(z[i]) {
            return EqSolution::GiveUp;
        }
    }
    // Consistency rows: non-pivot rows must be satisfied (their entries
    // live only in pivot columns by the echelon invariant).
    for (w, row) in e.h.iter().enumerate() {
        if e.pivot_rows.contains(&w) {
            continue;
        }
        let mut sum: i128 = 0;
        for (j, &zj) in z.iter().enumerate() {
            let term = match row[j].checked_mul(zj) {
                Some(t) => t,
                None => return EqSolution::GiveUp,
            };
            sum = match sum.checked_add(term) {
                Some(v) => v,
                None => return EqSolution::GiveUp,
            };
            if !fits(sum) {
                return EqSolution::GiveUp;
            }
        }
        if sum != b[w] {
            // The consistency row failed on its own; the earlier pivots
            // determined z, so their lineage is responsible too.
            let mut core: Vec<usize> = vec![w];
            core.extend_from_slice(&e.pivot_rows);
            core.sort_unstable();
            core.dedup();
            return EqSolution::Infeasible(core);
        }
    }
    // Witness: y = [z; 0] over the transformed columns, x = U·y.
    let mut x = vec![0i128; cols];
    for (c, xc) in x.iter_mut().enumerate() {
        let mut acc: i128 = 0;
        for (j, &zj) in z.iter().enumerate() {
            let term = match e.u[c][j].checked_mul(zj) {
                Some(t) => t,
                None => return EqSolution::GiveUp,
            };
            acc = match acc.checked_add(term) {
                Some(v) => v,
                None => return EqSolution::GiveUp,
            };
        }
        if !fits(acc) {
            return EqSolution::GiveUp;
        }
        *xc = acc;
    }
    EqSolution::Feasible(x)
}

impl HermiteNormalForm {
    /// Compute the canonical column-echelon (Hermite) normal form of
    /// `matrix` with checked arithmetic. Returns `None` when a magnitude
    /// or size guard trips (never a wrapped or malformed result).
    ///
    /// # Panics
    ///
    /// Panics only on ragged input (rows of differing length), which is a
    /// caller bug, not a data property.
    pub fn try_compute(matrix: &[Vec<i64>]) -> Option<Self> {
        let cols = matrix.first().map_or(0, |r| r.len());
        let wide: Vec<Vec<i128>> = matrix
            .iter()
            .map(|row| {
                assert_eq!(
                    row.len(),
                    cols,
                    "try_compute: ragged matrix is a caller bug"
                );
                row.iter().map(|&v| i128::from(v)).collect()
            })
            .collect();
        let mut e = column_echelon(&wide)?;
        // Canonical reduction: for every pivot row i (in order), reduce
        // each below-diagonal entry H[pr_i][j], j < i, modulo the row's
        // own pivot via `col_j <- col_j - k·col_i`. This leaves all rows
        // above i untouched (their entry in column i is zero — it is
        // right of their pivots), so a single top-down pass suffices.
        for i in 1..e.rank {
            let pr = e.pivot_rows[i];
            for j in 0..i {
                let d = e.h[pr][i];
                debug_assert!(d > 0, "pivot sign normalized during echelon");
                let k = e.h[pr][j].div_euclid(d);
                if k == 0 {
                    continue;
                }
                for row in e.h.iter_mut() {
                    let hi = row[i];
                    row[j] -= k * hi;
                    if !fits(row[j]) {
                        return None;
                    }
                }
                for row in e.u.iter_mut() {
                    let ui = row[i];
                    row[j] -= k * ui;
                    if !fits(row[j]) {
                        return None;
                    }
                }
            }
        }
        // Narrow back to i64 (guarded).
        let narrow = |v: i128| -> Option<i64> { i64::try_from(v).ok() };
        let mut matrix_i64 = Vec::with_capacity(e.h.len());
        for row in &e.h {
            let mut r = Vec::with_capacity(row.len());
            for &v in row {
                r.push(narrow(v)?);
            }
            matrix_i64.push(r);
        }
        let mut transform_i64 = Vec::with_capacity(e.u.len());
        for row in &e.u {
            let mut r = Vec::with_capacity(row.len());
            for &v in row {
                r.push(narrow(v)?);
            }
            transform_i64.push(r);
        }
        Some(HermiteNormalForm {
            matrix: matrix_i64,
            transform: transform_i64,
            pivot_rows: e.pivot_rows,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Exact integer determinant by fraction-free (Bareiss) elimination.
    fn det_i128(m: &[Vec<i128>]) -> i128 {
        let n = m.len();
        let mut a = m.to_vec();
        let mut sign = 1i128;
        let mut prev = 1i128;
        for i in 0..n {
            let Some(p) = (i..n).find(|&r| a[r][i] != 0) else {
                return 0;
            };
            if p != i {
                a.swap(p, i);
                sign = -sign;
            }
            for r in (i + 1)..n {
                for c in (i + 1)..n {
                    a[r][c] = (a[r][c] * a[i][i] - a[r][i] * a[i][c]) / prev;
                }
                a[r][i] = 0;
            }
            prev = a[i][i];
        }
        sign * a[n - 1][n - 1]
    }

    fn matmul(a: &[Vec<i128>], b: &[Vec<i128>]) -> Vec<Vec<i128>> {
        let (m, k, n) = (a.len(), b.len(), b[0].len());
        let mut out = vec![vec![0i128; n]; m];
        for i in 0..m {
            for j in 0..n {
                for l in 0..k {
                    out[i][j] += a[i][l] * b[l][j];
                }
            }
        }
        out
    }

    fn widen(m: &[Vec<i64>]) -> Vec<Vec<i128>> {
        m.iter()
            .map(|r| r.iter().map(|&v| i128::from(v)).collect())
            .collect()
    }

    /// Full invariant check on a computed HNF.
    fn check_hnf(a: &[Vec<i64>]) {
        let Some(hnf) = HermiteNormalForm::try_compute(a) else {
            panic!("try_compute gave up on a small matrix {a:?}");
        };
        let h = widen(&hnf.matrix);
        let u = widen(&hnf.transform);
        let aw = widen(a);
        // 1. The contract: A·U == H.
        assert_eq!(matmul(&aw, &u), h, "A·U != H for A = {a:?}");
        // 2. U unimodular.
        if !u.is_empty() {
            assert!(
                det_i128(&u).abs() == 1,
                "U not unimodular for A = {a:?}: det = {}",
                det_i128(&u)
            );
        }
        // 3. Echelon structure: pivot rows have zeros right of their
        //    pivot; pivots positive; pivot columns are 0..rank.
        for (i, &pr) in hnf.pivot_rows.iter().enumerate() {
            assert!(h[pr][i] > 0, "non-positive pivot for A = {a:?}");
            for &v in &h[pr][(i + 1)..] {
                assert_eq!(v, 0, "nonzero right of pivot for A = {a:?}");
            }
        }
        // 4. Canonical bounds among pivot rows: 0 <= H[pr_i][j] < H[pr_i][i].
        for (i, &pr) in hnf.pivot_rows.iter().enumerate() {
            for j in 0..i {
                assert!(
                    h[pr][j] >= 0 && h[pr][j] < h[pr][i],
                    "canonical bound violated at row {pr} col {j} for A = {a:?}"
                );
            }
        }
    }

    #[test]
    fn hnf_invariants_on_the_historical_broken_cases() {
        // The exact inputs the old implementation mishandled.
        check_hnf(&[vec![-2, 5], vec![0, 3]]);
        check_hnf(&[vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 10]]);
        check_hnf(&[vec![0, 1], vec![2, 0], vec![0, 3]]);
    }

    #[test]
    fn hnf_invariants_on_structured_cases() {
        check_hnf(&[vec![1, 1], vec![0, 0], vec![1, 0]]); // rank-deficient middle row
        check_hnf(&[vec![2, 4], vec![0, 3]]);
        check_hnf(&[vec![0]]);
        check_hnf(&[vec![0, 0], vec![0, 0]]);
        check_hnf(&[vec![-7]]);
        check_hnf(&[vec![3, 1], vec![-1, 2], vec![5, 5], vec![0, -4]]);
    }

    #[test]
    fn hnf_known_value() {
        // Lattice basis {(2,0), (1,3)} (columns of [[2,1],[0,3]]):
        // canonical column HNF is [[1, 0], [3, 6]] — pivot row 0
        // concentrates gcd(2,1) = 1 at column 0; entry 3 below the pivot
        // already reduced mod 6.
        let hnf = HermiteNormalForm::try_compute(&[vec![2, 1], vec![0, 3]]).unwrap();
        assert_eq!(hnf.matrix, vec![vec![1, 0], vec![3, 6]]);
        assert_eq!(hnf.pivot_rows, vec![0, 1]);
    }

    #[test]
    fn hnf_overflow_bails_instead_of_wrapping() {
        // Products in the first elimination step exceed the magnitude
        // guard: the honest answer is None, never a wrapped matrix.
        let big = (1i64 << 40) + 7;
        let a = vec![vec![big, big - 1], vec![1, 0]];
        assert!(HermiteNormalForm::try_compute(&a).is_none());
    }

    #[test]
    fn ext_gcd_bezout_identity_holds() {
        let cases: &[(i128, i128)] = &[
            (2, 3),
            (-4, 6),
            (0, 5),
            (5, 0),
            (-12, -18),
            (270, -192),
            (1 << 30, -(1 << 20) + 1),
        ];
        for &(a, b) in cases {
            let (g, s, t) = ext_gcd(a, b);
            assert_eq!(s * a + t * b, g);
            assert!(g >= 0);
            let (mut x, mut y) = (a.abs(), b.abs());
            while y != 0 {
                let t = x % y;
                x = y;
                y = t;
            }
            assert_eq!(g, x);
        }
    }

    #[test]
    fn solve_classic_systems() {
        // y = 2x ∧ y = 2z + 1 (columns x, y, z): subtracting the rows
        // gives 2x − 2z = 1, which has no integer solution.
        let a = vec![vec![2, -1, 0], vec![0, -1, 2]];
        let b = vec![0, -1];
        match solve_integer_eq_system(&a, &b) {
            EqSolution::Infeasible(core) => {
                assert!(!core.is_empty() && core.len() <= a.len());
            }
            other => panic!("expected Infeasible, got {other:?}"),
        }
        // 2x + y = 1 with y free: the classic row-Gaussian+free=0 trap
        // (x = (1−y)/2 is integral only for odd y). The column-echelon
        // solver must find the (0, 1) family member.
        let a = vec![vec![2, 1]];
        let b = vec![1];
        match solve_integer_eq_system(&a, &b) {
            EqSolution::Feasible(x) => assert_eq!(2 * x[0] + x[1], 1, "witness must satisfy"),
            other => panic!("expected Feasible, got {other:?}"),
        }
        // Zero row with nonzero rhs: infeasible.
        match solve_integer_eq_system(&[vec![0, 0]], &[5]) {
            EqSolution::Infeasible(core) => assert_eq!(core, vec![0]),
            other => panic!("expected Infeasible, got {other:?}"),
        }
        // Empty system: feasible with the empty witness.
        assert_eq!(
            solve_integer_eq_system(&[], &[]),
            EqSolution::Feasible(vec![])
        );
    }

    /// Deterministic randomized cross-check against brute force: every
    /// small system's verdict must agree with enumeration over a box.
    #[test]
    fn solve_agrees_with_brute_force() {
        let mut seed = 0x5EED_1234u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _case in 0..400 {
            let vars = 1 + (next() % 4) as usize;
            let rows = 1 + (next() % 4) as usize;
            let mut a = vec![vec![0i128; vars]; rows];
            for row in &mut a {
                for v in row.iter_mut() {
                    *v = i128::from((next() % 9) as i64) - 4;
                }
            }
            let b: Vec<i128> = (0..rows)
                .map(|_| i128::from((next() % 9) as i64) - 4)
                .collect();
            let got = solve_integer_eq_system(&a, &b);
            // Brute force over [-8, 8]^vars.
            let box_bound = 8i128;
            let mut witness = vec![0i128; vars];
            let mut total_steps = 1u64;
            for _ in 0..vars {
                total_steps *= (2 * box_bound + 1) as u64;
            }
            let mut found = None;
            let mut steps = 0u64;
            'outer: loop {
                if steps >= total_steps {
                    break;
                }
                // Decode steps as the mixed-radix assignment.
                let mut rem = steps;
                for v in witness.iter_mut() {
                    let digit = rem % (2 * box_bound + 1) as u64;
                    rem /= (2 * box_bound + 1) as u64;
                    *v = box_bound - i128::from(digit as i64);
                }
                if a.iter().zip(&b).all(|(row, &rhs)| {
                    row.iter().zip(&witness).map(|(&c, &x)| c * x).sum::<i128>() == rhs
                }) {
                    found = Some(witness.clone());
                    break 'outer;
                }
                steps += 1;
            }
            match got {
                EqSolution::Infeasible(core) => {
                    assert!(!core.is_empty() && core.len() <= rows);
                    assert!(
                        found.is_none(),
                        "solver said Infeasible but brute force found {found:?} for A={a:?} b={b:?}"
                    );
                }
                EqSolution::Feasible(ref x) => {
                    // The witness itself may lie outside the brute-force
                    // box; verify it directly instead.
                    for (row, &rhs) in a.iter().zip(&b) {
                        let val: i128 = row.iter().zip(x).map(|(&c, &xv)| c * xv).sum();
                        assert_eq!(val, rhs, "bad witness for A={a:?} b={b:?}");
                    }
                    // If brute force found nothing in-box, the solver may
                    // still be right (solutions can live outside); only
                    // cross-check when both have verdicts.
                    if found.is_none() {
                        continue;
                    }
                }
                EqSolution::GiveUp => {
                    panic!("small system must not GiveUp: A={a:?} b={b:?}")
                }
            }
            // If brute force found a witness, the solver must not say
            // Infeasible (checked above) — and any witness it produced is
            // verified above, so agreement is complete.
        }
    }

    #[test]
    fn solve_parity_shaped_system_is_feasible_for_even_charge() {
        // The 26-vertex parity shape, scaled down: 6 vertices, 8 edges,
        // slack per vertex, even total charge — the exact class that
        // stalled branch-and-bound (see the mixed-parity study).
        let verts = 6usize;
        let edges: Vec<(usize, usize)> = (1..verts)
            .map(|v| (v / 2, v))
            .chain([(0, 3), (2, 5), (1, 4)])
            .collect();
        // Total charge 2 (even): satisfiable.
        let charge = [0i128, 1, 0, 1, 0, 0];
        let n = edges.len() + verts; // i_e then k_v columns
        let mut a = vec![vec![0i128; n]; verts];
        for (e, &(x, y)) in edges.iter().enumerate() {
            a[x][e] += 1;
            a[y][e] += 1;
        }
        for v in 0..verts {
            a[v][edges.len() + v] = -2; // move slack to the left side
        }
        match solve_integer_eq_system(&a, &charge) {
            EqSolution::Feasible(x) => {
                for (row, &rhs) in a.iter().zip(charge.iter()) {
                    let val: i128 = row.iter().zip(&x).map(|(&c, &xv)| c * xv).sum();
                    assert_eq!(val, rhs);
                }
            }
            other => panic!("even-charge parity system must be feasible, got {other:?}"),
        }
        // Odd charge: infeasible, and the core spans every vertex row.
        let mut odd = charge;
        odd[0] += 1;
        match solve_integer_eq_system(&a, &odd) {
            EqSolution::Infeasible(core) => assert_eq!(core.len(), verts),
            other => panic!("odd charge must be infeasible, got {other:?}"),
        }
    }
}
