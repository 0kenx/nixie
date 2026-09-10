//! Barrel-shifter bit-blasting for `bvshl`, `bvlshr`, and `bvashr`.
//!
//! Split out of `solver.rs` to keep that file under the 2000-line policy.
//! All three encodings share the same structure: a logarithmic chain of mux
//! stages consumes the low `num_stages` bits of the shift amount, and any
//! *high* shift bit (index >= `num_stages`) forces an over-shift, whose result
//! is the SMT-LIB fill value (0 for `bvshl`/`bvlshr`, the sign bit for
//! `bvashr`).
//!
//! The high-bit handling is the soundness-critical part: without it a shift
//! amount whose only set bits are above `num_stages` (e.g. `#x10` for width 8)
//! would be silently treated as a shift by 0, encoding `bvshl x #x10` as `x`
//! instead of `0`.
//!
//! Every stage is composed over [`super::Sig`] through the folding gate
//! constructors, exactly like Z3's bit-blaster composes its muxes over the
//! rewriting layer: a constant shift-amount bit selects a branch at build
//! time (the whole stage becomes a wire), and constant value bits stay
//! constants through every stage.  The historical variable-per-stage chain
//! re-opacified each folded mux into a pinned variable the next stage's mux
//! could not see through, which is what kept a shift by a symbolic amount
//! over a partially-constant value from collapsing.

use super::BvSolver;
use nixie_core::ast::TermId;
use nixie_sat::Var;
use smallvec::SmallVec;

/// A signal-level shift stage: `sel ? if_true : if_false`, folded.
type SigVec = SmallVec<[super::Sig; 32]>;

impl BvSolver {
    /// Number of mux stages a barrel shifter needs for a given width.
    ///
    /// Stage `s` (for `s` in `0..num_stages`) shifts by `2^s`, so the stages
    /// cover shift-amount bits `0..num_stages`. `num_stages = ilog2(width) + 1`
    /// guarantees the covered bits can express every in-range shift and that
    /// the smallest *uncovered* bit already has value `2^num_stages > width`,
    /// i.e. any high bit means "shift >= width".
    fn barrel_stages(width: usize) -> u32 {
        width.ilog2() + 1
    }

    /// OR together the over-shift detector bits as a signal (`None` when the
    /// slice is empty: no shift-amount bit can reach past the width).
    fn overshift_sig(&mut self, bits: &[Var]) -> Option<super::Sig> {
        let mut acc: Option<super::Sig> = None;
        for &b in bits {
            let bs = self.sig(b);
            acc = Some(match acc {
                None => bs,
                Some(prev) => self.gate_or(prev, bs),
            });
        }
        acc
    }

    /// Commit the final stage signals into the result bits, applying the
    /// SMT-LIB over-shift fill (`fill`) when any high shift bit is set.
    /// `overshift` is `None` when no bit can express an over-shift at this
    /// width.
    fn commit_shift_result(
        &mut self,
        result: &[Var],
        current: &SigVec,
        overshift: Option<super::Sig>,
        fill: super::Sig,
    ) {
        match overshift {
            Some(ov) => {
                for (i, &cur) in current.iter().enumerate() {
                    let muxed = self.gate_mux(ov, fill, cur);
                    self.wire(result[i], muxed);
                }
            }
            None => {
                for (i, &cur) in current.iter().enumerate() {
                    self.wire(result[i], cur);
                }
            }
        }
    }

    /// One barrel-shifter pass over `value`: `num_stages` mux stages steered
    /// by the low bits of `amount`, each stage shifting by `2^s` according to
    /// `steer` (which supplies, per stage `s`, the index transform and fill).
    /// Returns the final stage's signals (over-shift fill still to apply).
    ///
    /// `shifted_index(i, shift_by)` gives the source index feeding result bit
    /// `i` when the stage shifts by `shift_by` (`None` = fill).
    #[allow(clippy::too_many_arguments)]
    fn barrel_pass(
        &mut self,
        value: &SigVec,
        amount_bits: &[Var],
        num_stages: u32,
        width: usize,
        fill: super::Sig,
        shifted_index: impl Fn(usize, usize) -> Option<usize>,
    ) -> SigVec {
        let mut current: SigVec = SmallVec::from_slice(value);
        for s in 0..num_stages {
            let shift_by = 1usize << s;
            let sel = self.sig(amount_bits[s as usize]);
            let mut next: SigVec = SmallVec::with_capacity(width);
            for i in 0..width {
                let next_sig = match shifted_index(i, shift_by) {
                    Some(src) => self.gate_mux(sel, current[src], current[i]),
                    None => self.gate_mux(sel, fill, current[i]),
                };
                next.push(next_sig);
            }
            current = next;
        }
        current
    }

    /// Left shift: result = a << b (SMT-LIB `bvshl`).
    ///
    /// Shift amounts >= width yield all-zero, per SMT-LIB semantics. The high
    /// bits of the shift amount participate via the over-shift detector.
    pub fn bv_shl(&mut self, result: TermId, a: TermId, shift_amount: TermId) -> bool {
        if let Some((va, shift)) = self.binop_bits(a, shift_amount) {
            let width = va.width as usize;
            if width == 0 {
                return false;
            }
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };
            let num_stages = Self::barrel_stages(width);

            let value: SigVec = va.bits.iter().map(|&b| self.sig(b)).collect();
            // Bit `i` of the shifted-out value comes from `i - shift_by`.
            let current = self.barrel_pass(
                &value,
                &shift.bits,
                num_stages,
                width,
                super::Sig::False,
                |i, shift_by| i.checked_sub(shift_by),
            );

            // Any shift bit at or above num_stages means shift >= width -> 0.
            let overshift = self.overshift_sig(&shift.bits[num_stages as usize..]);
            self.commit_shift_result(&r.bits, &current, overshift, super::Sig::False);
            self.finish_result(result);
            true
        } else {
            false
        }
    }

    /// Logical right shift: result = a >> b (unsigned, SMT-LIB `bvlshr`).
    ///
    /// Shift amounts >= width yield all-zero. High shift bits participate via
    /// the over-shift detector.
    pub fn bv_lshr(&mut self, result: TermId, a: TermId, shift_amount: TermId) -> bool {
        if let Some((va, shift)) = self.binop_bits(a, shift_amount) {
            let width = va.width as usize;
            if width == 0 {
                return false;
            }
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };
            let num_stages = Self::barrel_stages(width);

            let value: SigVec = va.bits.iter().map(|&b| self.sig(b)).collect();
            // Bit `i` of the shifted value comes from `i + shift_by` when in
            // range; past the top, the shift feeds zeros.
            let current = self.barrel_pass(
                &value,
                &shift.bits,
                num_stages,
                width,
                super::Sig::False,
                |i, shift_by| {
                    let src = i + shift_by;
                    (src < width).then_some(src)
                },
            );

            let overshift = self.overshift_sig(&shift.bits[num_stages as usize..]);
            self.commit_shift_result(&r.bits, &current, overshift, super::Sig::False);
            self.finish_result(result);
            true
        } else {
            false
        }
    }

    /// Arithmetic right shift: result = a >> b (signed, sign-extends;
    /// SMT-LIB `bvashr`).
    ///
    /// Shift amounts >= width yield an all-`sign` result (0 for non-negative
    /// `a`, all-ones for negative `a`). High shift bits participate via the
    /// over-shift detector, with the sign bit as the fill value.
    pub fn bv_ashr(&mut self, result: TermId, a: TermId, shift_amount: TermId) -> bool {
        if let Some((va, shift)) = self.binop_bits(a, shift_amount) {
            let width = va.width as usize;
            if width == 0 {
                return false;
            }
            let Some(r) = self.result_bits(result, va.width) else {
                return false;
            };
            let num_stages = Self::barrel_stages(width);

            // Sign bit is the fill for both in-range and over-shift cases.
            let sign = self.sig(va.bits[width - 1]);

            let value: SigVec = va.bits.iter().map(|&b| self.sig(b)).collect();
            // Bit `i` of the shifted value comes from `i + shift_by` when in
            // range; past the top, the shift replicates the sign bit.
            let current = self.barrel_pass(
                &value,
                &shift.bits,
                num_stages,
                width,
                sign,
                |i, shift_by| {
                    let src = i + shift_by;
                    (src < width).then_some(src)
                },
            );

            let overshift = self.overshift_sig(&shift.bits[num_stages as usize..]);
            self.commit_shift_result(&r.bits, &current, overshift, sign);
            self.finish_result(result);
            true
        } else {
            false
        }
    }
}
