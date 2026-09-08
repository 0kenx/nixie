//! Exact symbolic arithmetic. The unpack/alignment/GRS-rounding construction
//! follows Z3's ast/fpa/fpa2bv_converter.cpp (unpack, add_core, mk_mul, round).
//! Exponents are widened enough to hold both format bounds and normalization
//! distances, including small-exponent/large-significand custom formats.

use core::cell::{Cell, RefCell};
use nixie_core::ast::{RoundingMode, TermId, TermKind, TermManager};
use nixie_theories::{FpFormat, FpValue};
use num_bigint::BigInt;

#[derive(Clone, Copy, Debug)]
pub(super) struct Expr {
    pub id: TermId,
    /// Zero denotes Bool; all other widths denote a bit vector.
    pub width: u32,
}

pub(super) struct Circuit {
    pub manager: RefCell<TermManager>,
    serial: Cell<usize>,
}

impl Circuit {
    pub fn new() -> Self {
        Self {
            manager: RefCell::new(TermManager::new()),
            serial: Cell::new(0),
        }
    }
    fn node(&self, kind: TermKind, width: u32) -> Expr {
        let mut m = self.manager.borrow_mut();
        let sort = if width == 0 {
            m.sorts.bool_sort
        } else {
            m.sorts.bitvec(width)
        };
        Expr {
            id: m.intern_term(kind, sort),
            width,
        }
    }
    pub fn fresh(&self, width: u32) -> Expr {
        let serial = self.serial.get();
        self.serial.set(serial + 1);
        let mut m = self.manager.borrow_mut();
        let sort = if width == 0 {
            m.sorts.bool_sort
        } else {
            m.sorts.bitvec(width)
        };
        Expr {
            id: m.mk_var(&format!("fp_hybrid_{serial}"), sort),
            width,
        }
    }
    pub fn n(&self, value: impl Into<BigInt>, width: u32) -> Expr {
        let value = nixie_core::ast::bv_wrap_unsigned(&value.into(), width);
        Expr {
            id: self.manager.borrow_mut().mk_bitvec(value, width),
            width,
        }
    }
    pub fn boolean(&self, value: bool) -> Expr {
        Expr {
            id: self.manager.borrow_mut().mk_bool(value),
            width: 0,
        }
    }
    pub fn not(&self, x: Expr) -> Expr {
        self.node(TermKind::Not(x.id), 0)
    }
    pub fn and(&self, xs: &[Expr]) -> Expr {
        self.node(TermKind::And(xs.iter().map(|x| x.id).collect()), 0)
    }
    pub fn or(&self, xs: &[Expr]) -> Expr {
        self.node(TermKind::Or(xs.iter().map(|x| x.id).collect()), 0)
    }
    pub fn eq(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::Eq(x.id, y.id), 0)
    }
    pub fn ite(&self, cond: Expr, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::Ite(cond.id, x.id, y.id), x.width)
    }
    pub fn add(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::BvAdd(x.id, y.id), x.width)
    }
    pub fn sub(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::BvSub(x.id, y.id), x.width)
    }
    fn mul(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::BvMul(x.id, y.id), x.width)
    }
    pub fn bor(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::BvOr(x.id, y.id), x.width)
    }
    pub fn xor(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::BvXor(x.id, y.id), x.width)
    }
    fn neg(&self, x: Expr) -> Expr {
        self.sub(self.n(0, x.width), x)
    }
    pub fn ult(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::BvUlt(x.id, y.id), 0)
    }
    fn slt(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::BvSlt(x.id, y.id), 0)
    }
    pub fn cat(&self, x: Expr, y: Expr) -> Expr {
        self.node(TermKind::BvConcat(x.id, y.id), x.width + y.width)
    }
    pub fn extract(&self, x: Expr, hi: u32, lo: u32) -> Expr {
        self.node(
            TermKind::BvExtract {
                arg: x.id,
                high: hi,
                low: lo,
            },
            hi - lo + 1,
        )
    }
    fn zext(&self, x: Expr, width: u32) -> Expr {
        if width == x.width {
            x
        } else if width < x.width {
            self.extract(x, width - 1, 0)
        } else {
            self.cat(self.n(0, width - x.width), x)
        }
    }
    fn resize_shift(&self, shift: Expr, width: u32) -> Expr {
        // Truncating a shift count is unsound. Saturate first if narrowing.
        if shift.width > width {
            let capped = self.ite(
                self.ult(shift, self.n(width, shift.width)),
                shift,
                self.n(width, shift.width),
            );
            self.zext(capped, width)
        } else {
            self.zext(shift, width)
        }
    }
    fn shl(&self, x: Expr, n: Expr) -> Expr {
        let n = self.resize_shift(n, x.width);
        self.node(TermKind::BvShl(x.id, n.id), x.width)
    }
    fn shr(&self, x: Expr, n: Expr) -> Expr {
        let n = self.resize_shift(n, x.width);
        self.node(TermKind::BvLshr(x.id, n.id), x.width)
    }
    pub fn nonzero(&self, x: Expr) -> Expr {
        self.not(self.eq(x, self.n(0, x.width)))
    }
    fn bit(&self, x: Expr, i: u32) -> Expr {
        self.nonzero(self.extract(x, i, i))
    }
    fn bool_bits(&self, x: Expr, width: u32) -> Expr {
        self.ite(x, self.n(1, width), self.n(0, width))
    }
    /// Logical shift right with all discarded bits jammed into bit zero.
    fn jam(&self, x: Expr, n: Expr) -> Expr {
        let shifted = self.shr(x, n);
        let lost = self.not(self.eq(self.shl(shifted, n), x));
        self.bor(shifted, self.bool_bits(lost, x.width))
    }
    fn leading_zeros(&self, x: Expr, width: u32) -> Expr {
        let mut result = self.n(x.width, width);
        for i in 0..x.width {
            result = self.ite(self.bit(x, i), self.n(x.width - 1 - i, width), result);
        }
        result
    }
    fn ew(f: FpFormat) -> u32 {
        (f.exponent_bits + 3).max(32 - (4 * f.significand_bits + 32).leading_zeros() + 1)
    }
    pub fn sign(&self, x: Expr) -> Expr {
        self.extract(x, x.width - 1, x.width - 1)
    }
    pub fn exp(&self, x: Expr, f: FpFormat) -> Expr {
        self.extract(x, x.width - 2, f.significand_bits - 1)
    }
    pub fn fraction(&self, x: Expr, f: FpFormat) -> Expr {
        self.extract(x, f.significand_bits - 2, 0)
    }
    pub fn is_nan(&self, x: Expr, f: FpFormat) -> Expr {
        self.and(&[
            self.eq(self.exp(x, f), self.n(f.max_exponent(), f.exponent_bits)),
            self.nonzero(self.fraction(x, f)),
        ])
    }
    pub fn is_inf(&self, x: Expr, f: FpFormat) -> Expr {
        self.and(&[
            self.eq(self.exp(x, f), self.n(f.max_exponent(), f.exponent_bits)),
            self.eq(self.fraction(x, f), self.n(0, f.significand_bits - 1)),
        ])
    }
    pub fn is_zero(&self, x: Expr) -> Expr {
        self.eq(self.extract(x, x.width - 2, 0), self.n(0, x.width - 1))
    }
    pub fn is_subnormal(&self, x: Expr, f: FpFormat) -> Expr {
        self.and(&[
            self.eq(self.exp(x, f), self.n(0, f.exponent_bits)),
            self.nonzero(self.fraction(x, f)),
        ])
    }
    pub fn is_normal(&self, x: Expr, f: FpFormat) -> Expr {
        self.and(&[
            self.nonzero(self.exp(x, f)),
            self.not(self.eq(self.exp(x, f), self.n(f.max_exponent(), f.exponent_bits))),
        ])
    }
    pub fn datum_eq(&self, x: Expr, y: Expr, f: FpFormat) -> Expr {
        self.or(&[
            self.eq(x, y),
            self.and(&[self.is_nan(x, f), self.is_nan(y, f)]),
        ])
    }
    pub fn ieee_eq(&self, x: Expr, y: Expr, f: FpFormat) -> Expr {
        self.and(&[
            self.not(self.is_nan(x, f)),
            self.not(self.is_nan(y, f)),
            self.or(&[self.eq(x, y), self.and(&[self.is_zero(x), self.is_zero(y)])]),
        ])
    }
    pub fn lt(&self, x: Expr, y: Expr, f: FpFormat) -> Expr {
        let sx = self.sign(x);
        let sy = self.sign(y);
        let mx = self.extract(x, x.width - 2, 0);
        let my = self.extract(y, y.width - 2, 0);
        let order = self.ite(
            self.eq(sx, sy),
            self.ite(self.nonzero(sx), self.ult(my, mx), self.ult(mx, my)),
            self.nonzero(sx),
        );
        self.and(&[
            self.not(self.is_nan(x, f)),
            self.not(self.is_nan(y, f)),
            self.not(self.and(&[self.is_zero(x), self.is_zero(y)])),
            order,
        ])
    }
    pub fn constant(&self, v: FpValue) -> Expr {
        let f = v.format;
        let raw = (BigInt::from(v.sign as u8) << (f.width() - 1))
            | (BigInt::from(v.exponent) << (f.significand_bits - 1))
            | BigInt::from(v.significand);
        self.n(raw, f.width())
    }
    fn pack(&self, sign: Expr, exp: Expr, fraction: Expr) -> Expr {
        self.cat(sign, self.cat(exp, fraction))
    }
    fn zero(&self, sign: Expr, f: FpFormat) -> Expr {
        self.cat(sign, self.n(0, f.width() - 1))
    }
    fn inf(&self, sign: Expr, f: FpFormat) -> Expr {
        self.pack(
            sign,
            self.n(f.max_exponent(), f.exponent_bits),
            self.n(0, f.significand_bits - 1),
        )
    }
    pub fn fp_neg(&self, x: Expr) -> Expr {
        self.xor(x, self.n(BigInt::from(1) << (x.width - 1), x.width))
    }
    pub fn fp_abs(&self, x: Expr) -> Expr {
        self.cat(self.n(0, 1), self.extract(x, x.width - 2, 0))
    }
    fn unpack(&self, x: Expr, f: FpFormat, normalize: bool) -> (Expr, Expr) {
        let ew = Self::ew(f);
        let p = f.significand_bits;
        let normal = self.nonzero(self.exp(x, f));
        let sig = self.cat(self.bool_bits(normal, 1), self.fraction(x, f));
        let exp = self.sub(
            self.zext(
                self.ite(normal, self.exp(x, f), self.n(1, f.exponent_bits)),
                ew,
            ),
            self.n(f.bias(), ew),
        );
        if normalize {
            let lz = self.leading_zeros(sig, ew);
            (self.shl(sig, lz), self.sub(exp, lz))
        } else {
            debug_assert_eq!(sig.width, p);
            (sig, exp)
        }
    }
    /// Input significand has p+4 bits: carry, p significant bits, G/R/S.
    fn round(&self, sign: Expr, sig: Expr, exp: Expr, f: FpFormat, rm: RoundingMode) -> Expr {
        let p = f.significand_bits;
        let ew = exp.width;
        let emin = self.n(1 - f.bias(), ew);
        let emax = self.n(f.bias(), ew);
        let lz = self.leading_zeros(sig, ew);
        let beta = self.sub(self.add(exp, self.n(1, ew)), lz);
        let tiny = self.slt(beta, emin);
        let sigma = self.ite(tiny, self.add(self.sub(exp, emin), self.n(1, ew)), lz);
        let negative = self.slt(sigma, self.n(0, ew));
        let big = self.cat(sig, self.n(0, sig.width));
        let distance = self.neg(sigma);
        let cap = self.n(sig.width + 2, ew);
        let distance = self.ite(self.ult(distance, cap), distance, cap);
        let shifted = self.ite(negative, self.shr(big, distance), self.shl(big, sigma));
        let low = shifted.width - (p + 2);
        let sticky = self.nonzero(self.extract(shifted, low - 1, 0));
        let sig = self.bor(
            self.extract(shifted, shifted.width - 1, low),
            self.bool_bits(sticky, p + 2),
        );
        let guard = self.bit(sig, 1);
        let sticky = self.bit(sig, 0);
        let last = self.bit(sig, 2);
        let discarded = self.or(&[guard, sticky]);
        let inc = match rm {
            RoundingMode::RNE => self.and(&[guard, self.or(&[last, sticky])]),
            RoundingMode::RNA => guard,
            RoundingMode::RTP => self.and(&[self.not(self.nonzero(sign)), discarded]),
            RoundingMode::RTN => self.and(&[self.nonzero(sign), discarded]),
            RoundingMode::RTZ => self.boolean(false),
        };
        let sig = self.add(
            self.zext(self.extract(sig, p + 1, 2), p + 1),
            self.bool_bits(inc, p + 1),
        );
        let carry = self.bit(sig, p);
        let sig = self.ite(carry, self.extract(sig, p, 1), self.extract(sig, p - 1, 0));
        let exp = self.add(self.ite(tiny, emin, beta), self.bool_bits(carry, ew));
        let overflow = self.slt(emax, exp);
        let biased = self.add(exp, self.n(f.bias(), ew));
        let normal = self.bit(sig, p - 1);
        let packed = self.pack(
            sign,
            self.ite(
                normal,
                self.zext(biased, f.exponent_bits),
                self.n(0, f.exponent_bits),
            ),
            self.extract(sig, p - 2, 0),
        );
        let to_inf = match rm {
            RoundingMode::RNE | RoundingMode::RNA => self.boolean(true),
            RoundingMode::RTZ => self.boolean(false),
            RoundingMode::RTP => self.not(self.nonzero(sign)),
            RoundingMode::RTN => self.nonzero(sign),
        };
        let max = self.pack(
            sign,
            self.n(f.max_exponent() - 1, f.exponent_bits),
            self.n((BigInt::from(1) << (p - 1)) - 1, p - 1),
        );
        self.ite(overflow, self.ite(to_inf, self.inf(sign, f), max), packed)
    }
    pub fn fp_add(&self, x: Expr, y: Expr, f: FpFormat, rm: RoundingMode) -> Expr {
        let p = f.significand_bits;
        let ew = Self::ew(f);
        let (ax, ex) = self.unpack(x, f, false);
        let (ay, ey) = self.unpack(y, f, false);
        let swap = self.slt(ex, ey);
        let a = self.ite(swap, ay, ax);
        let b = self.ite(swap, ax, ay);
        let ea = self.ite(swap, ey, ex);
        let eb = self.ite(swap, ex, ey);
        let sa = self.ite(swap, self.sign(y), self.sign(x));
        let sb = self.ite(swap, self.sign(x), self.sign(y));
        let a = self.zext(self.cat(a, self.n(0, 3)), p + 5);
        let b = self.zext(self.jam(self.cat(b, self.n(0, 3)), self.sub(ea, eb)), p + 5);
        let sum = self.ite(self.eq(sa, sb), self.add(a, b), self.sub(a, b));
        let negative = self.bit(sum, p + 4);
        let sign = self.xor(sa, self.bool_bits(negative, 1));
        let sig = self.extract(self.ite(negative, self.neg(sum), sum), p + 3, 0);
        let zero_sign = self.n(u8::from(rm == RoundingMode::RTN), 1);
        let rounded = self.ite(
            self.nonzero(sig),
            self.round(sign, sig, ea, f, rm),
            self.zero(zero_sign, f),
        );
        let both_zero = self.and(&[self.is_zero(x), self.is_zero(y)]);
        let zero_sign = self.ite(self.eq(self.sign(x), self.sign(y)), self.sign(x), zero_sign);
        let result = self.ite(self.is_zero(y), x, rounded);
        let result = self.ite(self.is_zero(x), y, result);
        let result = self.ite(both_zero, self.zero(zero_sign, f), result);
        let result = self.ite(self.is_inf(y, f), y, result);
        let result = self.ite(self.is_inf(x, f), x, result);
        let invalid = self.and(&[
            self.is_inf(x, f),
            self.is_inf(y, f),
            self.not(self.eq(self.sign(x), self.sign(y))),
        ]);
        debug_assert_eq!(ea.width, ew);
        self.ite(
            self.or(&[self.is_nan(x, f), self.is_nan(y, f), invalid]),
            self.constant(FpValue::nan(f)),
            result,
        )
    }
    pub fn fp_mul(&self, x: Expr, y: Expr, f: FpFormat, rm: RoundingMode) -> Expr {
        let p = f.significand_bits;
        let (sx, ex) = self.unpack(x, f, true);
        let (sy, ey) = self.unpack(y, f, true);
        let product = self.mul(self.zext(sx, 2 * p), self.zext(sy, 2 * p));
        let sig = if p >= 4 {
            self.zext(self.jam(product, self.n(p - 4, 2 * p)), p + 4)
        } else {
            self.cat(product, self.n(0, 4 - p))
        };
        let sign = self.xor(self.sign(x), self.sign(y));
        let rounded = self.round(sign, sig, self.add(ex, ey), f, rm);
        let zero = self.or(&[self.is_zero(x), self.is_zero(y)]);
        let inf = self.or(&[self.is_inf(x, f), self.is_inf(y, f)]);
        let invalid = self.or(&[self.is_nan(x, f), self.is_nan(y, f), self.and(&[zero, inf])]);
        let result = self.ite(zero, self.zero(sign, f), rounded);
        let result = self.ite(inf, self.inf(sign, f), result);
        self.ite(invalid, self.constant(FpValue::nan(f)), result)
    }
}
