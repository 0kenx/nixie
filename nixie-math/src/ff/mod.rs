//! The `QF_FF` math layer (`docs/FF_THEORY_DESIGN.md` §4).
//!
//! This is the computer-algebra core the finite-field theory is built on —
//! in Nixie's case that is the larger half of the theory:
//!
//! * [`field`]: 𝔽_p elements in Montgomery form over 64-bit limbs;
//! * [`uni_poly`]: dense univariate polynomials over 𝔽_p with `divrem`,
//!   `gcd`, modular exponentiation and squarefree parts;
//! * [`roots`]: Rabin / Cantor–Zassenhaus root finding with a
//!   **deterministic** shift sequence (`a = 0, 1, 2, …` — never random);
//! * [`poly`]: sparse multivariate polynomials over 𝔽_p;
//! * [`grobner`]: Buchberger with Gebauer–Möller criteria over 𝔽_p, a
//!   cofactor tracer, the dimension test and minimal polynomials.
//!
//! The module is deliberately independent of the existing `BigRational`
//! polynomial machinery; see `field`'s module doc for why that duplication
//! is the cheaper trade.

pub mod field;
pub mod grobner;
pub mod poly;
pub mod roots;
pub mod uni_poly;

pub use field::{FieldCtx, FieldCtxError, Limbs};
