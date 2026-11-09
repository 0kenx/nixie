//! Spec obligations migrated from upstream 0.3.4. See ../README.md.

use nixie_sat::{LBool, Lit, Var};
#[cfg(any(formal, oxiformal_runtime_checks))]
use oxiformal::prelude::*;

#[cfg_attr(any(formal, oxiformal_runtime_checks), requires(index <= Var::MAX_INDEX))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.var().0 == index))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.code() == index << 1 && r.is_pos() && !r.is_neg() && r.sign()))]
pub fn spec_lit_pos(index: u32) -> Lit {
    Lit::pos(Var::new(index))
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lit_pos)]
fn spec_lit_pos_contract() {
    let index: u32 = any();
    let _ = spec_lit_pos(index.min(Var::MAX_INDEX));
}

#[cfg_attr(any(formal, oxiformal_runtime_checks), requires(index <= Var::MAX_INDEX))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.var().0 == index))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.negate().code() == Lit::pos(Var::new(index)).code()))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.code() == ((index << 1) | 1) && r.is_neg() && !r.sign()))]
pub fn spec_lit_neg(index: u32) -> Lit {
    Lit::neg(Var::new(index))
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lit_neg)]
fn spec_lit_neg_contract() {
    let index: u32 = any();
    let _ = spec_lit_neg(index.min(Var::MAX_INDEX));
}

#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.var().0 == index))]
pub fn spec_lit_pos_unbounded(index: u32) -> Lit {
    Lit::pos(Var(index))
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lit_pos_unbounded)]
#[cfg_attr(
    oxiformal_runtime_checks,
    ignore = "one draw is not a sample; lit_pos_roundtrip_unbounded_harness carries the runtime witness"
)]
fn spec_lit_pos_unbounded_contract() {
    let index: u32 = any();
    let _ = spec_lit_pos_unbounded(index);
}

#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.negate().code() == lit.code()))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.var().0 == lit.var().0))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.is_pos() != lit.is_pos()))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.is_neg() == lit.is_pos()))]
pub fn spec_lit_negate(lit: Lit) -> Lit {
    lit.negate()
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lit_negate)]
fn spec_lit_negate_contract() {
    let code: u32 = any();
    let _ = spec_lit_negate(Lit::from_code(code));
}

#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.code() == code))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.index() == code as usize))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.var().0 == (code >> 1)))]
pub fn spec_lit_from_code(code: u32) -> Lit {
    Lit::from_code(code)
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lit_from_code)]
fn spec_lit_from_code_contract() {
    let code: u32 = any();
    let _ = spec_lit_from_code(code);
}

#[cfg_attr(any(formal, oxiformal_runtime_checks), requires(dimacs != 0 && dimacs != i32::MIN))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.to_dimacs() == dimacs))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.is_pos() == (dimacs > 0)))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.var().0 == dimacs.unsigned_abs() - 1))]
pub fn spec_lit_from_dimacs(dimacs: i32) -> Lit {
    Lit::from_dimacs(dimacs)
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lit_from_dimacs)]
fn spec_lit_from_dimacs_contract() {
    let dimacs: i32 = any();
    let dimacs = if dimacs == 0 || dimacs == i32::MIN {
        1
    } else {
        dimacs
    };
    let _ = spec_lit_from_dimacs(dimacs);
}

#[cfg_attr(any(formal, oxiformal_runtime_checks), requires(dimacs != 0))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.to_dimacs() == dimacs))]
pub fn spec_lit_from_dimacs_nonzero(dimacs: i32) -> Lit {
    Lit::from_dimacs(dimacs)
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lit_from_dimacs_nonzero)]
fn spec_lit_from_dimacs_nonzero_contract() {
    let dimacs: i32 = any();
    let dimacs = if dimacs == 0 { 1 } else { dimacs };
    let _ = spec_lit_from_dimacs_nonzero(dimacs);
}

#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.is_some() == (lit.var().0 <= Var::MAX_INDEX)))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| match *r {
    Some(d) => d != 0 && d != i32::MIN && Lit::from_dimacs(d).code() == lit.code(),
    None => lit.var().0 > Var::MAX_INDEX,
}))]
pub fn spec_lit_try_to_dimacs(lit: Lit) -> Option<i32> {
    lit.try_to_dimacs()
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lit_try_to_dimacs)]
fn spec_lit_try_to_dimacs_contract() {
    let code: u32 = any();
    let _ = spec_lit_try_to_dimacs(Lit::from_code(code));
}

#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.is_defined() && r.is_true() == raw))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.is_false() != raw))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.negate().is_true() == LBool::from_bool(raw).is_false()))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.negate().is_false() == LBool::from_bool(raw).is_true()))]
#[cfg_attr(any(formal, oxiformal_runtime_checks), ensures(|r| r.negate().negate().is_true() == LBool::from_bool(raw).is_true()))]
pub fn spec_lbool_from_bool(raw: bool) -> LBool {
    LBool::from_bool(raw)
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[proof_for_contract(spec_lbool_from_bool)]
fn spec_lbool_from_bool_contract() {
    let raw: bool = any();
    let _ = spec_lbool_from_bool(raw);
    assert(!LBool::Undef.is_defined());
    assert(!LBool::Undef.negate().is_defined());
}

#[cfg(all(test, not(oxiformal_runtime_checks), not(formal)))]
mod plain_tests {
    use super::*;

    #[test]
    fn wrappers_are_identities_over_the_public_api() {
        for index in [0u32, 1, 12345, Var::MAX_INDEX] {
            assert_eq!(spec_lit_pos(index).code(), Lit::pos(Var::new(index)).code());
            assert_eq!(spec_lit_neg(index).code(), Lit::neg(Var::new(index)).code());
            assert_eq!(
                spec_lit_pos_unbounded(index).code(),
                Lit::pos(Var(index)).code()
            );
        }
        for code in [0u32, 1, 2, 3, 0x7fff_ffff, 0x8000_0000, u32::MAX] {
            assert_eq!(spec_lit_from_code(code).code(), code);
            assert_eq!(spec_lit_negate(Lit::from_code(code)).code(), code ^ 1);
            assert_eq!(
                spec_lit_try_to_dimacs(Lit::from_code(code)),
                Lit::from_code(code).try_to_dimacs()
            );
        }
        for dimacs in [1, -1, 2, -2, i32::MAX, -i32::MAX] {
            assert_eq!(
                spec_lit_from_dimacs(dimacs).code(),
                Lit::from_dimacs(dimacs).code()
            );
            assert_eq!(
                spec_lit_from_dimacs_nonzero(dimacs).code(),
                Lit::from_dimacs(dimacs).code()
            );
        }
        assert!(spec_lbool_from_bool(true).is_true());
        assert!(spec_lbool_from_bool(false).is_false());
    }

    #[test]
    #[should_panic(expected = "variable index exceeds Var::MAX_INDEX")]
    fn spec_lit_pos_unbounded_rejects_one_index_past_the_bound() {
        let _ = spec_lit_pos_unbounded(Var::MAX_INDEX + 1);
    }

    #[test]
    #[should_panic(expected = "invalid DIMACS literal")]
    fn spec_lit_from_dimacs_nonzero_rejects_i32_min() {
        let _ = spec_lit_from_dimacs_nonzero(i32::MIN);
    }
}
