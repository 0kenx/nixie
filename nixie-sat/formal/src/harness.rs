//! Harness obligations migrated from upstream 0.3.4. See ../README.md.

#[cfg(any(formal, oxiformal_runtime_checks))]
use oxiformal::prelude::*;

#[cfg_attr(
    not(any(formal, all(test, oxiformal_runtime_checks))),
    allow(unused_imports)
)]
use nixie_sat::{LBool, Lit, Var};

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
fn lit_pos_roundtrip_bounded_harness() {
    let index: u32 = any();
    assume(index <= Var::MAX_INDEX);
    let var = Var::new(index);
    let lit = Lit::pos(var);
    assert(lit.var().0 == index);
    assert(lit.is_pos());
    assert(!lit.is_neg());
    assert(lit.sign());
    assert(lit.code() == index << 1);
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
fn lit_neg_roundtrip_bounded_harness() {
    let index: u32 = any();
    assume(index <= Var::MAX_INDEX);
    let var = Var::new(index);
    let lit = Lit::neg(var);
    assert(lit.var().0 == index);
    assert(lit.is_neg());
    assert(!lit.sign());
    assert(lit.negate().code() == Lit::pos(var).code());
    assert(lit.code() == ((index << 1) | 1));
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
#[should_panic]
fn lit_pos_roundtrip_unbounded_harness() {
    let index: u32 = any();
    let var = Var(index);
    let lit = Lit::pos(var);
    assert(lit.var().0 == index);
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
fn lit_negate_involution_harness() {
    let code: u32 = any();
    let lit = Lit::from_code(code);
    let flipped = lit.negate();
    assert(flipped.negate().code() == lit.code());
    assert(flipped.var().0 == lit.var().0);
    assert(flipped.is_pos() != lit.is_pos());
    assert(flipped.is_neg() == lit.is_pos());
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
fn lit_code_roundtrip_harness() {
    let code: u32 = any();
    let lit = Lit::from_code(code);
    assert(lit.code() == code);
    assert(lit.index() == code as usize);
    assert(lit.var().0 == (code >> 1));
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
fn dimacs_roundtrip_harness() {
    let dimacs: i32 = any();
    assume(dimacs != 0);
    assume(dimacs != i32::MIN);
    let lit = Lit::from_dimacs(dimacs);
    assert(lit.to_dimacs() == dimacs);
    assert(lit.is_pos() == (dimacs > 0));
    assert(lit.var().0 == (dimacs.unsigned_abs() - 1));
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
fn dimacs_negation_harness() {
    let dimacs: i32 = any();
    assume(dimacs != 0);
    let lit = Lit::from_dimacs(dimacs);
    let _ = lit.to_dimacs();
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
fn try_to_dimacs_is_total_harness() {
    let code: u32 = any();
    let lit = Lit::from_code(code);
    match lit.try_to_dimacs() {
        Some(dimacs) => {
            assert(lit.var().0 <= Var::MAX_INDEX);
            assert(dimacs != 0);
            assert(dimacs != i32::MIN);
            assert(Lit::from_dimacs(dimacs).code() == lit.code());
        }
        None => {
            assert(lit.var().0 > Var::MAX_INDEX);
        }
    }
}

#[cfg(any(formal, all(test, oxiformal_runtime_checks)))]
#[harness]
fn lbool_negate_involution_harness() {
    let raw: bool = any();
    let value = LBool::from_bool(raw);
    assert(value.is_defined());
    assert(value.is_true() == raw);
    assert(value.is_false() != raw);
    assert(!LBool::Undef.is_defined());
    assert(!LBool::Undef.negate().is_defined());
    assert(value.negate().is_true() == value.is_false());
    assert(value.negate().is_false() == value.is_true());
    assert(value.negate().negate().is_true() == value.is_true());
}

#[cfg(all(test, not(oxiformal_runtime_checks), not(formal)))]
mod plain_tests {
    use super::*;

    #[test]
    fn the_packing_round_trips_at_both_ends_of_the_index_range() {
        for index in [0u32, 1, 12345, Var::MAX_INDEX] {
            let var = Var::new(index);
            let pos = Lit::pos(var);
            let neg = Lit::neg(var);
            assert_eq!(pos.var().0, index);
            assert_eq!(neg.var().0, index);
            assert_eq!(pos.code(), index << 1);
            assert_eq!(neg.code(), (index << 1) | 1);
            assert!(pos.is_pos() && !pos.is_neg() && pos.sign());
            assert!(neg.is_neg() && !neg.sign());
            assert_eq!(pos.negate().code(), neg.code());
        }
    }

    #[test]
    #[should_panic(expected = "variable index exceeds Var::MAX_INDEX")]
    fn lit_pos_rejects_the_reported_index_counterexample() {
        let _ = Lit::pos(Var(u32::MAX));
    }

    #[test]
    #[should_panic(expected = "variable index exceeds Var::MAX_INDEX")]
    fn lit_pos_rejects_one_index_past_the_bound() {
        let _ = Lit::pos(Var(Var::MAX_INDEX + 1));
    }

    #[test]
    #[should_panic(expected = "variable index exceeds Var::MAX_INDEX")]
    fn lit_pos_rejects_two_to_the_thirty_first() {
        let _ = Lit::pos(Var(1 << 31));
    }

    #[test]
    #[should_panic(expected = "invalid DIMACS literal")]
    fn from_dimacs_rejects_the_reported_dimacs_counterexample() {
        let _ = Lit::from_dimacs(i32::MIN);
    }

    #[test]
    #[should_panic(expected = "Lit::to_dimacs")]
    fn to_dimacs_panics_for_a_literal_above_the_bound() {
        let _ = Lit::from_code((Var::MAX_INDEX + 1) << 1).to_dimacs();
    }

    #[test]
    fn try_to_dimacs_is_none_exactly_above_the_bound() {
        let last_good = Lit::pos(Var::new(Var::MAX_INDEX));
        assert_eq!(last_good.try_to_dimacs(), Some(i32::MAX));
        assert_eq!(
            Lit::neg(Var::new(Var::MAX_INDEX)).try_to_dimacs(),
            Some(-i32::MAX)
        );

        let above = (Var::MAX_INDEX + 1) << 1;
        assert_eq!(Lit::from_code(above).var().0, Var::MAX_INDEX + 1);
        assert_eq!(Lit::from_code(above).try_to_dimacs(), None);
        assert_eq!(Lit::from_code(above | 1).try_to_dimacs(), None);
    }

    #[test]
    fn dimacs_round_trips_for_the_representable_extremes() {
        for dimacs in [1, -1, 2, -2, 12345, -12345, i32::MAX, -i32::MAX] {
            let lit = Lit::from_dimacs(dimacs);
            assert_eq!(lit.to_dimacs(), dimacs);
            assert_eq!(lit.try_to_dimacs(), Some(dimacs));
            assert_eq!(lit.is_pos(), dimacs > 0);
            assert_eq!(lit.var().0, dimacs.unsigned_abs() - 1);
        }
    }

    #[test]
    fn the_raw_code_representation_is_exact() {
        for code in [
            0u32,
            1,
            2,
            3,
            0x7fff_ffff,
            0x8000_0000,
            u32::MAX - 1,
            u32::MAX,
        ] {
            let lit = Lit::from_code(code);
            assert_eq!(lit.code(), code);
            assert_eq!(lit.index(), code as usize);
            assert_eq!(lit.var().0, code >> 1);
            let flipped = lit.negate();
            assert_eq!(flipped.negate().code(), code);
            assert_eq!(flipped.var().0, lit.var().0);
            assert_ne!(flipped.is_pos(), lit.is_pos());
        }
    }

    #[test]
    fn lbool_negation_is_an_involution_on_all_three_values() {
        for raw in [true, false] {
            let value = LBool::from_bool(raw);
            assert!(value.is_defined());
            assert_eq!(value.is_true(), raw);
            assert_ne!(value.is_false(), raw);
            assert_eq!(value.negate().is_true(), value.is_false());
            assert_eq!(value.negate().is_false(), value.is_true());
            assert_eq!(value.negate().negate().is_true(), value.is_true());
        }
        assert!(!LBool::Undef.is_defined());
        assert!(!LBool::Undef.negate().is_defined());
    }
}
