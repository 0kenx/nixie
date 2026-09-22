//! Independent tiny-field oracles. Polynomial arithmetic here uses coefficient
//! arrays; the production representation uses arbitrary-width packed bits.
use nixie_core::ast::{TermKind, TermManager};
use nixie_core::smtlib::{Command, Printer, parse_script};
use nixie_core::sort::binary_field::BinaryField;
use nixie_core::sort::field::FieldTable;
use num_bigint::BigUint;
use num_traits::One;

fn divide(mut a: u32, b: u32) -> u32 {
    while a != 0 && a.ilog2() >= b.ilog2() {
        a ^= b << (a.ilog2() - b.ilog2());
    }
    a
}

fn multiply(a: u32, b: u32, f: u32) -> u32 {
    let degree = f.ilog2() as usize;
    let mut coefficients = [false; 32];
    for i in 0..degree {
        for j in 0..degree {
            coefficients[i + j] ^= (a >> i & 1 != 0) && (b >> j & 1 != 0);
        }
    }
    for i in (degree..2 * degree).rev() {
        if coefficients[i] {
            for j in 0..=degree {
                coefficients[i - degree + j] ^= f >> j & 1 != 0;
            }
        }
    }
    coefficients
        .iter()
        .take(degree)
        .enumerate()
        .fold(0, |a, (i, &c)| a | (u32::from(c) << i))
}

#[test]
fn irreducibility_matches_trial_division_through_degree_eight() {
    for f in 4u32..512 {
        let degree = f.ilog2();
        let irreducible = (2..(1 << (degree / 2 + 1))).all(|d| divide(f, d) != 0);
        assert_eq!(BinaryField::new(f.into()).is_ok(), irreducible, "f={f}");
    }
    for f in 0u32..4 {
        assert!(BinaryField::new(f.into()).is_err());
    }
    assert!(BinaryField::new(BigUint::one() << 257u32).is_err());
}

#[test]
fn exhaustive_tiny_arithmetic_and_inversion() {
    for polynomial in [7u32, 11, 13, 19, 25, 31] {
        let f = BinaryField::new(polynomial.into()).unwrap();
        let q = 1u32 << f.degree();
        for a in 0..q {
            let aa = BigUint::from(a);
            assert_eq!(f.pow(&aa, &q.into()), Some(aa.clone()));
            if a == 0 {
                assert!(f.inverse(&aa).is_none());
            } else {
                let inv = f.inverse(&aa).unwrap();
                let expected = (1..q).find(|&b| multiply(a, b, polynomial) == 1).unwrap();
                assert_eq!(inv, expected.into());
            }
            for b in 0..q {
                assert_eq!(f.add(&aa, &b.into()), Some((a ^ b).into()));
                assert_eq!(
                    f.mul(&aa, &b.into()),
                    Some(multiply(a, b, polynomial).into())
                );
                for c in 0..q {
                    assert_eq!(
                        multiply(a, b ^ c, polynomial),
                        multiply(a, b, polynomial) ^ multiply(a, c, polynomial)
                    );
                }
            }
        }
        assert!(f.mul(&q.into(), &1u8.into()).is_none());
        assert!(f.inverse(&q.into()).is_none());
    }
}

#[test]
fn wide_arithmetic_aes_and_representation_identity() {
    let aes = BinaryField::new(283u32.into()).unwrap();
    assert_eq!(
        aes.mul(&0x57u32.into(), &0x83u32.into()),
        Some(0xc1u32.into())
    );
    let f = BinaryField::new((BigUint::one() << 128u32) | BigUint::from(135u32)).unwrap();
    let high = BigUint::one() << 127u32;
    assert_eq!(f.mul(&high, &2u8.into()), Some(135u32.into()));
    let a = &high | BigUint::from(43u8);
    assert_eq!(f.mul(&a, &f.inverse(&a).unwrap()), Some(BigUint::one()));
    let mut table = FieldTable::new();
    let a = table.intern_binary(11u8.into()).unwrap();
    assert_eq!(a, table.intern_binary(11u8.into()).unwrap());
    assert_ne!(a, table.intern_binary(13u8.into()).unwrap());
    assert!(
        table.modulus(a).is_none(),
        "never expose q as a prime modulus"
    );
    assert!(table.intern_prime(8u8.into()).is_err());
}

#[test]
fn syntax_printing_round_trips_and_rejects_bad_values() {
    let mut m = TermManager::new();
    let script = "(declare-const x (_ BinaryField 11)) (assert (= x (as ff6 (_ BinaryField 11))))";
    let cmds = parse_script(script, &mut m).unwrap();
    assert!(matches!(&cmds[0],Command::DeclareConst(_,s) if s=="(_ BinaryField 11)"));
    let Command::Assert(t) = cmds[1] else {
        panic!()
    };
    let rendered = Printer::new(&m).print_term(t);
    let round = parse_script(
        &format!("(declare-const x (_ BinaryField 11)) (assert {rendered})"),
        &mut m,
    )
    .unwrap();
    assert!(matches!(round[1],Command::Assert(r) if r==t));
    for value in [-1, 8, 11] {
        assert!(
            parse_script(
                &format!("(declare-const x (_ BinaryField 11)) (assert (= x (as ff{value} (_ BinaryField 11))))"),
                &mut m
            )
            .is_err()
        );
    }
    assert!(parse_script("(declare-const bad (_ BinaryField 21))", &mut m).is_err());
    assert!(
        parse_script(
            "(assert (= (as ff2 (_ BinaryField 11)) (as ff2 (_ BinaryField 13))))",
            &mut m
        )
        .is_err()
    );
    let sort = m.sorts.binary_field(11u8.into()).unwrap();
    let field = m.sorts.get(sort).unwrap().finite_field().unwrap();
    let x = m.mk_var("symbolic", sort);
    let neg = m.mk_ff_neg(x).unwrap();
    assert_eq!(neg, x);
    assert_eq!(m.mk_ff_bitsum([x, x]).unwrap(), x);
    let two = m.mk_ff_const(field, 2.into()).unwrap();
    let sum = m.mk_ff_add([two, two]).unwrap();
    assert!(matches!(&m.get(sum).unwrap().kind,TermKind::FfConst{value,..} if value==&0.into()));
}

#[test]
fn singleton_product_does_not_erase_field_identity() {
    let mut m = TermManager::new();
    let a = m.sorts.binary_field(11u8.into()).unwrap();
    let b = m.sorts.binary_field(13u8.into()).unwrap();
    let field = m.sorts.get(a).unwrap().finite_field().unwrap();
    let x = m.mk_var("x", b);
    assert!(m.mk_ff_mul_fields(field, [x]).is_err());
}
