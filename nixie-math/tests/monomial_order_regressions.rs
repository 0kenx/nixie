//! Monomial-order regressions: `grevlex_cmp` must be a term order.
//!
//! The first version ordered by variable index when the two monomials'
//! top variables differ — not grevlex, and not a well-order — which
//! broke the termination argument of Gröbner reduction: any system whose
//! monomials' top variables differ (six-plus random quadratics) looped
//! until budget death. These tests pin the comparator against a
//! dense-vector reference and the multiplicative-compatibility axiom.
use nixie_math::polynomial::{Monomial, MonomialOrder};
use std::cmp::Ordering;

/// Correct dense-vector grevlex reference.
fn ref_grevlex(a: &[(u32, u32)], b: &[(u32, u32)], nvars: u32) -> Ordering {
    let deg: u32 = a.iter().map(|(_, p)| p).sum();
    let deg_b: u32 = b.iter().map(|(_, p)| p).sum();
    match deg.cmp(&deg_b) {
        Ordering::Equal => {}
        o => return o,
    }
    let exp = |m: &[(u32, u32)], v: u32| m.iter().find(|(vv, _)| *vv == v).map_or(0, |(_, p)| *p);
    for v in (0..nvars).rev() {
        let (ea, eb) = (exp(a, v), exp(b, v));
        if ea != eb {
            return if ea < eb {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }
    }
    Ordering::Equal
}

fn advance(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

fn mk(next: &mut u64) -> Vec<(u32, u32)> {
    let nv = 6u32;
    let mut v: Vec<(u32, u32)> = Vec::new();
    for var in 0..nv {
        if advance(next) % 3u64 == 0 {
            let power = (advance(next) % 3u64) as u32 + 1;
            v.push((var, power));
        }
    }
    if v.is_empty() {
        vec![((advance(next) % nv as u64) as u32, 1)]
    } else {
        v
    }
}

#[test]
fn grevlex_matches_reference_and_is_multiplicative() {
    let mut rng: u64 = 7;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut mismatches = 0;
    let mut mult_violations = 0;
    for _ in 0..20000 {
        let a = mk(&mut state);
        let b = mk(&mut state);
        let ma = Monomial::from_powers(a.clone());
        let mb = Monomial::from_powers(b.clone());
        let got = MonomialOrder::GRevLex.compare(&ma, &mb);
        let want = ref_grevlex(&a, &b, 6);
        if got != want {
            mismatches += 1;
            if mismatches <= 5 {
                eprintln!("MISMATCH a={a:?} b={b:?}: got {got:?} want {want:?}");
            }
        }
        let k = (advance(&mut state) % 6u64) as u32;
        let xk = Monomial::from_var(k);
        let (lak, lbk) = (ma.mul(&xk), mb.mul(&xk));
        let (o, ok) = (
            MonomialOrder::GRevLex.compare(&ma, &mb),
            MonomialOrder::GRevLex.compare(&lak, &lbk),
        );
        if o != Ordering::Equal && o != ok {
            mult_violations += 1;
            if mult_violations <= 5 {
                eprintln!("MULT-VIOLATION a={a:?} b={b:?} x{k}: {o:?} vs {ok:?}");
            }
        }
    }
    eprintln!("mismatches={mismatches} mult_violations={mult_violations} / 20000");
    assert_eq!(mismatches, 0, "comparator disagrees with grevlex");
    assert_eq!(
        mult_violations, 0,
        "comparator is not multiplicative (not a monomial order)"
    );
}

#[test]
fn grevlex_hand_cases() {
    // x5*x0 vs x3^2, both degree 2. Dense vectors:
    //   (1,0,0,0,0,1) vs (0,0,0,2,0,0); highest difference at var 5:
    //   1 vs 0 → x5x0 has the LARGER exponent at the highest differing
    //   position → x5x0 is SMALLER (Less) in grevlex.
    let a = Monomial::from_powers([(0, 1), (5, 1)]);
    let b = Monomial::from_powers([(3, 2)]);
    let got = MonomialOrder::GRevLex.compare(&a, &b);
    eprintln!("hand: x5x0 vs x3^2 = {got:?} (want Less)");
    assert_eq!(got, Ordering::Less);

    // x5 vs x4 (degree 1 each): vector (0,0,0,0,0,1) vs (0,0,0,0,1,0);
    // highest difference at var 5 → x5 larger exponent → x5 < x4.
    let c = Monomial::from_var(5);
    let d = Monomial::from_var(4);
    let got2 = MonomialOrder::GRevLex.compare(&c, &d);
    eprintln!("hand: x5 vs x4 = {got2:?} (want Less)");
    assert_eq!(got2, Ordering::Less);
}
