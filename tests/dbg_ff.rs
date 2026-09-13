fn main() {}
#[cfg(test)]
mod dbg {
    use nixie_math::ff::*;
    use num_bigint::BigUint;
    #[test]
    fn dbg_sub() {
        let f = FieldCtx::new(BigUint::from(97u32)).unwrap();
        let a = UniPoly::from_coeffs(vec![f.from_biguint(&1u32.into()), f.from_biguint(&2u32.into()), f.from_biguint(&3u32.into())]);
        let b = UniPoly::from_coeffs(vec![f.from_biguint(&5u32.into()), f.from_biguint(&7u32.into())]);
        let sum = a.add(&f, &b);
        println!("a={:?}", a.coeffs());
        println!("b={:?}", b.coeffs());
        println!("sum={:?}", sum.coeffs());
        let negb = b.neg(&f);
        println!("neg(b)={:?}", negb.coeffs());
        let d = a.sub(&f, &sum);
        println!("a-sum={:?}", d.coeffs());
        // raw mont values:
        println!("mont1={:?}", f.to_biguint(&f.from_biguint(&1u32.into())));
    }
}
