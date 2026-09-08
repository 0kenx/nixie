use super::{Printer, pretty::PrettyPrinter};
use crate::ast::TermManager;
use num_bigint::BigInt;

#[test]
fn fp_fields_print_binary_digits_at_the_declared_width() {
    let mut m = TermManager::new();
    let small = m.mk_fp_lit(false, BigInt::from(3), BigInt::from(4), 3, 4);
    assert_eq!(Printer::new(&m).print_term(small), "(fp #b0 #b011 #b100)");
    assert_eq!(
        PrettyPrinter::new(&m).print_term(small),
        "(fp #b0 #b011 #b100)"
    );
    let wide = m.mk_fp_lit(true, BigInt::from(1), (BigInt::from(1) << 100) + 1, 15, 113);
    let expected = format!(
        "(fp #b1 #b{:015b} #b{:0112b})",
        1,
        (BigInt::from(1) << 100) + 1
    );
    assert_eq!(Printer::new(&m).print_term(wide), expected);
    assert_eq!(PrettyPrinter::new(&m).print_term(wide), expected);
}
