use nixie_core::{
    SortKind, TermManager,
    ast::{sequence::SeqOp, traversal::get_children},
};
use rustc_hash::FxHashMap;

#[test]
fn sort_interning_substitution_and_printing() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let boolean = tm.sorts.bool_sort;
    let seq = tm.sorts.seq(int);
    assert_eq!(seq, tm.sorts.seq(int));
    assert_ne!(seq, tm.sorts.seq(boolean));
    let nested = tm.sorts.seq(seq);
    let replaced = tm
        .sorts
        .substitute_sort(nested, &FxHashMap::from_iter([(int, boolean)]));
    let inner = tm.sorts.seq(boolean);
    let expected = tm.sorts.seq(inner);
    assert_eq!(replaced, expected);
    assert_eq!(tm.sorts.get(seq).expect("sort").kind, SortKind::Seq(int));
    let x = tm.mk_var("x", int);
    let y = tm.mk_int(7);
    let a = tm.mk_sequence(SeqOp::Unit, &[x]).expect("unit");
    assert_eq!(
        get_children(&tm.get(a).expect("term").kind).as_slice(),
        &[x]
    );
    let b = tm.substitute(a, &FxHashMap::from_iter([(x, y)]));
    let expected = tm.mk_sequence(SeqOp::Unit, &[y]).expect("unit");
    assert_eq!(b, expected);
    assert_eq!(
        nixie_core::smtlib::Printer::new(&tm).print_term(b),
        "(seq.unit 7)"
    );
    let empty = tm.mk_sequence(SeqOp::Empty(nested), &[]).expect("empty");
    assert_eq!(
        nixie_core::smtlib::Printer::new(&tm).print_term(empty),
        "(as seq.empty (Seq (Seq Int)))"
    );
}

#[test]
fn checked_constructor_rejects_invalid_signatures() {
    let mut tm = TermManager::new();
    let one = tm.mk_int(1);
    let t = tm.mk_true();
    let s = tm.mk_sequence(SeqOp::Unit, &[one]).expect("unit");
    for (op, args) in [
        (SeqOp::Len, vec![one]),
        (SeqOp::Nth, vec![s, t]),
        (SeqOp::Update, vec![s, one, one]),
        (SeqOp::Concat, vec![]),
        (SeqOp::Empty(tm.sorts.int_sort), vec![]),
    ] {
        assert!(tm.mk_sequence(op, &args).is_err());
    }
}
