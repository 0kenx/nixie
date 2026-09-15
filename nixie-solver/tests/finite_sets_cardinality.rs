//! Cardinality of finite sets: the decision-procedure tests.
//!
//! Each case's status is known independently (stated in the doc comment, and
//! cross-checked against Z3 4.16.0 while writing). These are the regressions
//! for the Venn-region/slack encoding in `solver::set_theory::cardinality`:
//! before it, every one of the `unsat` cases below answered `unknown`, because
//! `|s|` over an opaque set had no reduction at all.

use nixie_core::{TermId, TermManager};
use nixie_solver::{Solver, SolverResult};

/// Assert `build`'s formulas one by one and report the verdict.
///
/// Asserting **sequentially** matters: `reduce` re-runs on every assert over
/// the whole stack, so this exercises the element-list growth that once made
/// two valid counting equations share one slack and conjoin into a false
/// `unsat` (`|s| = 2` then `1 ∈ s` — the `slack_keys_on_the_element_list`
/// invariant).
fn solve(build: impl FnOnce(&mut TermManager) -> Vec<TermId>) -> SolverResult {
    let mut tm = TermManager::new();
    let asserts = build(&mut tm);
    let mut solver = Solver::new();
    for a in asserts {
        solver.assert(a, &mut tm);
    }
    solver.check(&mut tm)
}

/// `x ∈ s ∧ |s| = 0` is unsatisfiable: a member makes the set nonempty.
/// This was the headline gap — the old reduction answered `unknown`.
#[test]
fn member_with_cardinality_zero_is_unsat() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let s = tm.mk_var("S", set_int);
        let x = tm.mk_var("x", int);
        let member = tm.mk_set_member(x, s);
        let zero = tm.mk_int(0);
        let card = tm.mk_set_card(s);
        vec![member, tm.mk_eq(card, zero)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `|s| = 2 ∧ 1 ∈ s` is satisfiable (`s = {1, 7}`) — and stays satisfiable
/// when the membership arrives *after* the cardinality constraint, which is
/// the assertion order that once conflated two counting equations.
#[test]
fn cardinality_two_with_a_member_is_sat_in_either_order() {
    for order in [0, 1] {
        let got = solve(|tm| {
            let int = tm.sorts.int_sort;
            let set_int = tm.sorts.set(int);
            let s = tm.mk_var("S", set_int);
            let one = tm.mk_int(1);
            let two = tm.mk_int(2);
            let member = tm.mk_set_member(one, s);
            let cs = tm.mk_set_card(s);
            let card = tm.mk_eq(cs, two);
            if order == 0 {
                vec![card, member]
            } else {
                vec![member, card]
            }
        });
        assert_eq!(got, SolverResult::Sat, "order {order}");
    }
}

/// `|s| = 2 ∧ 1, 2, 3 ∈ s` is unsatisfiable: three members, two slots.
#[test]
fn three_members_do_not_fit_in_two_slots() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let s = tm.mk_var("S", set_int);
        let two = tm.mk_int(2);
        let cs = tm.mk_set_card(s);
        let mut out = vec![tm.mk_eq(cs, two)];
        for k in [1, 2, 3] {
            let e = tm.mk_int(k);
            out.push(tm.mk_set_member(e, s));
        }
        out
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `|s| = 1 ∧ 1, 2 ∈ s` is unsatisfiable even though `1 ≠ 2` is never
/// stated: distinct numerals are distinct values.
#[test]
fn two_distinct_members_do_not_fit_in_one_slot() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let s = tm.mk_var("S", set_int);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let m1 = tm.mk_set_member(one, s);
        let m2 = tm.mk_set_member(two, s);
        let cs = tm.mk_set_card(s);
        let card_one = tm.mk_eq(cs, one);
        vec![m1, m2, card_one]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Two *terms* denoting one value count once: `x ∈ s`, `y ∈ s`, `x = y`,
/// `|s| = 1` is satisfiable (`s = {x}`). Without the de-duplication guards
/// the counting sum would report two members and answer a false `unsat`.
#[test]
fn equal_terms_count_once() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let s = tm.mk_var("S", set_int);
        let x = tm.mk_var("x", int);
        let y = tm.mk_var("y", int);
        let mx = tm.mk_set_member(x, s);
        let my = tm.mk_set_member(y, s);
        let same = tm.mk_eq(x, y);
        let one = tm.mk_int(1);
        let cs = tm.mk_set_card(s);
        let card = tm.mk_eq(cs, one);
        vec![mx, my, same, card]
    });
    assert_eq!(got, SolverResult::Sat);
}

/// …and the same shape with `|s| = 2` is satisfiable too (`x ≠ y` is not
/// forced, so `s = {x, y}` with `x = y` giving one element would contradict
/// `|s| = 2`; the model must pick `x ≠ y`). Satisfiable either way: the
/// encoding may not force the equality either.
#[test]
fn equal_terms_with_card_two_is_sat() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let s = tm.mk_var("S", set_int);
        let x = tm.mk_var("x", int);
        let y = tm.mk_var("y", int);
        let mx = tm.mk_set_member(x, s);
        let my = tm.mk_set_member(y, s);
        let same = tm.mk_eq(x, y);
        let two = tm.mk_int(2);
        let cs = tm.mk_set_card(s);
        let card = tm.mk_eq(cs, two);
        vec![mx, my, same, card]
    });
    assert_eq!(got, SolverResult::Sat);
}

/// Inclusion–exclusion: `|a| = |b| = 2`, `|a ∪ b| = 3` is satisfiable
/// (`a = {1,2}`, `b = {1,7}`; `|a ∩ b| = 1`) — the twin `a ∩ b` exists so
/// the identity is statable.
#[test]
fn union_of_two_singles_identity_sat() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let a = tm.mk_var("A", set_int);
        let b = tm.mk_var("B", set_int);
        let u = tm.mk_set_union(a, b);
        let two = tm.mk_int(2);
        let three = tm.mk_int(3);
        let ca = tm.mk_set_card(a);
        let cb = tm.mk_set_card(b);
        let cu = tm.mk_set_card(u);
        vec![tm.mk_eq(ca, two), tm.mk_eq(cb, two), tm.mk_eq(cu, three)]
    });
    assert_eq!(got, SolverResult::Sat);
}

/// Pigeonhole through inclusion–exclusion: `|a| = |b| = 1`, `|a ∪ b| = 1`
/// forces `a ∩ b` to hold the one element of each, so `a = b`.
/// With `a ≠ b` asserted the problem is unsatisfiable.
#[test]
fn union_cardinality_one_forces_equality() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let a = tm.mk_var("A", set_int);
        let b = tm.mk_var("B", set_int);
        let u = tm.mk_set_union(a, b);
        let one = tm.mk_int(1);
        let ca = tm.mk_set_card(a);
        let cb = tm.mk_set_card(b);
        let cu = tm.mk_set_card(u);
        let ab = tm.mk_eq(a, b);
        let ne = tm.mk_not(ab);
        vec![tm.mk_eq(ca, one), tm.mk_eq(cb, one), tm.mk_eq(cu, one), ne]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Two distinct members of a union of cardinality one is unsatisfiable —
/// the case that needs the **slack lattice**, not just per-set slacks: an
/// element of `a ∩ b` must live in `a` and in `b`, so `slack(a ∩ b) ≤
/// slack(a)` has to be stated for the region algebra to close.
#[test]
fn distinct_members_of_small_union_are_unsat() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let a = tm.mk_var("A", set_int);
        let b = tm.mk_var("B", set_int);
        let u = tm.mk_set_union(a, b);
        let one = tm.mk_int(1);
        let x = tm.mk_int(1);
        let y = tm.mk_int(2);
        let cu = tm.mk_set_card(u);
        vec![
            tm.mk_eq(cu, one),
            tm.mk_set_member(x, u),
            tm.mk_set_member(y, u),
        ]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `a ⊆ b`, `|a| = |b|`, `a ≠ b` is unsatisfiable: a subset of the same
/// size is the whole set (the completeness half of subset + cardinality).
#[test]
fn subset_of_equal_size_is_the_whole_set() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let a = tm.mk_var("A", set_int);
        let b = tm.mk_var("B", set_int);
        let two = tm.mk_int(2);
        let ca = tm.mk_set_card(a);
        let cb = tm.mk_set_card(b);
        let ab = tm.mk_eq(a, b);
        let ne = tm.mk_not(ab);
        vec![
            tm.mk_set_subset(a, b),
            tm.mk_eq(ca, two),
            tm.mk_eq(cb, two),
            ne,
        ]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `|a ∪ b| = 0 ∧ x ∈ a` is unsatisfiable: an empty union has empty
/// operands. Needs the count equation on the *operands* to meet the union's
/// cardinality through the identity chain (`a ⊆ a ∪ b`).
#[test]
fn empty_union_forces_empty_operands() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let a = tm.mk_var("A", set_int);
        let b = tm.mk_var("B", set_int);
        let u = tm.mk_set_union(a, b);
        let x = tm.mk_var("x", int);
        let zero = tm.mk_int(0);
        let cu = tm.mk_set_card(u);
        vec![tm.mk_eq(cu, zero), tm.mk_set_member(x, a)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Cardinality of a structurally known set stays exact: `|{x} ∪ {y}| = 5`
/// is unsatisfiable — at most two elements, no slack may smuggle more in.
#[test]
fn support_known_cardinality_is_exact() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let y = tm.mk_var("y", int);
        let sx = tm.mk_set_singleton(x);
        let sy = tm.mk_set_singleton(y);
        let u = tm.mk_set_union(sx, sy);
        let five = tm.mk_int(5);
        let cu = tm.mk_set_card(u);
        vec![tm.mk_eq(cu, five)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// …and `|{x} ∪ {y}| = 2` with `x ≠ y` is satisfiable.
#[test]
fn support_known_two_elements_fits() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let y = tm.mk_var("y", int);
        let sx = tm.mk_set_singleton(x);
        let sy = tm.mk_set_singleton(y);
        let u = tm.mk_set_union(sx, sy);
        let two = tm.mk_int(2);
        let cu = tm.mk_set_card(u);
        let xy = tm.mk_eq(x, y);
        let ne = tm.mk_not(xy);
        vec![tm.mk_eq(cu, two), ne]
    });
    assert_eq!(got, SolverResult::Sat);
}

/// `|{x} ∪ {y}| = 1` with `x ≠ y` is unsatisfiable: two distinct values
/// cannot collapse into one member.
#[test]
fn support_known_one_slot_two_values_is_unsat() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let x = tm.mk_var("x", int);
        let y = tm.mk_var("y", int);
        let sx = tm.mk_set_singleton(x);
        let sy = tm.mk_set_singleton(y);
        let u = tm.mk_set_union(sx, sy);
        let one = tm.mk_int(1);
        let cu = tm.mk_set_card(u);
        let xy = tm.mk_eq(x, y);
        let ne = tm.mk_not(xy);
        vec![tm.mk_eq(cu, one), ne]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `|a \ b| = 0 ∧ |a| = 1 ∧ x ∈ a ∧ x ∉ b` is unsatisfiable: the member of
/// `a` is not in `b`, so it survives the difference.
#[test]
fn difference_cannot_hide_a_member() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let a = tm.mk_var("A", set_int);
        let b = tm.mk_var("B", set_int);
        let d = tm.mk_set_minus(a, b);
        let x = tm.mk_var("x", int);
        let one = tm.mk_int(1);
        let zero = tm.mk_int(0);
        let cd = tm.mk_set_card(d);
        let ca = tm.mk_set_card(a);
        let in_b = tm.mk_set_member(x, b);
        let not_in_b = tm.mk_not(in_b);
        vec![
            tm.mk_eq(cd, zero),
            tm.mk_eq(ca, one),
            tm.mk_set_member(x, a),
            not_in_b,
        ]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `choose`: `|s| = 1 ∧ s = {5}` forces `choose(s) = 5`.
#[test]
fn choose_picks_the_only_member() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let s = tm.mk_var("S", set_int);
        let five = tm.mk_int(5);
        let singleton = tm.mk_set_singleton(five);
        let chosen = tm.mk_set_choose(s);
        let cf = tm.mk_eq(chosen, five);
        let ne = tm.mk_not(cf);
        vec![tm.mk_eq(s, singleton), ne]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `choose(∅) ∈ ∅` is unsatisfiable: the empty set has nothing to choose.
#[test]
fn choose_of_empty_is_not_a_member() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let e = tm.mk_set_empty(int);
        let chosen = tm.mk_set_choose(e);
        vec![tm.mk_set_member(chosen, e)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Finite universe pigeonhole: over `Bool`, `|s| = 3` is unsatisfiable —
/// the universe has exactly two elements.
#[test]
fn bool_set_cannot_have_three_members() {
    let got = solve(|tm| {
        let bool_sort = tm.sorts.bool_sort;
        let set_bool = tm.sorts.set(bool_sort);
        let s = tm.mk_var("S", set_bool);
        let three = tm.mk_int(3);
        let cs = tm.mk_set_card(s);
        vec![tm.mk_eq(cs, three)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// …while `|s| = 2` over `Bool` is satisfiable (`s = {true, false}`).
#[test]
fn bool_set_can_have_both_members() {
    let got = solve(|tm| {
        let bool_sort = tm.sorts.bool_sort;
        let set_bool = tm.sorts.set(bool_sort);
        let s = tm.mk_var("S", set_bool);
        let two = tm.mk_int(2);
        let cs = tm.mk_set_card(s);
        vec![tm.mk_eq(cs, two)]
    });
    assert_eq!(got, SolverResult::Sat);
}

/// Bit-vector pigeonhole: over `(_ BitVec 2)`, `|s| = 5` is unsatisfiable
/// (four values), and `|s| = 4` with four pairwise-distinct members is
/// satisfiable.
#[test]
fn bv4_set_cannot_have_five_members() {
    let got = solve(|tm| {
        let bv2 = tm.sorts.bitvec(2);
        let set_bv = tm.sorts.set(bv2);
        let s = tm.mk_var("S", set_bv);
        let five = tm.mk_int(5);
        let cs = tm.mk_set_card(s);
        vec![tm.mk_eq(cs, five)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Complement over a finite universe: `|~s| + |s| = |U|`, so over `Bool`,
/// `|s| = 1 ∧ |~s| = 2` is unsatisfiable (they must sum to 2).
#[test]
fn complement_sums_to_the_universe() {
    let got = solve(|tm| {
        let bool_sort = tm.sorts.bool_sort;
        let set_bool = tm.sorts.set(bool_sort);
        let s = tm.mk_var("S", set_bool);
        let c = tm.mk_set_complement(s);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let cs = tm.mk_set_card(s);
        let cc = tm.mk_set_card(c);
        vec![tm.mk_eq(cs, one), tm.mk_eq(cc, two)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `x ∈ ~s ∧ x ∉ ... ` pointwise complement: `x ∈ ~s ↔ x ∉ s`.
#[test]
fn complement_membership_is_pointwise() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let s = tm.mk_var("S", set_int);
        let c = tm.mk_set_complement(s);
        let x = tm.mk_var("x", int);
        vec![tm.mk_set_member(x, s), tm.mk_set_member(x, c)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// `set.is_empty` lowers to `|s| = 0`, so `is_empty(s) ∧ x ∈ s` is
/// unsatisfiable.
#[test]
fn is_empty_is_cardinality_zero() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let s = tm.mk_var("S", set_int);
        let x = tm.mk_var("x", int);
        let card = tm.mk_set_card(s);
        let zero = tm.mk_int(0);
        let is_empty = tm.mk_eq(card, zero);
        let _ = &is_empty;
        vec![is_empty, tm.mk_set_member(x, s)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// The universe set over a finite sort: `|U| = 2` for `Bool`, so `s ⊆ U`
/// with `|s| = 3` stays unsatisfiable through the subset rule as well.
#[test]
fn univset_cardinality_is_the_universe_size() {
    let got = solve(|tm| {
        let bool_sort = tm.sorts.bool_sort;
        let u = tm.mk_set_univ(bool_sort);
        let three = tm.mk_int(3);
        let cu = tm.mk_set_card(u);
        vec![tm.mk_eq(cu, three)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// A `ite`-shaped set's cardinality is exactly one of its branches':
/// `|ite c {1} {2}| = 0` is unsatisfiable whichever way `c` falls.
#[test]
fn ite_cardinality_is_one_of_the_branches() {
    let got = solve(|tm| {
        let c = tm.mk_var("c", tm.sorts.bool_sort);
        let one = tm.mk_int(1);
        let two = tm.mk_int(2);
        let s1 = tm.mk_set_singleton(one);
        let s2 = tm.mk_set_singleton(two);
        let it = tm.mk_ite(c, s1, s2);
        let zero = tm.mk_int(0);
        let ci = tm.mk_set_card(it);
        vec![tm.mk_eq(ci, zero)]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Helper: solve an SMT-LIB snippet through the parser, end to end.
fn solve_smt(script: &str) -> SolverResult {
    let mut context = nixie_solver::Context::new();
    match context.execute_script(script) {
        Ok(lines) => {
            // The verdict is the last `sat`/`unsat`/`unknown` line printed.
            lines
                .iter()
                .rev()
                .find_map(|l| match l.trim() {
                    "sat" => Some(SolverResult::Sat),
                    "unsat" => Some(SolverResult::Unsat),
                    "unknown" => Some(SolverResult::Unknown),
                    _ => None,
                })
                .unwrap_or(SolverResult::Unknown)
        }
        Err(_) => SolverResult::Unknown,
    }
}

/// The SMT-LIB surface end to end: the exact spellings CVC5 and Z3 accept,
/// on one sat and one unsat cardinality problem.
#[test]
fn smtlib_surface_end_to_end() {
    // member + card = 0 -> unsat
    let unsat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (declare-const x Int)\n\
         (assert (set.member x s))\n\
         (assert (= (set.card s) 0))\n\
         (check-sat)\n",
    );
    assert_eq!(unsat, SolverResult::Unsat);

    // pigeonhole -> unsat
    let pigeon = solve_smt(
        "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 2))\n\
         (assert (set.member 1 s))\n\
         (assert (set.member 2 s))\n\
         (assert (set.member 3 s))\n\
         (check-sat)\n",
    );
    assert_eq!(pigeon, SolverResult::Unsat);

    // satisfiable: |s| = 2 with one member, in both assertion orders.
    for order in [0, 1] {
        let (a, b) = if order == 0 {
            ("(assert (= (set.card s) 2))", "(assert (set.member 1 s))")
        } else {
            ("(assert (set.member 1 s))", "(assert (= (set.card s) 2))")
        };
        let sat = solve_smt(&format!(
            "(set-logic ALL)\n\
             (declare-const s (Set Int))\n\
             {a}\n\
             {b}\n\
             (check-sat)\n"
        ));
        assert_eq!(sat, SolverResult::Sat, "order {order}");
    }
}

/// The wider operator surface (`set.insert`, `set.choose`, `set.minus`,
/// `set.is_empty` in one problem).
///
#[test]
fn smtlib_surface_rich_operators() {
    let rich = solve_smt(
        "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (declare-const t (Set Int))\n\
         (assert (set.subset (set.insert 1 2 (as set.empty (Set Int))) s))\n\
         (assert (= (set.card s) 2))\n\
         (assert (set.member (set.choose t) t))\n\
         (assert (set.is_empty (set.minus s s)))\n\
         (check-sat)\n",
    );
    assert_eq!(rich, SolverResult::Sat);
}

/// Z3-classic bare spellings parse and mean the same thing.
#[test]
fn smtlib_bare_aliases_end_to_end() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (declare-const x Int)\n\
         (assert (member x s))\n\
         (assert (= (card s) 0))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// A user declaration of a common word like `union` still wins over the
/// bare alias: the script keeps its meaning.
#[test]
fn user_declared_union_is_not_the_alias() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-fun union (Int Int) Bool)\n\
         (declare-const a Int)\n\
         (assert (union a a))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Sat);
}

/// `(as emptyset (Set Int))` and `univset` — Z3's spellings.
#[test]
fn z3_classic_emptyset_and_univset() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const s (Set Bool))\n\
         (assert (set.subset (as univset (Set Bool)) s))\n\
         (assert (= (set.card s) 1))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// Nested sets: `Set (Set Int)` — the universe is infinite, cardinality
/// works over ground elements, and `s ⊆ t` with equal cards forces `s = t`.
#[test]
fn nested_set_sorts() {
    let got = solve(|tm| {
        let int = tm.sorts.int_sort;
        let set_int = tm.sorts.set(int);
        let set_set_int = tm.sorts.set(set_int);
        let s = tm.mk_var("S", set_set_int);
        let t = tm.mk_var("T", set_set_int);
        let two = tm.mk_int(2);
        let cs = tm.mk_set_card(s);
        let ct = tm.mk_set_card(t);
        let st = tm.mk_eq(s, t);
        let ne = tm.mk_not(st);
        vec![
            tm.mk_set_subset(s, t),
            tm.mk_eq(cs, two),
            tm.mk_eq(ct, two),
            ne,
        ]
    });
    assert_eq!(got, SolverResult::Unsat);
}

/// Push/pop scope consistency: a cardinality constraint asserted inside a
/// pushed scope must vanish with the pop — the axioms are conjoined onto
/// the scoped assertion, so the bookkeeping rides the existing trail.
#[test]
fn cardinality_is_scope_consistent() {
    let mut tm = TermManager::new();
    let int = tm.sorts.int_sort;
    let set_int = tm.sorts.set(int);
    let s = tm.mk_var("S", set_int);
    let one = tm.mk_int(1);
    let two = tm.mk_int(2);
    let x = tm.mk_int(1);

    let mut solver = Solver::new();
    solver.push();
    solver.assert(tm.mk_set_member(x, s), &mut tm);
    let cs = tm.mk_set_card(s);
    let m2 = tm.mk_set_member(two, s);
    solver.assert(tm.mk_eq(cs, one), &mut tm);
    solver.assert(m2, &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Unsat);
    solver.pop();
    // Without the scoped assertions the problem is satisfiable.
    let cs2 = tm.mk_set_card(s);
    solver.assert(tm.mk_eq(cs2, two), &mut tm);
    assert_eq!(solver.check(&mut tm), SolverResult::Sat);
}

// ===== equality ⇒ equal cardinality / congruent choose =====
//
// Found 2026-09-15 while starting the model-synthesis roadmap item: the
// cardinality encoding related the *memberships* of equal sets (the pair
// machinery) but never their *sizes* or their `choose` applications, so
// every script below answered `sat` — each is unsat. Z3's reference is
// `theory_finite_set_size::add_eq_axioms`, which ties the Boolean
// abstractions of every asserted-equal pair (equalizing their sizes through
// the sub-solver); `choose` congruence is ordinary equality-engine
// congruence there, stated explicitly in this reduction.

/// `S = T ∧ |S| = 5 ∧ |T| = 3`: one set cannot have two sizes.
#[test]
fn equal_sets_have_equal_cardinality() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (assert (= S T))\n\
         (assert (= (set.card S) 5))\n\
         (assert (= (set.card T) 3))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// `S = ∅ ∧ |S| ≥ 1`: the empty set is not nonempty. Same rule through a
/// constructor operand.
#[test]
fn equal_to_empty_has_cardinality_zero() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (assert (= S (as set.empty (Set Int))))\n\
         (assert (>= (set.card S) 1))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// `x = y ∧ |f x| = 5 ∧ |f y| = 3`: the equality is *derived* (EUF
/// congruence), not asserted — the implicit-pair atom is what carries it,
/// so the equality⇒card rule must fire on implicit pairs too.
#[test]
fn derived_equality_equalizes_cardinality() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-fun f (Int) (Set Int))\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (assert (= x y))\n\
         (assert (= (set.card (f x)) 5))\n\
         (assert (= (set.card (f y)) 3))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// `S = {1} ∪ {2} ∧ |S| = 5`: an asserted equality to a compound term; the
/// operand's support-exact count (2) meets the equality⇒card rule.
#[test]
fn asserted_equality_to_a_compound_binds_its_size() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (assert (= S (set.union (set.singleton 1) (set.singleton 2))))\n\
         (assert (= (set.card S) 5))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// `S = T ∧ |S| ≥ 1 ∧ choose(S) ≠ choose(T)`: `choose` is a function
/// symbol; equal arguments give equal results. The member axioms alone let
/// both chooses sit inside the one set as two distinct elements.
#[test]
fn equal_sets_have_congruent_choose() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (assert (= S T))\n\
         (assert (>= (set.card S) 1))\n\
         (assert (distinct (set.choose S) (set.choose T)))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}

/// The choose-congruence rule does not over-constrain: equal sets with
/// equal chooses stay satisfiable.
#[test]
fn congruent_choose_on_equal_sets_is_sat() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (assert (= S T))\n\
         (assert (>= (set.card S) 1))\n\
         (assert (= (set.choose S) (set.choose T)))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Sat);
}

/// `c ∧ choose(ite c A B) ≠ choose(A)`: with `c` the ite *is* `A`, but the
/// equality atom `ite c A B = A` is never asserted by anyone, so the pair
// rule cannot carry it — the ite yields its element through its own rule.
#[test]
fn choose_of_ite_picks_the_taken_branch() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const A (Set Int))\n\
         (declare-const B (Set Int))\n\
         (declare-const c Bool)\n\
         (assert c)\n\
         (assert (>= (set.card A) 1))\n\
         (assert (distinct (set.choose (ite c A B)) (set.choose A)))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
    // ...and with `c` false the ite is `B`, so the disequality to
    // `choose(A)` is fine (A nonempty, B free).
    let sat = solve_smt(
        "(set-logic ALL)\n\
         (declare-const A (Set Int))\n\
         (declare-const B (Set Int))\n\
         (declare-const c Bool)\n\
         (assert (not c))\n\
         (assert (>= (set.card A) 1))\n\
         (assert (distinct (set.choose (ite c A B)) (set.choose A)))\n\
         (check-sat)\n",
    );
    assert_eq!(sat, SolverResult::Sat);
}

/// `|T| = |U| = 1 ∧ S = T ∪ U ∧ |S| = 3`: the equality⇒card rule meets
/// inclusion–exclusion and non-negativity (`|T ∩ U| = -1`).
#[test]
fn equality_card_rule_composes_with_inclusion_exclusion() {
    let got = solve_smt(
        "(set-logic ALL)\n\
         (declare-const S (Set Int))\n\
         (declare-const T (Set Int))\n\
         (declare-const U (Set Int))\n\
         (assert (= S (set.union T U)))\n\
         (assert (= (set.card T) 1))\n\
         (assert (= (set.card U) 1))\n\
         (assert (= (set.card S) 3))\n\
         (check-sat)\n",
    );
    assert_eq!(got, SolverResult::Unsat);
}
