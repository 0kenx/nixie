"""Basic tests for Nixie Python bindings"""

import nixie
import pytest

def test_term_manager_creation():
    """Test TermManager can be created"""
    tm = nixie.TermManager()
    assert tm is not None

def test_solver_creation():
    """Test Solver can be created"""
    solver = nixie.Solver()
    assert solver is not None
    assert solver.num_assertions == 0
    assert solver.context_level == 0

def test_optimizer_creation():
    """Test Optimizer can be created"""
    opt = nixie.Optimizer()
    assert opt is not None

def test_boolean_constants():
    """Test boolean constant creation"""
    tm = nixie.TermManager()
    t = tm.mk_bool(True)
    f = tm.mk_bool(False)
    assert t != f

def test_integer_constants():
    """Test integer constant creation"""
    tm = nixie.TermManager()
    zero = tm.mk_int(0)
    one = tm.mk_int(1)
    neg = tm.mk_int(-42)
    assert zero != one
    assert one != neg

def test_real_constants():
    """Test rational constant creation"""
    tm = nixie.TermManager()
    half = tm.mk_real(1, 2)
    third = tm.mk_real(1, 3)
    assert half != third

def test_real_invalid_denominator():
    """Test that zero denominator raises error"""
    tm = nixie.TermManager()
    with pytest.raises(ValueError):
        tm.mk_real(1, 0)

def test_variables():
    """Test variable creation with different sorts"""
    tm = nixie.TermManager()
    b = tm.mk_var("b", "Bool")
    i = tm.mk_var("i", "Int")
    r = tm.mk_var("r", "Real")
    bv = tm.mk_var("bv8", "BitVec[8]")

    assert b != i
    assert i != r
    assert r != bv

def test_invalid_sort():
    """Test that invalid sort name raises error"""
    tm = nixie.TermManager()
    with pytest.raises(ValueError):
        tm.mk_var("x", "InvalidSort")

def test_simple_sat():
    """Test simple SAT problem: p AND q"""
    tm = nixie.TermManager()
    solver = nixie.Solver()

    p = tm.mk_var("p", "Bool")
    q = tm.mk_var("q", "Bool")

    # Assert: p AND q
    pand_q = tm.mk_and([p, q])
    solver.assert_term(pand_q, tm)

    result = solver.check_sat(tm)
    assert result == nixie.SolverResult.Sat

    model = solver.get_model(tm)
    assert model["p"] == "true"
    assert model["q"] == "true"

def test_simple_unsat():
    """Test simple UNSAT problem: p AND NOT p"""
    tm = nixie.TermManager()
    solver = nixie.Solver()

    p = tm.mk_var("p", "Bool")

    # Assert: p AND NOT p
    solver.assert_term(p, tm)
    solver.assert_term(tm.mk_not(p), tm)

    result = solver.check_sat(tm)
    assert result == nixie.SolverResult.Unsat

def test_arithmetic_sat():
    """Test arithmetic SAT: x + y = 10, x > 5"""
    tm = nixie.TermManager()
    solver = nixie.Solver()
    solver.set_logic("QF_LIA")

    x = tm.mk_var("x", "Int")
    y = tm.mk_var("y", "Int")

    ten = tm.mk_int(10)
    five = tm.mk_int(5)

    # x + y = 10
    sum_xy = tm.mk_add([x, y])
    solver.assert_term(tm.mk_eq(sum_xy, ten), tm)

    # x > 5
    solver.assert_term(tm.mk_gt(x, five), tm)

    result = solver.check_sat(tm)
    assert result == nixie.SolverResult.Sat

    model = solver.get_model(tm)
    x_val = int(model["x"])
    y_val = int(model["y"])

    assert x_val > 5
    assert x_val + y_val == 10

def test_push_pop():
    """Test push/pop for incremental solving"""
    tm = nixie.TermManager()
    solver = nixie.Solver()

    p = tm.mk_var("p", "Bool")
    q = tm.mk_var("q", "Bool")

    # Assert: p
    solver.assert_term(p, tm)
    assert solver.check_sat(tm) == nixie.SolverResult.Sat

    # Push and add: NOT p
    solver.push()
    solver.assert_term(tm.mk_not(p), tm)
    assert solver.check_sat(tm) == nixie.SolverResult.Unsat

    # Pop back - should be SAT again
    solver.pop()
    assert solver.check_sat(tm) == nixie.SolverResult.Sat

def test_reset():
    """Test solver reset"""
    tm = nixie.TermManager()
    solver = nixie.Solver()

    p = tm.mk_var("p", "Bool")
    solver.assert_term(p, tm)

    assert solver.num_assertions > 0

    solver.reset()
    assert solver.num_assertions == 0

if __name__ == "__main__":
    pytest.main([__file__, "-v"])
