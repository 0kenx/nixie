"""Regression test for wide bitvector model values (audit finding infra-p3).

`Solver.model()` used to build its typed Python model dict by taking only
the lowest 64-bit limb of a bitvector constant's `BigInt` value
(`value.iter_u64_digits().next().unwrap_or(0)`) and hardcoding its width to
0. For any BV variable whose satisfying value needs more than 64 bits to
represent (as happens routinely in QF_BV crypto-style queries), `model()`
would silently hand back a wrong integer instead of erroring or preserving
the value.

The fix (`bigint_to_pyobject` / `PyModelValue::BitVec(BigInt, u32)` in
`oxiz-py/src/solver_py.rs`) is covered directly and exhaustively at the Rust
level by `solver_py::tests::build_model_value_preserves_bitvec_wider_than_64_bits`
and `..._bitvec_within_64_bits_round_trips`, which construct a `BitVecConst`
term with a value requiring >64 bits and assert it survives
`build_model_value` unchanged.

This file adds end-to-end Python-level coverage for the part of the fix
that *is* currently reachable through the public bindings: a wide
(128-bit) variable whose value comes back from the solver still round-trips
correctly as a plain Python `int` through `model()`.

`TermManager.mk_bv()` used to only accept a Rust `i64` (so a single call
could not literally exceed roughly 2**63); it now takes an arbitrary-size
Python `int` (converted to `num-bigint::BigInt` via PyO3's `num-bigint`
feature - see `oxiz-py/src/term.rs`), so `test_bv_mk_bv_accepts_literal_wider_than_i64`
below drives a *genuinely* >64-bit satisfying value through the public
Python API for a leaf constant. Composing a wider value out of narrower
pieces via `mk_bv_concat`/`mk_bv_mul` still runs into a separate,
pre-existing bug in the underlying BV theory's model construction for
composite (non-leaf-constant) wide-bitvector equalities - independent of
this fix and out of scope for the oxiz-py package. See the session notes
for that finding.
"""

import oxiz
import pytest


def test_bv_128bit_variable_small_value_round_trips_via_typed_model():
    """A 128-bit BV variable constrained to a value that fits in the u64
    fast path must still come back correct and as a plain Python int -
    i.e. widening the declared bitvector sort must not regress the
    existing (working) path."""
    tm = oxiz.TermManager()
    solver = oxiz.Solver()
    solver.set_logic("QF_BV")

    x = tm.mk_var("x", "BitVec[128]")
    const = tm.mk_bv(42, 128)
    solver.assert_term(tm.mk_eq(x, const), tm)

    result = solver.check_sat(tm)
    assert result == oxiz.SolverResult.Sat

    model = solver.model()
    assert model["x"] == 42
    assert isinstance(model["x"], int)

    # The string-valued API (unaffected by this fix, kept as a cross-check)
    # must agree with the typed API.
    string_model = solver.get_model(tm)
    assert int(string_model["x"].removeprefix("#x"), 16) == 42


def test_bv_64bit_and_below_still_plain_int():
    """Values that DO fit in 64 bits should still come back as a normal
    Python int (fast path), matching pre-fix behavior for the in-range case."""
    tm = oxiz.TermManager()
    solver = oxiz.Solver()
    solver.set_logic("QF_BV")

    x = tm.mk_var("x", "BitVec[8]")
    const = tm.mk_bv(200, 8)
    solver.assert_term(tm.mk_eq(x, const), tm)

    result = solver.check_sat(tm)
    assert result == oxiz.SolverResult.Sat

    model = solver.model()
    assert model["x"] == 200
    assert isinstance(model["x"], int)


def test_bv_mk_bv_accepts_literal_wider_than_i64():
    """`mk_bv()` must accept Python ints that don't fit in a Rust `i64`
    (regression test for infra-final oxiz-py: mk_bv used to take `i64`,
    silently making it impossible to construct >64-bit BV literals from
    Python at all - not even a truncating-but-wrong value, a hard
    overflow/TypeError). 2**100 + 12345 requires far more than 64 bits,
    so this both exercises the wide-literal path and confirms the value
    round-trips exactly (not truncated to a low limb) through the solver
    and back out via the typed model."""
    tm = oxiz.TermManager()
    solver = oxiz.Solver()
    solver.set_logic("QF_BV")

    wide_value = (1 << 100) + 12345
    x = tm.mk_var("x", "BitVec[128]")
    const = tm.mk_bv(wide_value, 128)
    solver.assert_term(tm.mk_eq(x, const), tm)

    result = solver.check_sat(tm)
    assert result == oxiz.SolverResult.Sat

    model = solver.model()
    assert model["x"] == wide_value
    assert isinstance(model["x"], int)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
