"""Tests for floating-point theory support in OxiZ Python bindings.

Covers:
- FPSort(eb, sb, tm)               — FP sort constructor
- FPVal(tm, sign, exp, sig, sort)  — FP value constructor
- fp_add / fp_sub / fp_mul / fp_div module-level combinators
- FPRoundingMode sentinel class
- mk_fp_* methods on TermManager
- mk_var with "Float[eb,sb]" / "FP[eb,sb]" sort strings
"""

import oxiz
import pytest


# --------------------------------------------------------------------------- #
# FPSort                                                                      #
# --------------------------------------------------------------------------- #

def test_fp_sort_exists():
    """FPSort is now exposed at module level."""
    assert hasattr(oxiz, "FPSort")


def test_fp_sort_half():
    """FPSort(5, 11, tm) creates a half-precision sort (IEEE 754)."""
    tm = oxiz.TermManager()
    s = oxiz.FPSort(tm, 5, 11)
    assert s is not None
    assert s.is_fp is True
    assert s.eb == 5
    assert s.sb == 11


def test_fp_sort_single():
    """FPSort(8, 24, tm) creates a single-precision sort."""
    tm = oxiz.TermManager()
    s = oxiz.FPSort(tm, 8, 24)
    assert s.eb == 8
    assert s.sb == 24


def test_fp_sort_double():
    """FPSort(11, 53, tm) creates a double-precision sort."""
    tm = oxiz.TermManager()
    s = oxiz.FPSort(tm, 11, 53)
    assert s.eb == 11
    assert s.sb == 53


def test_fp_sort_dedup():
    """Two FPSort calls with identical parameters return equal sort objects."""
    tm = oxiz.TermManager()
    s1 = oxiz.FPSort(tm, 8, 24)
    s2 = oxiz.FPSort(tm, 8, 24)
    assert s1 == s2


def test_fp_sort_repr():
    """FPSort repr includes exponent and significand widths."""
    tm = oxiz.TermManager()
    s = oxiz.FPSort(tm, 8, 24)
    assert "8" in repr(s) and "24" in repr(s)


# --------------------------------------------------------------------------- #
# FPVal                                                                       #
# --------------------------------------------------------------------------- #

def test_fp_val_exists():
    """FPVal is now exposed at module level."""
    assert hasattr(oxiz, "FPVal")


def test_fp_val_positive_one_fp32():
    """FPVal creates +1.0 in fp32 (sign=False, biased-exp=127, sig=0)."""
    tm = oxiz.TermManager()
    sort = oxiz.FPSort(tm, 8, 24)
    one = oxiz.FPVal(tm, False, 127, 0, sort)
    assert one is not None


def test_fp_val_negative():
    """FPVal creates a negative FP term (sign=True)."""
    tm = oxiz.TermManager()
    sort = oxiz.FPSort(tm, 8, 24)
    neg = oxiz.FPVal(tm, True, 127, 0, sort)
    assert neg is not None


def test_fp_val_distinct_from_plus_zero():
    """FPVal(+1.0) and FPVal(+0.0) produce different AST nodes."""
    tm = oxiz.TermManager()
    sort = oxiz.FPSort(tm, 8, 24)
    one = oxiz.FPVal(tm, False, 127, 0, sort)
    zero_term = tm.mk_fp_plus_zero(8, 24)
    assert one != zero_term


def test_fp_val_wrong_sort_raises():
    """FPVal with a non-FP sort object raises ValueError."""
    tm = oxiz.TermManager()
    int_sort = oxiz.IntSort(tm)
    with pytest.raises((ValueError, TypeError, Exception)):
        oxiz.FPVal(tm, False, 127, 0, int_sort)


# --------------------------------------------------------------------------- #
# FPRoundingMode                                                              #
# --------------------------------------------------------------------------- #

def test_fp_rounding_mode_exists():
    """FPRoundingMode is now exposed at module level."""
    assert hasattr(oxiz, "FPRoundingMode")


def test_fp_rounding_mode_instantiable():
    """FPRoundingMode() can be instantiated as a sentinel object."""
    rm = oxiz.FPRoundingMode()
    assert rm is not None
    assert "FPRoundingMode" in repr(rm)


# --------------------------------------------------------------------------- #
# Module-level FP arithmetic combinators                                      #
# --------------------------------------------------------------------------- #

def test_fp_add_exists():
    """fp_add is now exposed at module level."""
    assert hasattr(oxiz, "fp_add")


def test_fp_sub_exists():
    """fp_sub is now exposed at module level."""
    assert hasattr(oxiz, "fp_sub")


def test_fp_mul_exists():
    """fp_mul is now exposed at module level."""
    assert hasattr(oxiz, "fp_mul")


def test_fp_div_exists():
    """fp_div is now exposed at module level."""
    assert hasattr(oxiz, "fp_div")


def _fp32_val(tm, sign, exp, sig):
    sort = oxiz.FPSort(tm, 8, 24)
    return oxiz.FPVal(tm, sign, exp, sig, sort)


def test_fp_add_produces_term():
    """fp_add(tm, 'RNE', a, b) returns a Term."""
    tm = oxiz.TermManager()
    a = _fp32_val(tm, False, 127, 0)  # +1.0
    b = _fp32_val(tm, False, 127, 0)  # +1.0
    c = oxiz.fp_add(tm, "RNE", a, b)
    assert c is not None


def test_fp_sub_produces_term():
    """fp_sub(tm, 'RNE', a, b) returns a Term."""
    tm = oxiz.TermManager()
    a = _fp32_val(tm, False, 127, 0)
    b = _fp32_val(tm, False, 127, 0)
    c = oxiz.fp_sub(tm, "RNE", a, b)
    assert c is not None


def test_fp_mul_produces_term():
    """fp_mul(tm, 'RNE', a, b) returns a Term."""
    tm = oxiz.TermManager()
    a = _fp32_val(tm, False, 127, 0)
    b = _fp32_val(tm, False, 127, 0)
    c = oxiz.fp_mul(tm, "RNE", a, b)
    assert c is not None


def test_fp_div_produces_term():
    """fp_div(tm, 'RNE', a, b) returns a Term."""
    tm = oxiz.TermManager()
    a = _fp32_val(tm, False, 127, 0)
    b = _fp32_val(tm, False, 127, 0)
    c = oxiz.fp_div(tm, "RNE", a, b)
    assert c is not None


def test_fp_add_bad_rounding_mode_raises():
    """fp_add with an invalid rounding mode raises ValueError."""
    tm = oxiz.TermManager()
    a = _fp32_val(tm, False, 127, 0)
    b = _fp32_val(tm, False, 127, 0)
    with pytest.raises((ValueError, Exception)):
        oxiz.fp_add(tm, "INVALID_RM", a, b)


def test_fp_arithmetic_produces_distinct_terms():
    """fp_add, fp_sub, fp_mul, fp_div all produce distinct AST nodes."""
    tm = oxiz.TermManager()
    a = _fp32_val(tm, False, 127, 0)
    b = _fp32_val(tm, False, 128, 0)  # +2.0
    add = oxiz.fp_add(tm, "RNE", a, b)
    sub = oxiz.fp_sub(tm, "RNE", a, b)
    mul = oxiz.fp_mul(tm, "RNE", a, b)
    div = oxiz.fp_div(tm, "RNE", a, b)
    ids = {add.id, sub.id, mul.id, div.id}
    assert len(ids) == 4


# --------------------------------------------------------------------------- #
# TermManager FP methods                                                      #
# --------------------------------------------------------------------------- #

def test_tm_mk_fp_val():
    """TermManager.mk_fp_lit is exposed (used by FPVal)."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_fp_lit")
    t = tm.mk_fp_lit(False, 127, 0, 8, 24)
    assert t is not None


def test_tm_mk_fp_add():
    """TermManager.mk_fp_add is exposed."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_fp_add")
    a = tm.mk_fp_lit(False, 127, 0, 8, 24)
    b = tm.mk_fp_lit(False, 127, 0, 8, 24)
    c = tm.mk_fp_add("RNE", a, b)
    assert c is not None


def test_tm_mk_fp_sub():
    """TermManager.mk_fp_sub is exposed."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_fp_sub")


def test_tm_mk_fp_mul():
    """TermManager.mk_fp_mul is exposed."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_fp_mul")


def test_tm_mk_fp_special_values():
    """TermManager exposes special FP constructors (nan, +/-inf, +/-zero)."""
    tm = oxiz.TermManager()
    nan = tm.mk_fp_nan(8, 24)
    pi = tm.mk_fp_plus_infinity(8, 24)
    ni = tm.mk_fp_minus_infinity(8, 24)
    pz = tm.mk_fp_plus_zero(8, 24)
    nz = tm.mk_fp_minus_zero(8, 24)
    assert len({nan.id, pi.id, ni.id, pz.id, nz.id}) == 5


# --------------------------------------------------------------------------- #
# mk_var with FP sort string                                                  #
# --------------------------------------------------------------------------- #

def test_mk_var_fp_sort_float():
    """mk_var accepts 'Float[8,24]' as a sort name."""
    tm = oxiz.TermManager()
    x = tm.mk_var("x_fp", "Float[8,24]")
    assert x is not None


def test_mk_var_fp_sort_fp():
    """mk_var accepts 'FP[8,24]' as an alternate sort name."""
    tm = oxiz.TermManager()
    x = tm.mk_var("x_fp2", "FP[8,24]")
    assert x is not None


# --------------------------------------------------------------------------- #
# Module version sanity                                                       #
# --------------------------------------------------------------------------- #

def test_module_version_present():
    """Sanity check: the module loads correctly and exposes __version__."""
    assert hasattr(oxiz, "__version__")
    assert isinstance(oxiz.__version__, str)
    assert len(oxiz.__version__) > 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
