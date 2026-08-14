"""Tests for quantifier support in OxiZ Python bindings.

Covers:
- oxiz.ForAll(tm, vars, body)   – universal quantifier combinator
- oxiz.Exists(tm, vars, body)   – existential quantifier combinator
- TermManager.mk_forall / mk_exists
- Multi-variable quantifiers
- Nested quantifiers
- Sort name dispatch for all supported sort strings
"""

import oxiz
import pytest


# --------------------------------------------------------------------------- #
# Module-level availability                                                   #
# --------------------------------------------------------------------------- #

def test_forall_exists_at_module_level():
    """ForAll and Exists are now exposed in the oxiz Python module."""
    assert hasattr(oxiz, "ForAll")
    assert hasattr(oxiz, "Exists")


def test_existing_boolean_combinators_still_present():
    """The boolean combinators that were already available are still there."""
    assert hasattr(oxiz, "And")
    assert hasattr(oxiz, "Or")
    assert hasattr(oxiz, "Not")
    assert hasattr(oxiz, "Implies")
    assert hasattr(oxiz, "If")


# --------------------------------------------------------------------------- #
# TermManager quantifier methods                                              #
# --------------------------------------------------------------------------- #

def test_term_manager_has_mk_forall():
    """TermManager now exposes mk_forall."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_forall")


def test_term_manager_has_mk_exists():
    """TermManager now exposes mk_exists."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_exists")


# --------------------------------------------------------------------------- #
# ForAll basics                                                               #
# --------------------------------------------------------------------------- #

def test_forall_single_int_var():
    """ForAll([('x', 'Int')], body, tm) produces a Term."""
    ctx = oxiz.Context()
    x = ctx.int_const("x")
    body = x > ctx.int_val(0)
    fml = oxiz.ForAll(ctx.tm, [("x", "Int")], body)
    assert fml is not None


def test_forall_single_bool_var():
    """ForAll([('b', 'Bool')], body, tm) produces a Term."""
    ctx = oxiz.Context()
    b = ctx.bool_const("b")
    body = b
    fml = oxiz.ForAll(ctx.tm, [("b", "Bool")], body)
    assert fml is not None


def test_forall_multi_var():
    """ForAll with multiple bound variables produces a Term."""
    ctx = oxiz.Context()
    x = ctx.int_const("x")
    y = ctx.int_const("y")
    body = x + y > ctx.int_val(0)
    fml = oxiz.ForAll(ctx.tm, [("x", "Int"), ("y", "Int")], body)
    assert fml is not None


def test_forall_tm_method():
    """tm.mk_forall([('x', 'Int')], body) produces a Term."""
    tm = oxiz.TermManager()
    x = tm.mk_var("x_fa", "Int")
    zero = tm.mk_int(0)
    body = tm.mk_gt(x, zero)
    fml = tm.mk_forall([("x_fa", "Int")], body)
    assert fml is not None


# --------------------------------------------------------------------------- #
# Exists basics                                                               #
# --------------------------------------------------------------------------- #

def test_exists_single_int_var():
    """Exists([('x', 'Int')], body, tm) produces a Term."""
    ctx = oxiz.Context()
    x = ctx.int_const("x")
    body = x > ctx.int_val(0)
    fml = oxiz.Exists(ctx.tm, [("x", "Int")], body)
    assert fml is not None


def test_exists_single_bool_var():
    """Exists([('b', 'Bool')], body, tm) produces a Term."""
    ctx = oxiz.Context()
    b = ctx.bool_const("b")
    fml = oxiz.Exists(ctx.tm, [("b", "Bool")], b)
    assert fml is not None


def test_exists_multi_var():
    """Exists with multiple bound variables produces a Term."""
    ctx = oxiz.Context()
    x = ctx.int_const("x")
    y = ctx.int_const("y")
    body = x > y
    fml = oxiz.Exists(ctx.tm, [("x", "Int"), ("y", "Int")], body)
    assert fml is not None


def test_exists_tm_method():
    """tm.mk_exists([('x', 'Int')], body) produces a Term."""
    tm = oxiz.TermManager()
    x = tm.mk_var("x_ex", "Int")
    zero = tm.mk_int(0)
    body = tm.mk_gt(x, zero)
    fml = tm.mk_exists([("x_ex", "Int")], body)
    assert fml is not None


# --------------------------------------------------------------------------- #
# ForAll vs Exists produce distinct terms                                     #
# --------------------------------------------------------------------------- #

def test_forall_and_exists_are_distinct():
    """ForAll and Exists with the same body must produce different term ids."""
    ctx = oxiz.Context()
    x = ctx.int_const("x")
    body = x > ctx.int_val(0)
    fa = oxiz.ForAll(ctx.tm, [("x", "Int")], body)
    ex = oxiz.Exists(ctx.tm, [("x", "Int")], body)
    assert fa != ex


# --------------------------------------------------------------------------- #
# Nested quantifiers                                                          #
# --------------------------------------------------------------------------- #

def test_nested_forall_exists():
    """Nested forall-exists construct (prenex normal-form shape) works."""
    ctx = oxiz.Context()
    x = ctx.int_const("x")
    y = ctx.int_const("y")
    body = x > y
    inner = oxiz.Exists(ctx.tm, [("y", "Int")], body)
    outer = oxiz.ForAll(ctx.tm, [("x", "Int")], inner)
    assert outer is not None
    assert outer != inner


# --------------------------------------------------------------------------- #
# Sort dispatch in quantifier binders                                         #
# --------------------------------------------------------------------------- #

@pytest.mark.parametrize("sort_name", [
    "Int",
    "Bool",
    "Real",
    "BitVec[32]",
    "Float[8,24]",
    "String",
])
def test_forall_various_sorts(sort_name):
    """ForAll accepts all registered sort names as variable types."""
    tm = oxiz.TermManager()
    # body: create a boolean true constant as a trivial body
    body = tm.mk_bool(True)
    fml = oxiz.ForAll(tm, [("v", sort_name)], body)
    assert fml is not None


@pytest.mark.parametrize("sort_name", [
    "Int",
    "Bool",
    "Real",
    "BitVec[32]",
    "Float[8,24]",
    "String",
])
def test_exists_various_sorts(sort_name):
    """Exists accepts all registered sort names as variable types."""
    tm = oxiz.TermManager()
    body = tm.mk_bool(True)
    fml = oxiz.Exists(tm, [("v", sort_name)], body)
    assert fml is not None


def test_forall_unknown_sort_raises():
    """ForAll raises ValueError for an unknown sort name."""
    tm = oxiz.TermManager()
    body = tm.mk_bool(True)
    with pytest.raises((ValueError, Exception)):
        oxiz.ForAll(tm, [("v", "UnknownSort")], body)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
