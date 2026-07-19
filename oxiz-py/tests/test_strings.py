"""Tests for string theory support in OxiZ Python bindings.

Covers:
- StringSort   — the string sort object
- StringVal    — string literal constructor
- mk_string_val / mk_str_concat / mk_str_length / mk_str_contains on TermManager
- Concat / Length / Contains / PrefixOf / SuffixOf module-level combinators
- mk_var with "String" sort
- ctx.string_const / ctx.string_val on Context
"""

import oxiz
import pytest


# --------------------------------------------------------------------------- #
# Sort and sort name                                                           #
# --------------------------------------------------------------------------- #

def test_string_sort_exists():
    """StringSort is now exposed at module level."""
    assert hasattr(oxiz, "StringSort")


def test_string_sort_returns_sort_object():
    """StringSort(tm) returns a Sort object that identifies the string sort."""
    tm = oxiz.TermManager()
    ss = oxiz.StringSort(tm)
    assert ss is not None
    assert ss.is_fp is False
    assert repr(ss) == "StringSort"


def test_mk_var_string_sort():
    """mk_var accepts 'String' as a sort name (parsed via parse_sort_name)."""
    tm = oxiz.TermManager()
    s = tm.mk_var("s", "String")
    assert s is not None


# --------------------------------------------------------------------------- #
# StringVal and TermManager string methods                                    #
# --------------------------------------------------------------------------- #

def test_string_val_at_module_level():
    """oxiz.StringVal(tm, s) creates a string-literal Term."""
    tm = oxiz.TermManager()
    t = oxiz.StringVal(tm, "hello")
    assert t is not None


def test_tm_mk_string_val():
    """TermManager.mk_string_val creates a string literal Term."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_string_val")
    t = tm.mk_string_val("world")
    assert t is not None


def test_tm_mk_string_lit():
    """TermManager.mk_string_lit is still present as an alias."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_string_lit")
    t = tm.mk_string_lit("foo")
    assert t is not None


def test_string_val_distinct_literals():
    """Two different literal values produce distinct term ids."""
    tm = oxiz.TermManager()
    a = tm.mk_string_val("alpha")
    b = tm.mk_string_val("beta")
    # Distinct literals must be different nodes
    assert a != b


def test_string_val_same_literal_dedup():
    """The same literal string yields the same (hash-consed) term."""
    tm = oxiz.TermManager()
    x = tm.mk_string_val("same")
    y = tm.mk_string_val("same")
    assert x == y


# --------------------------------------------------------------------------- #
# Concat / Length                                                              #
# --------------------------------------------------------------------------- #

def test_concat_at_module_level():
    """oxiz.Concat(tm, s1, s2) produces a Term."""
    tm = oxiz.TermManager()
    s1 = tm.mk_string_val("hello")
    s2 = tm.mk_string_val(" world")
    cat = oxiz.Concat(tm, s1, s2)
    assert cat is not None


def test_tm_mk_str_concat():
    """TermManager.mk_str_concat is present and works."""
    tm = oxiz.TermManager()
    s1 = tm.mk_string_val("a")
    s2 = tm.mk_string_val("b")
    assert hasattr(tm, "mk_str_concat")
    cat = tm.mk_str_concat(s1, s2)
    assert cat is not None


def test_length_at_module_level():
    """oxiz.Length(tm, s) produces a Term (integer-sorted)."""
    tm = oxiz.TermManager()
    s = tm.mk_string_val("hello")
    n = oxiz.Length(tm, s)
    assert n is not None


def test_tm_mk_str_length():
    """TermManager.mk_str_length alias is present."""
    tm = oxiz.TermManager()
    s = tm.mk_string_val("test")
    assert hasattr(tm, "mk_str_length")
    n = tm.mk_str_length(s)
    assert n is not None


def test_concat_and_length_are_distinct_terms():
    """Concat and Length create distinct term ids."""
    tm = oxiz.TermManager()
    s1 = tm.mk_string_val("foo")
    s2 = tm.mk_string_val("bar")
    cat = oxiz.Concat(tm, s1, s2)
    n = oxiz.Length(tm, s1)
    assert cat != n


# --------------------------------------------------------------------------- #
# Contains / PrefixOf / SuffixOf                                              #
# --------------------------------------------------------------------------- #

def test_contains_at_module_level():
    """oxiz.Contains(tm, s, sub) produces a boolean Term."""
    tm = oxiz.TermManager()
    s = tm.mk_string_val("hello world")
    sub = tm.mk_string_val("world")
    b = oxiz.Contains(tm, s, sub)
    assert b is not None


def test_tm_mk_str_contains():
    """TermManager.mk_str_contains is present."""
    tm = oxiz.TermManager()
    s = tm.mk_string_val("hello world")
    sub = tm.mk_string_val("hello")
    assert hasattr(tm, "mk_str_contains")
    b = tm.mk_str_contains(s, sub)
    assert b is not None


def test_prefix_of_at_module_level():
    """oxiz.PrefixOf(tm, pre, s) produces a boolean Term."""
    tm = oxiz.TermManager()
    pre = tm.mk_string_val("he")
    s = tm.mk_string_val("hello")
    b = oxiz.PrefixOf(tm, pre, s)
    assert b is not None


def test_suffix_of_at_module_level():
    """oxiz.SuffixOf(tm, suf, s) produces a boolean Term."""
    tm = oxiz.TermManager()
    suf = tm.mk_string_val("lo")
    s = tm.mk_string_val("hello")
    b = oxiz.SuffixOf(tm, suf, s)
    assert b is not None


def test_contains_prefix_suffix_are_distinct():
    """Contains, PrefixOf, SuffixOf over the same inputs produce different terms."""
    tm = oxiz.TermManager()
    s = tm.mk_var("s", "String")
    sub = tm.mk_string_val("x")
    c = oxiz.Contains(tm, s, sub)
    p = oxiz.PrefixOf(tm, sub, s)
    sf = oxiz.SuffixOf(tm, sub, s)
    assert c != p
    assert c != sf
    assert p != sf


# --------------------------------------------------------------------------- #
# Context integration                                                          #
# --------------------------------------------------------------------------- #

def test_context_string_const():
    """ctx.string_const(name) declares a string-sorted variable."""
    ctx = oxiz.Context()
    assert hasattr(ctx, "string_const")
    s = ctx.string_const("myStr")
    assert s is not None


def test_context_string_val():
    """ctx.string_val(text) creates a string literal with owner."""
    ctx = oxiz.Context()
    assert hasattr(ctx, "string_val")
    t = ctx.string_val("literal")
    assert t is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
