"""Tests for array theory support in OxiZ Python bindings.

Covers:
- ArraySort(index_sort, elem_sort, tm)  — module-level sort constructor
- mk_var with "Array[Int,Int]" sort string
- mk_select / mk_store on TermManager
- Read-over-write sanity (AST structure tests only; no solver invocation)
"""

import oxiz
import pytest


# --------------------------------------------------------------------------- #
# Sort constructors                                                            #
# --------------------------------------------------------------------------- #

def test_array_sort_exists():
    """ArraySort is now exposed at module level."""
    assert hasattr(oxiz, "ArraySort")


def test_int_sort_exists():
    """IntSort is exposed at module level."""
    assert hasattr(oxiz, "IntSort")


def test_bool_sort_exists():
    """BoolSort is exposed at module level."""
    assert hasattr(oxiz, "BoolSort")


def test_array_sort_int_int():
    """ArraySort(IntSort, IntSort, tm) returns a Sort object."""
    tm = oxiz.TermManager()
    int_s = oxiz.IntSort(tm)
    arr_s = oxiz.ArraySort(tm, int_s, int_s)
    assert arr_s is not None
    assert arr_s.is_fp is False


def test_array_sort_int_bool():
    """ArraySort over Int index, Bool range."""
    tm = oxiz.TermManager()
    int_s = oxiz.IntSort(tm)
    bool_s = oxiz.BoolSort(tm)
    arr_s = oxiz.ArraySort(tm, int_s, bool_s)
    assert arr_s is not None


def test_array_sort_same_config_dedup():
    """Two identical ArraySort calls produce equal sort objects."""
    tm = oxiz.TermManager()
    int_s = oxiz.IntSort(tm)
    s1 = oxiz.ArraySort(tm, int_s, int_s)
    s2 = oxiz.ArraySort(tm, int_s, int_s)
    assert s1 == s2


# --------------------------------------------------------------------------- #
# mk_var with Array sort string                                               #
# --------------------------------------------------------------------------- #

def test_mk_var_array_sort_string():
    """mk_var accepts 'Array[Int,Int]' as a sort name."""
    tm = oxiz.TermManager()
    arr = tm.mk_var("arr", "Array[Int,Int]")
    assert arr is not None


def test_mk_var_array_bool_sort_string():
    """mk_var accepts 'Array[Int,Bool]' as a sort name."""
    tm = oxiz.TermManager()
    arr = tm.mk_var("flags", "Array[Int,Bool]")
    assert arr is not None


# --------------------------------------------------------------------------- #
# mk_select / mk_store                                                        #
# --------------------------------------------------------------------------- #

def test_tm_has_mk_select():
    """mk_select is exposed on TermManager."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_select")


def test_tm_has_mk_store():
    """mk_store is exposed on TermManager."""
    tm = oxiz.TermManager()
    assert hasattr(tm, "mk_store")


def test_select_on_typed_array_var():
    """mk_select works on a properly typed array variable."""
    tm = oxiz.TermManager()
    arr = tm.mk_var("myArr", "Array[Int,Int]")
    idx = tm.mk_int(0)
    sel = tm.mk_select(arr, idx)
    assert sel is not None


def test_store_on_typed_array_var():
    """mk_store works on a properly typed array variable."""
    tm = oxiz.TermManager()
    arr = tm.mk_var("myArr2", "Array[Int,Int]")
    idx = tm.mk_int(1)
    val = tm.mk_int(42)
    stored = tm.mk_store(arr, idx, val)
    assert stored is not None


def test_select_store_produce_distinct_terms():
    """Repeated select/store calls on different indices produce distinct terms."""
    tm = oxiz.TermManager()
    arr = tm.mk_var("arr2", "Array[Int,Int]")
    idx0 = tm.mk_int(0)
    idx1 = tm.mk_int(1)
    v10 = tm.mk_int(10)
    v20 = tm.mk_int(20)

    sel0 = tm.mk_select(arr, idx0)
    sel1 = tm.mk_select(arr, idx1)
    stored0 = tm.mk_store(arr, idx0, v10)
    stored1 = tm.mk_store(arr, idx1, v20)

    assert sel0 != sel1
    assert stored0 != stored1
    assert sel0 != stored0


def test_select_on_store_result():
    """mk_select on a mk_store result produces a distinct term (read-over-write AST node)."""
    tm = oxiz.TermManager()
    arr = tm.mk_var("base", "Array[Int,Int]")
    idx = tm.mk_int(5)
    val = tm.mk_int(99)
    arr2 = tm.mk_store(arr, idx, val)
    result = tm.mk_select(arr2, idx)
    assert result is not None
    # The select node is different from the store node
    assert result != arr2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
