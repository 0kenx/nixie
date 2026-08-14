//! Module-level theory combinators for strings, arrays, FP, and quantifiers.
//!
//! These mirror the z3-python top-level API, but every combinator here
//! additionally takes the owning `TermManager` as its *first* argument
//! (there is no implicit global context to resolve it from):
//!   `StringVal(tm, s)`, `Concat(tm, a, b)`, `Length(tm, s)`,
//!   `Contains(tm, s, sub)`, `PrefixOf(tm, pre, s)`, `SuffixOf(tm, suf, s)`,
//!   `FPSort(tm, eb, sb)`, `FPVal(tm, sign, exp, sig, sort)`,
//!   `fp_add(tm, rm, a, b)`, `fp_sub(...)`, `fp_mul(...)`, `fp_div(...)`,
//!   `FPRoundingMode` (sort object),
//!   `ArraySort(tm, index_sort, elem_sort)`,
//!   `ForAll(tm, vars, body)`, `Exists(tm, vars, body)`

// Allow non-snake-case names to mirror z3-python's capitalized API conventions.
#![allow(non_snake_case)]

use num_bigint::BigInt;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

use crate::term::{PySort, PyTerm, PyTermManager, parse_rounding_mode};

// ======== String theory combinators ========

/// Create a string literal Term.
///
/// Example::
///
///     s = oxiz.StringVal(tm, "hello")
///     # -- or if you want an owner for operator overloads --
///     s = ctx.string_val("hello")
#[pyfunction]
pub fn StringVal(tm: &PyTermManager, value: &str) -> PyTerm {
    let mut inner = tm.inner.borrow_mut();
    PyTerm::bare(inner.mk_string_lit(value))
}

/// Concatenate two string Terms.
///
/// Example::
///
///     result = oxiz.Concat(tm, s1, s2)
#[pyfunction]
pub fn Concat(tm: &PyTermManager, s1: &PyTerm, s2: &PyTerm) -> PyTerm {
    let mut inner = tm.inner.borrow_mut();
    PyTerm::bare(inner.mk_str_concat(s1.id, s2.id))
}

/// Return the length of a string Term as an integer Term.
///
/// Example::
///
///     n = oxiz.Length(tm, s)
#[pyfunction]
pub fn Length(tm: &PyTermManager, s: &PyTerm) -> PyTerm {
    let mut inner = tm.inner.borrow_mut();
    PyTerm::bare(inner.mk_str_len(s.id))
}

/// Test whether string Term ``s`` contains ``sub``, returning a boolean Term.
///
/// Example::
///
///     b = oxiz.Contains(tm, s, sub)
#[pyfunction]
pub fn Contains(tm: &PyTermManager, s: &PyTerm, sub: &PyTerm) -> PyTerm {
    let mut inner = tm.inner.borrow_mut();
    PyTerm::bare(inner.mk_str_contains(s.id, sub.id))
}

/// Test whether ``pre`` is a prefix of string Term ``s``, returning a boolean Term.
///
/// Example::
///
///     b = oxiz.PrefixOf(tm, pre, s)
#[pyfunction]
pub fn PrefixOf(tm: &PyTermManager, pre: &PyTerm, s: &PyTerm) -> PyTerm {
    let mut inner = tm.inner.borrow_mut();
    PyTerm::bare(inner.mk_str_prefixof(pre.id, s.id))
}

/// Test whether ``suf`` is a suffix of string Term ``s``, returning a boolean Term.
///
/// Example::
///
///     b = oxiz.SuffixOf(tm, suf, s)
#[pyfunction]
pub fn SuffixOf(tm: &PyTermManager, suf: &PyTerm, s: &PyTerm) -> PyTerm {
    let mut inner = tm.inner.borrow_mut();
    PyTerm::bare(inner.mk_str_suffixof(suf.id, s.id))
}

// ======== Floating-point sort and value constructors ========

/// Return the floating-point sort for a given (exponent-bits, significand-bits) format.
///
/// Mirrors z3-python's ``FPSort(eb, sb)``.
///
/// Example::
///
///     fp16 = oxiz.FPSort(tm, 5, 11)   # IEEE 754 half-precision
///     fp32 = oxiz.FPSort(tm, 8, 24)   # IEEE 754 single-precision
#[pyfunction]
pub fn FPSort(tm: &PyTermManager, eb: u32, sb: u32) -> PySort {
    let mut inner = tm.inner.borrow_mut();
    let sort_id = inner.sorts.float_sort(eb, sb);
    PySort {
        id: sort_id,
        eb: Some(eb),
        sb: Some(sb),
        is_array: false,
        is_string: false,
    }
}

/// Return the string sort object.
///
/// Example::
///
///     ss = oxiz.StringSort(tm)
#[pyfunction]
pub fn StringSort(tm: &PyTermManager) -> PySort {
    let mut inner = tm.inner.borrow_mut();
    let sort_id = inner.sorts.string_sort();
    PySort {
        id: sort_id,
        eb: None,
        sb: None,
        is_array: false,
        is_string: true,
    }
}

/// Return an array sort ``Array[index, element]``.
///
/// Mirrors z3-python's ``ArraySort(domain, range)``.
///
/// Example::
///
///     arr_sort = oxiz.ArraySort(tm, oxiz.IntSort(tm), oxiz.IntSort(tm))
#[pyfunction]
pub fn ArraySort(tm: &PyTermManager, index_sort: &PySort, elem_sort: &PySort) -> PySort {
    let mut inner = tm.inner.borrow_mut();
    let sort_id = inner.sorts.array(index_sort.id, elem_sort.id);
    PySort {
        id: sort_id,
        eb: None,
        sb: None,
        is_array: true,
        is_string: false,
    }
}

/// Return the integer sort object.
///
/// Example::
///
///     is_ = oxiz.IntSort(tm)
#[pyfunction]
pub fn IntSort(tm: &PyTermManager) -> PySort {
    let inner = tm.inner.borrow();
    PySort {
        id: inner.sorts.int_sort,
        eb: None,
        sb: None,
        is_array: false,
        is_string: false,
    }
}

/// Return the boolean sort object.
///
/// Example::
///
///     bs = oxiz.BoolSort(tm)
#[pyfunction]
pub fn BoolSort(tm: &PyTermManager) -> PySort {
    let inner = tm.inner.borrow();
    PySort {
        id: inner.sorts.bool_sort,
        eb: None,
        sb: None,
        is_array: false,
        is_string: false,
    }
}

/// Create a floating-point value Term from its components.
///
/// Args:
///     sign: Sign bit (``True`` = negative).
///     exp:  Bitvector exponent as a signed integer.
///     sig:  Bitvector significand as an unsigned integer.
///     sort: An ``FPSort`` object (created with :func:`FPSort`).
///     tm:   The :class:`TermManager` that should own the term.
///
/// Example::
///
///     sort = oxiz.FPSort(tm, 8, 24)
///     one  = oxiz.FPVal(tm, False, 127, 0, sort)   # +1.0 in fp32
#[pyfunction]
pub fn FPVal(
    tm: &PyTermManager,
    sign: bool,
    exp: i64,
    sig: u64,
    sort: &PySort,
) -> PyResult<PyTerm> {
    let (eb, sb) = match (sort.eb, sort.sb) {
        (Some(e), Some(s)) => (e, s),
        _ => {
            return Err(PyValueError::new_err(
                "FPVal: the 'sort' argument must be an FPSort (created with oxiz.FPSort(tm, eb, sb))",
            ));
        }
    };
    let mut inner = tm.inner.borrow_mut();
    let id = inner.mk_fp_lit(sign, BigInt::from(exp), BigInt::from(sig), eb, sb);
    Ok(PyTerm::bare(id))
}

/// An opaque token representing the FP rounding-mode "sort" (for z3-python parity).
///
/// In z3-python ``FPRoundingMode()`` is a sort; here it is a simple sentinel
/// object.  Use the string forms ``"RNE"``, ``"RNA"``, ``"RTP"``, ``"RTN"``,
/// ``"RTZ"`` with FP operations.
#[pyclass(name = "FPRoundingMode", from_py_object)]
#[derive(Clone)]
pub struct PyFPRoundingMode;

#[pymethods]
impl PyFPRoundingMode {
    #[new]
    fn new() -> Self {
        Self
    }

    fn __repr__(&self) -> &'static str {
        "FPRoundingMode()"
    }
}

// ======== Floating-point arithmetic combinators ========

/// Floating-point addition.
///
/// Args:
///     rm:  Rounding mode string: ``"RNE"``, ``"RNA"``, ``"RTP"``, ``"RTN"``, or ``"RTZ"``.
///     lhs: Left operand (FP Term).
///     rhs: Right operand (FP Term).
///     tm:  TermManager.
///
/// Example::
///
///     r = oxiz.fp_add(tm, "RNE", a, b)
#[pyfunction]
pub fn fp_add(tm: &PyTermManager, rm: &str, lhs: &PyTerm, rhs: &PyTerm) -> PyResult<PyTerm> {
    let rounding = parse_rounding_mode(rm)?;
    let mut inner = tm.inner.borrow_mut();
    Ok(PyTerm::bare(inner.mk_fp_add(rounding, lhs.id, rhs.id)))
}

/// Floating-point subtraction.
#[pyfunction]
pub fn fp_sub(tm: &PyTermManager, rm: &str, lhs: &PyTerm, rhs: &PyTerm) -> PyResult<PyTerm> {
    let rounding = parse_rounding_mode(rm)?;
    let mut inner = tm.inner.borrow_mut();
    Ok(PyTerm::bare(inner.mk_fp_sub(rounding, lhs.id, rhs.id)))
}

/// Floating-point multiplication.
#[pyfunction]
pub fn fp_mul(tm: &PyTermManager, rm: &str, lhs: &PyTerm, rhs: &PyTerm) -> PyResult<PyTerm> {
    let rounding = parse_rounding_mode(rm)?;
    let mut inner = tm.inner.borrow_mut();
    Ok(PyTerm::bare(inner.mk_fp_mul(rounding, lhs.id, rhs.id)))
}

/// Floating-point division.
#[pyfunction]
pub fn fp_div(tm: &PyTermManager, rm: &str, lhs: &PyTerm, rhs: &PyTerm) -> PyResult<PyTerm> {
    let rounding = parse_rounding_mode(rm)?;
    let mut inner = tm.inner.borrow_mut();
    Ok(PyTerm::bare(inner.mk_fp_div(rounding, lhs.id, rhs.id)))
}

// ======== Quantifier combinators ========

/// Construct a universally-quantified formula.
///
/// Args:
///     vars: List of ``(name, sort_name)`` pairs for the bound variables.
///           Sort name examples: ``"Int"``, ``"Bool"``, ``"Real"``,
///           ``"BitVec[32]"``, ``"Float[8,24]"``, ``"String"``,
///           ``"Array[Int,Bool]"``.
///     body: The body Term.
///     tm:   The TermManager that owns the term.
///
/// Example::
///
///     x = ctx.int_const("x")
///     body = x > ctx.int_val(0)
///     fml = oxiz.ForAll(ctx.tm, [("x", "Int")], body)
#[pyfunction]
pub fn ForAll(tm: &PyTermManager, vars: Vec<(String, String)>, body: &PyTerm) -> PyResult<PyTerm> {
    let mut inner = tm.inner.borrow_mut();
    let parsed: Vec<(String, ::oxiz::core::SortId)> = vars
        .iter()
        .map(|(name, sort_name)| {
            crate::term::parse_sort_name(&mut inner, sort_name).map(|sid| (name.clone(), sid))
        })
        .collect::<PyResult<_>>()?;
    let refs: Vec<(&str, ::oxiz::core::SortId)> =
        parsed.iter().map(|(n, s)| (n.as_str(), *s)).collect();
    Ok(PyTerm::bare(inner.mk_forall(refs, body.id)))
}

/// Construct an existentially-quantified formula.
///
/// Args:
///     vars: List of ``(name, sort_name)`` pairs for the bound variables.
///     body: The body Term.
///     tm:   The TermManager that owns the term.
///
/// Example::
///
///     x = ctx.int_const("x")
///     body = x > ctx.int_val(0)
///     fml = oxiz.Exists(ctx.tm, [("x", "Int")], body)
#[pyfunction]
pub fn Exists(tm: &PyTermManager, vars: Vec<(String, String)>, body: &PyTerm) -> PyResult<PyTerm> {
    let mut inner = tm.inner.borrow_mut();
    let parsed: Vec<(String, ::oxiz::core::SortId)> = vars
        .iter()
        .map(|(name, sort_name)| {
            crate::term::parse_sort_name(&mut inner, sort_name).map(|sid| (name.clone(), sid))
        })
        .collect::<PyResult<_>>()?;
    let refs: Vec<(&str, ::oxiz::core::SortId)> =
        parsed.iter().map(|(n, s)| (n.as_str(), *s)).collect();
    Ok(PyTerm::bare(inner.mk_exists(refs, body.id)))
}
