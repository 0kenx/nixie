# Nixie Python Bindings – z3-python Parity Matrix

Status as of version 0.3.1.

Ground truth: `nixie-py/src/lib.rs` (PyO3 module registration) and `nixie-py/src/` source files.

| z3 method / feature | nixie wrapper | status |
|---|---|---|
| `Bool(name)` / `ctx.bool_const(name)` | `Context.bool_const(name)` | ✅ supported |
| `Int(name)` / `ctx.int_const(name)` | `Context.int_const(name)` | ✅ supported |
| `Real(name)` / `ctx.real_const(name)` | `Context.real_const(name)` | ✅ supported |
| `BitVec(name, width)` / `ctx.bv_const(name, width)` | `Context.bv_const(name, width)` | ✅ supported |
| `Array(name, dom, rng)` | `nixie.ArraySort(dom, rng)`, the `"Array[D,R]"` sort string, `TermManager.mk_select` / `mk_store` | ✅ supported |
| `FP(name, sort)` / `FPSort(eb, sb)` | `nixie.FPSort(eb, sb)` / `nixie.FPVal(...)` / `fp_add`, `fp_sub`, `fp_mul`, `fp_div`; sort strings `"Float[eb,sb]"` and `"FP[eb,sb]"` | ✅ supported |
| `StringVal(s)` / string sort | `nixie.StringVal(s)` / `nixie.StringSort()`; `Concat`, `Length`, `Contains`, `PrefixOf`, `SuffixOf`; sort string `"String"` | ✅ supported |
| `ForAll(vars, body)` | `nixie.ForAll(vars, body)` / `TermManager.mk_forall` | ✅ supported |
| `Exists(vars, body)` | `nixie.Exists(vars, body)` / `TermManager.mk_exists` | ✅ supported |
| `Solver.check()` | `Solver.check(tm)` / `Solver.check_sat(tm)` | ✅ supported |
| `Solver.model()` | `Solver.model()` (typed) and `Solver.get_model(tm)` (string) | ✅ supported |
| `Solver.unsat_core()` | `Solver.unsat_core()` / `Solver.get_unsat_core()` | ✅ supported |
| `Optimizer.minimize(obj)` | `Optimizer.minimize(obj)` | ✅ supported |
| `Solver.push()` / `Solver.pop()` | `Solver.push()` / `Solver.pop(n=1)` | ✅ supported |
| `set_timeout(ms)` | `Solver.set_timeout(milliseconds)` | ✅ supported |
| `And(*args)` / `Or(*args)` / `Not(x)` | `nixie.And` / `nixie.Or` / `nixie.Not` | ✅ supported |
| `Implies(a, b)` | `nixie.Implies(a, b)` | ✅ supported |
| `If(cond, t, e)` | `nixie.If(cond, t, e)` | ✅ supported |
| `Solver.assert_and_track(expr, label)` | `Solver.assert_and_track(term, label, tm)` | ✅ supported |
| `set_option(key, value)` | `Solver.set_option(key, value)` | ✅ supported |

## Notes

- **Array**: `parse_sort_name()` accepts `"Array[D,R]"` (parsed iteratively, so arbitrarily deep nesting is safe), `nixie.ArraySort(dom, rng)` builds the sort directly, and `TermManager.mk_select` / `mk_store` build the AST nodes.
- **FP**: `parse_sort_name()` accepts `"Float[eb,sb]"` and `"FP[eb,sb]"`; `FPSort`, `FPVal`, the `PyFPRoundingMode` sentinel class, and `fp_add` / `fp_sub` / `fp_mul` / `fp_div` are exported at module level.
- **String**: `"String"` is registered in `parse_sort_name()`; `StringVal`, `StringSort`, `Concat`, `Length`, `Contains`, `PrefixOf`, `SuffixOf` are module-level functions, with the full `mk_str_*` family on `TermManager`.
- **ForAll / Exists**: `TermManager.mk_forall` / `mk_exists` take `(name, sort_name)` pairs plus a body; `nixie.ForAll` / `nixie.Exists` are the module-level z3-style wrappers.
- **Optimizer**: `Optimizer.push()` / `Optimizer.pop()` exist but take no arguments (z3-python's `pop()` also takes no arguments for Optimize).
- **Timeout for Optimizer**: not separately exposed; only `Solver.set_timeout()` is available.
