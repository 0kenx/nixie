//! Model printing functionality

use crate::ast::{model::Model, model::ModelValue};
#[allow(unused_imports)]
use crate::prelude::*;
use core::fmt::Write;

use super::basic::Printer;

impl<'a> Printer<'a> {
    /// Print a model in SMT-LIB2 format
    pub fn print_model(&self, model: &Model) -> String {
        let mut buf = String::new();
        self.write_model(&mut buf, model);
        buf
    }

    /// Write a model in SMT-LIB2 format
    pub fn write_model(&self, w: &mut impl Write, model: &Model) {
        let _ = writeln!(w, "(model");

        // Print variable assignments as define-fun declarations
        for (term_id, value) in model.assignments() {
            if let Some(term) = self.manager.get(*term_id)
                && let crate::ast::TermKind::Var(name_spur) = term.kind
            {
                let var_name = self.manager.resolve_str(name_spur);
                let _ = write!(w, "  (define-fun {} () ", var_name);
                self.write_sort(w, term.sort);
                let _ = write!(w, " ");
                self.write_model_value(w, value);
                let _ = writeln!(w, ")");
            }
        }

        // Print function interpretations
        for (name_spur, func_interp) in model.functions() {
            self.write_function_interpretation(
                w,
                self.manager.resolve_str(*name_spur),
                func_interp,
            );
        }

        let _ = writeln!(w, ")");
    }

    /// Write one `define-fun` for a function interpretation.
    ///
    /// Reconstructs parameter names/sorts and the return sort from the
    /// table entries' own `ModelValue`s (a `ModelValue` always determines
    /// its sort), and encodes the table as a chain of `ite`s over equality
    /// tests on the parameters, falling through to the default value. This
    /// used to just emit the literal (syntactically invalid) text `...)`
    /// for any function with table entries, and a hardcoded `Int` sort
    /// (regardless of the value's actual sort) for the nullary case.
    fn write_function_interpretation(
        &self,
        w: &mut impl Write,
        func_name: &str,
        func_interp: &crate::ast::model::FunctionInterpretation,
    ) {
        let arity = func_interp
            .table()
            .first()
            .map_or(0, |(args, _)| args.len());
        let param_names: Vec<String> = (0..arity).map(|i| format!("x!{i}")).collect();

        let mut param_decls = String::new();
        if let Some((args, _)) = func_interp.table().first() {
            for (name, val) in param_names.iter().zip(args.iter()) {
                if !param_decls.is_empty() {
                    param_decls.push(' ');
                }
                let _ = write!(param_decls, "({name} {})", self.model_value_sort(val));
            }
        }

        let return_sort = func_interp
            .table()
            .first()
            .map(|(_, r)| self.model_value_sort(r))
            .or_else(|| {
                func_interp
                    .default_value()
                    .map(|d| self.model_value_sort(d))
            })
            // No table entries and no default: nothing tells us the real
            // return sort, so this nullary function's body is left as `0`
            // under an honestly-unknown-but-syntactically-valid `Int` sort
            // rather than silently guessing a possibly-wrong non-Int sort.
            .unwrap_or_else(|| "Int".to_string());

        let _ = write!(
            w,
            "  (define-fun {func_name} ({param_decls}) {return_sort} "
        );

        let mut open_ites = 0usize;
        for (args, result) in func_interp.table() {
            let cond = if args.len() == 1 {
                format!("(= {} {})", param_names[0], self.model_value_repr(&args[0]))
            } else {
                let eqs: Vec<String> = param_names
                    .iter()
                    .zip(args.iter())
                    .map(|(name, v)| format!("(= {name} {})", self.model_value_repr(v)))
                    .collect();
                format!("(and {})", eqs.join(" "))
            };
            let _ = write!(w, "(ite {cond} {} ", self.model_value_repr(result));
            open_ites += 1;
        }

        match func_interp.default_value() {
            Some(default) => {
                let _ = write!(w, "{}", self.model_value_repr(default));
            }
            None => {
                // No fallback value is known for arguments outside the
                // table; `0` keeps the term well-sorted (every sort we can
                // name here has a `0`/`false`-like zero element) rather than
                // leaving the s-expression unterminated.
                let _ = write!(w, "{}", self.zero_value_for_sort(&return_sort));
            }
        }

        for _ in 0..open_ites {
            let _ = write!(w, ")");
        }
        let _ = writeln!(w, ")");
    }

    /// The SMT-LIB sort name that `value` inhabits.
    fn model_value_sort(&self, value: &ModelValue) -> String {
        match value {
            ModelValue::Bool(_) => "Bool".to_string(),
            ModelValue::Int(_) => "Int".to_string(),
            ModelValue::Real(_) => "Real".to_string(),
            ModelValue::BitVec { width, .. } => format!("(_ BitVec {width})"),
            ModelValue::Uninterpreted { sort, .. } => {
                let mut s = String::new();
                self.write_sort(&mut s, *sort);
                s
            }
        }
    }

    /// A syntactically valid zero/default term for `sort_str`, used only
    /// when no default value is available to fall back on.
    fn zero_value_for_sort(&self, sort_str: &str) -> String {
        match sort_str {
            "Bool" => "false".to_string(),
            "Real" => "0.0".to_string(),
            s if s.starts_with("(_ BitVec") => format!(
                "(_ bv0 {})",
                s.trim_start_matches("(_ BitVec ").trim_end_matches(')')
            ),
            _ => "0".to_string(),
        }
    }

    /// Write a model value
    fn write_model_value(&self, w: &mut impl Write, value: &ModelValue) {
        let _ = write!(w, "{}", self.model_value_repr(value));
    }

    /// Render a model value as an SMT-LIB term.
    fn model_value_repr(&self, value: &ModelValue) -> String {
        match value {
            ModelValue::Bool(b) => b.to_string(),
            ModelValue::Int(n) => n.to_string(),
            ModelValue::Real(r) => r.to_string(),
            ModelValue::BitVec { value, width } => {
                // `BigInt::from(BigUint)` is exact at any width, so a
                // 128-bit (or wider) value prints at its full declared
                // width instead of being narrowed to its low 64 bits.
                super::format_bitvec_literal(&num_bigint::BigInt::from(value.clone()), *width)
            }
            ModelValue::Uninterpreted { sort, id } => format!("uninterp_{}_{}", sort.0, id),
        }
    }
}

#[cfg(test)]
mod wide_bitvec_tests {
    use crate::ast::TermManager;
    use crate::ast::model::{Model, ModelValue};
    use crate::smtlib::printer::basic::Printer;
    use num_bigint::BigUint;
    use num_traits::One;

    /// A 128-bit value prints at its full declared width, not narrowed to the
    /// low 64 bits it happens to share with a much smaller value.
    #[test]
    fn wide_bitvec_value_prints_at_full_width() {
        let mut manager = TermManager::new();
        let bv128 = manager.sorts.bitvec(128);
        let x = manager.mk_var("x", bv128);

        let mut model = Model::new();
        // 2^64 + 5: low 64 bits are `5`, which is what a `u64` payload kept.
        model.assign_bitvec_big(x, (BigUint::one() << 64u32) + BigUint::from(5u32), 128);

        let printer = Printer::new(&manager);
        let output = printer.print_model(&model);

        assert!(output.contains("(define-fun x () (_ BitVec 128) "));
        // 128 bits is 32 hex digits, and the `1` sits in digit 16 from the end.
        assert!(
            output.contains("#x00000000000000010000000000000005"),
            "wide value was narrowed: {output}"
        );
    }

    /// A width that is not a multiple of 4 prints in binary, zero-padded to
    /// the full declared width.
    #[test]
    fn wide_non_nibble_width_prints_zero_padded_binary() {
        let manager = TermManager::new();
        let printer = Printer::new(&manager);
        let value = ModelValue::from_bitvec_bits(BigUint::one() << 70u32, 71);
        let repr = printer.model_value_repr(&value);

        assert_eq!(repr.len(), 2 + 71);
        assert!(repr.starts_with("#b1"));
        assert_eq!(repr.matches('1').count(), 1);
    }

    /// The sort annotation follows the declared width, not the value's own
    /// bit length.
    #[test]
    fn wide_bitvec_sort_annotation_uses_declared_width() {
        let manager = TermManager::new();
        let printer = Printer::new(&manager);
        let value = ModelValue::from_bitvec_bits(BigUint::from(1u32), 256);
        assert_eq!(printer.model_value_sort(&value), "(_ BitVec 256)");
        assert_eq!(printer.model_value_repr(&value).len(), 2 + 64);
    }
}
