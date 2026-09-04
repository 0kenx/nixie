//! Core solver operations: lifecycle, check-sat, execute, push/pop, cancel.

use crate::WasmSolver;
use crate::async_utils;
use crate::string_utils;
use crate::{WasmError, WasmErrorKind};
use wasm_bindgen::prelude::*;

/// Split an SMT-LIB2 script into complete top-level command strings.
///
/// Each returned chunk is a balanced parenthesized `(...)` s-expression
/// (plus any leading comments/whitespace immediately preceding it), so a
/// script can be chunked for progressive/async execution without ever
/// cutting a command in half the way naive line-based slicing does. This
/// mirrors what `nixie_core`'s SMT-LIB tokenizer treats as syntax:
///
/// - Line comments (`;` to end of line) are passed through verbatim.
/// - String literals (`"..."`), with `""` as an escaped quote inside one,
///   are scanned as opaque spans so parentheses inside them don't affect
///   nesting depth.
/// - Quoted symbols (`|...|`) are likewise scanned as opaque spans.
///
/// Any trailing, never-balanced content (e.g. malformed input, or bare
/// non-parenthesized text) is returned as a final chunk so `execute()`
/// can surface a proper parse error instead of the text being silently
/// dropped.
fn split_into_commands(script: &str) -> Vec<String> {
    let mut commands = Vec::new();
    let mut current = String::new();
    let mut depth: i32 = 0;
    let mut chars = script.chars().peekable();
    let mut in_string = false;
    let mut in_quoted_symbol = false;

    while let Some(c) = chars.next() {
        if in_string {
            current.push(c);
            if c == '"' {
                // SMT-LIB2 escapes a quote inside a string literal by
                // doubling it ("" -> a literal ").
                if chars.peek() == Some(&'"') {
                    if let Some(next) = chars.next() {
                        current.push(next);
                    }
                } else {
                    in_string = false;
                }
            }
            continue;
        }
        if in_quoted_symbol {
            current.push(c);
            if c == '|' {
                in_quoted_symbol = false;
            }
            continue;
        }
        match c {
            ';' => {
                // Line comment: consume through end of line verbatim.
                current.push(c);
                for nc in chars.by_ref() {
                    current.push(nc);
                    if nc == '\n' {
                        break;
                    }
                }
            }
            '"' => {
                in_string = true;
                current.push(c);
            }
            '|' => {
                in_quoted_symbol = true;
                current.push(c);
            }
            '(' => {
                depth += 1;
                current.push(c);
            }
            ')' => {
                depth -= 1;
                current.push(c);
                if depth <= 0 {
                    let trimmed = current.trim();
                    if !trimmed.is_empty() {
                        commands.push(trimmed.to_string());
                    }
                    current.clear();
                    depth = 0; // guard against stray/unbalanced closers
                }
            }
            _ => current.push(c),
        }
    }

    let trailing = current.trim();
    if !trailing.is_empty() {
        commands.push(trailing.to_string());
    }

    commands
}

#[wasm_bindgen]
impl WasmSolver {
    /// Create a new solver instance
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// ```
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        use nixie_solver::Context;
        Self {
            ctx: Context::new(),
            last_result: None,
            cancelled: false,
        }
    }

    /// Execute an SMT-LIB2 script and return the results
    ///
    /// This method takes a complete SMT-LIB2 script as a string and executes it,
    /// returning the output as a string. This is useful for batch operations or
    /// when you have a complete SMT-LIB2 file to execute.
    ///
    /// # Parameters
    ///
    /// * `script` - An SMT-LIB2 script string
    ///
    /// # Returns
    ///
    /// The output of the script execution as a string
    ///
    /// # Errors
    ///
    /// Returns an error if the script contains syntax errors or invalid commands
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// const script = `
    ///   (set-logic QF_LIA)
    ///   (declare-const x Int)
    ///   (assert (> x 0))
    ///   (check-sat)
    /// `;
    /// const result = solver.execute(script);
    /// console.log(result); // outputs: sat
    /// ```
    #[wasm_bindgen]
    pub fn execute(&mut self, script: &str) -> Result<JsValue, JsValue> {
        if string_utils::is_effectively_empty(script) {
            return Err(
                WasmError::new(WasmErrorKind::InvalidInput, "Script cannot be empty").into(),
            );
        }

        match self.ctx.execute_script(script) {
            Ok(output) => {
                let result = string_utils::join_lines(&output);
                Ok(JsValue::from_str(&result))
            }
            Err(e) => Err(WasmError::new(
                WasmErrorKind::ParseError,
                format!("Failed to execute script: {}", e),
            )
            .into()),
        }
    }

    /// Set the logic for the solver
    ///
    /// This sets the SMT logic to use for the solver. Common logics include:
    /// - `QF_UF` - Quantifier-free uninterpreted functions
    /// - `QF_LIA` - Quantifier-free linear integer arithmetic
    /// - `QF_LRA` - Quantifier-free linear real arithmetic
    /// - `QF_BV` - Quantifier-free bitvectors
    /// - `ALL` - All supported theories
    ///
    /// # Parameters
    ///
    /// * `logic` - The SMT-LIB2 logic name
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// solver.setLogic("QF_LIA");
    /// ```
    #[wasm_bindgen(js_name = setLogic)]
    pub fn set_logic(&mut self, logic: &str) {
        let _ = self.ctx.set_logic(logic);
    }

    /// Check satisfiability of the current assertions
    ///
    /// This method checks whether the current set of assertions is satisfiable.
    /// It returns one of three possible results:
    /// - `"sat"` - The assertions are satisfiable
    /// - `"unsat"` - The assertions are unsatisfiable
    /// - `"unknown"` - The solver could not determine satisfiability
    ///
    /// After calling this method with a "sat" result, you can call `getModel()`
    /// to get a satisfying assignment. With an "unsat" result, you can call
    /// `getUnsatCore()` to get the unsatisfiable core.
    ///
    /// # Returns
    ///
    /// A string indicating the satisfiability result: "sat", "unsat", or "unknown"
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// solver.setLogic("QF_UF");
    /// solver.declareConst("p", "Bool");
    /// solver.assertFormula("p");
    /// const result = solver.checkSat();
    /// if (result === "sat") {
    ///   const model = solver.getModel();
    ///   console.log(model);
    /// }
    /// ```
    #[wasm_bindgen(js_name = checkSat)]
    pub fn check_sat(&mut self) -> String {
        // Honor a pending `cancel()` request. Previously this flag was only
        // ever consulted by the chunked `executeAsync`/`executeWithProgress`
        // loops; a cancelled solver's `checkSat()`/`checkSatAsync()` (the
        // latter simply delegates to this method) would run the full solve
        // to completion regardless, silently ignoring the documented
        // cancellation contract. Report the honest "we did not actually
        // solve this" answer -- "unknown" -- instead of either fabricating
        // "sat"/"unsat" or running an operation the caller asked to abort.
        // The flag is sticky (matching `execute_async`'s existing
        // interpretation) until `reset()` clears it.
        if self.cancelled {
            self.last_result = Some("unknown".to_string());
            return "unknown".to_string();
        }

        let result = match self.ctx.check_sat() {
            nixie_solver::SolverResult::Sat => "sat",
            nixie_solver::SolverResult::Unsat => "unsat",
            nixie_solver::SolverResult::Unknown => "unknown",
        };
        self.last_result = Some(result.to_string());
        result.to_string()
    }

    /// Check satisfiability under a set of assumptions
    ///
    /// This method checks whether the current assertions are satisfiable under
    /// the given temporary assumptions. The assumptions are only used for this
    /// single check and do not modify the assertion stack.
    ///
    /// This is useful for:
    /// - Incremental solving with different scenarios
    /// - Computing minimal unsatisfiable cores
    /// - Exploring different branches without push/pop overhead
    ///
    /// # Parameters
    ///
    /// * `assumptions` - An array of SMT-LIB2 boolean expressions to assume
    ///
    /// # Returns
    ///
    /// A string indicating the satisfiability result: "sat", "unsat", or "unknown"
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Any assumption is empty or malformed
    /// - Any assumption contains syntax errors
    /// - Any assumption references undeclared variables
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// solver.setLogic("QF_UF");
    /// solver.declareConst("p", "Bool");
    /// solver.declareConst("q", "Bool");
    /// solver.assertFormula("(or p q)");
    ///
    /// // Check if satisfiable assuming p is true
    /// const result1 = solver.checkSatAssuming(["p"]);
    /// console.log(result1); // "sat"
    ///
    /// // Check if satisfiable assuming both p and q are false
    /// const result2 = solver.checkSatAssuming(["(not p)", "(not q)"]);
    /// console.log(result2); // "unsat"
    /// ```
    #[wasm_bindgen(js_name = checkSatAssuming)]
    pub fn check_sat_assuming(&mut self, assumptions: Vec<String>) -> Result<String, JsValue> {
        if assumptions.is_empty() {
            return Err(WasmError::new(
                WasmErrorKind::InvalidInput,
                "Assumptions array cannot be empty",
            )
            .into());
        }

        // Validate all assumptions are non-empty
        for (idx, assumption) in assumptions.iter().enumerate() {
            if assumption.trim().is_empty() {
                return Err(WasmError::new(
                    WasmErrorKind::InvalidInput,
                    format!("Assumption at index {} cannot be empty", idx),
                )
                .into());
            }
        }

        // Build check-sat-assuming command
        let assumptions_str = assumptions.join(" ");
        let script = format!("(check-sat-assuming ({}))", assumptions_str);

        match self.ctx.execute_script(&script) {
            Ok(output) => {
                let result = output.join("");
                // Normalize the result
                let normalized = match result.trim() {
                    "sat" => "sat",
                    "unsat" => "unsat",
                    _ => "unknown",
                };
                self.last_result = Some(normalized.to_string());
                Ok(normalized.to_string())
            }
            Err(e) => Err(WasmError::new(
                WasmErrorKind::ParseError,
                format!("Failed to check-sat with assumptions: {}", e),
            )
            .into()),
        }
    }

    /// Push a new context level
    ///
    /// Creates a new backtracking point. Assertions and declarations made after
    /// pushing can be undone by calling `pop()`. This is useful for trying
    /// different sets of constraints without resetting the entire solver.
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// solver.declareConst("x", "Int");
    /// solver.assertFormula("(> x 0)");
    /// solver.push(); // Create backtracking point
    /// solver.assertFormula("(< x 5)");
    /// console.log(solver.checkSat()); // sat
    /// solver.pop(); // Undo the (< x 5) assertion
    /// ```
    #[wasm_bindgen]
    pub fn push(&mut self) {
        self.ctx.push();
    }

    /// Pop a context level
    ///
    /// Backtracks to the previous context level, undoing all assertions and
    /// declarations made since the last `push()` call.
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// solver.declareConst("x", "Int");
    /// solver.push();
    /// solver.assertFormula("(> x 10)");
    /// solver.pop(); // Remove the (> x 10) assertion
    /// ```
    #[wasm_bindgen]
    pub fn pop(&mut self) {
        self.ctx.pop();
    }

    /// Reset the solver completely
    ///
    /// Clears all assertions, declarations, options, and state, returning the
    /// solver to its initial state as if newly constructed.
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// solver.declareConst("x", "Int");
    /// solver.assertFormula("(> x 0)");
    /// solver.reset(); // Clear everything
    /// // Solver is now empty, must redeclare and reassert
    /// ```
    #[wasm_bindgen]
    pub fn reset(&mut self) {
        self.ctx.reset();
        self.last_result = None;
        self.cancelled = false;
    }

    /// Reset only assertions, keeping declarations and options
    ///
    /// Removes all assertions but keeps variable and function declarations
    /// and solver options. This is useful for solving multiple related
    /// problems with the same variables.
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// solver.declareConst("x", "Int");
    /// solver.assertFormula("(> x 0)");
    /// solver.checkSat();
    /// solver.resetAssertions(); // Keep x declared, remove assertions
    /// solver.assertFormula("(< x 0)"); // Can still use x
    /// ```
    #[wasm_bindgen(js_name = resetAssertions)]
    pub fn reset_assertions(&mut self) {
        self.ctx.reset_assertions();
        self.last_result = None;
    }

    /// Cancel the current solver operation
    ///
    /// Sets a cancellation flag that can be checked during long-running
    /// operations. Note: This is a hint to the solver and may not take
    /// effect immediately.
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// // In a web worker or with async operations
    /// setTimeout(() => solver.cancel(), 5000); // Cancel after 5 seconds
    /// const result = await solver.checkSatAsync();
    /// ```
    #[wasm_bindgen]
    pub fn cancel(&mut self) {
        self.cancelled = true;
    }

    /// Check if the solver has been cancelled
    ///
    /// # Returns
    ///
    /// `true` if cancellation has been requested, `false` otherwise
    #[wasm_bindgen(js_name = isCancelled)]
    pub fn is_cancelled(&self) -> bool {
        self.cancelled
    }

    /// Check satisfiability asynchronously
    ///
    /// This is an async version of `checkSat()` that allows the browser to remain
    /// responsive during long-running solver operations. It returns a Promise that
    /// resolves to the satisfiability result.
    ///
    /// # Returns
    ///
    /// A Promise that resolves to a string: "sat", "unsat", or "unknown"
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// solver.setLogic("QF_LIA");
    /// solver.declareConst("x", "Int");
    /// solver.assertFormula("(> x 0)");
    ///
    /// const result = await solver.checkSatAsync();
    /// console.log(result); // "sat"
    ///
    /// if (result === "sat") {
    ///   const model = solver.getModel();
    ///   console.log(model);
    /// }
    /// ```
    #[wasm_bindgen(js_name = checkSatAsync)]
    pub async fn check_sat_async(&mut self) -> String {
        // Yield to event loop before starting
        async_utils::yield_now().await;

        // Perform the actual check-sat operation
        let result = self.check_sat();

        // Yield again after completion to ensure UI responsiveness
        async_utils::yield_now().await;

        result
    }

    /// Execute an SMT-LIB2 script asynchronously
    ///
    /// This is an async version of `execute()` that allows the browser to remain
    /// responsive during execution of complex scripts.
    ///
    /// # Parameters
    ///
    /// * `script` - An SMT-LIB2 script string
    ///
    /// # Returns
    ///
    /// A Promise that resolves to the output string
    ///
    /// # Errors
    ///
    /// Returns a Promise that rejects if the script contains errors
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// const script = `
    ///   (set-logic QF_LIA)
    ///   (declare-const x Int)
    ///   (assert (> x 0))
    ///   (check-sat)
    ///   (get-model)
    /// `;
    /// const result = await solver.executeAsync(script);
    /// console.log(result);
    /// ```
    #[wasm_bindgen(js_name = executeAsync)]
    pub async fn execute_async(&mut self, script: String) -> Result<JsValue, JsValue> {
        // Yield to event loop before starting
        async_utils::yield_now().await;

        // Split the script into complete top-level commands (never mid
        // s-expression) so chunking for responsiveness cannot break
        // multi-line commands the way naive line-slicing did.
        let commands = split_into_commands(&script);
        let total_commands = commands.len();

        // For small scripts (< 10 commands), just execute directly.
        if total_commands < 10 {
            let result = self.execute(&script);
            async_utils::yield_now().await;
            return result;
        }

        // For larger scripts, yield periodically.
        // Process script in chunks of complete commands to maintain
        // responsiveness without ever splitting a command in half.
        let chunk_size = 20; // Process 20 commands before yielding
        let mut result_parts = Vec::new();

        for (i, chunk) in commands.chunks(chunk_size).enumerate() {
            // Yield every 5 chunks (every ~100 commands)
            if i > 0 && i % 5 == 0 {
                async_utils::yield_now().await;

                // Check for cancellation
                if self.cancelled {
                    return Err(JsValue::from_str("Operation cancelled"));
                }
            }

            // Execute this chunk of complete commands.
            let chunk_script = chunk.join("\n");
            match self.execute(&chunk_script) {
                Ok(output) => {
                    if let Some(s) = output.as_string()
                        && !s.trim().is_empty()
                    {
                        result_parts.push(s);
                    }
                }
                Err(e) => return Err(e),
            }
        }

        // Yield before returning final result
        async_utils::yield_now().await;

        Ok(JsValue::from_str(&result_parts.join("\n")))
    }

    /// Execute an SMT-LIB2 script asynchronously with progress callbacks
    ///
    /// This method is similar to `executeAsync()` but also accepts a callback function
    /// that will be invoked periodically with progress updates. This is useful for
    /// long-running operations where you want to show progress to the user.
    ///
    /// # Parameters
    ///
    /// * `script` - An SMT-LIB2 script string
    /// * `progress_callback` - Optional callback function that receives progress updates
    ///   The callback receives two arguments: (commands_processed, total_commands),
    ///   counted in complete top-level SMT-LIB2 commands rather than lines,
    ///   since a single command may span multiple lines.
    ///
    /// # Returns
    ///
    /// A Promise that resolves to the output string
    ///
    /// # Errors
    ///
    /// Returns a Promise that rejects if the script contains errors
    ///
    /// # Example (JavaScript)
    ///
    /// ```javascript
    /// const solver = new WasmSolver();
    /// const script = `
    ///   (set-logic QF_LIA)
    ///   (declare-const x Int)
    ///   (assert (> x 0))
    ///   (check-sat)
    ///   (get-model)
    /// `;
    ///
    /// const result = await solver.executeWithProgress(script, (current, total) => {
    ///   console.log(`Progress: ${current}/${total} lines processed`);
    ///   document.getElementById('progress').innerText =
    ///     `${Math.round(current / total * 100)}%`;
    /// });
    /// console.log(result);
    /// ```
    #[wasm_bindgen(js_name = executeWithProgress)]
    pub async fn execute_with_progress(
        &mut self,
        script: String,
        progress_callback: Option<js_sys::Function>,
    ) -> Result<JsValue, JsValue> {
        // Yield to event loop before starting
        async_utils::yield_now().await;

        // Split the script into complete top-level commands (never mid
        // s-expression) so chunking for progress reporting cannot break
        // multi-line commands the way naive line-slicing did.
        let commands = split_into_commands(&script);
        let total_commands = commands.len();

        // For small scripts, just execute directly
        if total_commands < 10 {
            let result = self.execute(&script);
            if let Some(callback) = progress_callback {
                let this = JsValue::NULL;
                let _ = callback.call2(
                    &this,
                    &JsValue::from(total_commands),
                    &JsValue::from(total_commands),
                );
            }
            async_utils::yield_now().await;
            return result;
        }

        // For larger scripts, process in chunks of complete commands with
        // progress updates.
        let chunk_size = 20;
        let mut result_parts = Vec::new();
        let mut commands_processed = 0;

        for (i, chunk) in commands.chunks(chunk_size).enumerate() {
            // Yield every 5 chunks
            if i > 0 && i % 5 == 0 {
                async_utils::yield_now().await;

                // Check for cancellation
                if self.cancelled {
                    return Err(JsValue::from_str("Operation cancelled"));
                }
            }

            // Execute this chunk of complete commands.
            let chunk_script = chunk.join("\n");
            match self.execute(&chunk_script) {
                Ok(output) => {
                    if let Some(s) = output.as_string()
                        && !s.trim().is_empty()
                    {
                        result_parts.push(s);
                    }
                }
                Err(e) => return Err(e),
            }

            // Update progress
            commands_processed += chunk.len();
            if let Some(ref callback) = progress_callback {
                let this = JsValue::NULL;
                let _ = callback.call2(
                    &this,
                    &JsValue::from(commands_processed),
                    &JsValue::from(total_commands),
                );
            }
        }

        // Final progress update
        if let Some(callback) = progress_callback {
            let this = JsValue::NULL;
            let _ = callback.call2(
                &this,
                &JsValue::from(total_commands),
                &JsValue::from(total_commands),
            );
        }

        // Yield before returning
        async_utils::yield_now().await;

        Ok(JsValue::from_str(&result_parts.join("\n")))
    }
}

/// Regression tests for the `cancel()`/`checkSat()` interaction (audit
/// finding: "cancel() flag is never observed by checkSat/checkSatAsync").
/// `checkSat()` returns a plain `String` (never touches `js_sys`/`JsValue`),
/// so -- unlike most of this crate's `Result<_, JsValue>`-returning API --
/// it can run natively without a real wasm32/JS engine.
#[cfg(test)]
mod cancel_tests {
    use crate::WasmSolver;

    #[test]
    fn check_sat_honors_a_pending_cancellation() {
        let mut solver = WasmSolver::new();
        solver.set_logic("QF_UF");
        solver
            .declare_const("p", "Bool")
            .expect("declare_const should succeed");
        solver
            .assert_formula("p")
            .expect("assert_formula should succeed");

        // Without cancellation, this trivially satisfiable problem reports sat.
        assert_eq!(solver.check_sat(), "sat");

        solver.cancel();
        assert!(solver.is_cancelled());
        // A cancelled solver must not silently report "sat"/"unsat" for a
        // check it was asked not to perform.
        assert_eq!(solver.check_sat(), "unknown");
        // The cancellation is sticky across repeated checkSat() calls...
        assert_eq!(solver.check_sat(), "unknown");
    }

    #[test]
    fn reset_clears_a_pending_cancellation() {
        let mut solver = WasmSolver::new();
        solver.set_logic("QF_UF");
        solver.declare_const("p", "Bool").unwrap();
        solver.assert_formula("p").unwrap();

        solver.cancel();
        assert_eq!(solver.check_sat(), "unknown");

        // ...until an explicit reset() clears it, matching `cancelled`'s
        // existing documented reset-clears-it contract.
        solver.reset();
        assert!(!solver.is_cancelled());
        solver.set_logic("QF_UF");
        solver.declare_const("p", "Bool").unwrap();
        solver.assert_formula("p").unwrap();
        assert_eq!(solver.check_sat(), "sat");
    }
}

#[cfg(test)]
mod split_into_commands_tests {
    use super::split_into_commands;

    #[test]
    fn splits_simple_single_line_commands() {
        let script = "(set-logic QF_LIA)\n(declare-const x Int)\n(check-sat)";
        let commands = split_into_commands(script);
        assert_eq!(commands.len(), 3);
        assert_eq!(commands[0], "(set-logic QF_LIA)");
        assert_eq!(commands[2], "(check-sat)");
    }

    /// Regression: a command whose parentheses span many lines must stay
    /// intact as a single chunk, even when the script is much longer than
    /// the old fixed 20-line chunk boundary.
    fn multiline_assert(depth: usize) -> String {
        // Build `(assert (and true (and true (and true ... ))))` deep
        // enough that a naive 20-line chunker would previously have cut
        // straight through the middle of it.
        let mut s = String::from("(assert\n  (and true\n");
        for _ in 0..depth {
            s.push_str("    (and true\n");
        }
        for _ in 0..depth {
            s.push_str("    )\n");
        }
        s.push_str("  )\n)");
        s
    }

    #[test]
    fn keeps_deeply_nested_multiline_command_intact() {
        let assertion = multiline_assert(30); // spans well over 20 lines
        let script = format!(
            "(set-logic QF_LIA)\n(declare-const x Int)\n{}\n(check-sat)",
            assertion
        );
        let commands = split_into_commands(&script);
        assert_eq!(commands.len(), 4);
        assert_eq!(commands[2], assertion);
        assert_eq!(commands[3], "(check-sat)");
    }

    #[test]
    fn ignores_parens_inside_string_literals() {
        let script = r#"(assert (= s "a ( b ) c"))(check-sat)"#;
        let commands = split_into_commands(script);
        assert_eq!(commands.len(), 2);
        assert_eq!(commands[0], r#"(assert (= s "a ( b ) c"))"#);
    }

    #[test]
    fn handles_escaped_quotes_in_string_literals() {
        let script = r#"(assert (= s "a ""quoted"" b"))(check-sat)"#;
        let commands = split_into_commands(script);
        assert_eq!(commands.len(), 2);
    }

    #[test]
    fn ignores_parens_inside_quoted_symbols() {
        let script = "(declare-const |a ( weird ) name| Int)(check-sat)";
        let commands = split_into_commands(script);
        assert_eq!(commands.len(), 2);
    }

    #[test]
    fn ignores_parens_inside_line_comments() {
        let script = "; a comment with ( unbalanced parens\n(check-sat)";
        let commands = split_into_commands(script);
        assert_eq!(commands.len(), 1);
        assert!(commands[0].ends_with("(check-sat)"));
    }
}
