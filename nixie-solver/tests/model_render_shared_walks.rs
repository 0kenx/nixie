//! Two model-rendering walks are paid once per render, not once per row.
//!
//! * `(get-value (t1 … tn))` answered decision (67)'s gate – "does the
//!   asserted goal contain a quantifier" – before testing whether the term
//!   asked was a leaf, so Q queries on a quantifier-free goal of size G walked
//!   the whole goal Q times: Θ(QG).  2,048 asserted Booleans queried together
//!   spent 112 ms on the gate alone, where the whole script now takes
//!   7.3 ms with parsing and `check-sat`.  The leaf test comes first and the
//!   gate is computed at most once per request.
//! * `(get-model)`'s default-completion arm re-collected the conjunct-level
//!   `(= b φ)` definitions of the goal for every declared Boolean that
//!   reached it, so U unassigned rows over A conjuncts cost Θ(UA) before any
//!   definition was found – 107 ms for 2,048 asserted and 2,048 unconstrained
//!   Booleans, where most rows have no definition.  One render now shares one
//!   lazily built map (`model_fmt::DefinedBools`).
//!
//! What must not change is what these tests pin: every answer of a batch is
//! still the row `(get-model)` prints for the same term; a quantified goal's
//! compound queries still read the printed model; a defined Boolean is still
//! completed from its definition, in any declaration order, with its chains
//! resolved and its unevaluable definitions defaulted; and a definition
//! outside conjunct level is still no definition.

use std::collections::BTreeMap;

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

/// `(name, value)` for every constant row `(define-fun name () sort value)`
/// of a printed model, for the atomic sorts these tests use.
fn bool_rows(model: &str) -> BTreeMap<String, String> {
    model
        .lines()
        .filter_map(|line| {
            let rest = line.trim().strip_prefix("(define-fun ")?;
            let (name, rest) = rest.split_once(" () Bool ")?;
            Some((name.to_string(), rest.trim_end_matches(')').to_string()))
        })
        .collect()
}

/// Every top-level parenthesised group in `text`, in order.
fn parenthesized_groups(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut groups = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'(' {
            index += 1;
            continue;
        }
        let start = index;
        let mut depth = 0usize;
        while index < bytes.len() {
            match bytes[index] {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        index += 1;
                        break;
                    }
                }
                _ => {}
            }
            index += 1;
        }
        groups.push(&text[start..index]);
    }
    groups
}

/// `(key, value)` for every entry of a `(get-value …)` response: the term as
/// queried, and its answer (a bare symbol ends at the first space, a
/// compound term is the first balanced group).
fn get_value_entries(response: &str) -> Vec<(String, String)> {
    let [list] = parenthesized_groups(response)[..] else {
        panic!("the response is one parenthesised list: {response}");
    };
    parenthesized_groups(&list[1..list.len() - 1])
        .into_iter()
        .map(|entry| {
            let entry = &entry[1..entry.len() - 1];
            let split = if entry.starts_with('(') {
                let [key] = parenthesized_groups(entry)[..1] else {
                    panic!("a compound key is one parenthesised group: {entry}")
                };
                key.len()
            } else {
                entry.find(' ').expect("key, space, value")
            };
            (entry[..split].to_string(), entry[split + 1..].to_string())
        })
        .collect()
}

/// A quantifier-free goal of 2,048 asserted Booleans, queried together with
/// 2,048 unconstrained ones: the gate is walked once, and every answer is the
/// model's own row for the term.
#[test]
fn a_large_quantifier_free_batch_answers_with_the_model_rows() {
    let mut script = String::from("(set-logic QF_UF)\n");
    let mut asserted = Vec::new();
    for index in 0..2048 {
        script.push_str(&format!("(declare-const p{index} Bool)\n"));
        asserted.push(format!("p{index}"));
    }
    let mut unconstrained = Vec::new();
    for index in 0..2048 {
        script.push_str(&format!("(declare-const q{index} Bool)\n"));
        unconstrained.push(format!("q{index}"));
    }
    script.push_str(&format!("(assert (and {}))\n", asserted.join(" ")));
    script.push_str("(check-sat)\n(get-model)\n");
    // Leaves first, compounds last: the gate is needed by no leaf, so a
    // request of leaves alone never walks the goal, and the compounds at the
    // end walk it once between them.
    let mut batch = unconstrained.clone();
    batch.extend(asserted.iter().map(|p| format!("(not {p})")));
    batch.extend(asserted.iter().cloned());
    script.push_str(&format!("(get-value ({}))\n", batch.join(" ")));

    let output = run(&script);
    assert_eq!(output[0], "sat");
    let rows = bool_rows(&output[1]);
    assert_eq!(rows.len(), 4_096);
    for index in 0..2048 {
        assert_eq!(rows[&format!("p{index}")], "true");
        assert_eq!(rows[&format!("q{index}")], "false");
    }
    let entries = get_value_entries(&output[2]);
    assert_eq!(entries.len(), batch.len(), "one answer per queried term");
    for (key, value) in &entries {
        if let Some(name) = key.strip_prefix("(not ") {
            assert_eq!(value, "false", "the negation of an asserted Boolean");
            assert!(name.ends_with(')'));
        } else {
            assert_eq!(
                rows.get(key).map(String::as_str),
                Some(value.as_str()),
                "the answer for {key} is not the row `(get-model)` prints for it"
            );
        }
    }
}

/// A quantified goal: the gate still routes a compound query through the
/// printed model (decision (67)) while a leaf is answered from its row, in
/// a batch whose compounds come after its leaves.
#[test]
fn a_quantified_goal_still_reads_its_compound_queries_from_the_printed_model() {
    let output = run("(set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const q0 Bool)
        (declare-const q1 Bool)
        (assert (forall ((x Int)) (= (f x) (g x))))
        (assert (= (g 1) 7))
        (assert (= (f 2) 7))
        (check-sat)
        (get-model)
        (get-value (q0 q1 (+ (f 1) (g 2)) (f 1) (g 2) (>= (f 3) 0)))
        (get-value (q1 q0))");
    assert_eq!(output[0], "sat");
    let rows = bool_rows(&output[1]);
    assert_eq!(rows["q0"], "false");
    assert_eq!(rows["q1"], "false");
    let entries = get_value_entries(&output[2]);
    let answer = |key: &str| {
        entries
            .iter()
            .find(|(asked, _)| asked == key)
            .map(|(_, value)| value.as_str())
            .unwrap_or_else(|| panic!("no answer for {key}: {entries:?}"))
    };
    assert_eq!(answer("q0"), "false");
    assert_eq!(answer("q1"), "false");
    assert_eq!(answer("(f 1)"), "7");
    assert_eq!(answer("(g 2)"), "7");
    assert_eq!(answer("(+ (f 1) (g 2))"), "14");
    // A leaves-only batch over the same quantified goal answers from the rows.
    let leaves = get_value_entries(&output[3]);
    assert_eq!(
        leaves,
        vec![
            ("q1".to_string(), "false".to_string()),
            ("q0".to_string(), "false".to_string())
        ]
    );
}

/// Definition Booleans complete from their definitions under one shared
/// map: declared after a thousand unconstrained Booleans (so the first row
/// that reaches the completion arm has no definition), chained through one
/// another, one of them defined twice (the first definition wins), one
/// whose definition does not evaluate (the sort default), and one whose
/// "definition" sits under an `or` (no definition).  Every row is what the
/// per-row collection printed.
#[test]
fn definition_bools_complete_from_one_shared_map_in_any_declaration_order() {
    let mut script = String::from("(set-logic QF_NIA)\n");
    script.push_str("(declare-const x Int)\n");
    script.push_str("(assert (>= x 1))\n");
    script.push_str("(assert (<= x 5))\n");
    script.push_str("(declare-const b1 Bool)\n");
    script.push_str("(declare-const b2 Bool)\n");
    script.push_str("(declare-const twice Bool)\n");
    script.push_str("(declare-const unknown Bool)\n");
    script.push_str("(declare-const nested Bool)\n");
    let mut unconstrained = Vec::new();
    for index in 0..1000 {
        script.push_str(&format!("(declare-const u{index} Bool)\n"));
        unconstrained.push(format!("u{index}"));
    }
    script.push_str("(assert (= b1 (not (= x 0))))\n");
    script.push_str("(assert (= b2 (or b1 (not (= x 1)))))\n");
    script.push_str("(assert (= twice true))\n");
    script.push_str("(assert (= twice true))\n");
    // `(> (div x 2) 7)` does not evaluate to a definite truth under the
    // definition evaluator: `twice` is defined, `unknown` is left alone.
    script.push_str("(assert (= unknown (> (div x 2) 7)))\n");
    script.push_str("(assert (or nested (= x 1)))\n");
    for index in 0..1000 {
        script.push_str(&format!("(declare-const v{index} Bool)\n"));
        unconstrained.push(format!("v{index}"));
    }
    script.push_str("(assert (= (* x x) x))\n");
    script.push_str("(check-sat)\n(get-model)\n");
    let mut batch = vec!["b1".to_string(), "b2".to_string(), "twice".to_string()];
    batch.extend(unconstrained.iter().cloned());
    script.push_str(&format!("(get-value ({}))\n", batch.join(" ")));

    let output = run(&script);
    assert_eq!(output[0], "sat");
    let model = &output[1];
    assert!(
        model.contains("(define-fun x () Int 1)"),
        "x * x = x with 1 <= x <= 5 pins x = 1: {model}"
    );
    let rows = bool_rows(model);
    assert_eq!(rows["b1"], "true", "{model}");
    assert_eq!(rows["b2"], "true", "{model}");
    assert_eq!(rows["twice"], "true", "{model}");
    assert_eq!(rows["unknown"], "false", "{model}");
    assert_eq!(rows["nested"], "false", "{model}");
    for name in &unconstrained {
        assert_eq!(rows[name], "false", "{model}");
    }
    let entries = get_value_entries(&output[2]);
    assert_eq!(entries.len(), batch.len());
    for (key, value) in &entries {
        assert_eq!(
            rows.get(key).map(String::as_str),
            Some(value.as_str()),
            "the answer for {key} is not the row `(get-model)` prints for it"
        );
    }
}

/// A definition that evaluates `false` prints `false` for the same reason
/// the default would – and one whose definition chain runs through a
/// model-pinned numeric still resolves.
#[test]
fn a_false_definition_and_a_chain_over_model_values_complete_from_the_map() {
    let output = run("(set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const c Bool)
        (declare-const d Bool)
        (declare-const e Bool)
        (assert (= x 3))
        (assert (= c (= x 4)))
        (assert (= d c))
        (assert (= e (or d (= y 3))))
        (check-sat)
        (get-model)
        (get-value (c d e x y))");
    assert_eq!(output[0], "sat");
    let rows = bool_rows(&output[1]);
    assert_eq!(rows["c"], "false", "{}", output[1]);
    assert_eq!(rows["d"], "false", "{}", output[1]);
    // `y` is unconstrained, so `(= y 3)` does not evaluate: `e` is defaulted.
    assert_eq!(rows["e"], "false", "{}", output[1]);
    let entries = get_value_entries(&output[2]);
    let answer = |key: &str| {
        entries
            .iter()
            .find(|(asked, _)| asked == key)
            .map(|(_, value)| value.as_str())
            .unwrap_or_else(|| panic!("no answer for {key}: {entries:?}"))
    };
    assert_eq!(entries.len(), 5);
    assert_eq!(answer("c"), "false");
    assert_eq!(answer("d"), "false");
    assert_eq!(answer("e"), "false");
    assert_eq!(answer("x"), "3");
    // `y` is unconstrained: the query answers it with some numeral.
    assert!(answer("y").parse::<i64>().is_ok(), "{}", output[2]);
}
