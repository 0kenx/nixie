//! A batched `(get-value (t1 … tn))` reads ONE rendering of the model.
//!
//! A bare constant the model left unassigned is answered with the row
//! `(get-model)` prints for it – sort default, `@uc_S_n` witness or array
//! chain.  That row used to be read back by rendering the *whole* model per
//! queried term, so a batch of n unconstrained constants built n² rows: 0.37 s
//! of CPU at n = 512 and 2.85 s at n = 1024, against 8 ms for printing the
//! same 1,024-row model with `(get-model)` (`Context::get_model`).  The rows
//! describe the model rather than the term asked, so
//! `model_fmt::get_value::ModelRows` now renders them once per request, at
//! the first term that needs one.
//!
//! What that must not change is what these tests pin: every answer of a batch
//! is still the row `(get-model)` prints for the same constant, the
//! uninterpreted-sort witnesses keep the numbering of the WHOLE declaration
//! list (constants outside the batch included), and a term that is not a
//! declared constant still takes its own reading.  Both query paths are
//! covered – the structural one, and the legacy one a set-sorted term
//! switches the whole request to.

use std::collections::BTreeMap;

use nixie_solver::Context;

fn run(script: &str) -> Vec<String> {
    let mut ctx = Context::new();
    ctx.execute_script(script)
        .expect("script should parse and run")
}

/// `(name, value)` for every constant row `(define-fun name () sort value)`
/// of a printed model, in printed order.
///
/// A compound sort – `(_ BitVec 3)`, `(Array Int Int)` – is one balanced
/// parenthesis group; a quoted sort name is one `|…|` group; so the value is
/// whatever follows it up to the row's closing parenthesis.
fn model_rows(model: &str) -> Vec<(String, String)> {
    let mut rows = Vec::new();
    for line in model.lines().map(str::trim) {
        let Some(rest) = line.strip_prefix("(define-fun ") else {
            continue;
        };
        // A function interpretation carries parameters; a constant's list is empty.
        let Some((name, rest)) = rest.split_once(" () ") else {
            continue;
        };
        let sort_end = if let Some(quoted) = rest.strip_prefix('|') {
            quoted.find('|').map(|position| position + 2)
        } else if rest.starts_with('(') {
            let mut depth = 0usize;
            rest.bytes()
                .position(|byte| match byte {
                    b'(' => {
                        depth += 1;
                        false
                    }
                    b')' => {
                        depth -= 1;
                        depth == 0
                    }
                    _ => false,
                })
                .map(|position| position + 1)
        } else {
            rest.find(' ')
        };
        let Some(sort_end) = sort_end else {
            continue;
        };
        let Some(value) = rest[sort_end..]
            .strip_prefix(' ')
            .and_then(|rest| rest.strip_suffix(')'))
        else {
            continue;
        };
        rows.push((name.to_string(), value.to_string()));
    }
    rows
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
/// queried, and its answer.
fn get_value_entries(response: &str) -> Vec<(String, String)> {
    let [list] = parenthesized_groups(response)[..] else {
        panic!("the response is one parenthesised list: {response}");
    };
    parenthesized_groups(&list[1..list.len() - 1])
        .into_iter()
        .map(|entry| {
            let (key, value) = split_key_value(&entry[1..entry.len() - 1]);
            (key.to_string(), value.to_string())
        })
        .collect()
}

/// An entry's `key value` halves: a bare symbol ends at the first space, a
/// compound term is the first balanced group (a compound value is a group of
/// its own).
fn split_key_value(entry: &str) -> (&str, &str) {
    if entry.starts_with('(') {
        let groups = parenthesized_groups(entry);
        let Some((key, _)) = groups.split_first() else {
            panic!("a compound key is one parenthesised group: {entry}");
        };
        let value = entry[key.len()..]
            .strip_prefix(' ')
            .expect("key, space, value");
        (key, value)
    } else {
        entry.split_once(' ').expect("key, space, value")
    }
}

/// Declares `count` unconstrained constants of each sort in `sorts` – named
/// `k0…`, `p0…`, `v0…`, `u0…`, `a0…` by sort – and returns their names in
/// declaration order.
fn declare(script: &mut String, count: usize, sorts: &[&str]) -> Vec<String> {
    let mut names = Vec::new();
    for sort in sorts {
        let slug = match *sort {
            "Int" => "k",
            "Bool" => "p",
            "(_ BitVec 3)" => "v",
            "U" => "u",
            "(Array Int Int)" => "a",
            other => panic!("no name prefix for {other}"),
        };
        for index in 0..count {
            let name = format!("{slug}{index}");
            script.push_str(&format!("(declare-const {name} {sort})\n"));
            names.push(name);
        }
    }
    names
}

/// One request over a batch of unconstrained constants of every row-rendering
/// sort: each answer is the model's own row for that constant, and the
/// uninterpreted-sort witnesses are distinct and numbered in declaration
/// order – the first declared constant of the sort holds `@uc_U_0`.
#[test]
fn a_batch_of_unconstrained_constants_answers_with_the_model_rows() {
    let mut script = String::from("(set-logic QF_AUFLIA)\n(declare-sort U 0)\n");
    let sorts = ["Int", "Bool", "(_ BitVec 3)", "U", "(Array Int Int)"];
    // 512 of each sort: the batch size at which the per-term rendering built
    // 262,144 rows for one request.
    let names = declare(&mut script, 512, &sorts);
    // Read at one array so its row is a store chain rather than the sort default.
    script.push_str("(assert (= (select a0 3) 7))\n");
    script.push_str("(check-sat)\n(get-model)\n");
    script.push_str(&format!("(get-value ({}))\n", names.join(" ")));

    let output = run(&script);
    assert_eq!(output[0], "sat", "nothing is constrained beyond one read");
    let rows: BTreeMap<String, String> = model_rows(&output[1]).into_iter().collect();
    assert_eq!(
        rows.len(),
        names.len(),
        "one model row per declared constant"
    );
    assert_eq!(rows["a0"], "(store ((as const (Array Int Int)) 0) 3 7)");

    let entries = get_value_entries(&output[2]);
    assert_eq!(entries.len(), names.len(), "one answer per queried term");
    for (name, value) in &entries {
        assert_eq!(
            rows.get(name).map(String::as_str),
            Some(value.as_str()),
            "the answer for {name} is not the row `(get-model)` prints for it"
        );
    }

    // The witnesses are a property of the declaration list: distinct constants
    // of an unconstrained sort are distinct elements, numbered from the first
    // declared one, whatever the batch asks for.
    let witnesses: Vec<&String> = entries
        .iter()
        .filter(|(name, _)| name.starts_with('u'))
        .map(|(_, value)| value)
        .collect();
    assert_eq!(witnesses.len(), 512);
    assert_eq!(witnesses[0], "@uc_U_0");
    assert_eq!(witnesses[511], "@uc_U_511");
}

/// A constant left out of the batch still holds its place in the witness
/// numbering, and a term that is not a declared constant in the same batch
/// takes its own reading without disturbing the constant rows.
#[test]
fn witness_numbering_counts_the_whole_declaration_list_not_the_batch() {
    let output = run("(set-logic QF_UF)
         (declare-sort U 0)
         (declare-const a U)
         (declare-const b U)
         (declare-const c U)
         (assert (distinct a b))
         (declare-const k Int)
         (declare-fun f (U) Int)
         (assert (= (f a) 1))
         (check-sat)
         (get-model)
         (get-value (c (= a b) k (+ k 1) (f b) a))");
    assert_eq!(output[0], "sat");
    let rows: BTreeMap<String, String> = model_rows(&output[1]).into_iter().collect();
    let entries = get_value_entries(&output[2]);
    let answer = |key: &str| {
        entries
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value.as_str())
            .unwrap_or_else(|| panic!("no answer for {key}: {entries:?}"))
    };
    // `a` and `b` are declared first and are distinct, so `c` is the third element.
    assert_eq!(rows["a"], "@uc_U_0");
    assert_eq!(rows["b"], "@uc_U_1");
    assert_eq!(answer("c"), "@uc_U_2");
    assert_eq!(answer("c"), rows["c"]);
    assert_eq!(answer("a"), rows["a"]);
    assert_eq!(answer("k"), rows["k"]);
    assert_eq!(answer("(= a b)"), "false");
    assert_eq!(answer("(+ k 1)"), "1");
    assert_eq!(answer("(f b)"), "1");
}

/// The legacy query path – the one a set-sorted term switches the whole
/// request to – answers the batch's scalar constants from the same rows.
#[test]
fn the_legacy_query_path_answers_a_batch_from_the_model_rows() {
    let mut script = String::from("(set-logic QF_LIA)\n");
    let names = declare(&mut script, 256, &["Int", "Bool"]);
    script.push_str("(declare-const s (Set Int))\n(assert (= (card s) 0))\n");
    script.push_str("(check-sat)\n(get-model)\n");
    script.push_str(&format!(
        "(get-value ({} s (set.union s (set.singleton 1))))\n",
        names.join(" ")
    ));

    let output = run(&script);
    assert_eq!(output[0], "sat");
    let rows: BTreeMap<String, String> = model_rows(&output[1]).into_iter().collect();
    let entries = get_value_entries(&output[2]);
    assert_eq!(
        entries.len(),
        names.len() + 2,
        "one answer per queried term"
    );
    for (name, value) in entries.iter().filter(|(name, _)| !name.contains('(')) {
        if name == "s" {
            continue;
        }
        assert_eq!(
            rows.get(name).map(String::as_str),
            Some(value.as_str()),
            "the answer for {name} is not the row `(get-model)` prints for it"
        );
    }
    assert_eq!(rows["s"], "(as set.empty (Set Int))");
}
