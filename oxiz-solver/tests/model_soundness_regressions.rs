//! Model-soundness regression guards — a `sat` must be backed by a model that
//! satisfies the formula.
//!
//! Distinct from `known_unsound_regressions.rs` (verdict soundness: never
//! `sat` on a z3-unsat instance). These pin **model soundness**: when the
//! solver answers `sat`, the model it emits must actually satisfy the
//! assertions. A model that contradicts the formula is a wrong answer dressed
//! as a right one — invisible to verdict-only tests, found by the z3-validated
//! differential harness.
//!
//! Two independent defects were found this way (see
//! `bench/differential/VALIDATED_RESCORE.md`) and are pinned here:
//!
//! * **Construction** (`Solver::build_model`): the emitted model violates the
//!   formula on a *correct* `sat` verdict. z3 rejects `asserts ∧ model`.
//!   **2 confirmed instances** (DLX1C0 QF_UFIDL; 1659 QF_NIA), pinned
//!   `#[ignore]`d below. (An earlier run counted 4 — `21.lp`/`3.lp` were a
//!   validator quoting bug in the harness, since fixed; their models are valid.)
//! * **Evaluator** (`Model::eval`, behind `Context::eval_in_model`): on a
//!   *correct* model it false-alarms (reports an assertion unsatisfied that
//!   z3 confirms is satisfied) — so `(get-value)`/`(get-model)` and the CLI's
//!   `--validate-model` are unreliable. Pinned `#[ignore]`d below (iso_brn1083).
//!
//! The two were disambiguated with z3 as an independent oracle AND with
//! declaration-accurate symbol quoting in the validator (the quoting bug that
//! false-flagged `21.lp`/`3.lp` is the cautionary tale: a validator artifact
//! that looked exactly like a construction defect until re-checked). They are
//! in different components (`build_model` vs `Model::eval`) and fixing one does
//! not fix the other.
//!
//! Tests skip (pass) when the `smt-lib/` corpus or `z3` is unavailable, so CI
//! without the corpus/z3 is not broken; CI that cares about these guards must
//! provision both.

use oxiz_solver::{Context, SolverResult};

const TIMEOUT_MS: u64 = 10_000;

/// True if `z3` is runnable on PATH.
fn z3_available() -> bool {
    std::process::Command::new("z3")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok()
}

/// Read a corpus file relative to the workspace root, or `None` if absent.
fn read_corpus(rel: &str) -> Option<String> {
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../");
    std::fs::read_to_string(format!("{root}{rel}")).ok()
}

/// Strip a trailing `(check-sat)`/`(exit)` so an appended `(check-sat)`
/// `(get-model)` is actually parsed (`execute_script` breaks on `Exit`).
fn strip_trailing_checksat(text: &str) -> &str {
    match text.rfind("(check-sat)") {
        Some(i) => &text[..i],
        None => text,
    }
}

/// Solve `script` and, on `sat`, return the emitted model text. The script is
/// expected to be the file body with `(check-sat)`/`(exit)` already stripped;
/// this appends its own `(check-sat)` + `(get-model)`.
fn solve_get_model(script_body: &str) -> (SolverResult, Option<String>) {
    let mut ctx = Context::new();
    ctx.set_timeout_ms(TIMEOUT_MS);
    let probe = format!("{script_body}\n(check-sat)\n(get-model)\n");
    let outputs = ctx.execute_script(&probe).unwrap_or_default();
    let mut verdict = SolverResult::Unknown;
    let mut model: Option<String> = None;
    let mut last_sat_idx: Option<usize> = None;
    for (i, o) in outputs.iter().enumerate() {
        match o.trim() {
            "sat" => {
                verdict = SolverResult::Sat;
                last_sat_idx = Some(i);
            }
            "unsat" => verdict = SolverResult::Unsat,
            "unknown" => verdict = SolverResult::Unknown,
            _ => {}
        }
    }
    if verdict == SolverResult::Sat {
        if let Some(idx) = last_sat_idx {
            // Everything after the final `sat` line is the model response.
            model = Some(outputs[idx + 1..].join("\n"));
        }
    }
    (verdict, model)
}

/// Crude scan of a model response for nullary `(define-fun NAME () SORT VAL)`,
/// returning `(name, sort, value)` triples. Test-only; no SMT parser needed.
fn nullary_defines(model: &str) -> Vec<(String, String, String)> {
    let mut out = Vec::new();
    let marker = "(define-fun ";
    let mut rest = model;
    while let Some(start) = rest.find(marker) {
        rest = &rest[start + marker.len()..];
        // NAME runs to the next space
        let name_end = match rest.find(|c: char| c.is_whitespace()) {
            Some(e) => e,
            None => break,
        };
        let name = rest[..name_end].to_string();
        let after_name = rest[name_end..].trim_start();
        // Expect "()" for nullary; if not nullary, skip to next define-fun.
        let Some(rest2) = after_name.strip_prefix("()") else {
            continue;
        };
        let rest2 = rest2.trim_start();
        // SORT runs to the next whitespace.
        let sort_end = match rest2.find(|c: char| c.is_whitespace()) {
            Some(e) => e,
            None => break,
        };
        let sort = rest2[..sort_end].to_string();
        let after_sort = rest2[sort_end..].trim_start();
        // VALUE runs to the next ')'.
        let val_end = match after_sort.find(')') {
            Some(e) => e,
            None => break,
        };
        let value = after_sort[..val_end].trim().to_string();
        out.push((name, sort, value));
    }
    out
}

/// Declared nullary symbols, keyed by the *unquoted* name -> the EXACT token
/// the file uses (incl. SMT-LIB `|...|` quoting). A model pin must use the
/// file's exact token or it references a disconnected fresh symbol — pinning
/// `hc(18,17)` bare while the file declares `|hc(18,17)|` makes z3 parse the
/// pin as the application `hc (18 17)` and return a spurious verdict. This is
/// the harness quoting bug that once false-flagged 21.lp/3.lp as bad models.
fn declared_nullary_tokens(orig: &str) -> std::collections::HashMap<String, String> {
    let mut decl = std::collections::HashMap::new();
    for ln in orig.lines() {
        let t = ln.trim_start();
        let inner = if let Some(r) = t.strip_prefix("(declare-fun ") {
            r.strip_suffix(')').unwrap_or(r)
        } else if let Some(r) = t.strip_prefix("(declare-const ") {
            r.strip_suffix(')').unwrap_or(r)
        } else {
            continue;
        };
        let mut it = inner.split_whitespace();
        let Some(tok) = it.next() else { continue };
        // nullary fun: the next token must be "()"; const has no args marker.
        let next = it.next();
        let nullary = next == Some("()");
        if nullary || t.starts_with("(declare-const ") {
            decl.insert(tok.trim_matches('|').to_string(), tok.to_string());
        }
    }
    decl
}

/// Build `(asserts ∧ model-pins)` and ask z3. Returns:
///   `Some(true)`  — model consistent with the assertions (good),
///   `Some(false)` — model contradicts the assertions (BAD),
///   `None`        — z3 unavailable.
///
/// Each nullary define-fun is pinned to its value with the file's EXACT
/// declared token (declaration-accurate quoting); model names not present as
/// declared nullary symbols are skipped. Function models are skipped (only
/// top-level constants are pinned): this can only make the check *lenient*,
/// never a false `false`, because `(asserts ∧ pinned-constants)` unsat already
/// implies no function extension rescues the formula — see
/// `bench/differential/VALIDATED_RESCORE.md`.
fn model_validates(orig: &str, model: &str) -> Option<bool> {
    if !z3_available() {
        return None;
    }
    let mut head = strip_trailing_checksat(orig).to_string();
    let decl = declared_nullary_tokens(orig);
    let declared: std::collections::HashSet<&str> =
        decl.values().map(String::as_str).collect();
    let mut extra_decl: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut pins = Vec::new();
    for (name, sort, value) in nullary_defines(model) {
        let key = name.trim_matches('|');
        let Some(tok) = decl.get(key) else {
            continue; // not a declared nullary user symbol
        };
        let mut rest = value.as_str();
        while let Some(at) = rest.find('@').or_else(|| rest.find('!')) {
            let tail = &rest[at + 1..];
            let end = tail
                .find(|c: char| !c.is_alphanumeric() && c != '_')
                .unwrap_or(tail.len());
            let ident = format!("{}{}", &rest[at..at + 1], &tail[..end]);
            if !declared.contains(ident.as_str()) && !extra_decl.contains(&ident) {
                extra_decl.insert(ident.clone());
                head.push_str(&format!("\n(declare-const {ident} {sort})"));
            }
            rest = &tail[end..];
        }
        pins.push(format!("(assert (= {tok} {value}))"));
    }
    head.push_str("\n");
    head.push_str(&pins.join("\n"));
    head.push_str("\n(check-sat)\n");
    let out = std::process::Command::new("z3")
        .arg("-in")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .ok()
        .and_then(|mut c| {
            use std::io::Write;
            c.stdin.as_mut()?.write_all(head.as_bytes()).ok()?;
            c.wait_with_output().ok()
        });
    let stdout = out.and_then(|o| String::from_utf8(o.stdout).ok())?;
    for line in stdout.lines().rev() {
        match line.trim() {
            "sat" => return Some(true),
            "unsat" => return Some(false),
            _ => {}
        }
    }
    None
}

/// Assert that `rel` solves to `sat` and that the emitted model satisfies the
/// assertions (z3: `asserts ∧ model` is `sat`). `#[ignore]`d until
/// `build_model` is fixed for that instance.
fn assert_model_valid(label: &str, rel: &str) {
    let Some(orig) = read_corpus(rel) else {
        eprintln!("skipping {label}: corpus file absent");
        return;
    };
    let body = strip_trailing_checksat(&orig);
    let (verdict, model) = solve_get_model(body);
    assert_eq!(
        verdict,
        SolverResult::Sat,
        "{label}: expected sat (z3 says sat), got {verdict:?}"
    );
    let Some(model) = model else {
        panic!("{label}: sat but no model emitted");
    };
    match model_validates(&orig, &model) {
        Some(true) => {}
        Some(false) => panic!(
            "{label}: emitted model contradicts the assertions (z3: asserts∧model = unsat) — \
             build_model produced an unsatisfying witness for a correct sat verdict"
        ),
        None => eprintln!("skipping {label}: z3 unavailable"),
    }
}

// ─── Defect B: build_model emits a model that violates the formula ────────
// Both solve to a CORRECT `sat` (z3 agrees sat) but emit a model z3 rejects.
// `#[ignore]`d until the construction defect is fixed; un-ignore is the
// acceptance criterion.
//
// (An earlier version of this file also pinned 21.lp and 3.lp here. Those
// were a HARNESS validator quoting bug — the models are valid; removed.)

#[ignore = "build_model construction defect: DLX1C0 (QF_UFIDL) emits negative \
            Int values (impl.fdType=-4 …) where z3's model is non-negative; \
            z3 rejects asserts∧model. The sat verdict is correct; the witness \
            is not. Un-ignore when build_model produces a model that satisfies \
            the assertions for this instance."]
#[test]
fn dlx1c0_model_satisfies_assertions() {
    assert_model_valid(
        "DLX1C0",
        "smt-lib/non-incremental/QF_UFIDL/UCLID-pred/DLX/DLX1C0.smt2",
    );
}

#[ignore = "build_model construction defect: 1659 (QF_NIA, VeryMax/SAT14) emits \
            a model z3 rejects (482/482 declared symbols pinned, declaration- \
            accurate quoting). Correct sat, wrong witness. Un-ignore when fixed."]
#[test]
fn verymax_1659_model_satisfies_assertions() {
    assert_model_valid(
        "1659",
        "smt-lib/non-incremental/QF_NIA/20170427-VeryMax/SAT14/1659.smt2",
    );
}

// ─── Defect A: Model::eval false-alarms on a CORRECT model ────────────────
// iso_brn1083 (QF_UF) solves to a CORRECT sat whose model z3 ACCEPTS — so this
// non-ignored test asserts the model really is good. The `#[ignore]`d test
// below it pins the separate evaluator defect: `Context::eval_in_model`
// (Model::eval) reports 5 of 19 assertions as not-true under that correct
// model. Un-ignore when Model::eval correctly reduces equalities over
// uninterpreted-sort witnesses.

#[test]
fn iso_brn1083_model_is_actually_valid() {
    // Guards against regression of the *opposite* kind: if someone "fixes" the
    // evaluator by downgrading models, this test catches a correct model being
    // wrongly rejected. Currently the model IS valid (z3 accepts).
    let Some(orig) =
        read_corpus("smt-lib/non-incremental/QF_UF/QG-classification/qg5/iso_brn1083.smt2")
    else {
        eprintln!("skipping iso_brn1083: corpus file absent");
        return;
    };
    let (verdict, model) = solve_get_model(strip_trailing_checksat(&orig));
    assert_eq!(verdict, SolverResult::Sat);
    match model_validates(&orig, &model.expect("sat must emit a model")) {
        Some(true) => {}
        Some(false) => panic!("iso_brn1083: model that z3 previously accepted is now rejected"),
        None => eprintln!("skipping iso_brn1083: z3 unavailable"),
    }
}

#[ignore = "Model::eval evaluator defect: iso_brn1083's model is correct (z3 \
            accepts it — see iso_brn1083_model_is_actually_valid) but \
            Context::eval_in_model reports assertions as not-true. This makes \
            (get-value)/(get-model) and the CLI's --validate-model unreliable \
            for UF. Un-ignore when eval_in_model returns true for every \
            assertion z3 confirms the model satisfies."]
#[test]
fn iso_brn1083_eval_in_model_does_not_false_alarm() {
    let Some(orig) =
        read_corpus("smt-lib/non-incremental/QF_UF/QG-classification/qg5/iso_brn1083.smt2")
    else {
        eprintln!("skipping iso_brn1083: corpus file absent");
        return;
    };
    let body = strip_trailing_checksat(&orig);
    let mut ctx = Context::new();
    ctx.set_timeout_ms(TIMEOUT_MS);
    // Assert + check-sat (no get-model needed for the evaluator test).
    ctx.execute_script(&format!("{body}\n(check-sat)\n"))
        .unwrap_or_default();
    let true_id = ctx.terms.mk_true();
    let assertions = ctx.get_assertions().to_vec();
    let mut bad = 0usize;
    for term in &assertions {
        match ctx.eval_in_model(*term) {
            Some(v) if v == true_id => {}
            _ => bad += 1,
        }
    }
    assert!(
        bad == 0,
        "Model::eval false-alarm: {bad} of {} assertions did not evaluate to true under a \
         model z3 confirms is satisfying",
        assertions.len()
    );
}
