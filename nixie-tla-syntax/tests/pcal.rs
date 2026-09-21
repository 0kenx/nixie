//! PlusCal translator tests.
//!
//! Every test translates a whole (small) module and re-parses the output
//! through the ordinary TLA+ front end, so a translation that does not
//! round-trip cannot pass. The structural assertions then pin the pieces
//! the label-placement rules decide: what the atomic steps are, where the
//! `pc` guards and updates land, which variables a step leaves unchanged,
//! and what the declines refuse to guess at.
//!
//! The corpus-level parity (against `pcal.trans` and TLC) lives in
//! `bench/tla_pcal`; these tests are the unit-level contract.

use nixie_tla_syntax::parse_file;
use nixie_tla_syntax::pcal::translate_file;

/// Translate and re-parse; panics with the error if either step fails.
fn roundtrip(src: &str) -> String {
    let t = match translate_file(src) {
        Ok(t) => t,
        Err(e) => panic!("translation failed: {e}"),
    };
    match parse_file(&t.text) {
        Ok(p) => {
            let _ = p;
            t.text
        }
        Err(e) => panic!("translated module does not re-parse: {e}\n{}", t.text),
    }
}

/// The text of one definition (through its trailing blank line).
fn def_of(text: &str, name: &str) -> String {
    let needle = format!("{name} ==");
    let start = text
        .lines()
        .position(|l| l.trim_start() == needle || l.trim_start().starts_with(&format!("{needle} ")))
        .unwrap_or_else(|| panic!("no definition {name} in:\n{text}"));
    let end = text
        .lines()
        .skip(start + 1)
        .position(|l| l.trim().is_empty())
        .map(|n| start + 1 + n)
        .unwrap_or(text.lines().count());
    text.lines()
        .skip(start)
        .take(end - start)
        .collect::<Vec<_>>()
        .join("\n")
}

fn module(body: &str) -> String {
    format!("---- MODULE T ----\nEXTENDS Naturals\n{body}\n====\n")
}

#[test]
fn uniprocess_while_translates_to_pc_steps() {
    let text = roundtrip(&module(
        r"
(* --algorithm Count
variables x = 0
begin
  Up: while x < 3 do x := x + 1; end while;
end algorithm; *)
",
    ));
    let up = def_of(&text, "Up");
    assert!(up.contains("pc = \"Up\""), "guard missing: {up}");
    assert!(up.contains("x' = x + 1"), "update missing: {up}");
    // The loop's exit: pc' = "Done".
    assert!(text.contains("pc = \"Done\""), "no Done exit: {text}");
    let next = def_of(&text, "Next");
    assert!(next.contains("Up"), "Next misses the action: {next}");
    assert!(text.contains("Terminating == pc = \"Done\""));
}

#[test]
fn multiprocess_process_sets_subscript_their_variables() {
    let text = roundtrip(&module(
        r"
(* --algorithm Ring
variables box = {}
process P \in 1..2
variables mine = 0
begin
  A: mine := mine + 1;
     box := box \union {mine};
end process;
end algorithm; *)
",
    ));
    let a = def_of(&text, "A(self)");
    assert!(
        a.contains("A(self) =="),
        "action not self-parameterised: {a}"
    );
    assert!(
        a.contains("mine' = [mine EXCEPT ![self] = mine[self] + 1]"),
        "process variable not self-subscripted: {a}"
    );
    // Reading `mine` after assigning it in the same step reads the new
    // value, self-subscripted -- the reference's `Changed` rule.
    assert!(
        a.contains("box' = box \\cup {mine'[self]}"),
        "global box stays unsubscripted, mine reads primed: {a}"
    );
    assert!(
        text.contains("Init ==") && text.contains("mine = [self \\in 1 .. 2 |-> 0]"),
        "Init must lift process variables to functions: {text}"
    );
    let next = def_of(&text, "Next");
    assert!(
        next.contains("\\E self \\in 1 .. 2 : P(self)"),
        "Next must existentially quantify the process set: {next}"
    );
}

#[test]
fn fair_processes_get_weak_fairness_in_spec() {
    let text = roundtrip(&module(
        r"
(* --algorithm One
variables x = 0
fair process W \in {1}
begin  S: x := 1;  end process;
end algorithm; *)
",
    ));
    assert!(
        text.contains("WF_vars(W(self))"),
        "fair process must yield weak fairness: {text}"
    );
}

#[test]
fn goto_becomes_a_pc_update() {
    let text = roundtrip(&module(
        r"
(* --algorithm G
variables x = 0
begin
  A: x := 1;
     goto B;
  B: x := 2;
end algorithm; *)
",
    ));
    let a = def_of(&text, "A");
    assert!(
        a.contains("pc' = \"B\"") || a.contains("pc' = [pc EXCEPT"),
        "goto must update pc toward its target: {a}"
    );
    // No unreachable-code illusion: the statements after the goto are gone.
    assert!(
        !a.contains("x' = 2"),
        "statements after goto must not run: {a}"
    );
}

#[test]
fn label_inside_if_splits_the_step() {
    let text = roundtrip(&module(
        r"
(* --algorithm Split
variables x = 0, y = 0
begin
  A: if x = 0 then
       x := 1;
     else
  B:   y := 1;
     end if;
end algorithm; *)
",
    ));
    // The `A` step branches; each branch updates pc toward its own next
    // label — the THEN toward B, the ELSE to Done.
    let a = def_of(&text, "A");
    assert!(a.contains("IF x = 0"), "test missing: {a}");
    assert!(a.contains("\"B\""), "then-branch must target B: {a}");
    // B is its own atomic step.
    let b = def_of(&text, "B");
    assert!(b.contains("pc = \"B\""), "B must guard on its own pc: {b}");
    assert!(b.contains("y' = 1"), "B must assign y: {b}");
}

#[test]
fn compound_assignment_merges_into_one_except() {
    let text = roundtrip(&module(
        r"
(* --algorithm M
variables f = [i \in 1..2 |-> 0]
begin
  A: f[1] := 9 || f[2] := 8;
end algorithm; *)
",
    ));
    let a = def_of(&text, "A");
    assert!(
        a.contains("![1] = 9, ![2] = 8"),
        "simultaneous updates must merge into one EXCEPT: {a}"
    );
}

#[test]
fn macros_expand_before_translation() {
    let text = roundtrip(&module(
        r"
(* --algorithm Mac
variables n = 0
macro Bump(by) begin n := n + by; end macro;
begin
  A: Bump(2);
end algorithm; *)
",
    ));
    let a = def_of(&text, "A");
    assert!(
        a.contains("n' = n + 2"),
        "macro argument must substitute: {a}"
    );
}

#[test]
fn await_is_a_guard_not_a_step() {
    let text = roundtrip(&module(
        r"
(* --algorithm W
variables ready = FALSE, done = 0
begin
  A: await ready;
     done := 1;
end algorithm; *)
",
    ));
    let a = def_of(&text, "A");
    assert!(
        a.contains("/\\ ready"),
        "await must guard the same step, not block: {a}"
    );
    assert!(
        a.contains("done' = 1"),
        "the guarded statement must run: {a}"
    );
}

#[test]
fn while_true_single_cluster_elides_pc() {
    let text = roundtrip(&module(
        r"
(* --algorithm Spin
variables x = 0
begin
  S: while TRUE do x := x + 1; end while;
end algorithm; *)
",
    ));
    assert!(
        !text.contains("VARIABLE pc"),
        "a single while-TRUE cluster needs no pc: {text}"
    );
    assert!(
        text.contains("Next == "),
        "the one action must be named Next when pc is elided: {text}"
    );
    assert!(
        !text.contains("Terminating"),
        "no termination is possible; Terminating must be elided: {text}"
    );
}

#[test]
fn define_block_is_hoisted_between_the_declarations() {
    let text = roundtrip(&module(
        r"
(* --algorithm D
variables g = 0
define
  Helper == 1
end define;
process P \in {1}
variables pv = 2
begin  A: g := Helper;  end process;
end algorithm; *)
",
    ));
    assert!(
        text.contains("(* define statement *)") && text.contains("Helper == 1"),
        "define block must be emitted verbatim: {text}"
    );
    assert!(
        text.contains("VARIABLE pv"),
        "the process-local declaration must follow the define block: {text}"
    );
}

#[test]
fn duplicate_labels_in_different_processes_are_disambiguated() {
    let text = roundtrip(&module(
        r"
(* --algorithm Two
variables x = 0
process A \in {1}
begin  L: x := 1;  end process;
process B \in {2}
begin  L: x := 2;  end process;
end algorithm; *)
",
    ));
    // The reference's suffix rule: the first of two like-spelled labels
    // grows an underscore.
    assert!(
        text.contains("L_"),
        "the first duplicate label must be renamed: {text}"
    );
}

#[test]
fn uninitialised_variable_becomes_default_init_value() {
    let text = roundtrip(&module(
        r"
(* --algorithm U
variables v
begin  A: v := 1;  end algorithm; *)
",
    ));
    assert!(
        text.contains("CONSTANT defaultInitValue"),
        "a bare declaration must introduce defaultInitValue: {text}"
    );
    assert!(
        text.contains("v = defaultInitValue"),
        "Init must read the default: {text}"
    );
}

#[test]
fn existing_translation_region_is_replaced() {
    let src = format!(
        "{}{}",
        r#"(* --algorithm R
variables x = 0
begin  A: x := 1;  end algorithm; *)
"#,
        r#"\* BEGIN TRANSLATION (chksum(pcal) = "old" /\ chksum(tla) = "old")
Stale == TRUE
\* END TRANSLATION
"#
    )
    .replace("MODULE T", "MODULE T");
    let src = format!("---- MODULE T ----\nEXTENDS Naturals\n{src}====\n");
    let t = translate_file(&src).expect("translates");
    assert!(t.replaced, "the existing region must be replaced");
    assert!(
        !t.text.contains("Stale"),
        "the stale translation must be gone: {}",
        t.text
    );
}

// ---- declines --------------------------------------------------------------

#[test]
fn procedures_are_declined_not_approximated() {
    let err = translate_file(&module(
        r"
(* --algorithm Proc
variables x = 0
procedure SetOne() begin  S: x := 1;  end procedure;
begin  A: call SetOne();  end algorithm; *)
",
    ))
    .expect_err("procedures must be declined");
    let msg = format!("{err}");
    assert!(
        msg.contains("procedure"),
        "the decline must name the construct: {msg}"
    );
}

#[test]
fn a_missing_required_label_is_an_error() {
    // `while` must be labeled; the reference rejects auto-insertion by
    // default, and so does this port.
    // One user label makes the policy strict, as in the reference; the
    // unlabeled `while` is then the violation.
    let err = translate_file(&module(
        r"
(* --algorithm Missing
variables x = 0
begin
  A: x := 1;
  while x < 3 do x := x + 1; end while;
end algorithm; *)
",
    ))
    .expect_err("the while needs its own label");
    let msg = format!("{err}");
    assert!(
        msg.contains("label"),
        "the error must name the missing label: {msg}"
    );
}

#[test]
fn a_label_inside_with_is_rejected() {
    let err = translate_file(&module(
        r"
(* --algorithm InWith
variables x = 0
begin
  A: with y \in {1} do
  B:   x := y;
     end with;
end algorithm; *)
",
    ))
    .expect_err("labels cannot appear inside with");
    let msg = format!("{err}");
    assert!(
        msg.contains("with") || msg.contains("label"),
        "the error must name the construct: {msg}"
    );
}

#[test]
fn no_algorithm_is_an_error_not_a_guess() {
    let err = translate_file(&module("Plain == 1\n")).expect_err("no algorithm");
    assert!(
        format!("{err}").contains("--algorithm"),
        "the error must say what is missing: {err}"
    );
}
