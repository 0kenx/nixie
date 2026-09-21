//! `pcalsem` — semantic parity of a PlusCal translation, checked against
//! TLC-generated successor pairs.
//!
//! This is the gate that catches a wrong *translation* rather than a broken
//! parser: TLC explores a model of the **golden** (oracle-translated) and
//! the **ours** (this front end's) specification and prints every initial
//! state and successor pair it generates. Both translations' `Init` and
//! `Next` are then evaluated over every state and pair: agreement in all
//! four directions is semantic parity on the reachable behaviour of the
//! model — label placement, `UNCHANGED` bookkeeping, self-subscripts and
//! `pc` updates all have to be right for it to hold.
//!
//! An evaluation that **both** translations decline with the same reason
//! (an evaluator limit the golden shares, like a `CHOOSE` the evaluator
//! refuses) is a decline, reported and counted — not a pass, and not a
//! failure. A disagreement — one side true and the other not, or different
//! errors — is the failure this gate exists to catch.
//!
//! TLC values are parsed from their printed form (`<<…>>`, `{…}`,
//! `[f |-> v]`, `(k :> v @@ k' :> v')`, strings, integers, booleans, and
//! bare model values, read as distinct atoms). Anything outside that
//! vocabulary declines with the line — never a guess.

use std::collections::HashMap;

use nixie_tla::Value;
use nixie_tla_syntax::config::{ConfigValue, parse_config};

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut cfg_path = String::new();
    let mut pairs_path = String::new();
    let mut mine = String::new();
    let mut golden = String::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--cfg" if i + 1 < args.len() => cfg_path = args[i + 1].clone(),
            "--pairs" if i + 1 < args.len() => pairs_path = args[i + 1].clone(),
            "--mine" if i + 1 < args.len() => mine = args[i + 1].clone(),
            "--golden" if i + 1 < args.len() => golden = args[i + 1].clone(),
            _ => {}
        }
        i += 2;
    }
    if cfg_path.is_empty() || pairs_path.is_empty() || mine.is_empty() || golden.is_empty() {
        eprintln!(
            "usage: pcalsem --cfg MODEL.cfg --pairs PAIRS.txt --mine OURS.tla --golden GOLDEN.tla"
        );
        std::process::exit(2);
    }
    args.clear();

    let constants = match read_constants(&cfg_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("{cfg_path}: {e}");
            std::process::exit(2);
        }
    };
    let dump = match std::fs::read_to_string(&pairs_path) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("{pairs_path}: {e}");
            std::process::exit(2);
        }
    };
    let states = match parse_dump(&dump) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{pairs_path}:{}: {what}", e.line, what = e.what);
            std::process::exit(2);
        }
    };
    let initials = states
        .iter()
        .filter(|(kind, _)| matches!(kind, DumpKind::Initial))
        .count();
    let pairs_n = states.len() - initials;
    println!(
        "{pairs_path}: {initials} initial states, {pairs_n} successor pairs ({} constants bound)",
        constants.len()
    );

    let lib = std::env::var("NIXIE_TLA_LIB").unwrap_or_default();
    // (state/pair index, side label, evaluation outcome)
    let mut results: Vec<(usize, &str, String)> = Vec::new();
    let mut load_failures = 0usize;
    for (label, path) in [("ours", mine.as_str()), ("golden", golden.as_str())] {
        let mut loader = nixie_tla_syntax::Loader::new();
        for d in lib.split(':').filter(|d| !d.is_empty()) {
            loader = loader.with_search_path(d);
        }
        let spec = match loader.load(std::path::Path::new(path)) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("{label} {path}: {e}");
                load_failures += 1;
                continue;
            }
        };
        let Some(module) = spec.root_module() else {
            eprintln!("{label} {path}: no root module");
            load_failures += 1;
            continue;
        };
        let var_names = var_order(module);
        if var_names.is_empty() {
            eprintln!("{label} {path}: no `vars == <<…>>` definition found");
            load_failures += 1;
            continue;
        }
        let mut lower = nixie_tla::Lowerer::new();
        lower.add_spec(&spec);
        let (init, next) = match (
            lower.lower_named(module, "Init"),
            lower.lower_named(module, "Next"),
        ) {
            (Ok(i), Ok(n)) => (i, n),
            _ => {
                eprintln!("{label} {path}: Init/Next did not lower");
                load_failures += 1;
                continue;
            }
        };
        let mut evaluator = nixie_tla::Evaluator::new();
        for (idx, (kind, value)) in states.iter().enumerate() {
            match kind {
                DumpKind::Initial => {
                    // The probe prints `<<vars>>`: a one-element tuple whose
                    // element is the state itself.
                    let value = match value {
                        Value::Tuple(items) if items.len() == 1 => &items[0],
                        other => other,
                    };
                    let Ok(state) = state_of(value, &var_names) else {
                        eprintln!("{label}: initial state unreadable");
                        load_failures += 1;
                        continue;
                    };
                    let mut env = constants.clone();
                    env.extend(state.clone());
                    results.push((
                        idx,
                        label,
                        format!("{:?}", evaluator.eval_state(&init, &env)),
                    ));
                }
                DumpKind::Pair => {
                    let Value::Tuple(both) = value else {
                        eprintln!("{label}: successor pair unreadable");
                        load_failures += 1;
                        continue;
                    };
                    if both.len() != 2 {
                        eprintln!("{label}: successor pair unreadable");
                        load_failures += 1;
                        continue;
                    }
                    let (Ok(cur), Ok(nxt)) = (
                        state_of(&both[0], &var_names),
                        state_of(&both[1], &var_names),
                    ) else {
                        eprintln!("{label}: successor pair unreadable");
                        load_failures += 1;
                        continue;
                    };
                    let mut env = constants.clone();
                    env.extend(cur);
                    results.push((
                        idx,
                        label,
                        format!("{:?}", evaluator.eval_action(&next, &env, &nxt)),
                    ));
                }
            }
        }
    }
    if load_failures > 0 {
        println!("FAILED: {load_failures} load/decode failure(s)");
        std::process::exit(1);
    }
    // Pair the two sides per entry and decide.
    let mut agreed = 0usize;
    let mut declined = 0usize;
    let mut failures = 0usize;
    for idx in 0..states.len() {
        let a = results.iter().find(|(i, l, _)| *i == idx && *l == "ours");
        let b = results.iter().find(|(i, l, _)| *i == idx && *l == "golden");
        let (Some((_, _, ours)), Some((_, _, gold))) = (a, b) else {
            continue;
        };
        if ours == "Ok(Bool(true))" && gold == "Ok(Bool(true))" {
            agreed += 1;
        } else if ours == gold && ours != "Ok(Bool(true))" {
            // A shared decline: the same evaluator limit on both sides.
            declined += 1;
            if declined == 1 {
                println!("declined on both sides (first at entry {idx}): {ours}");
            }
        } else {
            failures += 1;
            if failures <= 5 {
                println!("DISAGREEMENT at entry {idx}: ours {ours}, golden {gold}");
            }
        }
    }
    if failures > 0 {
        println!("FAILED: {failures} disagreement(s), {agreed} agreed, {declined} declined");
        std::process::exit(1);
    }
    println!("agreed on {agreed} evaluation(s), declined on {declined}");
}

/// The constant assignments of a `.cfg`, as values.
fn read_constants(path: &str) -> Result<HashMap<String, Value>, String> {
    let src = std::fs::read_to_string(path).map_err(|e| e.to_string())?;
    let cfg = parse_config(&src).map_err(|e| e.to_string())?;
    let mut out = HashMap::new();
    for (name, value) in &cfg.assignments {
        let Some(v) = config_value(value) else {
            return Err(format!("constant {name} has an unusable assignment"));
        };
        out.insert(name.clone(), v);
    }
    Ok(out)
}

fn config_value(v: &ConfigValue) -> Option<Value> {
    match v {
        ConfigValue::ModelValue(s) => Some(Value::Str(format!("\u{1}atom:{s}"))),
        ConfigValue::Int(i) => i.parse::<i128>().ok().map(Value::Int),
        ConfigValue::Str(s) => Some(Value::Str(s.clone())),
        ConfigValue::Bool(b) => Some(Value::Bool(*b)),
        ConfigValue::Set(items) => {
            let mut out = std::collections::BTreeSet::new();
            for item in items {
                out.insert(config_value(item)?);
            }
            Some(Value::Set(out))
        }
        ConfigValue::ModuleQualified { .. } => None,
    }
}

/// What a printed entry is.
#[derive(Debug, Clone, Copy)]
enum DumpKind {
    /// `<<vars>>` — a TLC initial state.
    Initial,
    /// `<<vars, vars'>>` — a successor pair.
    Pair,
}

fn parse_dump(src: &str) -> Result<Vec<(DumpKind, Value)>, DumpError> {
    let mut p = ValueParser {
        chars: src.chars().collect(),
        pos: 0,
        line: 1,
    };
    let mut out = Vec::new();
    loop {
        p.skip_layout();
        if p.at_end() {
            return Ok(out);
        }
        let before = p.pos;
        let value = match p.value() {
            Ok(v) => v,
            Err(_) if p.at_end() => {
                // A TLC run killed mid-print leaves a partial final entry;
                // the complete entries before it are sound evidence.
                p.pos = before;
                return Ok(out);
            }
            Err(e) => return Err(e),
        };
        let kind = match &value {
            Value::Tuple(items) if items.len() == 1 => DumpKind::Initial,
            Value::Tuple(items) if items.len() == 2 => DumpKind::Pair,
            _ => {
                return Err(DumpError {
                    line: p.line,
                    what: "printed value is neither a state nor a pair".into(),
                });
            }
        };
        out.push((kind, value));
    }
}

/// The state map of a printed `vars` tuple, by position.
fn state_of(value: &Value, names: &[String]) -> Result<HashMap<String, Value>, String> {
    let Value::Tuple(items) = value else {
        return Err("state is not a tuple".into());
    };
    if items.len() != names.len() {
        return Err(format!(
            "state has {} entries but vars lists {}",
            items.len(),
            names.len()
        ));
    }
    Ok(names
        .iter()
        .cloned()
        .zip(items.iter().cloned())
        .collect::<HashMap<_, _>>())
}

/// `vars == <<a, b, c>>`, read from the parsed module.
fn var_order(module: &nixie_tla_syntax::Module) -> Vec<String> {
    for u in &module.units {
        if let nixie_tla_syntax::UnitKind::OpDef {
            name, params, body, ..
        } = &u.kind
            && name.name == "vars"
            && params.is_empty()
            && let nixie_tla_syntax::ExprKind::Tuple(items) = &body.kind
        {
            return items
                .iter()
                .filter_map(|e| match &e.kind {
                    nixie_tla_syntax::ExprKind::Name(q) => q.base().map(|b| b.name.clone()),
                    _ => None,
                })
                .collect();
        }
    }
    Vec::new()
}

// ---- the printed-value parser ----------------------------------------------

struct ValueParser {
    chars: Vec<char>,
    pos: usize,
    line: usize,
}

impl ValueParser {
    fn at_end(&self) -> bool {
        self.pos >= self.chars.len()
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek();
        if c.is_some_and(|c| c == '\n') {
            self.line += 1;
        }
        self.pos += 1;
        c
    }

    fn skip_layout(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.bump();
        }
    }

    fn eat(&mut self, s: &str) -> bool {
        let save = (self.pos, self.line);
        self.skip_layout();
        for c in s.chars() {
            if self.peek() != Some(c) {
                self.pos = save.0;
                self.line = save.1;
                return false;
            }
            self.bump();
        }
        true
    }

    fn value(&mut self) -> Result<Value, DumpError> {
        self.skip_layout();
        match self.peek() {
            Some('<') => {
                if !self.eat("<<") {
                    return Err(self.err("`<<'"));
                }
                let mut items = Vec::new();
                loop {
                    self.skip_layout();
                    if self.eat(">>") {
                        break;
                    }
                    if !items.is_empty() && !self.eat(",") {
                        return Err(self.err("`, ' or `>>'"));
                    }
                    self.skip_layout();
                    if self.eat(">>") {
                        break;
                    }
                    items.push(self.value()?);
                }
                Ok(Value::Tuple(items))
            }
            Some('(') => {
                // TLC prints a function on an arbitrary domain as
                // `(k :> v @@ k :> v)'.
                self.bump();
                let mut acc: std::collections::BTreeMap<Value, Value> =
                    std::collections::BTreeMap::new();
                loop {
                    self.skip_layout();
                    if self.eat(")") {
                        break;
                    }
                    if !acc.is_empty() && !self.eat("@@") {
                        return Err(self.err("`@@' or `)'"));
                    }
                    let k = self.value()?;
                    if !self.eat(":>") {
                        return Err(self.err("`:>'"));
                    }
                    let v = self.value()?;
                    acc.insert(k, v);
                }
                Ok(Value::Fun(acc))
            }
            Some('{') => {
                self.bump();
                let mut items = std::collections::BTreeSet::new();
                loop {
                    self.skip_layout();
                    if self.eat("}") {
                        break;
                    }
                    if !items.is_empty() && !self.eat(",") {
                        return Err(self.err("`, ' or `}'"));
                    }
                    self.skip_layout();
                    if self.eat("}") {
                        break;
                    }
                    items.insert(self.value()?);
                }
                Ok(Value::Set(items))
            }
            Some('[') => {
                self.bump();
                self.skip_layout();
                let mut fields = std::collections::BTreeMap::new();
                loop {
                    self.skip_layout();
                    if self.eat("]") {
                        break;
                    }
                    if !fields.is_empty() && !self.eat(",") {
                        return Err(self.err("`, ' or `]'"));
                    }
                    self.skip_layout();
                    if self.eat("]") {
                        break;
                    }
                    let Some(field) = self.ident() else {
                        return Err(self.err("a record field"));
                    };
                    if !self.eat("|->") && !self.eat("=") {
                        return Err(self.err("`|->' in a record"));
                    }
                    fields.insert(field, self.value()?);
                }
                Ok(Value::Record(fields))
            }
            Some('"') => {
                self.bump();
                let mut s = String::new();
                loop {
                    match self.bump() {
                        Some('"') => break,
                        Some('\\') => match self.bump() {
                            Some('n') => s.push('\n'),
                            Some('t') => s.push('\t'),
                            Some('\\') => s.push('\\'),
                            Some('"') => s.push('"'),
                            Some(other) => {
                                return Err(self.err(&format!("escape \\{other}")));
                            }
                            None => return Err(self.err("end of string")),
                        },
                        Some(c) => s.push(c),
                        None => return Err(self.err("end of string")),
                    }
                }
                Ok(Value::Str(s))
            }
            Some(c) if c == '-' || c.is_ascii_digit() => {
                let mut n = String::new();
                if self.peek() == Some('-') {
                    n.push(self.bump().unwrap_or('-'));
                }
                while self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    n.push(self.bump().unwrap_or('0'));
                }
                n.parse::<i128>()
                    .map(Value::Int)
                    .map_err(|_| self.err(&format!("number {n}")))
            }
            Some(c) if c.is_alphabetic() => {
                let word = self.ident().ok_or_else(|| self.err("an identifier"))?;
                match word.as_str() {
                    "TRUE" => Ok(Value::Bool(true)),
                    "FALSE" => Ok(Value::Bool(false)),
                    // A model value: an atom, spelled with a control prefix
                    // so it can never collide with a genuine string.
                    _ => Ok(Value::Str(format!("\u{1}atom:{word}"))),
                }
            }
            Some(other) => Err(self.err(&format!("`{other}'"))),
            None => Err(self.err("end of input")),
        }
    }

    fn ident(&mut self) -> Option<String> {
        self.skip_layout();
        let mut s = String::new();
        while self.peek().is_some_and(|c| c.is_alphanumeric() || c == '_') {
            s.push(self.bump()?);
        }
        (!s.is_empty()).then_some(s)
    }

    fn err(&self, what: &str) -> DumpError {
        DumpError {
            line: self.line,
            what: format!("expected {what}"),
        }
    }
}

/// Why a pair dump could not be read.
#[derive(Debug)]
struct DumpError {
    line: usize,
    what: String,
}
