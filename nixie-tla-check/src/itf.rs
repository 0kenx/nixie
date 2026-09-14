//! Counterexamples in the **Informal Trace Format** (ITF).
//!
//! ITF is Apalache's JSON counterexample format, specified in its ADR-015. It
//! is the interface every downstream consumer already speaks: `itf-rs` and
//! `itf-py` parse it, the VSCode trace viewer renders it, Quint emits it, and
//! `tla-connect` — model-based testing for Rust — collects `*.itf.json` from a
//! model checker and replays each trace against a `Driver`.
//!
//! So this is what makes a Nixie counterexample *usable* rather than merely
//! true. The rest of the crate decides whether a violation exists and (in
//! [`crate::trace`]) whether the states behind it are real; this hands them to
//! a tool that will drive an implementation with them.
//!
//! # What is written
//!
//! ```js
//! {
//!   "#meta": { "description": …, "source": … },
//!   "params": [ <CONSTANT names> ],
//!   "vars":   [ <VARIABLE names> ],
//!   "states": [ { "#meta": { "index": 0 }, … }, … ]
//! }
//! ```
//!
//! `params` are the specification's `CONSTANT`s, which ADR-015 says must be
//! set in the initial state; they are written into state 0 and not repeated,
//! because a state's fields are supposed to be the declared `vars`.
//!
//! # Tuples and sequences
//!
//! ITF has both a list (`[…]`, "TLA+ sequences are written as lists") and a
//! tuple (`{"#tup": […]}`), and says there is no strict rule about which to
//! use — Apalache picks by the *type* it inferred. TLA+ itself does not
//! distinguish: a sequence **is** a function on `1..n`, which is what
//! `nixie_tla::Value::fun` normalises to a tuple, so there is nothing here to
//! pick by. Everything sequence-shaped is written as `#tup`, which `itf-rs`
//! accepts wherever it accepts a list (`deserialize_seq` takes lists, tuples
//! and sets alike), so a consumer deserialising into a `Vec` is unaffected.
//!
//! # Integers
//!
//! Always `{"#bigint": "…"}`, never a JSON number. ADR-015 requires it — "big
//! and small integers *must be* written in this format" — because JSON parsers
//! impose their own limits, and a TLA+ integer is unbounded.

use crate::trace::Trace;
use nixie_tla::Value;
use serde_json::{Map, Value as Json, json};

/// The `#meta` object of a trace.
#[derive(Debug, Clone, Default)]
pub struct Meta {
    /// What produced the trace.
    pub description: String,
    /// The specification it came from.
    pub source: String,
}

/// Render a counterexample as an ITF trace object.
///
/// `vars` are the `VARIABLE`s and `params` the `CONSTANT`s; both are written
/// out even when a state happens not to mention one, because ADR-015 requires
/// every declared variable to have a value in every state.
///
/// A name in `vars` that the trace has no value for is written as
/// `{"#unserializable": …}` rather than omitted: ITF's own escape hatch, and
/// the honest thing to hand a consumer that is about to drive a system with
/// it. Silently dropping the field would let a driver read a stale value.
#[must_use]
pub fn to_itf(trace: &Trace, vars: &[String], params: &[String], meta: &Meta) -> Json {
    let mut states = Vec::with_capacity(trace.states.len());
    for (i, st) in trace.states.iter().enumerate() {
        let mut obj = Map::new();
        obj.insert("#meta".to_string(), json!({ "index": i }));
        // The parameters belong to the initial state; the variables to all.
        let names = if i == 0 {
            params.iter().chain(vars.iter()).collect::<Vec<_>>()
        } else {
            vars.iter().collect::<Vec<_>>()
        };
        for name in names {
            let v = st.get(name).map_or_else(
                || json!({ "#unserializable": format!("{name} has no value in this state") }),
                value_to_itf,
            );
            obj.insert(name.clone(), v);
        }
        states.push(Json::Object(obj));
    }
    let mut root = Map::new();
    root.insert(
        "#meta".to_string(),
        json!({ "description": meta.description, "source": meta.source }),
    );
    if !params.is_empty() {
        root.insert("params".to_string(), json!(params));
    }
    root.insert("vars".to_string(), json!(vars));
    root.insert("states".to_string(), Json::Array(states));
    Json::Object(root)
}

/// Render one TLA+ value as an ITF expression.
#[must_use]
pub fn value_to_itf(v: &Value) -> Json {
    match v {
        Value::Bool(b) => json!(b),
        // Never a JSON number: ADR-015 requires the `#bigint` form for every
        // integer, big or small, because a TLA+ integer is unbounded and JSON
        // parsers are not.
        Value::Int(i) => json!({ "#bigint": i.to_string() }),
        Value::Str(s) => json!(s),
        Value::Set(xs) => json!({ "#set": xs.iter().map(value_to_itf).collect::<Vec<_>>() }),
        Value::Tuple(xs) => json!({ "#tup": xs.iter().map(value_to_itf).collect::<Vec<_>>() }),
        Value::Record(fs) => {
            let mut obj = Map::new();
            for (k, x) in fs {
                obj.insert(k.clone(), value_to_itf(x));
            }
            Json::Object(obj)
        }
        // A TLA+ function is an ITF map: an array of `[key, value]` pairs,
        // because a key may be any expression and JSON object keys may not.
        Value::Fun(m) => json!({
            "#map": m
                .iter()
                .map(|(k, x)| json!([value_to_itf(k), value_to_itf(x)]))
                .collect::<Vec<_>>()
        }),
    }
}
