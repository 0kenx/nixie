//! Debug: dump the per-depth BMC assertion set for one spec, SMT-LIB text.
//!
//! Mirrors `Bmc::prepare`'s declaration phase exactly (one lowerer, one
//! inference, sorted declarations, native sets) and then prints the terms
//! `Bmc::check` would assert at each depth, so the query can be inspected and
//! cross-checked against another solver.
use nixie_core::TermManager;
use nixie_core::smtlib::Printer;
use nixie_tla::types::Inference;
use nixie_tla_check::encode::{Encoder, SetEncoding};
use nixie_tla_check::sorts::sort_of;

fn main() {
    let path = std::env::args().nth(1).expect("spec path");
    let inv = std::env::args().nth(2).expect("invariant");
    let j: u32 = std::env::args()
        .nth(3)
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);
    let src = std::fs::read_to_string(&path).expect("read");
    let parsed = nixie_tla_syntax::parse_file(&src).expect("parses");
    let spec = nixie_tla_syntax::LoadedSpec::single(parsed);
    let module = spec.root_module().expect("root");

    let mut low = nixie_tla::Lowerer::new();
    low.add_spec(&spec);
    let init = low.lower_named(module, "Init").expect("Init lowers");
    let next = low.lower_named(module, "Next").expect("Next lowers");
    let invt = low.lower_named(module, &inv).expect("Inv lowers");

    let mut tm = TermManager::new();
    let mut inf = Inference::new();
    for t in [&init, &next, &invt] {
        inf.infer(t).expect("types");
    }
    let required: std::collections::HashSet<String> =
        inf.free_names().map(|(n, _)| n.to_string()).collect();
    let state: Vec<String> = module.variables().iter().map(|v| v.name.clone()).collect();
    let mut encoder = Encoder::new().with_set_encoding(SetEncoding::Native);
    let mut names: Vec<(String, nixie_tla::TyId)> = inf
        .free_names()
        .map(|(n, id)| (n.to_string(), id))
        .collect();
    names.sort();
    for (name, id) in names {
        let ty = inf.to_type(id).expect("type");
        let Ok(sort) = sort_of(&ty, &mut tm) else {
            if required.contains(&name) {
                panic!("no sort for {name}");
            }
            continue;
        };
        if state.iter().any(|v| v == &name) {
            encoder.declare_state(name, sort);
        } else {
            encoder.declare(name, sort);
        }
    }

    let init_t = encoder.encode_at(&init, 0, &mut tm).expect("init encodes");
    let mut trans = Vec::new();
    for i in 0..j {
        trans.push(encoder.encode_at(&next, i, &mut tm).expect("next encodes"));
    }
    let inv_t = encoder.encode_at(&invt, j, &mut tm).expect("inv encodes");
    let p = Printer::new(&tm);
    println!(";; INIT\n(assert {}\n)\n", p.print_term(init_t));
    for (i, t) in trans.iter().enumerate() {
        println!(";; TRANSITION {i}\n(assert {}\n)\n", p.print_term(*t));
    }
    println!(
        ";; NEGATED INVARIANT at {j}: the checker asserts its negation\n(assert (not {}\n))\n",
        p.print_term(inv_t)
    );
}
