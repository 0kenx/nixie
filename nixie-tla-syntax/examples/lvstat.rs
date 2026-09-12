//! Print the level computed for each definition of the named modules.
//!
//! A diagnostic for validating `nixie_tla_syntax::level` against real specs:
//! `Init` should come out state level, `Next` action level, `Spec` temporal.

fn main() {
    for path in std::env::args().skip(1) {
        let Ok(src) = std::fs::read_to_string(&path) else {
            continue;
        };
        let Ok(p) = nixie_tla_syntax::parse_file(&src) else {
            eprintln!("parse failed: {path}");
            continue;
        };
        let r = nixie_tla_syntax::check_module(&p.module);
        println!("== {path}");
        for (name, level) in &r.definitions {
            println!("   {level:9} {name}");
        }
        if !r.unresolved.is_empty() {
            println!("   unresolved: {}", r.unresolved.join(", "));
        }
        for e in &r.errors {
            println!("   LEVEL ERROR {e}");
        }
    }
}
