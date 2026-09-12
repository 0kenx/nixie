//! Parse each TLA+ file named on the command line and report the outcome.
//!
//! This is the harness the parser differential suite grows into: point it at a
//! corpus and it prints an accept/reject line per file.

fn main() {
    let mut fail = 0usize;
    let mut ok = 0usize;
    for path in std::env::args().skip(1) {
        let src = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                println!("READ {path}: {e}");
                fail += 1;
                continue;
            }
        };
        match nixie_tla_syntax::parse_file(&src) {
            Ok(p) => {
                ok += 1;
                println!(
                    "OK   {path}  ({} units, {} comments)",
                    p.module.units.len(),
                    p.comments.len()
                );
            }
            Err(e) => {
                fail += 1;
                println!("FAIL {path}\n       {e}");
            }
        }
    }
    println!("--- {ok} accepted, {fail} rejected");
    if fail > 0 {
        std::process::exit(1);
    }
}
