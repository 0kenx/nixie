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
                let report = nixie_tla_syntax::check_module(&p.module);
                if std::env::var_os("NIXIE_TLA_LEVELS").is_some() {
                    for e in &report.errors {
                        println!("LEVEL {path}\n       {e}");
                    }
                }
                println!(
                    "OK   {path}  ({} units, {} comments, {} level errors)",
                    p.module.units.len(),
                    p.comments.len(),
                    report.errors.len()
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
