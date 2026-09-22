//! `dumptrans` — translate one PlusCal file and print the module (debug).
fn main() {
    let Some(path) = std::env::args().nth(1) else {
        eprintln!("usage: dumptrans SPEC.tla");
        std::process::exit(2);
    };
    let src = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{path}: {e}");
            std::process::exit(2);
        }
    };
    match nixie_tla_syntax::pcal::translate_file(&src) {
        Ok(t) => print!("{}", t.text),
        Err(e) => {
            eprintln!("{path}: {e}");
            std::process::exit(1);
        }
    }
}
