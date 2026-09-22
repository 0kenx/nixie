//! Minimal SMT-LIB repro driver: read a script, print check-sat answers.
use nixie_solver::Context;

fn main() {
    let path = std::env::args().nth(1).expect("script path");
    let script = std::fs::read_to_string(path).expect("read");
    let mut ctx = Context::new();
    for line in ctx.execute_script(&script).expect("executes") {
        println!("{line}");
    }
}
