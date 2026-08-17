//! Check an LRAT proof against a DIMACS CNF.
//!
//! ```text
//! cargo run --release -p oxiz-proof --example check_lrat -- file.cnf file.lrat
//! ```

fn main() {
    let mut args = std::env::args().skip(1);
    let cnf = args.next().expect("cnf path");
    let lrat = args.next().expect("lrat path");
    let report = oxiz_proof::lrat_check::check_lrat_files(&cnf, &lrat).expect("io");
    println!("verified: {}", report.verified);
    if let Some(f) = report.failure {
        println!("failure: {f}");
    }
    println!(
        "additions: {} deletions: {}",
        report.additions_checked, report.deletions_applied
    );
}
