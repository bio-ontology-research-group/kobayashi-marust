//! `ofn`: OWL functional-syntax normalisation frontend (standalone shim).
//!
//! The implementation lives in `kobayashi_marust::cli::run_ofn`, shared with the
//! `km ofn` subcommand so the reasoner can ship as a single binary. See that
//! function for the usage / output contract.

fn main() {
    let args: Vec<String> = std::env::args().collect();
    kobayashi_marust::cli::run_ofn(&args[1..]);
}
