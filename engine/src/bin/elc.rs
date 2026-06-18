//! `elc`: EL++ completion fast path (standalone shim).
//!
//! Reads `{"clauses":[...]}` on stdin; classifies with the ELK-style completion
//! and prints `{"subsumptions":{...}, "inconsistent":<bool>, "dropped":0}`, or
//! exits 3 (not EL++) / 4 (PARTIAL certificate residue). The implementation is
//! `kobayashi_marust::cli::run_elc`, shared with the `km elc` subcommand.

fn main() {
    kobayashi_marust::cli::run_elc();
}
