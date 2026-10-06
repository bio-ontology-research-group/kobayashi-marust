//! Bounded diagnostic linked against the existing release libraries.
//! The measurements are separate calls, not additive phase accounting.
use std::time::Instant;

fn timed(name: &str, check: impl FnOnce() -> Result<(), String>) {
    let start = Instant::now();
    let result = check();
    println!("{name}\t{:.9}\t{}", start.elapsed().as_secs_f64(), result.is_ok());
    if let Err(message) = result {
        eprintln!("{name}: {message}");
        std::process::exit(1);
    }
}

fn main() {
    // Force every total measurement to execute every conformance check.
    std::env::remove_var("KM_CACHE_CONFORMANCE");
    for path in std::env::args().skip(1) {
        let source = std::fs::read_to_string(&path).unwrap();
        for repetition in 0..3 {
            println!("input\t{path}\trepetition={repetition}\tbytes={}", source.len());
            let grammar = || km_owl_functional_syntax::validate(&source);
            let complete = || kobayashi_marust::frontend::conformance::check_source(&source);
            if repetition % 2 == 0 {
                timed("complete-source", complete);
                timed("grammar", grammar);
            } else {
                timed("grammar", grammar);
                timed("complete-source", complete);
            }
            timed("literal-datatypes", ||
                kobayashi_marust::frontend::conformance::check_literal_datatypes(&source));
            timed("declarations", ||
                kobayashi_marust::frontend::conformance::check_declarations(&source));
            timed("iri-prefixes", ||
                kobayashi_marust::frontend::conformance::check_iri_prefixes(&source));
        }
    }
}
