//! Bounded grammar-only comparison; successful and failed results must match.
use std::time::Instant;
fn main() {
    for path in std::env::args().skip(1) {
        let source = std::fs::read_to_string(&path).unwrap();
        for repetition in 0..6 {
            let mut results = Vec::new();
            for fast in if repetition % 2 == 0 { [false, true] } else { [true, false] } {
                let start = Instant::now();
                let result = if fast {
                    km_owl_functional_syntax::validate_iri_cached_ascii(&source)
                } else {
                    km_owl_functional_syntax::validate_iri_cached(&source)
                };
                println!("{path}\t{repetition}\t{}\t{:.9}\t{}",
                    if fast { "ascii" } else { "cached" },
                    start.elapsed().as_secs_f64(), result.is_ok());
                results.push(result);
            }
            assert_eq!(results[0], results[1], "acceptance or refusal text changed: {path}");
        }
    }
}
