//! Direct paired grammar diagnostic; no ontology classification or release claim.
use std::time::Instant;

fn main() {
    std::env::remove_var("KM_FAST_IRI_GRAMMAR");
    for path in std::env::args().skip(1) {
        let source = std::fs::read_to_string(&path).unwrap();
        for repetition in 0..4 {
            let mut results = Vec::new();
            for cached in if repetition % 2 == 0 { [false, true] } else { [true, false] } {
                let start = Instant::now();
                let result = if cached {
                    km_owl_functional_syntax::validate_iri_cached(&source)
                } else {
                    km_owl_functional_syntax::validate(&source)
                };
                println!("{path}\t{repetition}\t{}\t{:.9}\t{}",
                    if cached { "cached-iri" } else { "original" },
                    start.elapsed().as_secs_f64(), result.is_ok());
                results.push(result);
            }
            assert_eq!(results[0], results[1], "grammar result or refusal explanation changed: {path}");
        }
    }
}
