//! One-arm grammar equivalence check. Debug output preserves exact error text.
fn main() {
    std::env::remove_var("KM_FAST_IRI_GRAMMAR");
    std::env::remove_var("KM_ASCII_IRI_GRAMMAR");
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 3);
    let source = std::fs::read_to_string(&args[2]).unwrap();
    let result = match args[1].as_str() {
        "original" => km_owl_functional_syntax::validate(&source),
        "ascii" => km_owl_functional_syntax::validate_iri_cached_ascii(&source),
        _ => panic!("unknown arm"),
    };
    println!("{result:?}");
}
