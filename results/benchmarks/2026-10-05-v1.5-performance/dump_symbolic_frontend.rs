// Diagnostic only: serialize every symbolic frontend field in declaration order.
// Exhaustive destructuring makes an added frontend field a compile error.
use kobayashi_marust::frontend::{ofn_to_symbolic_frontend, FrontendResult};
use std::io::{BufWriter, Write};
fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 3);
    std::env::set_var("KM_TRIGGER_ABSORB", "1");
    let text = std::fs::read_to_string(&args[1]).unwrap();
    let result = ofn_to_symbolic_frontend(&text).unwrap();
    let FrontendResult { clauses, rbox, iri_map, named, declared, el_rbox_safe, abox_inconsistent, asserted_classes, nominal_abox, cardinalities, definers, source_axioms, rules, profile, route } = result.evidence();
    let mut out = BufWriter::new(std::fs::File::create(&args[2]).unwrap());
    serde_json::to_writer(&mut out, &("clauses", clauses)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("rbox", rbox)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("iri_map", iri_map)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("named", named)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("declared", declared)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("el_rbox_safe", el_rbox_safe)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("abox_inconsistent", abox_inconsistent)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("asserted_classes", asserted_classes)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("nominal_abox", nominal_abox)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("cardinalities", cardinalities)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("definers", definers)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("source_axioms", source_axioms)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("rules", rules)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("profile", profile)).unwrap();
    out.write_all(b"\n").unwrap();
    serde_json::to_writer(&mut out, &("route", route)).unwrap();
    out.write_all(b"\n").unwrap();
    out.flush().unwrap();
}
