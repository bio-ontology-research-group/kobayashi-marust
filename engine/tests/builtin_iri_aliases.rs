//! Public builtin alias regression tests. Exact source bytes remain Session keys.
use std::collections::BTreeSet;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use serde_json::{json, Value};
static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Fixture(PathBuf);
impl Fixture {
    fn new(label: &str, text: &str) -> Self {
        let p=std::env::temp_dir().join(format!("km-builtin-{}-{}-{label}.ofn",std::process::id(),NEXT.fetch_add(1,Ordering::Relaxed)));
        std::fs::write(&p,text).unwrap();Self(p)
    }
}
impl Drop for Fixture { fn drop(&mut self) { let _=std::fs::remove_file(&self.0); } }
fn command() -> Command {
    let mut c=Command::new(env!("CARGO_BIN_EXE_km"));
    for (key,_) in std::env::vars_os() { if key.to_string_lossy().starts_with("KM_") { c.env_remove(key); } }
    c.env("KM_THREADS","1").env("KM_ROUTE","auto").env("RAYON_NUM_THREADS","1").env("OMP_NUM_THREADS","1");c
}
fn source(body: &str) -> String {
    format!("Prefix(o:=<http://www.w3.org/2002/07/owl#>) Ontology(Declaration(Class(<urn:A>)) Declaration(Class(<urn:E>)) Declaration(Class(<urn:F>)) Declaration(ObjectProperty(<urn:r>)) Declaration(DataProperty(<urn:d>)) Declaration(NamedIndividual(<urn:a>)) SubClassOf(<urn:E> <urn:F>) {body})")
}
fn nothing_source() -> String { source("SubClassOf(<urn:A> o:Nothing) ClassAssertion(<urn:A> <urn:a>)") }
fn frontend(path: &Path, split: bool) -> (Vec<u8>,Vec<u8>) {
    // Worker output exercises the complete OfnClausesOnly and OfnMeta serializers.
    let meta=Fixture::new("meta","");let mut c=command();c.arg("ofn").arg(path);
    if split { c.arg("--meta").arg(&meta.0); }
    let out=c.output().unwrap();assert!(out.status.success(),"{}",String::from_utf8_lossy(&out.stderr));
    assert!(!out.stdout.is_empty());
    (out.stdout,if split {std::fs::read(&meta.0).unwrap()}else{Vec::new()})
}
fn classify(path: &Path, split: bool) -> Output {
    let mut c=command();c.args(["classify","--json-edges"]).arg(path).env("KM_TIMING","1");
    if split { c.env("KM_NO_INPROC_OFN","1"); }
    c.output().unwrap()
}
// Independently close tiny graph1 outputs. Strictly parse both verdicts/shapes
// before comparing; never treat a failed process as a semantic answer.
fn canonical(v: &Value) -> (bool,BTreeSet<String>,BTreeSet<(String,String)>) {
    let consistent=v["consistent"].as_bool().expect("boolean verdict");assert_eq!(v["dropped"].as_u64(),Some(0));
    let unsat:BTreeSet<String>=v["unsatisfiable"].as_array().unwrap().iter().map(|x|x.as_str().unwrap().to_owned()).collect();
    let mut pairs=BTreeSet::new();
    for p in v["subsumptions"].as_array().unwrap() {let a=p.as_array().unwrap();assert_eq!(a.len(),2);pairs.insert((a[0].as_str().unwrap().to_owned(),a[1].as_str().unwrap().to_owned()));}
    loop {let mut add=Vec::new();for (a,b) in &pairs {for (c,d) in &pairs {if b==c && !pairs.contains(&(a.clone(),d.clone())) {add.push((a.clone(),d.clone()));}}}if add.is_empty(){break;}pairs.extend(add);}
    pairs.retain(|(a,b)|a!=b && !unsat.contains(a) && !unsat.contains(b));(consistent,unsat,pairs)
}
#[test]
fn builtin_alias_direct_frontend_six_valid_fixtures_have_identical_clause_and_meta_bytes() {
    let fixtures=[("Thing","SubClassOf(<urn:A> o:Thing)"),("Nothing","SubClassOf(<urn:A> o:Nothing)"),("topObjectProperty","SubObjectPropertyOf(<urn:r> o:topObjectProperty)"),("bottomObjectProperty","SubObjectPropertyOf(o:bottomObjectProperty <urn:r>)"),("topDataProperty","SubDataPropertyOf(<urn:d> o:topDataProperty)"),("bottomDataProperty","SubDataPropertyOf(o:bottomDataProperty <urn:d>)")];
    for (local,body) in fixtures {
        let alias=source(body);let full=alias.replace(&format!("o:{local}"),&format!("<http://www.w3.org/2002/07/owl#{local}>"));
        // Prove test fixtures are valid source, rather than comparing two drops.
        kobayashi_marust::frontend::conformance::check_user_source(&alias).unwrap();
        kobayashi_marust::frontend::conformance::check_user_source(&full).unwrap();
        let a=Fixture::new(local,&alias);let f=Fixture::new("canonical",&full);
        for split in [false,true] {assert_eq!(frontend(&a.0,split),frontend(&f.0,split),"{local},split={split}");}
    }
}
#[test]
fn builtin_alias_public_nothing_is_inconsistent_in_both_frontend_modes() {
    let alias=nothing_source();let full=alias.replace("o:Nothing","<http://www.w3.org/2002/07/owl#Nothing>");
    let a=Fixture::new("alias",&alias);let f=Fixture::new("canonical",&full);
    for split in [false,true] {
        let ao=classify(&a.0,split);let fo=classify(&f.0,split);
        for o in [&ao,&fo] {assert!(o.status.success(),"{}",String::from_utf8_lossy(&o.stderr));}
        let av:Value=serde_json::from_slice(&ao.stdout).unwrap();let fv:Value=serde_json::from_slice(&fo.stdout).unwrap();
        let ac=canonical(&av);assert!(!ac.0);assert_eq!(ac,canonical(&fv));
        let log=String::from_utf8_lossy(&ao.stderr);
        let rewrite=log.find("builtin IRI aliases canonicalized").expect("alias rewrite reached");
        let checked=log.find("second source check done").expect("canonical source passed entry boundary");
        assert!(rewrite<checked,"rewrite must precede probes at entry: {log}");
    }
}
#[test]
fn builtin_alias_incremental_source_delta_and_invalid_update_rollback_preserve_original_identity() {
    let alias=source("SubClassOf(<urn:A> o:Thing)");let full=alias.replace("o:Thing","<http://www.w3.org/2002/07/owl#Thing>");
    let invalid=full.replace("<urn:A> <http://www.w3.org/2002/07/owl#Thing>",r"<urn:A> o:Th\u0069ng");assert_ne!(invalid,full);
    let requests=[json!({"op":"init","functional_syntax":alias}),json!({"op":"replace","functional_syntax":full}),json!({"op":"replace","functional_syntax":invalid}),json!({"op":"classify"})];
    let mut child=command().arg("incremental-source").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    {let mut input=child.stdin.take().unwrap();for request in requests {serde_json::to_writer(&mut input,&request).unwrap();input.write_all(b"\n").unwrap();}}
    let out=child.wait_with_output().unwrap();assert!(out.status.success(),"{}",String::from_utf8_lossy(&out.stderr));
    let rows:Vec<Value>=String::from_utf8(out.stdout).unwrap().lines().map(|s|serde_json::from_str(s).unwrap()).collect();assert_eq!(rows.len(),4);
    assert_eq!(rows[0]["status"],"ok");assert_eq!(rows[1]["status"],"ok");assert_eq!(canonical(&rows[0]["result"]),canonical(&rows[1]["result"]));
    assert_eq!(rows[1]["receipt"]["statement_delta_verified"],true);assert_eq!(rows[1]["receipt"]["added_statements"],1);assert_eq!(rows[1]["receipt"]["removed_statements"],1);assert_eq!(rows[1]["receipt"]["added_axioms"],1);assert_eq!(rows[1]["receipt"]["removed_axioms"],1);
    assert_eq!(rows[1]["receipt"]["reused_complete_answer"],false,"different original statement bytes must not become exact replay");
    assert_eq!(rows[2]["status"],"error");assert_eq!(rows[3]["status"],"ok");assert_eq!(rows[3]["revision"],rows[1]["revision"]);assert_eq!(canonical(&rows[3]["result"]),canonical(&rows[1]["result"]));
}
#[test]
fn builtin_alias_invalid_original_input_refuses_before_rewrite() {
    for bad in [
        source("SubClassOf(<urn:A> o:Th\\u0069ng)"),source("SubClassOf(<urn:A> o:Th\\~ing)"),source("SubClassOf(<urn:A> o:Noth%69ng)"),
        nothing_source().replace("Prefix(o:=<http://www.w3.org/2002/07/owl#>)","Prefix(owl:=<urn:evil#>) Prefix(o:=<http://www.w3.org/2002/07/owl#>)"),
        nothing_source().replace("Ontology(","Ontology(Import(<urn:unresolved>) "),
        nothing_source().replace("ClassAssertion(<urn:A> <urn:a>)","DataPropertyAssertion(<urn:d> <urn:a> \"x\"^^rdfs:Literal)"),
    ] {
        let f=Fixture::new("invalid-original",&bad);let out=classify(&f.0,false);assert!(!out.status.success());assert!(out.stdout.is_empty());
        assert!(!String::from_utf8_lossy(&out.stderr).contains("builtin IRI aliases canonicalized"),"original must reject before rewrite: {}",String::from_utf8_lossy(&out.stderr));
    }
}
#[test]
fn builtin_alias_configured_rdfxml_and_turtle_keep_generated_functional_input_typed() {
    let rdfxml=r##"<?xml version="1.0"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#" xmlns:o="http://www.w3.org/2002/07/owl#">
<o:Class rdf:about="urn:A"><rdfs:subClassOf rdf:resource="http://www.w3.org/2002/07/owl#Nothing"/></o:Class>
<o:NamedIndividual rdf:about="urn:a"><rdf:type rdf:resource="urn:A"/></o:NamedIndividual>
</rdf:RDF>"##;
    let turtle=r##"@prefix o: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
<urn:A> a o:Class ; rdfs:subClassOf o:Nothing .
<urn:a> a o:NamedIndividual, <urn:A> ."##;
    for (format,source) in [("rdfxml",rdfxml),("turtle",turtle)] {
        let file=Fixture::new(format,source);
        for split in [false,true] { for no_trust in [false,true] {
            let mut c=command();c.args(["classify","--json-edges"]).arg(&file.0).env("KM_INPUT_FORMAT",format);
            if split {c.env("KM_NO_INPROC_OFN","1");}
            if no_trust {c.env("KM_NO_TRUSTED_REWRITES","1");}
            let out=c.output().unwrap();assert!(out.status.success(),"{format}, split={split}, no_trust={no_trust}: {}",String::from_utf8_lossy(&out.stderr));
            let v:Value=serde_json::from_slice(&out.stdout).unwrap();assert!(!canonical(&v).0,"A <= Nothing and A(a): {format}");
        }}
    }
}
