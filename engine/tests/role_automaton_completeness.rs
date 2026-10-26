//! Completeness of the regular role-inclusion encoding on every clause-based
//! route. Each case is an OWL EL ontology whose entailment needs a role word
//! that the one-level chain and transitivity encodings miss; the first case is
//! the seven-axiom core extracted from ORE 2015 ontology 14101. The negative
//! case checks that a sub-role's loop does not leak into its super-role.

use std::process::Command;

const ROUTES: [&str; 6] = ["elc", "cb_plain1", "cb_absorb8", "production_all", "nominals", "ht_bridge"];

fn subsumptions(case: &str, route: &str, ontology: &str) -> Vec<(String, String)> {
    let dir = std::env::temp_dir().join(format!(
        "km-ria-{}-{}-{}",
        std::process::id(),
        case.replace(' ', "-"),
        route
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{:x}.ofn", ontology.len() * 31 + route.len()));
    std::fs::write(&path, ontology).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", route])
        .arg(&path)
        .output()
        .expect("run km classify");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(out.status.success(), "{route}: {}", String::from_utf8_lossy(&out.stderr));
    let value: serde_json::Value = serde_json::from_slice(&out.stdout).expect("JSON result");
    value["subsumptions"]
        .as_array()
        .unwrap()
        .iter()
        .map(|p| (p[0].as_str().unwrap().to_string(), p[1].as_str().unwrap().to_string()))
        .collect()
}

fn ontology(axioms: &str) -> String {
    let mut decl = String::new();
    for c in ["X", "X2", "Y", "Y2", "Z", "W", "D"] {
        decl.push_str(&format!("Declaration(Class(:{c}))\n"));
    }
    for r in ["R", "R2", "R4", "P", "S", "T", "U"] {
        decl.push_str(&format!("Declaration(ObjectProperty(:{r}))\n"));
    }
    format!("Prefix(:=<urn:km-ria#>)\nOntology(<urn:km-ria>\n{decl}{axioms}\n)\n")
}

fn check(name: &str, axioms: &str, entailed: &[(&str, &str)], not_entailed: &[(&str, &str)]) {
    let text = ontology(axioms);
    for route in ROUTES {
        let subs = subsumptions(name, route, &text);
        let has = |a: &str, b: &str| subs.iter().any(|(x, y)| x == &format!(":{a}") && y == &format!(":{b}"));
        for (a, b) in entailed {
            assert!(has(a, b), "{name}, route {route}: missing {a} ⊑ {b}; got {subs:?}");
        }
        for (a, b) in not_entailed {
            assert!(!has(a, b), "{name}, route {route}: unsound {a} ⊑ {b}");
        }
    }
}

#[test]
fn chain_below_a_transitive_super_role() {
    // The ORE 14101 core: R2∘P ⊑ R2, R2 ⊑ R4, R4∘R4 ⊑ R4.
    check(
        "14101 core",
        "SubObjectPropertyOf(ObjectPropertyChain(:R2 :P) :R2)
         SubObjectPropertyOf(:R2 :R4)
         SubObjectPropertyOf(ObjectPropertyChain(:R4 :R4) :R4)
         SubClassOf(:X ObjectSomeValuesFrom(:R2 :Y))
         SubClassOf(:Y ObjectSomeValuesFrom(:P :Z))
         SubClassOf(:Z ObjectSomeValuesFrom(:R4 :W))
         SubClassOf(ObjectSomeValuesFrom(:R4 :W) :D)",
        &[("X", "D"), ("Z", "D")],
        &[],
    );
}

#[test]
fn left_recursive_chain() {
    // T∘S ⊑ T: T S S ⊑ T.
    check(
        "left recursion",
        "SubObjectPropertyOf(ObjectPropertyChain(:T :S) :T)
         SubClassOf(:X ObjectSomeValuesFrom(:T :Y))
         SubClassOf(:Y ObjectSomeValuesFrom(:S :Z))
         SubClassOf(:Z ObjectSomeValuesFrom(:S :W))
         SubClassOf(ObjectSomeValuesFrom(:T :W) :D)",
        &[("X", "D")],
        &[],
    );
}

#[test]
fn right_recursive_chain() {
    // R∘T ⊑ T: R R T ⊑ T.
    check(
        "right recursion",
        "SubObjectPropertyOf(ObjectPropertyChain(:R :T) :T)
         SubClassOf(:X ObjectSomeValuesFrom(:R :Y))
         SubClassOf(:Y ObjectSomeValuesFrom(:R :Z))
         SubClassOf(:Z ObjectSomeValuesFrom(:T :W))
         SubClassOf(ObjectSomeValuesFrom(:T :W) :D)",
        &[("X", "D")],
        &[],
    );
}

#[test]
fn transitive_chain_target() {
    // Trans(T) and R∘S ⊑ T: R S T ⊑ T.
    check(
        "transitive chain target",
        "TransitiveObjectProperty(:T)
         SubObjectPropertyOf(ObjectPropertyChain(:R :S) :T)
         SubClassOf(:X ObjectSomeValuesFrom(:R :Y))
         SubClassOf(:Y ObjectSomeValuesFrom(:S :Z))
         SubClassOf(:Z ObjectSomeValuesFrom(:T :W))
         SubClassOf(ObjectSomeValuesFrom(:T :W) :D)",
        &[("X", "D")],
        &[],
    );
}

#[test]
fn sub_role_loop_stays_local() {
    // U∘S ⊑ U and U ⊑ T: U S ⊑ T, but T S is not below T.
    check(
        "local sub-role loop",
        "SubObjectPropertyOf(ObjectPropertyChain(:U :S) :U)
         SubObjectPropertyOf(:U :T)
         SubClassOf(:X ObjectSomeValuesFrom(:U :Y))
         SubClassOf(:Y ObjectSomeValuesFrom(:S :W))
         SubClassOf(:X2 ObjectSomeValuesFrom(:T :Y2))
         SubClassOf(:Y2 ObjectSomeValuesFrom(:S :W))
         SubClassOf(ObjectSomeValuesFrom(:T :W) :D)",
        &[("X", "D")],
        &[("X2", "D")],
    );
}
