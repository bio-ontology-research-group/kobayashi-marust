use std::process::Command;

fn classify(name: &str, body: &str) -> serde_json::Value {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/unary-rule-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}-{name}.ofn", std::process::id()));
    std::fs::write(&path, format!("Ontology(
      Declaration(Class(<http://e/P>)) Declaration(Class(<http://e/Q>))
      {body}
      DLSafeRule(Body(ClassAtom(<http://e/P> Variable(<http://e/x>)))
        Head(ClassAtom(<http://e/Q> Variable(<http://e/x>))))
    )")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", "auto"]).arg(&path).output().unwrap();
    std::fs::remove_file(path).unwrap();
    assert!(output.status.success(), "{name}: {}", String::from_utf8_lossy(&output.stderr));
    let answer: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(answer["dropped"], 0, "{name}");
    answer
}

#[test]
fn nominal_rule_consequence_enters_taxonomy() {
    let answer = classify("covered", "EquivalentClasses(<http://www.w3.org/2002/07/owl#Thing> ObjectOneOf(<http://e/a>))");
    assert_eq!(answer["consistent"], true);
    assert!(answer["subsumptions"].as_array().unwrap().contains(&serde_json::json!(["http://e/P", "http://e/Q"])));
}

#[test]
fn anonymous_query_witness_is_not_added_to_the_named_guard() {
    for (name, body) in [("no_names", ""), ("declared_name", "Declaration(NamedIndividual(<http://e/a>))")] {
        let answer = classify(name, body);
        assert_eq!(answer["consistent"], true);
        assert!(!answer["subsumptions"].as_array().unwrap().contains(&serde_json::json!(["http://e/P", "http://e/Q"])));
    }
}

#[test]
fn named_rule_clash_is_preserved() {
    let answer = classify("clash", "ClassAssertion(<http://e/P> <http://e/a>) DisjointClasses(<http://e/P> <http://e/Q>)");
    assert_eq!(answer["consistent"], false);
}

#[test]
fn alias_individual_names_need_no_unique_name_assumption() {
    let answer = classify("alias", "EquivalentClasses(<http://www.w3.org/2002/07/owl#Thing> ObjectOneOf(<http://e/a> <http://e/b>)) SameIndividual(<http://e/a> <http://e/b>)");
    assert_eq!(answer["consistent"], true);
    assert!(answer["subsumptions"].as_array().unwrap().contains(&serde_json::json!(["http://e/P", "http://e/Q"])));
}

#[test]
fn conjunctions_and_every_head_consequence_are_preserved() {
    let answer = classify("conjunctions", "
      Declaration(Class(<http://e/R>)) Declaration(Class(<http://e/S>))
      EquivalentClasses(<http://www.w3.org/2002/07/owl#Thing> ObjectOneOf(<http://e/a>))
      SubClassOf(<http://e/P> <http://e/R>)
      DLSafeRule(Body(ClassAtom(<http://e/P> Variable(<http://e/y>)) ClassAtom(<http://e/R> Variable(<http://e/y>)))
        Head(ClassAtom(<http://e/Q> Variable(<http://e/y>)) ClassAtom(<http://e/S> Variable(<http://e/y>))))");
    let pairs = answer["subsumptions"].as_array().unwrap();
    assert!(pairs.contains(&serde_json::json!(["http://e/P", "http://e/Q"])));
    assert!(pairs.contains(&serde_json::json!(["http://e/P", "http://e/S"])));
    assert!(!pairs.contains(&serde_json::json!(["http://e/R", "http://e/S"])));
}

#[test]
fn a_nonunary_rule_prevents_partial_rule_elision() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
        .join(".work/inputs/unary-rule-tests");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}-mixed.ofn", std::process::id()));
    std::fs::write(&path, "Ontology(
      Declaration(NamedIndividual(<http://e/a>))
      DLSafeRule(Body(ClassAtom(<http://e/P> Variable(<http://e/x>))) Head(ClassAtom(<http://e/Q> Variable(<http://e/x>))))
      DLSafeRule(Body(ObjectPropertyAtom(<http://e/r> Variable(<http://e/x>) Variable(<http://e/y>))) Head(ClassAtom(<http://e/Q> Variable(<http://e/x>))))
    )").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("profile").arg(&path).output().unwrap();
    std::fs::remove_file(path).unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let answer: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(answer["profile"]["normalized_unary_rules"], 0);
    assert_eq!(answer["profile"]["source"]["rule_axioms"], 2);
    assert_eq!(answer["selected_route"], "ht_rules");
}

#[test]
fn anonymous_source_individual_is_not_a_dl_safe_name() {
    let answer = classify("anonymous_source", "ClassAssertion(<http://e/P> _:anonymous) DisjointClasses(<http://e/P> <http://e/Q>)");
    assert_eq!(answer["consistent"], true);
}
