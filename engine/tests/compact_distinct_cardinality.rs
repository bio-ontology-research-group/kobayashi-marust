use std::process::Command;

#[test]
fn compact_distinct_witnesses_preserve_exact_cardinality_classification() {
    let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = std::env::temp_dir().join(format!("km-compact-cardinality-{}-{unique}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let input = directory.join("counted.ofn");
    std::fs::write(&input, r#"Ontology(
      Declaration(Class(<http://km.test/counts#A>))
      Declaration(Class(<http://km.test/counts#B>))
      Declaration(Class(<http://km.test/counts#C>))
      Declaration(Class(<http://km.test/counts#D>))
      Declaration(Class(<http://km.test/counts#E>))
      Declaration(ObjectProperty(<http://km.test/counts#r>))
      EquivalentClasses(<http://km.test/counts#A> ObjectExactCardinality(128 <http://km.test/counts#r>))
      EquivalentClasses(<http://km.test/counts#B> ObjectExactCardinality(129 <http://km.test/counts#r>))
      EquivalentClasses(<http://km.test/counts#C> ObjectIntersectionOf(<http://km.test/counts#A> <http://km.test/counts#B>))
      EquivalentClasses(<http://km.test/counts#D> ObjectIntersectionOf(ObjectMinCardinality(128 <http://km.test/counts#r>) ObjectComplementOf(ObjectMinCardinality(128 <http://km.test/counts#r>))))
      EquivalentClasses(<http://km.test/counts#E> ObjectIntersectionOf(ObjectMinCardinality(127 <http://km.test/counts#r>) ObjectComplementOf(ObjectMinCardinality(128 <http://km.test/counts#r>))))
    )"#).unwrap();
    let mut results = Vec::new();
    for compressed in [false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.env_remove("KM_COMPACT_DISTINCT_GROUPS");
        if compressed { command.env("KM_COMPACT_DISTINCT_GROUPS", "1"); }
        let result = command.args(["classify", "--route", "auto"]).arg(&input).output().unwrap();
        assert!(result.status.success(), "compressed={compressed}: {}", String::from_utf8_lossy(&result.stderr));
        let result: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
        assert_eq!(result["consistent"], true, "{result}");
        assert_eq!(result["dropped"], 0, "{result}");
        assert!(result["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://km.test/counts#C")), "{result}");
        assert!(!result["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://km.test/counts#A")), "{result}");
        assert!(!result["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://km.test/counts#B")), "{result}");
        assert!(result["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://km.test/counts#D")), "{result}");
        assert!(!result["unsatisfiable"].as_array().unwrap().contains(&serde_json::json!("http://km.test/counts#E")), "{result}");
        results.push(result);
    }
    assert_eq!(results[0], results[1]);
    std::fs::remove_dir_all(directory).unwrap();
}
