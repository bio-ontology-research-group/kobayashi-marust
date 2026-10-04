use std::process::Command;

#[test]
fn isolated_rule_frontend_preserves_source_counts_and_refuses_connected_names() {
    let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let directory = std::env::temp_dir().join(format!("km-isolated-rule-{}-{unique}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let source = include_str!("fixtures/isolated_list_rules.ofn");
    for (name, text, enabled, expected_projected) in [
        ("default", source.to_string(), false, 8),
        ("disabled", source.to_string(), false, 0),
        ("isolated", source.to_string(), true, 8),
        ("connected", source.replacen("ClassAssertion(owl:Thing", "ClassAssertion(<http://purl.org/co/List>", 1), true, 0),
        ("prefix_alias", source.replace("owl:=<http://www.w3.org/2002/07/owl#>", "owl:=<http://example.org/alias#>"), true, 0),
    ] {
        let input = directory.join(format!("{name}.ofn"));
        let meta = directory.join(format!("{name}.meta.json"));
        std::fs::write(&input, text).unwrap();
        let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
        command.env_remove("KM_ISOLATED_RULE_NORMALIZE").env_remove("KM_UNARY_DATA_RULE_NORMALIZE")
            .env_remove("KM_NO_ISOLATED_RULE_NORMALIZE");
        if name == "disabled" { command.env("KM_NO_ISOLATED_RULE_NORMALIZE", "1"); }
        if enabled { command.env("KM_ISOLATED_RULE_NORMALIZE", "1"); }
        let output = command.arg("ofn").arg(input).arg("--meta").arg(&meta).output().unwrap();
        if expected_projected == 0 {
            assert!(!output.status.success(), "{name}: an uncertified rule set was admitted");
            assert!(String::from_utf8_lossy(&output.stderr).contains("DL-safe rules"), "{name}");
            continue;
        }
        assert!(output.status.success(), "{name}: {}", String::from_utf8_lossy(&output.stderr));
        let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(meta).unwrap()).unwrap();
        assert_eq!(meta["profile"]["source"]["rule_axioms"], 8, "{name}");
        assert_eq!(meta["profile"]["isolated_named_domain_rules"], expected_projected, "{name}");
        assert_eq!(meta["profile"]["source"]["unsupported_rule_axioms"], 8 - expected_projected, "{name}");
    }
    std::fs::remove_dir_all(directory).unwrap();
}
