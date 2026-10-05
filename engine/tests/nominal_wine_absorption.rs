use std::process::Command;

#[test]
fn production_bridge_preserves_functional_nominal_universal_subsumption() {
    let input = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/nominal_wine_absorption.ofn");
    let result = Command::new(env!("CARGO_BIN_EXE_km"))
        .args(["classify", "--route", "ht_bridge"])
        .arg(input).output().expect("run km classification");
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let output: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    let pairs = output["subsumptions"].as_array().unwrap();
    for subclass in ["WhiteTableWine", "DryWhiteWine"] {
        let expected = serde_json::json!([
            format!("http://www.ifomis.org/bfo/1.1#{subclass}"),
            "http://www.ifomis.org/bfo/1.1#WhiteNonSweetWine",
        ]);
        assert!(pairs.contains(&expected),
            "{subclass}: functional hasWineSugar with the Dry nominal entails the universal restriction");
    }
    let unsupported_subsumption = serde_json::json!([
        "http://www.ifomis.org/bfo/1.1#DryWine",
        "http://www.ifomis.org/bfo/1.1#WhiteNonSweetWine",
    ]);
    assert!(!pairs.contains(&unsupported_subsumption),
        "the sugar restriction does not imply that a wine is white");
}
