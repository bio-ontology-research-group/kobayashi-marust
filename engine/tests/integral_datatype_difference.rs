//! Regression: `nonNegativeInteger \ positiveInteger = {0}`, so a class with
//! two distinct non-negative-integer values and no positive one is empty.
//! Pairwise datatype relation clauses alone admit that model; the frontend's
//! finite-difference cover makes every route decide it.
use std::path::PathBuf;
use std::process::Command;

fn classify(route: &str) -> String {
    classify_fixture("integral_datatype_difference.ofn", route)
}

fn classify_fixture(name: &str, route: &str) -> String {
    let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name);
    let output = Command::new(env!("CARGO_BIN_EXE_km"))
        .arg("classify")
        .arg(fixture)
        .env("KM_ROUTE", route)
        .env("KM_THREADS", "1")
        .env("KM_HT_DDB", "1")
        .env("KM_HT_NATIVE_FULL", "1")
        .output()
        .expect("run km classify");
    assert!(output.status.success(), "{route}: {}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8(output.stdout).expect("UTF-8 output")
}

#[test]
fn finite_integral_difference_is_decided_on_every_route() {
    for route in ["auto", "production_all", "ht_bridge", "nominals"] {
        let answer: serde_json::Value = serde_json::from_str(classify(route).trim()).expect("JSON answer");
        let unsat: Vec<&str> = answer["unsatisfiable"].as_array().expect("unsat list")
            .iter().filter_map(|value| value.as_str()).collect();
        assert!(unsat.contains(&"http://x#A") && unsat.contains(&"http://x#B"), "{route}: {answer}");
    }
}

/// `DataUnionOf(integer string)` is covered by its members: a `Z` with a
/// union-valued `p` is an `X` (integer value) or a `Y` (string value).
#[test]
fn data_union_range_is_covered_by_its_members_on_every_route() {
    for route in ["auto", "production_all", "ht_bridge"] {
        let answer: serde_json::Value = serde_json::from_str(
            classify_fixture("datatype_union_cover.ofn", route).trim()).expect("JSON answer");
        let pairs = answer["subsumptions"].as_array().expect("subsumptions");
        assert!(pairs.iter().any(|pair| pair[0] == "http://x#Z" && pair[1] == "http://x#W"), "{route}: {answer}");
        assert!(!pairs.iter().any(|pair| pair[0] == "http://x#Z" && pair[1] == "http://x#X"), "{route}: {answer}");
    }
}

/// `A` has a `p` value below 100 and one from 8 on, but is neither `Low`
/// (some value <= 24) nor `High` (some value > 24): every integer is one or
/// the other, so `A` is empty. Only a cell cover of `integer` derives this;
/// pairwise relation clauses admit a value outside both halves. `B` (any
/// integer value) is `Low` or `High` but neither alone.
#[test]
fn integral_cells_decide_partitioned_ranges_on_every_route() {
    for route in ["auto", "production_all", "ht_bridge"] {
        let answer: serde_json::Value = serde_json::from_str(
            classify_fixture("integral_datatype_cells.ofn", route).trim()).expect("JSON answer");
        let unsat: Vec<&str> = answer["unsatisfiable"].as_array().expect("unsat list")
            .iter().filter_map(|value| value.as_str()).collect();
        assert!(unsat.contains(&"http://x#A"), "{route}: {answer}");
        assert!(!unsat.contains(&"http://x#B"), "{route}: {answer}");
    }
}
