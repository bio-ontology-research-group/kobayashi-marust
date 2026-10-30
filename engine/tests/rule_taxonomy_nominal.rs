//! DL-safe rules whose conclusions reach class queries through a nominal
//! (docs/DL-SAFE-RULES.md, "Rule-aware taxonomy beside a nominal",
//! 2026-10-30). Expected answers are HermiT's, with the swrlb built-ins
//! grounded over the asserted literals
//! (results/agents/2026-10-30/fr282-dropped-rules).

use std::process::{Command, Output};

fn classify(source: &str, configure: impl FnOnce(&mut Command)) -> Output {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let path = std::env::temp_dir()
        .join(format!("km-rule-taxonomy-{}-{unique}.ofn", std::process::id()));
    std::fs::write(&path, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.args(["classify", "--route", "auto"]).arg(&path);
    configure(&mut command);
    let output = command.output().unwrap();
    std::fs::remove_file(path).unwrap();
    output
}

fn answer(output: &Output) -> serde_json::Value {
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    serde_json::from_slice(&output.stdout).unwrap()
}

/// fr282 minimised: `A ⊑ {c, b}`, `D(c)`, `t(b, b)` with domain `∃s.{c}`,
/// `v(c, 4)` and the rule `s(x, y) ∧ v(y, n) ∧ n ≥ 0 → D(x)`. The rule
/// fires on `b` only through the derived edge `s(b, c)`, and `A ⊑ D` holds
/// only because `b` is `D`. v1.5.4 published `CONSISTENT 1`, `DROPPED 1`
/// without `A ⊑ D`.
const FR282_MIN: &str = include_str!("fixtures/rule_taxonomy_nominal_fr282_min.ofn");

/// `⊤ ⊑ {a}`, `⊤ ⊑ ≥2 u`, `A(a)`, `r(a, a)`, rule `r(x, y) → B(x)`: the
/// sorted stream is needed (data successors are not `a`), and the rule
/// conclusion `B(a)` makes `A ≡ B ≡ ⊤`. v1.5.4 refused it.
const TOP_ONE_OF: &str = include_str!("fixtures/rule_taxonomy_nominal_top_one_of.ofn");

#[test]
fn rule_conclusion_reaches_class_through_nominal() {
    let output = answer(&classify(FR282_MIN, |_| {}));
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(
        output["subsumptions"],
        serde_json::json!([["http://example.org/m#A", "http://example.org/m#D"]])
    );
    assert_eq!(output["unsatisfiable"], serde_json::json!([]));
}

#[test]
fn consistency_only_check_still_counts_the_rules_as_dropped() {
    let output = answer(&classify(FR282_MIN, |command| {
        command.env("KM_RULES_NO_TAXONOMY", "1");
    }));
    assert_eq!(output["consistent"], true);
    assert_ne!(output["dropped"], 0);
}

#[test]
fn binary_object_rule_beside_top_nominal_and_data_property() {
    let output = answer(&classify(TOP_ONE_OF, |_| {}));
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(
        output["subsumptions"],
        serde_json::json!([
            [":A", ":B"],
            [":B", ":A"]
        ])
    );
}

#[test]
fn declared_class_without_axioms_is_classified() {
    let source = TOP_ONE_OF.replacen("Declaration(Class(:B))", "Declaration(Class(:B)) Declaration(Class(:Z))", 1);
    let output = answer(&classify(&source, |_| {}));
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(
        output["subsumptions"],
        serde_json::json!([
            [":A", ":B"],
            [":B", ":A"],
            [":Z", ":A"],
            [":Z", ":B"]
        ])
    );
}

#[test]
fn rule_clash_beside_top_nominal_is_inconsistent() {
    let source = TOP_ONE_OF.replacen(
        "ObjectPropertyAssertion(:r :a :a)",
        "ObjectPropertyAssertion(:r :a :a) ClassAssertion(ObjectComplementOf(:B) :a)",
        1,
    );
    let output = answer(&classify(&source, |_| {}));
    assert_eq!(output["consistent"], false);
}

#[test]
fn unrepresented_rule_beside_nominal_is_refused() {
    // A `DifferentIndividualsAtom` rule has no encoding in the rule worker;
    // the taxonomy would omit it, so the input is refused with a reason
    // instead of published as DROPPED.
    let rule = "DLSafeRule(Body(ObjectPropertyAtom(<http://example.org/m#t> Variable(<http://example.org/m#x>) \
        Variable(<http://example.org/m#y>)) DifferentIndividualsAtom(Variable(<http://example.org/m#x>) \
        Variable(<http://example.org/m#y>))) Head(ClassAtom(<http://example.org/m#A> Variable(<http://example.org/m#x>))))\n)";
    let source = format!("{}{rule}\n", FR282_MIN.trim_end().strip_suffix(')').unwrap());
    let output = classify(&source, |_| {});
    assert!(!output.status.success(), "{}", String::from_utf8_lossy(&output.stdout));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("rule-aware taxonomy"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The fr282 minimum plus `K ≡ {b} ⊓ {c}` and `DifferentIndividuals(b c)`:
/// `K` is unsatisfiable only through the distinctness, which the rule
/// worker used to record without encoding (HermiT: `A ⊑ D`, `K` unsat).
#[test]
fn ground_distinctness_reaches_the_rule_taxonomy() {
    let source = include_str!("fixtures/rule_taxonomy_nominal_different.ofn");
    let output = answer(&classify(source, |_| {}));
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(
        output["subsumptions"],
        serde_json::json!([["http://example.org/m#A", "http://example.org/m#D"]])
    );
    assert_eq!(output["unsatisfiable"], serde_json::json!(["http://example.org/m#K"]));
}

/// The CB-first schedule (the rule-aware classification past its budget)
/// publishes the same answers.
#[test]
fn cb_first_schedule_gives_the_same_answers() {
    let budget = |command: &mut Command| {
        command.env("KM_RULES_TAXONOMY_BUDGET_S", "0");
    };
    let output = answer(&classify(FR282_MIN, budget));
    assert_eq!(output["consistent"], true);
    assert_eq!(output["dropped"], 0);
    assert_eq!(
        output["subsumptions"],
        serde_json::json!([["http://example.org/m#A", "http://example.org/m#D"]])
    );
    let output = answer(&classify(TOP_ONE_OF, budget));
    assert_eq!(output["dropped"], 0);
    assert_eq!(output["subsumptions"], serde_json::json!([[":A", ":B"], [":B", ":A"]]));
    let output = answer(&classify(include_str!("fixtures/rule_taxonomy_nominal_different.ofn"), budget));
    assert_eq!(output["dropped"], 0);
    assert_eq!(output["unsatisfiable"], serde_json::json!(["http://example.org/m#K"]));
}
