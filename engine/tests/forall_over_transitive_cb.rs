//! Universals over transitive roles on the CB routes.
//!
//! The CB clause stream drops the raw transitivity axioms and kept only the
//! `∃`-consumer recognitions, so `∀t.F` was applied along one edge only. Each
//! case states the subsumption HermiT 1.4.3 entails (`isEntailed`); every CB
//! route that answers, and the automatic route, must print it.

use std::path::PathBuf;
use std::process::Command;

const P: &str = "Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n";
const DECL: &str = "Declaration(Class(:A)) Declaration(Class(:C)) Declaration(Class(:D)) Declaration(Class(:E))\n\
    Declaration(Class(:F)) Declaration(Class(:Q)) Declaration(ObjectProperty(:s0)) Declaration(ObjectProperty(:s2))\n\
    Declaration(ObjectProperty(:t0))\n";

/// (name, axioms, entailed `SUB` row as `sub sup`).
const CASES: &[(&str, &str, &str)] = &[
    (
        // Q ⊑ ∀t.F, t transitive ⟹ Q ⊑ ∀t.∀t.F
        "forward",
        "TransitiveObjectProperty(:t0) SubClassOf(:Q ObjectAllValuesFrom(:t0 :F))\n\
         EquivalentClasses(:E ObjectAllValuesFrom(:t0 ObjectAllValuesFrom(:t0 :F)))",
        "Q E",
    ),
    (
        // through a sub-role: s ⊑ t ⟹ Q ⊑ ∀s.∀s.F
        "subrole",
        "TransitiveObjectProperty(:t0) SubObjectPropertyOf(:s0 :t0) SubClassOf(:Q ObjectAllValuesFrom(:t0 :F))\n\
         EquivalentClasses(:E ObjectAllValuesFrom(:s0 ObjectAllValuesFrom(:s0 :F)))",
        "Q E",
    ),
    (
        // the reported case: the loop t(q,x), t(x,q) through a symmetric sub-role,
        // with an unrelated inverse existential that makes the HT bridge decline
        "symmetric_loop_with_inverse_existential",
        "SymmetricObjectProperty(:s0) TransitiveObjectProperty(:t0) SubObjectPropertyOf(:s0 :t0)\n\
         SubClassOf(:D ObjectSomeValuesFrom(:s0 :D)) SubClassOf(:C :D)\n\
         SubClassOf(:C ObjectSomeValuesFrom(ObjectInverseOf(:s2) :A))\n\
         EquivalentClasses(:Q ObjectIntersectionOf(:C ObjectAllValuesFrom(:t0 :F)))",
        "Q F",
    ),
    (
        // an inverse sub-role: s⁻ ⊑ t
        "inverse_subrole_loop",
        "TransitiveObjectProperty(:t0) SubObjectPropertyOf(:s0 :t0) SubObjectPropertyOf(ObjectInverseOf(:s0) :t0)\n\
         SubClassOf(:D ObjectSomeValuesFrom(:s0 owl:Thing))\n\
         EquivalentClasses(:Q ObjectIntersectionOf(:D ObjectAllValuesFrom(:t0 :F)))",
        "Q F",
    ),
    (
        // a universal over the inverse of a transitive role: Q ⊑ ∀t⁻.F
        "universal_over_inverse",
        "TransitiveObjectProperty(:t0) SubClassOf(:Q ObjectAllValuesFrom(ObjectInverseOf(:t0) :F))\n\
         EquivalentClasses(:E ObjectAllValuesFrom(ObjectInverseOf(:t0) ObjectAllValuesFrom(ObjectInverseOf(:t0) :F)))",
        "Q E",
    ),
];

fn write_case(name: &str, axioms: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("forall_over_transitive_cb");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.ofn"));
    std::fs::write(&path, format!("{P}Ontology(<http://ex.org/{name}>\n{DECL}{axioms}\n)\n")).unwrap();
    path
}

/// `None` when the route declines (non-zero exit).
fn subs(path: &PathBuf, route: &str) -> Option<Vec<String>> {
    let mut command = Command::new(env!("CARGO_BIN_EXE_km"));
    for (key, _) in std::env::vars() {
        if key.starts_with("KM_") {
            command.env_remove(key);
        }
    }
    command.env("KM_THREADS", "1").env("KM_ROUTE", route).arg("classify").arg("--lines").arg(path);
    let out = command.output().unwrap();
    if !out.status.success() {
        return None;
    }
    Some(
        String::from_utf8(out.stdout)
            .unwrap()
            .lines()
            .filter_map(|l| l.strip_prefix("SUB\t"))
            .map(|l| l.split('\t').map(|t| t.trim_start_matches(':')).collect::<Vec<_>>().join(" "))
            .collect(),
    )
}

#[test]
fn universals_over_transitive_roles_on_cb_routes() {
    for (name, axioms, expected) in CASES {
        let path = write_case(name, axioms);
        let mut answered = 0;
        for route in ["auto", "production_all", "cb_plain1", "cb_absorb1", "cb_trigger1", "lean"] {
            if let Some(rows) = subs(&path, route) {
                answered += 1;
                assert!(rows.iter().any(|r| r == expected), "{name} on {route}: missing SUB {expected}: {rows:?}");
            }
        }
        assert!(answered >= 2, "{name}: fewer than two routes answered");
    }
}
