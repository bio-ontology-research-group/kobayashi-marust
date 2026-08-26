//! Synthetic positive and counterexample coverage for the certified mirror
//! route.
//!
//! The positive tests classify a small ontology that carries the fragment and
//! require the reconstructed taxonomy to equal an independently stated table
//! read directly from the fixture's axioms.
//! The counterexample tests take that same ontology and break exactly one
//! premise, then require the route to decline.

use std::collections::BTreeSet;

use super::*;

/// Namespace used by every fixture.
const NS: &str = "http://example.org/mirror#";

fn iri(local: &str) -> String {
    format!("{NS}{local}")
}

fn header() -> String {
    "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
     Prefix(:=<http://example.org/mirror#>)\n"
        .to_string()
}

/// A base terminology with an inverse pair, a transitive mirror role, named
/// disjointness, and one conjunction definition through the inverse role (the
/// shape that makes a mirror inverse-relevant).
fn base_axioms() -> Vec<String> {
    [
        "Declaration(ObjectProperty(<http://example.org/mirror#hasPart>))",
        "Declaration(ObjectProperty(<http://example.org/mirror#partOf>))",
        "InverseObjectProperties(<http://example.org/mirror#partOf> <http://example.org/mirror#hasPart>)",
        "TransitiveObjectProperty(<http://example.org/mirror#hasPart>)",
        "TransitiveObjectProperty(<http://example.org/mirror#partOf>)",
        "Declaration(Class(<http://example.org/mirror#Thing1>))",
        "Declaration(Class(<http://example.org/mirror#Wheel>))",
        "Declaration(Class(<http://example.org/mirror#Spoke>))",
        "Declaration(Class(<http://example.org/mirror#Bike>))",
        "Declaration(Class(<http://example.org/mirror#Vehicle>))",
        "Declaration(Class(<http://example.org/mirror#Process>))",
        "Declaration(Class(<http://example.org/mirror#Quality>))",
        "Declaration(Class(<http://example.org/mirror#SpokeOfWheel>))",
        "SubClassOf(<http://example.org/mirror#Wheel> <http://example.org/mirror#Thing1>)",
        "SubClassOf(<http://example.org/mirror#Spoke> <http://example.org/mirror#Thing1>)",
        "SubClassOf(<http://example.org/mirror#Bike> <http://example.org/mirror#Vehicle>)",
        "SubClassOf(<http://example.org/mirror#Vehicle> <http://example.org/mirror#Thing1>)",
        // Bike has a wheel, and a wheel has a spoke: transitivity makes the
        // proxy relation reach past plain monotonicity.
        "SubClassOf(<http://example.org/mirror#Bike> ObjectSomeValuesFrom(<http://example.org/mirror#hasPart> <http://example.org/mirror#Wheel>))",
        "SubClassOf(<http://example.org/mirror#Wheel> ObjectSomeValuesFrom(<http://example.org/mirror#hasPart> <http://example.org/mirror#Spoke>))",
        // Inverse-definable filler: reached through the mirror role's inverse.
        "EquivalentClasses(<http://example.org/mirror#SpokeOfWheel> ObjectIntersectionOf(<http://example.org/mirror#Spoke> ObjectSomeValuesFrom(<http://example.org/mirror#partOf> <http://example.org/mirror#Wheel>)))",
        "DisjointClasses(<http://example.org/mirror#Process> <http://example.org/mirror#Quality>)",
        // A domain or range axiom anywhere in the mirror role's inverse/
        // hierarchy closure is refused, so the fixture states neither; the
        // counterexamples below add them one at a time.
        "Declaration(ObjectProperty(<http://example.org/mirror#actsOn>))",
        "ObjectPropertyDomain(<http://example.org/mirror#actsOn> <http://example.org/mirror#Process>)",
        "ObjectPropertyRange(<http://example.org/mirror#actsOn> <http://example.org/mirror#Quality>)",
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

/// Every mirror fixture uses the same role, so the family is a single
/// same-role block over the fillers below plus `owl:Thing`.
fn mirror_fillers() -> Vec<String> {
    [
        "http://example.org/mirror#Wheel",
        "http://example.org/mirror#Spoke",
        "http://example.org/mirror#Bike",
        "http://example.org/mirror#Vehicle",
        "http://example.org/mirror#SpokeOfWheel",
        "http://example.org/mirror#Thing1",
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

fn negative_iri(filler: &str) -> String {
    format!("{NS}not_hasPart_{}", filler.rsplit('#').next().unwrap())
}

fn mirror_axioms() -> Vec<String> {
    let mut out = Vec::new();
    for filler in mirror_fillers() {
        let negative = negative_iri(&filler);
        out.push(format!("Declaration(Class(<{negative}>))"));
        out.push(format!(
            "EquivalentClasses(<{negative}> ObjectComplementOf(ObjectSomeValuesFrom(<{NS}hasPart> <{filler}>)))"
        ));
    }
    // The owl:Thing mirror: its proxy sits above every other proxy, so its
    // negative sits below every other negative.
    let negative = format!("{NS}not_hasPart_Thing");
    out.push(format!("Declaration(Class(<{negative}>))"));
    out.push(format!(
        "EquivalentClasses(<{negative}> ObjectComplementOf(ObjectSomeValuesFrom(<{NS}hasPart> owl:Thing)))"
    ));
    out
}

fn document(axioms: &[String]) -> String {
    let mut text = header();
    text.push_str("Ontology(<http://example.org/mirror>\n");
    for axiom in axioms {
        text.push_str(axiom);
        text.push('\n');
    }
    text.push_str(")\n");
    text
}

fn fixture() -> String {
    let mut axioms = base_axioms();
    axioms.extend(mirror_axioms());
    document(&axioms)
}

// ---------------------------------------------------------------------------
// detection
// ---------------------------------------------------------------------------

#[test]
fn detects_the_private_mirror_family() {
    let fragment = detect(&fixture())
        .expect("no premise failure")
        .expect("fragment present");
    assert_eq!(fragment.mirrors().len(), mirror_fillers().len() + 1);
    // Exactly the inverse-definable filler is selected for exact treatment.
    assert_eq!(fragment.selected_count(), 1);
    let selected: Vec<&str> = fragment
        .mirrors()
        .iter()
        .filter(|m| m.selected)
        .map(|m| m.negative.as_str())
        .collect();
    assert_eq!(selected, vec![negative_iri(&iri("SpokeOfWheel"))]);
}

#[test]
fn tracks_transitivity_per_mirror_role() {
    let axioms = [
        "Declaration(ObjectProperty(<http://example.org/mirror#transitive>))",
        "Declaration(ObjectProperty(<http://example.org/mirror#plain>))",
        "TransitiveObjectProperty(<http://example.org/mirror#transitive>)",
        "Declaration(Class(<http://example.org/mirror#A>))",
        "Declaration(Class(<http://example.org/mirror#B>))",
        "Declaration(Class(<http://example.org/mirror#notTransitiveA>))",
        "Declaration(Class(<http://example.org/mirror#notPlainB>))",
        "EquivalentClasses(<http://example.org/mirror#notTransitiveA> ObjectComplementOf(ObjectSomeValuesFrom(<http://example.org/mirror#transitive> <http://example.org/mirror#A>)))",
        "EquivalentClasses(<http://example.org/mirror#notPlainB> ObjectComplementOf(ObjectSomeValuesFrom(<http://example.org/mirror#plain> <http://example.org/mirror#B>)))",
    ]
    .into_iter()
    .map(str::to_string)
    .collect::<Vec<_>>();
    let fragment = detect(&document(&axioms))
        .expect("no premise failure")
        .expect("fragment present");
    assert_eq!(
        fragment.transitive_mirror_roles,
        BTreeSet::from([iri("transitive")])
    );
}

#[test]
fn an_ontology_without_complements_is_not_the_fragment() {
    assert!(detect(&document(&base_axioms()))
        .expect("no premise failure")
        .is_none());
}

/// Entity identity follows the frontend: a prefixed name is keyed on the token
/// as written, `owl:Thing` and its full IRI are the same semantic constant, and
/// `<ex:A>` and `ex:A` are the same class. Nothing here needs a prefix map.
#[test]
fn entity_identity_matches_the_frontend() {
    assert_eq!(class_key("owl:Thing"), ClassRef::Top);
    assert_eq!(class_key(&format!("<{OWL_THING}>")), ClassRef::Top);
    assert_eq!(class_key("owl:Nothing"), ClassRef::Bottom);
    assert_eq!(class_key(&format!("<{OWL_NOTHING}>")), ClassRef::Bottom);
    assert_eq!(class_key("<ex:A>"), class_key("ex:A"));
    assert_eq!(class_key("ex:A"), ClassRef::Iri("ex:A".into()));
}

/// A prefixed-name ontology is detected exactly like a full-IRI one, in every
/// whitespace variant OWL functional syntax allows.
#[test]
fn detects_the_family_through_prefixed_names() {
    for header in [
        "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\nPrefix(ex:=<http://example.org/mirror#>)\n",
        "Prefix( owl: = <http://www.w3.org/2002/07/owl#> )\nPrefix( ex: = <http://example.org/mirror#> )\n",
        "Prefix(:=<http://example.org/mirror#>)\n",
    ] {
        let text = format!(
            "{header}Ontology(<http://example.org/mirror>\n\
             Declaration(ObjectProperty(ex:hasPart))\n\
             Declaration(Class(ex:A))\n\
             Declaration(Class(ex:N))\n\
             EquivalentClasses(ex:N ObjectComplementOf(ObjectSomeValuesFrom(ex:hasPart ex:A)))\n\
             )\n"
        );
        let fragment = detect(&text)
            .expect("no premise failure")
            .expect("fragment present");
        assert_eq!(fragment.mirrors().len(), 1);
        assert_eq!(fragment.mirrors()[0].negative, "ex:N");
        assert_eq!(fragment.mirrors()[0].role, "ex:hasPart");
    }
}

// ---------------------------------------------------------------------------
// counterexamples: one broken premise each
// ---------------------------------------------------------------------------

/// Add axioms to the fixture and return the premise the route refused on.
fn refusal(extra: &[String]) -> Premise {
    let mut axioms = base_axioms();
    axioms.extend(mirror_axioms());
    axioms.extend(extra.iter().cloned());
    refusal_of(axioms)
}

fn refusal_of(axioms: Vec<String>) -> Premise {
    match detect(&document(&axioms)) {
        Err(premise) => premise,
        Ok(other) => panic!("premise must fail, detected {}", other.is_some()),
    }
}

#[test]
fn refuses_a_negative_used_outside_its_definition() {
    let negative = negative_iri(&iri("Wheel"));
    let premise = refusal(&[format!("SubClassOf(<{negative}> <{NS}Thing1>)")]);
    assert_eq!(premise, Premise::NegativeNotPrivate(negative));
}

#[test]
fn refuses_a_complement_outside_a_mirror_definition() {
    let premise = refusal(&[format!(
        "SubClassOf(<{NS}Bike> ObjectComplementOf(<{NS}Process>))"
    )]);
    assert!(
        matches!(premise, Premise::ComplementOutsideMirror(_)),
        "{premise}"
    );
}

#[test]
fn refuses_a_disjunction_in_the_residual() {
    let premise = refusal(&[format!(
        "SubClassOf(<{NS}Bike> ObjectUnionOf(<{NS}Process> <{NS}Quality>))"
    )]);
    assert!(
        matches!(premise, Premise::NotPositiveResidual(_)),
        "{premise}"
    );
}

#[test]
fn refuses_a_universal_restriction_in_the_residual() {
    let premise = refusal(&[format!(
        "SubClassOf(<{NS}Bike> ObjectAllValuesFrom(<{NS}hasPart> <{NS}Wheel>))"
    )]);
    assert!(
        matches!(premise, Premise::NotPositiveResidual(_)),
        "{premise}"
    );
}

#[test]
fn refuses_a_cardinality_restriction_in_the_residual() {
    let premise = refusal(&[format!(
        "SubClassOf(<{NS}Bike> ObjectMinCardinality(2 <{NS}hasPart> <{NS}Wheel>))"
    )]);
    assert!(
        matches!(premise, Premise::NotPositiveResidual(_)),
        "{premise}"
    );
}

#[test]
fn refuses_a_nominal_in_the_residual() {
    let premise = refusal(&[format!("SubClassOf(<{NS}Bike> ObjectOneOf(<{NS}b1>))")]);
    assert!(
        matches!(premise, Premise::NotPositiveResidual(_)),
        "{premise}"
    );
}

#[test]
fn refuses_a_top_gci() {
    let premise = refusal(&[format!("SubClassOf(owl:Thing <{NS}Thing1>)")]);
    assert_eq!(premise, Premise::TopGci);
}

#[test]
fn refuses_a_top_equivalence() {
    let premise = refusal(&[format!("EquivalentClasses(owl:Thing <{NS}Thing1>)")]);
    assert_eq!(premise, Premise::TopGci);
}

#[test]
fn refuses_a_bottom_constructor() {
    let premise = refusal(&[format!("SubClassOf(<{NS}Bike> owl:Nothing)")]);
    assert!(
        matches!(premise, Premise::NotPositiveResidual(_)),
        "{premise}"
    );
}

#[test]
fn refuses_a_reflexive_role() {
    let premise = refusal(&[format!("ReflexiveObjectProperty(<{NS}hasPart>)")]);
    assert_eq!(premise, Premise::ReflexiveRole(iri("hasPart")));
}

#[test]
fn refuses_the_universal_role() {
    let premise = refusal(&[format!(
        "SubObjectPropertyOf(<{NS}hasPart> owl:topObjectProperty)"
    )]);
    assert_eq!(premise, Premise::UniversalRole);
}

#[test]
fn refuses_an_abox() {
    let premise = refusal(&[format!("ClassAssertion(<{NS}Bike> <{NS}b1>)")]);
    assert_eq!(premise, Premise::NotPureTbox("ClassAssertion".into()));
}

#[test]
fn refuses_a_declared_individual() {
    let premise = refusal(&[format!("Declaration(NamedIndividual(<{NS}b1>))")]);
    assert_eq!(
        premise,
        Premise::NotPureTbox("declared NamedIndividual".into())
    );
}

#[test]
fn refuses_a_data_property() {
    let premise = refusal(&[format!("DataPropertyDomain(<{NS}weight> <{NS}Bike>)")]);
    assert_eq!(premise, Premise::NotPureTbox("DataPropertyDomain".into()));
}

#[test]
fn refuses_a_rule() {
    let premise = refusal(&["DLSafeRule(Body() Head())".to_string()]);
    assert_eq!(premise, Premise::NotPureTbox("DLSafeRule".into()));
}

#[test]
fn refuses_an_import() {
    let premise = refusal(&["Import(<http://example.org/other>)".to_string()]);
    assert_eq!(premise, Premise::Imports);
}

/// A left-position existential over the mirror role would let a proxy acquire
/// base supersumers, which both the zero-cross argument and the monotonicity
/// reconstruction rule out.
#[test]
fn refuses_a_left_existential_over_the_mirror_role() {
    let premise = refusal(&[format!(
        "SubClassOf(ObjectSomeValuesFrom(<{NS}hasPart> <{NS}Wheel>) <{NS}Vehicle>)"
    )]);
    assert_eq!(
        premise,
        Premise::NoMirrorRoleLeftExistential(iri("hasPart"))
    );
}

#[test]
fn refuses_a_domain_axiom_on_the_mirror_role() {
    let premise = refusal(&[format!("ObjectPropertyDomain(<{NS}hasPart> <{NS}Thing1>)")]);
    assert_eq!(
        premise,
        Premise::NoMirrorRoleLeftExistential(iri("hasPart"))
    );
}

/// A super-role of the mirror role is just as dangerous: `∃hasPart.C` entails
/// `∃super.C`, so a left-position existential over the super-role reaches the
/// proxy all the same.
#[test]
fn refuses_a_left_existential_over_a_mirror_super_role() {
    let premise = refusal(&[
        format!("Declaration(ObjectProperty(<{NS}related>))"),
        format!("SubObjectPropertyOf(<{NS}hasPart> <{NS}related>)"),
        format!("SubClassOf(ObjectSomeValuesFrom(<{NS}related> <{NS}Wheel>) <{NS}Vehicle>)"),
    ]);
    assert_eq!(
        premise,
        Premise::NoMirrorRoleLeftExistential(iri("related"))
    );
}

#[test]
fn refuses_a_functional_mirror_role() {
    let premise = refusal(&[format!("FunctionalObjectProperty(<{NS}hasPart>)")]);
    assert_eq!(premise, Premise::MirrorRoleCardinality(iri("hasPart")));
}

/// Functionality on the *inverse* merges predecessors just as badly.
#[test]
fn refuses_a_functional_inverse_of_the_mirror_role() {
    let premise = refusal(&[format!("FunctionalObjectProperty(<{NS}partOf>)")]);
    assert_eq!(premise, Premise::MirrorRoleCardinality(iri("partOf")));
}

/// A range on the mirror role turns `P_F` into `∃R.(F ⊓ Range)`, so the filler
/// taxonomy no longer decides the proxy hierarchy.
#[test]
fn refuses_a_range_on_the_mirror_role() {
    let premise = refusal(&[format!("ObjectPropertyRange(<{NS}hasPart> <{NS}Thing1>)")]);
    assert_eq!(
        premise,
        Premise::MirrorRoleConstraint {
            role: iri("hasPart"),
            constraint: "a range axiom".into()
        }
    );
}

/// A domain on the inverse is the same axiom as a range on the mirror role.
#[test]
fn refuses_a_domain_on_the_inverse_of_the_mirror_role() {
    let premise = refusal(&[format!("ObjectPropertyDomain(<{NS}partOf> <{NS}Thing1>)")]);
    assert_eq!(
        premise,
        Premise::MirrorRoleConstraint {
            role: iri("partOf"),
            constraint: "a domain axiom".into()
        }
    );
}

/// A range on the inverse is a domain on the mirror role.
#[test]
fn refuses_a_range_on_the_inverse_of_the_mirror_role() {
    let premise = refusal(&[format!("ObjectPropertyRange(<{NS}partOf> <{NS}Thing1>)")]);
    assert_eq!(
        premise,
        Premise::MirrorRoleConstraint {
            role: iri("partOf"),
            constraint: "a range axiom".into()
        }
    );
}

/// A range on a super-role types the mirror successor just as effectively.
#[test]
fn refuses_a_range_on_a_mirror_super_role() {
    let premise = refusal(&[
        format!("Declaration(ObjectProperty(<{NS}related>))"),
        format!("SubObjectPropertyOf(<{NS}hasPart> <{NS}related>)"),
        format!("ObjectPropertyRange(<{NS}related> <{NS}Thing1>)"),
    ]);
    assert_eq!(
        premise,
        Premise::MirrorRoleConstraint {
            role: iri("related"),
            constraint: "a range axiom".into()
        }
    );
}

/// Symmetry adds the back edge, so the mirror successor is also a predecessor.
#[test]
fn refuses_a_symmetric_mirror_role() {
    let premise = refusal(&[format!("SymmetricObjectProperty(<{NS}hasPart>)")]);
    assert_eq!(
        premise,
        Premise::MirrorRoleConstraint {
            role: iri("hasPart"),
            constraint: "symmetry".into()
        }
    );
}

#[test]
fn refuses_an_asymmetric_mirror_role() {
    let premise = refusal(&[format!("AsymmetricObjectProperty(<{NS}hasPart>)")]);
    assert_eq!(
        premise,
        Premise::MirrorRoleConstraint {
            role: iri("hasPart"),
            constraint: "asymmetry".into()
        }
    );
}

#[test]
fn refuses_an_irreflexive_mirror_role() {
    let premise = refusal(&[format!("IrreflexiveObjectProperty(<{NS}partOf>)")]);
    assert_eq!(
        premise,
        Premise::MirrorRoleConstraint {
            role: iri("partOf"),
            constraint: "irreflexivity".into()
        }
    );
}

#[test]
fn refuses_a_disjoint_mirror_role() {
    let premise = refusal(&[
        format!("Declaration(ObjectProperty(<{NS}other>))"),
        format!("DisjointObjectProperties(<{NS}hasPart> <{NS}other>)"),
    ]);
    assert_eq!(
        premise,
        Premise::MirrorRoleConstraint {
            role: iri("hasPart"),
            constraint: "a property disjointness".into()
        }
    );
}

/// A domain or range on a role unrelated to any mirror role is fine: the
/// fixture states one, and the family is still detected.
#[test]
fn an_unrelated_role_may_carry_a_domain_and_range() {
    let fragment = detect(&fixture())
        .expect("no premise failure")
        .expect("fragment present");
    assert_eq!(fragment.mirrors().len(), mirror_fillers().len() + 1);
}

#[test]
fn refuses_a_chain_composed_mirror_role() {
    let premise = refusal(&[
        format!("Declaration(ObjectProperty(<{NS}other>))"),
        format!("SubObjectPropertyOf(ObjectPropertyChain(<{NS}other> <{NS}other>) <{NS}hasPart>)"),
    ]);
    assert_eq!(premise, Premise::MirrorRoleComposed(iri("hasPart")));
}

#[test]
fn refuses_comparable_mirror_roles() {
    let mut axioms = base_axioms();
    axioms.extend(mirror_axioms());
    axioms.push(format!("Declaration(ObjectProperty(<{NS}hasComponent>))"));
    axioms.push(format!(
        "SubObjectPropertyOf(<{NS}hasComponent> <{NS}hasPart>)"
    ));
    let negative = format!("{NS}not_hasComponent_Wheel");
    axioms.push(format!("Declaration(Class(<{negative}>))"));
    axioms.push(format!(
        "EquivalentClasses(<{negative}> ObjectComplementOf(ObjectSomeValuesFrom(<{NS}hasComponent> <{NS}Wheel>)))"
    ));
    let premise = refusal_of(axioms);
    assert_eq!(
        premise,
        Premise::ComparableMirrorRoles(iri("hasComponent"), iri("hasPart"))
    );
}

#[test]
fn refuses_an_undeclared_negative() {
    let mut axioms = base_axioms();
    let declaration = format!("Declaration(Class(<{NS}not_hasPart_Wheel>))");
    axioms.extend(mirror_axioms().into_iter().filter(|a| *a != declaration));
    let premise = refusal_of(axioms);
    assert_eq!(
        premise,
        Premise::UndeclaredNegative(negative_iri(&iri("Wheel")))
    );
}

#[test]
fn refuses_the_reserved_proxy_namespace() {
    let premise = refusal(&[format!("Declaration(Class(<{PROXY_IRI_PREFIX}0>))")]);
    assert_eq!(
        premise,
        Premise::ProxyNamespaceInUse(format!("{PROXY_IRI_PREFIX}0"))
    );
}

// ---------------------------------------------------------------------------
// the base-agreement certificate
// ---------------------------------------------------------------------------

fn taxonomy_of(pairs: &[(&str, &str)], unsat: &[&str]) -> Taxonomy {
    let classification = Classification {
        consistent: true,
        subsumptions: pairs
            .iter()
            .map(|(a, b)| [(*a).to_string(), (*b).to_string()])
            .collect(),
        unsatisfiable: unsat.iter().map(|c| (*c).to_string()).collect(),
        dropped: 0,
    };
    index(&classification)
}

#[test]
fn identical_base_taxonomies_agree() {
    let pairs = [("A", "B"), ("B", "C")];
    let left = taxonomy_of(&pairs, &["D"]);
    let right = taxonomy_of(&pairs, &["D"]);
    assert_eq!(base_disagreement(&left, &right), None);
}

/// The count check the certificate used to make would have passed here: the
/// same number of pairs, but a different relation.
#[test]
fn equal_pair_counts_with_different_pairs_are_a_disagreement() {
    let left = taxonomy_of(&[("A", "B"), ("B", "C")], &[]);
    let right = taxonomy_of(&[("A", "B"), ("B", "D")], &[]);
    assert_eq!(left.base_pairs, right.base_pairs);
    assert_eq!(
        base_disagreement(&left, &right),
        Some("slice lost B ⊑ C".to_string())
    );
}

#[test]
fn a_lost_base_subject_is_a_disagreement() {
    let left = taxonomy_of(&[("A", "B"), ("B", "C")], &[]);
    let right = taxonomy_of(&[("A", "B")], &[]);
    assert_eq!(
        base_disagreement(&left, &right),
        Some("slice lost every super of B".to_string())
    );
}

#[test]
fn an_invented_base_subject_is_a_disagreement() {
    let left = taxonomy_of(&[("A", "B")], &[]);
    let right = taxonomy_of(&[("A", "B"), ("C", "B")], &[]);
    assert_eq!(
        base_disagreement(&left, &right),
        Some("slice invented a base subject C".to_string())
    );
}

#[test]
fn differing_unsatisfiable_sets_are_a_disagreement() {
    let left = taxonomy_of(&[("A", "B")], &["X"]);
    let right = taxonomy_of(&[("A", "B")], &["Y"]);
    assert_eq!(
        base_disagreement(&left, &right),
        Some("slice lost unsatisfiable X".to_string())
    );
    assert_eq!(
        base_disagreement(&right, &left),
        Some("slice lost unsatisfiable Y".to_string())
    );
}

/// An unsatisfiable *proxy* is expected in the slice and absent from the base
/// projection, so it must not count as a disagreement.
#[test]
fn an_unsatisfiable_proxy_is_not_a_base_disagreement() {
    let proxy = format!("{PROXY_IRI_PREFIX}7");
    let left = taxonomy_of(&[("A", "B")], &[]);
    let right = taxonomy_of(&[("A", "B")], &[proxy.as_str()]);
    assert_eq!(base_disagreement(&left, &right), None);
}

/// The whole reconstruction must refuse, not just the helper.
#[test]
fn reconstruction_refuses_a_base_disagreement() {
    let text = fixture();
    let fragment = detect(&text).unwrap().unwrap();
    let good = taxonomy_of(&[], &[]);
    let bad = taxonomy_of(&[(&iri("Bike"), &iri("Vehicle"))], &[]);
    match reconstruct(&fragment, &good, &bad) {
        Err(premise) => assert!(
            matches!(premise, Premise::BaseTaxonomyDisagreement(_)),
            "{premise}"
        ),
        Ok(_) => panic!("reconstruction accepted a base disagreement"),
    }
}

// ---------------------------------------------------------------------------
// projection shape
// ---------------------------------------------------------------------------

#[test]
fn the_projection_declaration_universe_is_base_plus_proxies() {
    let text = fixture();
    let fragment = detect(&text).unwrap().unwrap();
    let base_path = TempPath::new(".mirror-base-test.ofn");
    let slice_path = TempPath::new(".mirror-slice-test.ofn");
    write_projections(&text, &fragment, base_path.path(), slice_path.path()).unwrap();

    let base_text = std::fs::read_to_string(base_path.path()).unwrap();
    let slice_text = std::fs::read_to_string(slice_path.path()).unwrap();
    // No private definition and no negative declaration survives.
    assert!(!base_text.contains("ObjectComplementOf"));
    assert!(!slice_text.contains("ObjectComplementOf"));
    for mirror in fragment.mirrors() {
        assert!(
            !base_text.contains(&format!("Declaration(Class(<{}>))", mirror.negative)),
            "negative declaration survived: {}",
            mirror.negative
        );
        assert!(slice_text.contains(&format!("Declaration(Class(<{}>))", mirror.proxy)));
        // Every mirror gets the neighbour slice; only the selected ones also
        // get the source half that makes them query roots.
        let source_half = format!("SubClassOf(<{}> ObjectSomeValuesFrom", mirror.proxy);
        assert_eq!(slice_text.contains(&source_half), mirror.selected);
    }
}

#[test]
fn large_source_prefilter_requires_a_mirror_scale_complement_family() {
    assert!(mirror_parse_worthwhile(1024, 0));
    assert!(!mirror_parse_worthwhile(
        MIRROR_PREFILTER_LARGE_BYTES,
        MIRROR_PREFILTER_MIN_COMPLEMENTS - 1
    ));
    assert!(mirror_parse_worthwhile(
        MIRROR_PREFILTER_LARGE_BYTES,
        MIRROR_PREFILTER_MIN_COMPLEMENTS
    ));
}
