//! Object guard for the native bridge (docs/NOMINALS-CB.md, "Object guard
//! for the native bridge").
//!
//! The native Konclude bridge keeps data successors in its completion graph
//! as ordinary nodes. Its datatype admission therefore requires that every
//! non-datatype source axiom holds at an element with no concept name, no
//! role edge and no individual (a "blank" element), and defers otherwise
//! (`a non-datatype axiom rejects a blank data node`, `a complex datatype
//! subclass axiom can fire on a data node`). Under OWL 2's two sorts such an
//! axiom constrains objects only; read one-sorted, it would also constrain
//! the data successors.
//!
//! This pass rewrites the parsed ontology `O` into `O'` with a fresh internal
//! class `G` (`__objguard__`):
//!
//! * every class axiom that fails at a blank element gets `G` on its left:
//!   `C ⊑ D` becomes `G ⊓ C ⊑ D` (an equivalence is split into its two
//!   inclusions, a disjointness `C ⊓ D ⊑ ⊥` becomes `G ⊓ C ⊓ D ⊑ ⊥`);
//! * a class axiom with a datatype becomes its inclusions (the bridge's
//!   datatype admission reads inclusions only), and each of them whose left
//!   side holds at a blank element, `⊤` included, gets `G` (guarding an
//!   axiom that already holds there is as exact as guarding one that fails);
//! * `A ⊑ G` for every class name `A` of the signature: used in an axiom,
//!   declared only, or named only in an RBox domain or range record;
//! * `∃r.⊤ ⊑ G` and `⊤ ⊑ ∀r.G` for every object role `r` (an inverse role
//!   `r⁻` has its edges covered by the same two axioms);
//! * `{a} ⊑ G` for every named individual `a`.
//!
//! Two equivalence-preserving normalisations ride along, because the bridge's
//! datatype admission reads only one spelling of each:
//!
//! * a class assertion `C(a)` whose `C` holds a datatype outside the bridge's
//!   admitted assertion shape becomes the nominal inclusion `{a} ⊑ C`
//!   (`a ∈ C` iff `{a} ⊆ C`);
//! * `∃u.⊤` for a data role `u` becomes `≥1 u.⊤` (the same concept).
//!
//! The pass applies only when `O` has a data role and a named individual, no
//! DL-safe rule, no reflexive role, no self restriction and no universal
//! role, and when at least one axiom is guarded, an assertion moves, or a
//! datatype-bearing axiom is normalised. Otherwise `O` is returned unchanged.
//!
//! Exactness (two-sorted OWL 2 semantics, object domain `Δ`):
//!
//! 1. A model `I` of `O` is a model of `O'` with `G := Δ`: every added
//!    axiom has `G` on its right or concludes `G`, and every guarded axiom is
//!    weaker than the original.
//! 2. Let `J` be a model of `O'` and `K` its restriction to `G^J` (the object
//!    domain cut down to `G^J`; data values and their data edges unchanged).
//!    `G^J` contains every individual, so `K` interprets them; it is closed
//!    under object edges in both directions (domain and range of every object
//!    role), and it contains every member of a named class. By induction on
//!    concepts, every class expression of `O` has in `K` the extension it has
//!    in `J`, intersected with `G^J`: names by restriction, nominals because
//!    individuals stay, `∃`, `∀`, number restrictions on object roles because
//!    every neighbour of a `G` element is a `G` element, data restrictions
//!    because data edges are unchanged. So every axiom of `O`, guarded or
//!    not, holds at every element of `K`, and the assertions hold.
//!    (No reflexive role, self restriction or universal role occurs, so no
//!    edge leaves `G^J` through those either.)
//!
//! Hence `O` and `O'` have the same consistency; and since `A ⊑ G` for every
//! named class, a named class `A ⊓ ¬B` is satisfiable in `O'` iff it is in
//! `O` (take `K` above, which keeps the witness, a `G` element), so the
//! subsumptions and unsatisfiable classes over the source signature agree.
//! `G` is internal (`__` prefix, never a named IRI), so it is not published.
//!
//! After the pass every class axiom holds at a blank element (its left side
//! starts with `G`, or it held there already, or it is one of the added
//! axioms, each of which holds at a blank element), so the bridge's blank
//! data node gate is met by construction. Whether the bridge's one-sorted
//! reading of `O'` is exact is the bridge's own admission argument, which
//! this pass does not change. The bridge has no Lean model. Step 2 is proved
//! in `lean/ContextCalculus/ObjectGuardRestriction.lean` (`restrict_holds`,
//! `guarded_inclusion_restricted`, `witness_restricted`); the correspondence
//! between this code and that model (the blank evaluation, the collected
//! vocabulary) is argued, not checked.

use std::collections::BTreeSet;

use super::syntax::{mk_and, Axiom, Concept, Ontology, Role};

/// The guard class. The `__` prefix keeps it out of the named-class output.
pub const GUARD: &str = "__objguard__";

/// Environment switch set by the orchestrator for the guarded bridge attempt.
pub const ENV: &str = "KM_BRIDGE_OBJECT_GUARD";

/// A raw source name in the OWL, RDF, RDFS or XSD vocabulary (a builtin
/// class or a datatype), which never gets `A ⊑ G`.
pub fn builtin_vocabulary(raw: &str) -> bool {
    let raw = raw.trim_start_matches('<');
    ["owl:", "rdf:", "rdfs:", "xsd:"].iter().any(|prefix| raw.starts_with(prefix))
        || [
            "http://www.w3.org/2002/07/owl#",
            "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
            "http://www.w3.org/2000/01/rdf-schema#",
            "http://www.w3.org/2001/XMLSchema#",
        ]
        .iter()
        .any(|namespace| raw.starts_with(namespace))
}

pub fn requested() -> bool {
    std::env::var_os(ENV).is_some_and(|value| value != "0")
}

/// Truth value of `concept` at an element with no concept name, no role
/// edge (object or data) and no individual. `None` for a self restriction
/// or a universal-role restriction, which the pass refuses.
pub fn holds_at_blank(concept: &Concept) -> Option<bool> {
    Some(match concept {
        Concept::Name(_) | Concept::Bottom | Concept::Nominal(_) => false,
        Concept::Top => true,
        Concept::Not(inner) => !holds_at_blank(inner)?,
        Concept::And(conjuncts) => {
            let mut value = true;
            for conjunct in conjuncts {
                value &= holds_at_blank(conjunct)?;
            }
            value
        }
        Concept::Or(disjuncts) => {
            let mut value = false;
            for disjunct in disjuncts {
                value |= holds_at_blank(disjunct)?;
            }
            value
        }
        Concept::Exists(Role::Universal, _)
        | Concept::Forall(Role::Universal, _)
        | Concept::AtLeast(_, Role::Universal, _)
        | Concept::AtMost(_, Role::Universal, _)
        | Concept::HasSelf(_) => return None,
        Concept::Exists(..) => false,
        Concept::Forall(..) => true,
        Concept::AtLeast(n, ..) => *n <= 0,
        Concept::AtMost(n, ..) => *n >= 0,
    })
}

fn guarded(left: &Concept) -> Concept {
    mk_and([Concept::Name(GUARD.to_string()), left.clone()])
}

fn collect_concept(
    concept: &Concept,
    names: &mut BTreeSet<String>,
    roles: &mut BTreeSet<String>,
    individuals: &mut BTreeSet<String>,
    refused: &mut bool,
) {
    let mut role = |role: &Role, roles: &mut BTreeSet<String>, refused: &mut bool| match role {
        Role::Name(name) | Role::Inverse(name) => {
            roles.insert(name.clone());
        }
        Role::Universal => *refused = true,
    };
    match concept {
        Concept::Name(name) => {
            names.insert(name.clone());
        }
        Concept::Top | Concept::Bottom => {}
        Concept::Nominal(individual) => {
            individuals.insert(individual.clone());
        }
        Concept::Not(inner) => collect_concept(inner, names, roles, individuals, refused),
        Concept::And(parts) | Concept::Or(parts) => {
            for part in parts {
                collect_concept(part, names, roles, individuals, refused);
            }
        }
        Concept::Exists(r, filler)
        | Concept::Forall(r, filler)
        | Concept::AtLeast(_, r, filler)
        | Concept::AtMost(_, r, filler) => {
            role(r, roles, refused);
            collect_concept(filler, names, roles, individuals, refused);
        }
        Concept::HasSelf(_) => *refused = true,
    }
}

fn contains_datatype(concept: &Concept) -> bool {
    match concept {
        Concept::Name(name) => name.starts_with("__dt__"),
        Concept::Not(inner) => contains_datatype(inner),
        Concept::And(parts) | Concept::Or(parts) => parts.iter().any(contains_datatype),
        Concept::Exists(_, filler)
        | Concept::Forall(_, filler)
        | Concept::AtLeast(_, _, filler)
        | Concept::AtMost(_, _, filler) => contains_datatype(filler),
        Concept::Top | Concept::Bottom | Concept::Nominal(_) | Concept::HasSelf(_) => false,
    }
}

/// The bridge's admitted shape of a datatype assertion (`bridge.rs`,
/// `positive_data_assertion`), admitted only on the data-assertion attempt.
fn positive_data_assertion(concept: &Concept) -> bool {
    match concept {
        Concept::And(parts) => parts.iter().all(positive_data_assertion),
        Concept::Exists(_, filler) => match filler.as_ref() {
            Concept::Name(name) if name.starts_with("__dt__") => true,
            other => !contains_datatype(other),
        },
        other => !contains_datatype(other),
    }
}

/// A class assertion `C(a)` with a datatype the bridge's ABox path does not
/// admit. It becomes the equivalent nominal inclusion `{a} ⊑ C` (`a ∈ C^I`
/// iff `{a}^I ⊆ C^I`), which the bridge's TBox admission reads.
fn assertion_to_tbox(concept: &Concept) -> bool {
    contains_datatype(concept)
        && !(std::env::var_os("KM_DATA_ASSERTION_AS_CLASS").is_some_and(|value| value != "0")
            && positive_data_assertion(concept))
}

/// `∃u.⊤` for a data role `u` becomes the equal `≥1 u.⊤`, the form the
/// bridge's data-role admission reads (`DataPropertyDomain(u C)` parses to
/// `∃u.⊤ ⊑ C`, `DataMinCardinality(1 u)` to `≥1 u.⊤`). Returns `None` when
/// nothing changes.
fn normalize_data_exists(concept: &Concept, data_roles: &BTreeSet<String>) -> Option<Concept> {
    let mut changed = false;
    let rewritten = normalize_into(concept, data_roles, &mut changed);
    changed.then_some(rewritten)
}

fn normalize_into(concept: &Concept, data_roles: &BTreeSet<String>, changed: &mut bool) -> Concept {
    let mut inner = |c: &Concept, changed: &mut bool| Box::new(normalize_into(c, data_roles, changed));
    match concept {
        Concept::Exists(Role::Name(role), filler)
            if data_roles.contains(role) && matches!(filler.as_ref(), Concept::Top) =>
        {
            *changed = true;
            Concept::AtLeast(1, Role::Name(role.clone()), Box::new(Concept::Top))
        }
        Concept::Not(c) => Concept::Not(inner(c, changed)),
        Concept::And(parts) => Concept::And(parts.iter().map(|c| normalize_into(c, data_roles, changed)).collect()),
        Concept::Or(parts) => Concept::Or(parts.iter().map(|c| normalize_into(c, data_roles, changed)).collect()),
        Concept::Exists(r, c) => Concept::Exists(r.clone(), inner(c, changed)),
        Concept::Forall(r, c) => Concept::Forall(r.clone(), inner(c, changed)),
        Concept::AtLeast(n, r, c) => Concept::AtLeast(*n, r.clone(), inner(c, changed)),
        Concept::AtMost(n, r, c) => Concept::AtMost(*n, r.clone(), inner(c, changed)),
        other => other.clone(),
    }
}

/// The replacement of one source axiom, `None` when it stays.
fn rewrite(axiom: &Axiom, data_roles: &BTreeSet<String>) -> Option<Vec<Axiom>> {
    let normalized = |c: &Concept| normalize_data_exists(c, data_roles);
    let (left, right) = match axiom {
        Axiom::SubClassOf(l, r) | Axiom::EquivalentClasses(l, r)
        | Axiom::DisjointClasses(l, r) => (l, r),
        Axiom::ConceptAssertion(concept, individual) => {
            let new = normalized(concept);
            let concept_now = new.as_ref().unwrap_or(concept);
            if assertion_to_tbox(concept_now) {
                return Some(vec![Axiom::SubClassOf(
                    Concept::Nominal(individual.clone()),
                    concept_now.clone(),
                )]);
            }
            return new.map(|c| vec![Axiom::ConceptAssertion(c, individual.clone())]);
        }
        _ => return None,
    };
    let (new_left, new_right) = (normalized(left), normalized(right));
    let changed = new_left.is_some() || new_right.is_some();
    let left = new_left.as_ref().unwrap_or(left);
    let right = new_right.as_ref().unwrap_or(right);
    let (l, r) = (holds_at_blank(left)?, holds_at_blank(right)?);
    let guard = Concept::Name(GUARD.to_string());
    if contains_datatype(left) || contains_datatype(right) {
        return datatype_inclusions(axiom, left, right, changed);
    }
    match axiom {
        Axiom::SubClassOf(..) if l && !r => {
            Some(vec![Axiom::SubClassOf(guarded(left), right.clone())])
        }
        Axiom::EquivalentClasses(..) if l != r => {
            let (blank_true, other) = if l { (left, right) } else { (right, left) };
            Some(vec![
                Axiom::SubClassOf(guarded(blank_true), other.clone()),
                Axiom::SubClassOf(other.clone(), blank_true.clone()),
            ])
        }
        Axiom::DisjointClasses(..) if l && r => Some(vec![Axiom::SubClassOf(
            mk_and([guard, left.clone(), right.clone()]),
            Concept::Bottom,
        )]),
        Axiom::SubClassOf(..) if changed => {
            Some(vec![Axiom::SubClassOf(left.clone(), right.clone())])
        }
        Axiom::EquivalentClasses(..) if changed => {
            Some(vec![Axiom::EquivalentClasses(left.clone(), right.clone())])
        }
        Axiom::DisjointClasses(..) if changed => {
            Some(vec![Axiom::DisjointClasses(left.clone(), right.clone())])
        }
        _ => None,
    }
}

/// A construct the pass refuses anywhere in a concept: a self restriction or
/// the universal role.
fn refused_construct(concept: &Concept) -> bool {
    match concept {
        Concept::HasSelf(_) => true,
        Concept::Exists(Role::Universal, _)
        | Concept::Forall(Role::Universal, _)
        | Concept::AtLeast(_, Role::Universal, _)
        | Concept::AtMost(_, Role::Universal, _) => true,
        Concept::Not(inner) => refused_construct(inner),
        Concept::And(parts) | Concept::Or(parts) => parts.iter().any(refused_construct),
        Concept::Exists(_, filler)
        | Concept::Forall(_, filler)
        | Concept::AtLeast(_, _, filler)
        | Concept::AtMost(_, _, filler) => refused_construct(filler),
        Concept::Name(_) | Concept::Top | Concept::Bottom | Concept::Nominal(_) => false,
    }
}

fn mentions_nominal(concept: &Concept) -> bool {
    match concept {
        Concept::Nominal(_) => true,
        Concept::Not(inner) => mentions_nominal(inner),
        Concept::And(parts) | Concept::Or(parts) => parts.iter().any(mentions_nominal),
        Concept::Exists(_, filler)
        | Concept::Forall(_, filler)
        | Concept::AtLeast(_, _, filler)
        | Concept::AtMost(_, _, filler) => mentions_nominal(filler),
        Concept::Name(_) | Concept::Top | Concept::Bottom | Concept::HasSelf(_) => false,
    }
}

/// `∃u.⊤` for a data role `u` occurs (what `normalize_data_exists` changes).
fn mentions_data_exists_top(concept: &Concept, data_roles: &BTreeSet<String>) -> bool {
    match concept {
        Concept::Exists(Role::Name(role), filler)
            if data_roles.contains(role) && matches!(filler.as_ref(), Concept::Top) => true,
        Concept::Not(inner) => mentions_data_exists_top(inner, data_roles),
        Concept::And(parts) | Concept::Or(parts) => {
            parts.iter().any(|part| mentions_data_exists_top(part, data_roles))
        }
        Concept::Exists(_, filler)
        | Concept::Forall(_, filler)
        | Concept::AtLeast(_, _, filler)
        | Concept::AtMost(_, _, filler) => mentions_data_exists_top(filler, data_roles),
        Concept::Name(_) | Concept::Top | Concept::Bottom | Concept::Nominal(_)
        | Concept::HasSelf(_) => false,
    }
}

/// Whether [`encode`] would change `ontology`: it has a data role and an
/// individual, no refused construct, and some axiom is guarded, an assertion
/// moves, or a datatype-bearing axiom is normalised. One pass, no
/// allocation; run on every frontend pass.
pub fn applies(ontology: &Ontology, data_roles: &BTreeSet<String>) -> bool {
    if data_roles.is_empty() {
        return false;
    }
    let mut individual = false;
    let mut effective = false;
    for axiom in ontology.axioms_iter() {
        match axiom {
            Axiom::SubClassOf(left, right)
            | Axiom::EquivalentClasses(left, right)
            | Axiom::DisjointClasses(left, right) => {
                if refused_construct(left) || refused_construct(right) {
                    return false;
                }
                individual = individual || mentions_nominal(left) || mentions_nominal(right);
                if !effective {
                    let (l, r) = (holds_at_blank(left), holds_at_blank(right));
                    let (Some(l), Some(r)) = (l, r) else { return false };
                    let fails = match axiom {
                        Axiom::SubClassOf(..) => l && !r,
                        Axiom::EquivalentClasses(..) => l != r,
                        _ => l && r,
                    };
                    let datatype = contains_datatype(left) || contains_datatype(right);
                    effective = fails
                        || (datatype
                            && (!matches!(axiom, Axiom::SubClassOf(..))
                                || l
                                || mentions_data_exists_top(left, data_roles)
                                || mentions_data_exists_top(right, data_roles)));
                }
            }
            Axiom::ConceptAssertion(concept, _) => {
                if refused_construct(concept) {
                    return false;
                }
                individual = true;
                effective = effective
                    || assertion_to_tbox(concept)
                    || (contains_datatype(concept) && mentions_data_exists_top(concept, data_roles));
            }
            Axiom::RoleAssertion(..)
            | Axiom::NegativeRoleAssertion(..)
            | Axiom::SameIndividual(..)
            | Axiom::DifferentIndividuals(..) => individual = true,
            Axiom::ReflexiveRole(_) | Axiom::Rule(..) | Axiom::DataRule(..) => return false,
            _ => {}
        }
    }
    individual && effective
}

struct Scan {
    names: BTreeSet<String>,
    roles: BTreeSet<String>,
    individuals: BTreeSet<String>,
}

/// The vocabulary of `ontology`: class names, role names, individuals.
fn scan(ontology: &Ontology) -> Scan {
    let mut names = BTreeSet::new();
    let mut roles = BTreeSet::new();
    let mut individuals = BTreeSet::new();
    let mut refused = false;
    for axiom in ontology.axioms_iter() {
        match axiom {
            Axiom::SubClassOf(left, right)
            | Axiom::EquivalentClasses(left, right)
            | Axiom::DisjointClasses(left, right) => {
                collect_concept(left, &mut names, &mut roles, &mut individuals, &mut refused);
                collect_concept(right, &mut names, &mut roles, &mut individuals, &mut refused);
            }
            Axiom::ConceptAssertion(concept, individual) => {
                collect_concept(concept, &mut names, &mut roles, &mut individuals, &mut refused);
                individuals.insert(individual.clone());
            }
            Axiom::RoleAssertion(role, a, b) | Axiom::NegativeRoleAssertion(role, a, b) => {
                roles.insert(role.clone());
                individuals.insert(a.clone());
                individuals.insert(b.clone());
            }
            Axiom::SameIndividual(a, b) | Axiom::DifferentIndividuals(a, b) => {
                individuals.insert(a.clone());
                individuals.insert(b.clone());
            }
            Axiom::RoleInclusion(sub, sup) | Axiom::InverseRoles(sub, sup)
            | Axiom::DisjointRoles(sub, sup) => {
                roles.insert(sub.clone());
                roles.insert(sup.clone());
            }
            Axiom::RoleChain(chain, sup) => {
                roles.extend(chain.iter().cloned());
                roles.insert(sup.clone());
            }
            Axiom::TransitiveRole(role)
            | Axiom::SymmetricRole(role)
            | Axiom::AsymmetricRole(role)
            | Axiom::IrreflexiveRole(role)
            | Axiom::FunctionalRole(role)
            | Axiom::InverseFunctionalRole(role)
            | Axiom::ReflexiveRole(role) => {
                roles.insert(role.clone());
            }
            Axiom::Rule(..) | Axiom::DataRule(..) => {}
        }
    }
    debug_assert!(!refused, "applies() refuses these constructs first");
    Scan { names, roles, individuals }
}

/// A datatype-bearing class axiom. The bridge's datatype admission reads
/// inclusions whose left side is false at a blank node, so the axiom becomes
/// its inclusions (an equivalence both directions, a disjointness
/// `C ⊓ D ⊑ ⊥`) and every inclusion whose left side holds at a blank element
/// (`⊤` included) gets the guard. `None` when a plain inclusion needs
/// neither the guard nor the normalisation.
fn datatype_inclusions(axiom: &Axiom, left: &Concept, right: &Concept, changed: bool) -> Option<Vec<Axiom>> {
    let inclusions: Vec<(Concept, Concept)> = match axiom {
        Axiom::SubClassOf(..) => vec![(left.clone(), right.clone())],
        Axiom::EquivalentClasses(..) => {
            vec![(left.clone(), right.clone()), (right.clone(), left.clone())]
        }
        _ => vec![(mk_and([left.clone(), right.clone()]), Concept::Bottom)],
    };
    let mut rewritten = !matches!(axiom, Axiom::SubClassOf(..)) || changed;
    let mut out = Vec::with_capacity(inclusions.len());
    for (sub, sup) in inclusions {
        if holds_at_blank(&sub)? {
            rewritten = true;
            out.push(Axiom::SubClassOf(guarded(&sub), sup));
        } else {
            out.push(Axiom::SubClassOf(sub, sup));
        }
    }
    rewritten.then_some(out)
}

/// Apply the guard to `ontology`. `data_roles` are the internal names of the
/// source data properties; `is_named_class` tells a source class name from a
/// datatype or internal name; `declared_classes` are the declared source
/// classes, which get `A ⊑ G` even when no axiom mentions them.
pub fn encode(
    ontology: &mut Ontology,
    data_roles: &BTreeSet<String>,
    declared_classes: &[String],
    is_named_class: impl Fn(&str) -> bool,
) -> Encoded {
    if !applies(ontology, data_roles) {
        return Encoded::default();
    }
    let Scan { names, roles, individuals } = scan(ontology);
    let guard = Concept::Name(GUARD.to_string());
    let mut replacements = Vec::new();
    let mut encoded = Encoded::default();
    for axiom in ontology.axioms_iter() {
        if let Some(rewritten) = rewrite(axiom, data_roles) {
            encoded.rewritten += 1;
            if matches!(axiom, Axiom::ConceptAssertion(..))
                && !matches!(rewritten.as_slice(), [Axiom::ConceptAssertion(..)])
            {
                encoded.moved_assertions += 1;
            }
            replacements.extend(rewritten);
        }
    }
    ontology.retain_axioms(|axiom| rewrite(axiom, data_roles).is_none());
    for axiom in replacements {
        ontology.add(axiom);
    }
    let declared = declared_classes.iter().filter(|name| !name.starts_with("__"));
    for name in names.iter().filter(|name| is_named_class(name)).chain(declared) {
        ontology.add(Axiom::SubClassOf(Concept::Name(name.clone()), guard.clone()));
    }
    for role in &roles {
        if data_roles.contains(role) {
            continue;
        }
        ontology.add(Axiom::SubClassOf(
            Concept::Exists(Role::Name(role.clone()), Box::new(Concept::Top)),
            guard.clone(),
        ));
        ontology.add(Axiom::SubClassOf(
            Concept::Top,
            Concept::Forall(Role::Name(role.clone()), Box::new(guard.clone())),
        ));
    }
    // `{a} ⊑ G` rather than the assertion `G(a)`: the native ABox coverage
    // check counts class assertions against the source.
    for individual in &individuals {
        ontology.add(Axiom::SubClassOf(Concept::Nominal(individual.clone()), guard.clone()));
    }
    encoded
}

/// What [`encode`] changed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Encoded {
    /// Source axioms replaced (0: the ontology is unchanged).
    pub rewritten: usize,
    /// Class assertions moved to nominal inclusions.
    pub moved_assertions: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(n: &str) -> Concept {
        Concept::Name(n.to_string())
    }

    #[test]
    fn blank_values_follow_the_empty_element() {
        let u = Role::Name("u".into());
        assert_eq!(holds_at_blank(&Concept::AtMost(1, u.clone(), Box::new(Concept::Top))), Some(true));
        assert_eq!(holds_at_blank(&Concept::AtLeast(1, u.clone(), Box::new(Concept::Top))), Some(false));
        assert_eq!(holds_at_blank(&Concept::Not(Box::new(name("A")))), Some(true));
        assert_eq!(holds_at_blank(&Concept::Nominal("a".into())), Some(false));
        assert_eq!(holds_at_blank(&Concept::Forall(u, Box::new(Concept::Bottom))), Some(true));
        assert_eq!(holds_at_blank(&Concept::HasSelf(Role::Name("r".into()))), None);
    }

    #[test]
    fn guards_only_axioms_that_fail_on_a_blank_element() {
        let mut ontology = Ontology::new();
        let u = Role::Name("u".into());
        let at_most = Concept::AtMost(1, u.clone(), Box::new(Concept::Top));
        ontology.add(Axiom::SubClassOf(at_most.clone(), Concept::Nominal("a".into())));
        ontology.add(Axiom::SubClassOf(name("A"), name("B")));
        ontology.add(Axiom::RoleAssertion("r".into(), "a".into(), "b".into()));
        let data: BTreeSet<String> = ["u".to_string()].into();
        let guarded_count = encode(&mut ontology, &data, &[], |n| !n.starts_with("__"));
        assert_eq!(guarded_count, Encoded { rewritten: 1, moved_assertions: 0 });
        let axioms: Vec<Axiom> = ontology.axioms_iter().cloned().collect();
        assert!(axioms.contains(&Axiom::SubClassOf(name("A"), name("B"))));
        assert!(axioms.contains(&Axiom::SubClassOf(
            mk_and([name(GUARD), at_most.clone()]), Concept::Nominal("a".into()))));
        assert!(!axioms.contains(&Axiom::SubClassOf(at_most, Concept::Nominal("a".into()))));
        assert!(axioms.contains(&Axiom::SubClassOf(name("A"), name(GUARD))));
        assert!(axioms.contains(&Axiom::SubClassOf(Concept::Nominal("b".into()), name(GUARD))));
        assert!(axioms.contains(&Axiom::SubClassOf(
            Concept::Top, Concept::Forall(Role::Name("r".into()), Box::new(name(GUARD))))));
        // A data role never gets the guard as its range.
        assert!(!axioms.contains(&Axiom::SubClassOf(
            Concept::Top, Concept::Forall(u.clone(), Box::new(name(GUARD))))));
        assert!(!axioms.iter().any(|axiom| matches!(axiom,
            Axiom::SubClassOf(Concept::Exists(role, _), _) if *role == u)));
        // Every class axiom now holds at a blank element.
        for axiom in &axioms {
            if let Axiom::SubClassOf(l, r) = axiom {
                assert!(!holds_at_blank(l).unwrap() || holds_at_blank(r).unwrap());
            }
        }
    }

    #[test]
    fn leaves_the_ontology_alone_without_individuals_or_failing_axioms() {
        let data: BTreeSet<String> = ["u".to_string()].into();
        let mut no_individual = Ontology::new();
        no_individual.add(Axiom::SubClassOf(Concept::Not(Box::new(name("A"))), name("B")));
        assert_eq!(encode(&mut no_individual, &data, &[], |_| true).rewritten, 0);
        assert_eq!(no_individual.axioms_iter().count(), 1);
        let mut nothing_fails = Ontology::new();
        nothing_fails.add(Axiom::SubClassOf(name("A"), Concept::Nominal("a".into())));
        assert_eq!(encode(&mut nothing_fails, &data, &[], |_| true).rewritten, 0);
        assert_eq!(nothing_fails.axioms_iter().count(), 1);
        let mut reflexive = Ontology::new();
        reflexive.add(Axiom::SubClassOf(Concept::Not(Box::new(name("A"))), Concept::Nominal("a".into())));
        reflexive.add(Axiom::ReflexiveRole("r".into()));
        assert_eq!(encode(&mut reflexive, &data, &[], |_| true).rewritten, 0);
    }

    #[test]
    fn datatype_assertion_moves_to_a_nominal_inclusion_and_data_exists_is_normalised() {
        let data: BTreeSet<String> = ["u".to_string()].into();
        let u = Role::Name("u".into());
        let value = Concept::Exists(u.clone(), Box::new(name("__dt__integer")));
        let assertion = Concept::Or([value.clone(), name("A")].into());
        let domain = Axiom::SubClassOf(Concept::Exists(u.clone(), Box::new(Concept::Top)), value.clone());
        let mut ontology = Ontology::new();
        ontology.add(Axiom::ConceptAssertion(assertion.clone(), "a".into()));
        ontology.add(domain.clone());
        assert!(applies(&ontology, &data));
        assert_eq!(encode(&mut ontology, &data, &[], |n| !n.starts_with("__")), Encoded { rewritten: 2, moved_assertions: 1 });
        let axioms: Vec<Axiom> = ontology.axioms_iter().cloned().collect();
        assert!(axioms.contains(&Axiom::SubClassOf(Concept::Nominal("a".into()), assertion.clone())));
        assert!(!axioms.contains(&Axiom::ConceptAssertion(assertion, "a".into())));
        assert!(!axioms.contains(&domain));
        assert!(axioms.contains(&Axiom::SubClassOf(
            Concept::AtLeast(1, u, Box::new(Concept::Top)), value)));
        assert!(axioms.contains(&Axiom::SubClassOf(Concept::Nominal("a".into()), name(GUARD))));
    }

    #[test]
    fn a_nested_self_restriction_or_universal_role_refuses() {
        let data: BTreeSet<String> = ["u".to_string()].into();
        let failing = Axiom::SubClassOf(Concept::Not(Box::new(name("A"))), Concept::Nominal("a".into()));
        for nested in [
            Concept::Exists(Role::Name("r".into()), Box::new(Concept::HasSelf(Role::Name("r".into())))),
            Concept::Exists(Role::Name("r".into()), Box::new(Concept::Forall(Role::Universal, Box::new(name("B"))))),
        ] {
            let mut ontology = Ontology::new();
            ontology.add(failing.clone());
            ontology.add(Axiom::SubClassOf(name("B"), nested));
            assert!(!applies(&ontology, &data));
            assert_eq!(encode(&mut ontology, &data, &[], |_| true).rewritten, 0);
        }
    }
}
