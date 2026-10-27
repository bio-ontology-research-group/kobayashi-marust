//! Object and data sorts for the nominal clause set.
//!
//! OWL 2 Direct Semantics interprets class expressions over the object domain
//! `Δ_I` and data ranges over the data domain `Δ_D`, with `Δ_I ∩ Δ_D = ∅`.
//! The clause set is one-sorted: a data value is an element of the same
//! domain as every object, carrying its `__dt__` concept. That is exact as
//! long as nothing forces a data value into object structure. Under nominal
//! clausification a data value becomes a ground individual (the data-value
//! singleton of `reasoner::Builder`), and every empty-body fact `⊤ ⊑ C`
//! (`owl:Thing ⊑ C`, which should range over `Δ_I` only) is instantiated at
//! it. With a universal-role hub or another `⊤ ⊑ ∃R.{o}` axiom that gives
//! the value object successors, merges it with named individuals through
//! `⊤ ⊑ ¬{v} ⊔ {v}`, and lets the ground context explode.
//!
//! This pass makes the two sorts explicit with one fresh marker concept
//! [`DATA_SORT`] (`D`, interpreted as `Δ_D`), linearly in the signature:
//!
//! * every data range `⊑ D`; every object-sorted concept `⊑ ¬D`;
//! * every role: domain `⊑ ¬D`; range `⊑ ¬D` for object roles and `⊑ D`
//!   for data roles;
//! * every class-level fact `⊤ ⊑ C` becomes `¬D ⊑ C`, i.e. `→ C(x) ∨ D(x)`:
//!   `owl:Thing` is `¬D`.
//!
//! Data-range-level facts (the excluded middle `→ Q(x) ∨ R(x)` of a
//! `DataComplementOf` definer `Q`) stay unrelativized: they must keep
//! applying to data nodes, and on object nodes they only place the node on
//! the complement side of the range, which every two-sorted model agrees
//! with. The sort of every concept and role position is inferred from the
//! clause set itself (data ranges and data properties are data, source
//! classes and named individuals are objects, and atoms on one term share a
//! sort; a Skolem term `f(x)` and an individual denote the same element in
//! every clause), so the pass needs no provenance from the clausifier. A
//! concept used in both sorts (the `⊤` definer of an unqualified
//! cardinality) gets no sort clause and keeps its facts as they are.
//!
//! The exactness argument is in docs/NOMINALS-CB.md, "Object and data sorts".

use std::collections::{BTreeMap, BTreeSet};

use super::clauses::{clause, Atom, DLClause, Term};

/// Marker concept interpreted as the data domain `Δ_D`.
pub const DATA_SORT: &str = "__data__";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sort {
    Unknown,
    Object,
    Data,
    /// Evidence for both sorts: a sort-polymorphic internal concept.
    Both,
}

impl Sort {
    fn join(self, other: Sort) -> Sort {
        match (self, other) {
            (Sort::Unknown, s) | (s, Sort::Unknown) => s,
            (a, b) if a == b => a,
            _ => Sort::Both,
        }
    }

    fn definite(self) -> bool {
        matches!(self, Sort::Object | Sort::Data)
    }
}

fn is_data_range(name: &str) -> bool {
    name.starts_with("__dt__")
}

/// A role named by the source: not an inverse bridge, chain, or
/// cardinality-colour role.
fn is_source_role(name: &str) -> bool {
    !name.starts_with("__")
}

/// A concept named by the source: neither a definer nor an internal name.
fn is_source_concept(name: &str) -> bool {
    !(name.starts_with("Q_")
        || name.starts_with("__")
        || matches!(name, "Thing" | "Nothing" | "owl:Thing" | "owl:Nothing"))
}

/// The variable a term is built on, if any.
fn term_var(term: &Term) -> Option<&Term> {
    match term {
        Term::Var(_) => Some(term),
        Term::Fun(_, inner) => term_var(inner),
        Term::Ind(_) | Term::Aux(..) => None,
    }
}

/// Whether the encoding applies to this clause set: it carries a data value
/// (every `__dt__val__` concept also yields a data-value singleton in nominal
/// mode) and the caller has established that the source has nominals or
/// individuals.
pub fn has_data_values(tbox: &[DLClause]) -> bool {
    tbox.iter().any(|c| {
        c.body.iter().chain(c.head.iter()).any(|atom| {
            matches!(atom, Atom::Concept(name, _) if name.starts_with("__dt__val__"))
        })
    })
}

struct Sorts {
    /// Concept sort and whether it is a fixed seed.
    concepts: BTreeMap<String, (Sort, bool)>,
    /// Role (domain, range) sorts.
    roles: BTreeMap<String, (Sort, Sort)>,
}

impl Sorts {
    fn infer(tbox: &[DLClause], data_roles: &BTreeSet<String>) -> Sorts {
        let mut concepts: BTreeMap<String, (Sort, bool)> = BTreeMap::new();
        let mut roles: BTreeMap<String, (Sort, Sort)> = BTreeMap::new();
        for c in tbox {
            for atom in c.body.iter().chain(c.head.iter()) {
                match atom {
                    Atom::Concept(name, _) => {
                        concepts.entry(name.clone()).or_insert_with(|| {
                            if is_data_range(name) {
                                (Sort::Data, true)
                            } else if is_source_concept(name) || name.starts_with("__nom__") {
                                (Sort::Object, true)
                            } else {
                                (Sort::Unknown, false)
                            }
                        });
                    }
                    Atom::Role(name, _, _) => {
                        roles.entry(name.clone()).or_insert_with(|| {
                            // Every property has an object domain; a data
                            // property has a data range and every other
                            // source property an object range. Internal
                            // roles learn their range from their fillers.
                            let range = if data_roles.contains(name) {
                                Sort::Data
                            } else if is_source_role(name) {
                                Sort::Object
                            } else {
                                Sort::Unknown
                            };
                            (Sort::Object, range)
                        });
                    }
                    Atom::Eq(..) => {}
                }
            }
        }
        let mut sorts = Sorts { concepts, roles };
        // Phase 1, structural evidence: a term's sort comes from the seeded
        // concepts on it and from the role positions it fills. A variable is
        // local to its clause; a Skolem term `f(x)` (one function per
        // definer) and an individual denote one element across the whole
        // clause set, so their evidence is kept globally. Definers and role
        // positions learn from that evidence; a definer that meets both sorts
        // is polymorphic (`Both`), and only definite sorts ever propagate.
        let mut global: BTreeMap<&Term, Sort> = BTreeMap::new();
        loop {
            let mut changed = false;
            let mut local: BTreeMap<&Term, Sort> = BTreeMap::new();
            for c in tbox {
                local.clear();
                let mut terms = TermSorts { local: &mut local, global: &mut global };
                for atom in c.body.iter().chain(c.head.iter()) {
                    match atom {
                        Atom::Concept(name, t) => {
                            let (sort, fixed) = sorts.concepts[name];
                            if fixed {
                                terms.join(t, sort);
                            }
                        }
                        Atom::Role(name, s, t) => {
                            let (domain, range) = sorts.roles[name];
                            terms.join(s, domain);
                            terms.join(t, range);
                        }
                        Atom::Eq(..) => {}
                    }
                }
                for atom in c.body.iter().chain(c.head.iter()) {
                    if let Atom::Eq(s, t) = atom {
                        let joined = terms.get(s).join(terms.get(t));
                        terms.join(s, joined);
                        terms.join(t, joined);
                    }
                }
                for atom in c.body.iter().chain(c.head.iter()) {
                    match atom {
                        Atom::Concept(name, t) => {
                            let term_sort = terms.get(t);
                            if !term_sort.definite() {
                                continue;
                            }
                            let entry = sorts.concepts.get_mut(name).expect("registered concept");
                            if entry.1 {
                                continue;
                            }
                            let joined = entry.0.join(term_sort);
                            if joined != entry.0 {
                                entry.0 = joined;
                                changed = true;
                            }
                        }
                        Atom::Role(name, s, t) => {
                            let (domain_sort, range_sort) = (terms.get(s), terms.get(t));
                            let entry = sorts.roles.get_mut(name).expect("registered role");
                            if domain_sort.definite() {
                                let joined = entry.0.join(domain_sort);
                                if joined != entry.0 {
                                    entry.0 = joined;
                                    changed = true;
                                }
                            }
                            if range_sort.definite() {
                                let joined = entry.1.join(range_sort);
                                if joined != entry.1 {
                                    entry.1 = joined;
                                    changed = true;
                                }
                            }
                        }
                        Atom::Eq(..) => {}
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // Phase 2: a definer without structural evidence (`⊤ ⊑ Q`, `Q ⊑ Q'`)
        // takes the sort of the definite concepts it shares a term with.
        // Already-definite concepts and roles do not change here, so a
        // polymorphic concept cannot spread a spurious sort.
        loop {
            let mut changed = false;
            let mut local: BTreeMap<&Term, Sort> = BTreeMap::new();
            for c in tbox {
                local.clear();
                let mut terms = TermSorts { local: &mut local, global: &mut global };
                for atom in c.body.iter().chain(c.head.iter()) {
                    if let Atom::Concept(name, t) = atom {
                        let structural = if matches!(t, Term::Var(_)) {
                            Sort::Unknown
                        } else {
                            terms.get(t)
                        };
                        let mut sort = structural;
                        for other in c.body.iter().chain(c.head.iter()) {
                            if let Atom::Concept(other_name, other_t) = other {
                                if other_t == t {
                                    sort = sort.join(sorts.concepts[other_name].0);
                                }
                            }
                        }
                        if !sort.definite() {
                            continue;
                        }
                        let entry = sorts.concepts.get_mut(name).expect("registered concept");
                        if entry.0 == Sort::Unknown {
                            entry.0 = sort;
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        sorts
    }

    fn concept(&self, name: &str) -> Sort {
        self.concepts.get(name).map_or(Sort::Unknown, |entry| entry.0)
    }
}

/// Term sorts of the clause being scanned: variables per clause, Skolem
/// terms and individuals across the clause set.
struct TermSorts<'a, 'b> {
    local: &'a mut BTreeMap<&'b Term, Sort>,
    global: &'a mut BTreeMap<&'b Term, Sort>,
}

impl<'a, 'b> TermSorts<'a, 'b> {
    fn map(&mut self, term: &Term) -> &mut BTreeMap<&'b Term, Sort> {
        if matches!(term, Term::Var(_)) { self.local } else { self.global }
    }

    fn get(&mut self, term: &'b Term) -> Sort {
        self.map(term).get(term).copied().unwrap_or(Sort::Unknown)
    }

    /// Record definite evidence for `term`; indefinite evidence is ignored.
    fn join(&mut self, term: &'b Term, sort: Sort) {
        if sort.definite() {
            let entry = self.map(term).entry(term).or_insert(Sort::Unknown);
            *entry = entry.join(sort);
        }
    }
}

/// Apply the encoding in place. Returns the number of clauses added plus
/// the number of facts relativized. `data_roles` holds the clause-set names
/// of the source's data properties.
pub fn encode(tbox: &mut Vec<DLClause>, data_roles: &BTreeSet<String>) -> usize {
    let sorts = Sorts::infer(tbox, data_roles);
    let x = Term::Var("x".to_string());
    let y = Term::Var("y".to_string());
    let d = |t: &Term| Atom::Concept(DATA_SORT.to_string(), t.clone());
    let mut count = 0usize;
    // Class-level facts: `⊤ ⊑ C` becomes `¬D ⊑ C`. A fact is class-level
    // when it mentions exactly one variable and every concept in its head is
    // object-sorted; data-range-level, polymorphic and unresolved facts are
    // left as they are (see the module documentation), and so are ground
    // facts, whose individuals carry their own sort.
    for c in tbox.iter_mut() {
        if !c.body.is_empty() {
            continue;
        }
        let mut vars: BTreeSet<&Term> = BTreeSet::new();
        let mut object_level = true;
        for atom in &c.head {
            match atom {
                Atom::Concept(name, t) => {
                    vars.extend(term_var(t));
                    object_level &= sorts.concept(name) == Sort::Object;
                }
                Atom::Role(_, s, t) => {
                    vars.extend(term_var(s));
                    vars.extend(term_var(t));
                }
                Atom::Eq(s, t) => {
                    vars.extend(term_var(s));
                    vars.extend(term_var(t));
                }
            }
        }
        if !object_level || vars.len() != 1 {
            continue;
        }
        let v = (*vars.iter().next().expect("one variable")).clone();
        let mut head = std::mem::take(&mut c.head);
        head.push(d(&v));
        *c = clause(Vec::new(), head);
        count += 1;
    }
    let mut added: Vec<DLClause> = Vec::new();
    for (name, (sort, _)) in &sorts.concepts {
        let atom = Atom::Concept(name.clone(), x.clone());
        match sort {
            // Every data range lies in Δ_D. A data-sorted definer gets no
            // clause: its unrelativized excluded middle also holds on
            // object nodes.
            Sort::Data if is_data_range(name) => added.push(clause([atom], [d(&x)])),
            Sort::Object => added.push(clause([atom, d(&x)], [])),
            _ => {}
        }
    }
    for (name, (domain, range)) in &sorts.roles {
        let atom = Atom::Role(name.clone(), x.clone(), y.clone());
        match domain {
            Sort::Object => added.push(clause([atom.clone(), d(&x)], [])),
            Sort::Data => added.push(clause([atom.clone()], [d(&x)])),
            _ => {}
        }
        match range {
            Sort::Object => added.push(clause([atom.clone(), d(&y)], [])),
            Sort::Data => added.push(clause([atom.clone()], [d(&y)])),
            _ => {}
        }
    }
    count += added.len();
    tbox.extend(added);
    count
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::clauses::fact;

    fn x() -> Term {
        Term::Var("x".into())
    }
    fn y() -> Term {
        Term::Var("y".into())
    }
    fn fx(f: &str) -> Term {
        Term::Fun(f.into(), Box::new(x()))
    }
    fn c(name: &str, t: Term) -> Atom {
        Atom::Concept(name.into(), t)
    }
    fn r(name: &str, s: Term, t: Term) -> Atom {
        Atom::Role(name.into(), s, t)
    }

    const VAL: &str = "__dt__val__\"1\"^^xsd:integer";

    /// `¬(u value 1) ⊑ B` next to a nominal: the fixture's shape.
    fn fixture() -> Vec<DLClause> {
        vec![
            // Q_0 = ∀u.Q_1, Q_1 = ¬{1}, Q_2 = ∃u.{1}, B ⊒ Q_0
            clause([c("Q_0", x()), r("u", x(), y())], [c("Q_1", y())]),
            fact([c("Q_1", x()), c(VAL, x())]),
            clause([c("Q_1", x()), c(VAL, x())], []),
            fact([c("Q_0", x()), c("Q_2", x())]),
            clause([c("Q_2", x())], [r("u", x(), fx("f"))]),
            clause([c("Q_2", x())], [c(VAL, fx("f"))]),
            clause([c("Q_0", x())], [c("B", x())]),
            // ⊤ ⊑ ∃r.{o}
            fact([c("Q_3", x())]),
            clause([c("Q_3", x())], [r("r", x(), fx("g"))]),
            clause([c("Q_3", x())], [c("__nom__o", fx("g"))]),
            fact([c("__nom__o", Term::Ind("o".into()))]),
            clause([c("__nom__o", x())], [Atom::Eq(x(), Term::Ind("o".into()))]),
        ]
    }

    #[test]
    fn infers_sorts_from_the_clause_set() {
        let tbox = fixture();
        let sorts = Sorts::infer(&tbox, &BTreeSet::from(["u".to_string()]));
        assert_eq!(sorts.concept("B"), Sort::Object);
        assert_eq!(sorts.concept("__nom__o"), Sort::Object);
        assert_eq!(sorts.concept(VAL), Sort::Data);
        assert_eq!(sorts.concept("Q_1"), Sort::Data, "¬{{1}} is a data-range definer");
        assert_eq!(sorts.concept("Q_0"), Sort::Object);
        assert_eq!(sorts.concept("Q_2"), Sort::Object);
        assert_eq!(sorts.concept("Q_3"), Sort::Object);
        assert_eq!(sorts.roles["u"], (Sort::Object, Sort::Data));
        assert_eq!(sorts.roles["r"], (Sort::Object, Sort::Object));
    }

    #[test]
    fn relativizes_class_level_facts_only_and_adds_sort_clauses() {
        let mut tbox = fixture();
        let before = tbox.len();
        let count = encode(&mut tbox, &BTreeSet::from(["u".to_string()]));
        let dx = c(DATA_SORT, x());
        // Class-level facts gained the D disjunct ...
        assert!(tbox.contains(&fact([c("Q_0", x()), c("Q_2", x()), dx.clone()])));
        assert!(tbox.contains(&fact([c("Q_3", x()), dx.clone()])));
        // ... the data-range excluded middle and the ground fact did not.
        assert!(tbox.contains(&fact([c("Q_1", x()), c(VAL, x())])));
        assert!(tbox.contains(&fact([c("__nom__o", Term::Ind("o".into()))])));
        // Sort clauses: data range ⊑ D, object concepts ⊑ ¬D, no clause for
        // the data-sorted definer, role domain/range sorts.
        assert!(tbox.contains(&clause([c(VAL, x())], [dx.clone()])));
        assert!(tbox.contains(&clause([c("B", x()), dx.clone()], [])));
        assert!(tbox.contains(&clause([c("__nom__o", x()), dx.clone()], [])));
        assert!(tbox.contains(&clause([c("Q_0", x()), dx.clone()], [])));
        assert!(!tbox.iter().any(|cl| cl.body.contains(&c("Q_1", x())) && cl.body.contains(&dx)));
        assert!(!tbox.contains(&clause([c("Q_1", x())], [dx.clone()])));
        assert!(tbox.contains(&clause([r("u", x(), y()), dx.clone()], [])));
        assert!(tbox.contains(&clause([r("u", x(), y())], [c(DATA_SORT, y())])));
        assert!(tbox.contains(&clause([r("r", x(), y()), dx.clone()], [])));
        assert!(tbox.contains(&clause([r("r", x(), y()), c(DATA_SORT, y())], [])));
        assert_eq!(tbox.len() - before, count - 2);
    }

    #[test]
    fn a_concept_used_in_both_sorts_keeps_its_fact_and_gets_no_sort_clause() {
        // Q_t is the ⊤ definer, the filler of both `≥1 u` and `≥1 r`.
        let mut tbox = vec![
            fact([c("Q_t", x())]),
            clause([c("A", x())], [r("u", x(), fx("f"))]),
            clause([c("A", x())], [c("Q_t", fx("f"))]),
            clause([c("A", x())], [r("r", x(), fx("g"))]),
            clause([c("A", x())], [c("Q_t", fx("g"))]),
            clause([c("A", x())], [c(VAL, fx("f"))]),
        ];
        let sorts = Sorts::infer(&tbox, &BTreeSet::from(["u".to_string()]));
        assert_eq!(sorts.concept("Q_t"), Sort::Both);
        encode(&mut tbox, &BTreeSet::from(["u".to_string()]));
        assert!(tbox.contains(&fact([c("Q_t", x())])));
        assert!(!tbox.iter().any(|cl| cl.body.contains(&c("Q_t", x()))));
    }

    #[test]
    fn gate_needs_a_data_value() {
        assert!(has_data_values(&fixture()));
        assert!(!has_data_values(&[clause([c("A", x())], [c("__dt__integer", fx("f"))])]));
    }
}
