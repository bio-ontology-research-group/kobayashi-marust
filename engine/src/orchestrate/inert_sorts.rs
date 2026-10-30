//! Inert object sorts in the rule-consistency worker input.
//!
//! The two-sorted encoding of the nominal clause set (`frontend/sorts.rs`,
//! docs/NOMINALS-CB.md section 6) relativizes every class-level fact
//! `Q_⊤(x) → Q(x)` to `Q_⊤(x) → Q(x) ∨ D(x)` and adds the sort clause
//! `Q(x) ∧ D(x) → ⊥` for an object-sorted definer `Q`. The clausal
//! `Tableau` of the rule-consistency worker branches on that disjunction at
//! every node, and every branch restarts its Horn saturation over the whole
//! graph: on ore_ont_7278 the 11 range definers of `DataPropertyRange`
//! axioms give 11 × 221 = 2,431 branch points, each followed by a full
//! saturation, and the worker takes 25 s instead of 4 s.
//!
//! For a definer whose object sort no clause can observe, both clauses are
//! unnecessary: the definer may hold on data elements too. This pass finds
//! the set `P` of such definers and, for `Q ∈ P`, drops the `D` disjunct of
//! the facts that carry `Q` and the sort clause `Q ∧ D → ⊥`.
//!
//! A *guard* of a term `t` in a clause body is an atom that is false at every
//! data element in every model of the clause set: a concept `G(t)` with a
//! sort clause `G ∧ D → ⊥` and `G ∉ P`, a role atom `p(t, u)` with a domain
//! sort clause `p(x, y) ∧ D(x) → ⊥`, or `p(u, t)` with a range sort clause
//! `p(x, y) ∧ D(y) → ⊥`. Those sort clauses stay in the clause set. An
//! individual `a` is *pinned* when a unit fact `→ G(a)` with such a `G`, or
//! `→ p(a, b)` (`→ p(b, a)`) with a domain (range) sort clause of `p`, puts it
//! outside `D` in every model; a pinned individual needs no guard. A
//! concept `Q` is in `P` when it is an internal definer (not a source name,
//! not a `__` marker, not used by a rule, a cardinality or a definer
//! record), it has a sort clause, and
//!
//! * (B) every clause with `Q(t)` in its body has a guard of `t` or a pinned
//!   `t`, and
//! * (H) every clause with `Q(t)` in its head either has `D(t)` in its head
//!   too (a relativized fact) or has a guard of `t` in its body or a pinned
//!   `t`.
//!
//! The pass starts from every candidate and removes the failing ones until
//! none fails; the resulting `P` has both properties. Let `S` be the input
//! and `S'` the result.
//!
//! * A model `M` of `S` yields a model `M'` of `S'`: add `Q` to every element
//!   of `D` for each `Q ∈ P`. A clause with `Q(t)` in its body is false at a
//!   data `t` by (B) (a pinned `t` is never data), so it holds as before. A
//!   clause with `Q(t)` in its head only gains. A fact whose `D(t)` was
//!   dropped holds at a data `t` through `Q(t)` and at an object `t` as in
//!   `M`, where `D(t)` was false. No other clause mentions `Q`.
//! * A model `M'` of `S'` yields a model `M` of `S`: remove `Q` from every
//!   element of `D`. `Q ∧ D → ⊥` then holds. A clause with `Q(t)` in its
//!   body only loses premises. A clause with `Q(t)` in its head and no `D(t)`
//!   has a guard or a pinned `t` by (H), so its body is false at a data
//!   `t`; one whose `D(t)` was dropped holds at a data `t` through the
//!   restored `D(t)`. No other clause mentions `Q`.
//!
//! The two clause sets therefore have the same models up to the
//! interpretation of internal definers on data elements, and in particular
//! the same consistency verdict, which is all the worker reports. Every name
//! the worker reads with a meaning of its own (source names, queries,
//! `__nom__` proxies, `__dt__` ranges, rule atoms, cardinality and definer
//! records) is outside `P`, and the guard sort clauses are kept.

use std::collections::{BTreeSet, HashSet};

use crate::frontend::sorts::DATA_SORT;
use crate::json_io::{CardMeta, DefinerMeta, JAtom, JClause, JInput, JRule, JRuleAtom, JTerm};

/// What [`release_inert_object_sorts`] removed.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Released {
    /// The definers whose object sort was released (`P`), sorted.
    pub concepts: Vec<String>,
    /// Facts whose `D(t)` disjunct was dropped.
    pub facts: usize,
    /// Sort clauses `Q ∧ D → ⊥` removed.
    pub sort_clauses: usize,
}

fn is_data(atom: &JAtom, term: &JTerm) -> bool {
    matches!(atom, JAtom::Concept { concept, term: t } if concept == DATA_SORT && t == term)
}

/// `G` of a concept sort clause `G(x) ∧ D(x) → ⊥`.
fn concept_sort_clause(clause: &JClause) -> Option<&str> {
    if !clause.head.is_empty() || clause.body.len() != 2 {
        return None;
    }
    match (&clause.body[0], &clause.body[1]) {
        (JAtom::Concept { concept: a, term: ta }, JAtom::Concept { concept: b, term: tb })
            if ta == tb && matches!(ta, JTerm::Var { .. }) =>
        {
            match (a == DATA_SORT, b == DATA_SORT) {
                (true, false) => Some(b),
                (false, true) => Some(a),
                _ => None,
            }
        }
        _ => None,
    }
}

/// `(p, domain)` of a role sort clause `p(x, y) ∧ D(x) → ⊥` (domain) or
/// `p(x, y) ∧ D(y) → ⊥` (range).
fn role_sort_clause(clause: &JClause) -> Option<(&str, bool)> {
    if !clause.head.is_empty() || clause.body.len() != 2 {
        return None;
    }
    let (role, concept) = match (&clause.body[0], &clause.body[1]) {
        (r @ JAtom::Role { .. }, c @ JAtom::Concept { .. }) | (c @ JAtom::Concept { .. }, r @ JAtom::Role { .. }) => (r, c),
        _ => return None,
    };
    let (JAtom::Role { role, source, target }, JAtom::Concept { concept, term }) = (role, concept) else {
        return None;
    };
    if concept != DATA_SORT
        || source == target
        || !matches!(source, JTerm::Var { .. })
        || !matches!(target, JTerm::Var { .. })
    {
        return None;
    }
    if term == source {
        Some((role, true))
    } else if term == target {
        Some((role, false))
    } else {
        None
    }
}

struct Guards<'a> {
    object_concepts: HashSet<&'a str>,
    object_domain: HashSet<&'a str>,
    object_range: HashSet<&'a str>,
    /// Unit facts `→ G(a)` and `→ p(a, b)` on individuals.
    ground_concepts: Vec<(&'a str, &'a JTerm)>,
    ground_roles: Vec<(&'a str, &'a JTerm, &'a JTerm)>,
}

impl<'a> Guards<'a> {
    /// Individuals that a unit fact puts outside `D` in every model: `→ G(a)`
    /// with a guard concept `G`, or `→ p(a, b)` with an object domain (`a`)
    /// or an object range (`b`) of `p`.
    fn pinned(&self, released: &BTreeSet<&str>) -> HashSet<&'a JTerm> {
        let mut pinned: HashSet<&JTerm> = HashSet::new();
        for &(concept, term) in &self.ground_concepts {
            if self.object_concepts.contains(concept) && !released.contains(concept) {
                pinned.insert(term);
            }
        }
        for &(role, source, target) in &self.ground_roles {
            if self.object_domain.contains(role) {
                pinned.insert(source);
            }
            if self.object_range.contains(role) {
                pinned.insert(target);
            }
        }
        pinned
    }

    /// Whether `term` is outside `D` at every instance of `clause`: it is a
    /// pinned individual, or the body holds a guard of it outside `released`.
    fn guarded(&self, clause: &JClause, term: &JTerm, released: &BTreeSet<&str>, pinned: &HashSet<&JTerm>) -> bool {
        pinned.contains(term) || clause.body.iter().any(|atom| match atom {
            JAtom::Concept { concept, term: t } => {
                t == term
                    && self.object_concepts.contains(concept.as_str())
                    && !released.contains(concept.as_str())
            }
            JAtom::Role { role, source, target } => {
                (source == term && self.object_domain.contains(role.as_str()))
                    || (target == term && self.object_range.contains(role.as_str()))
            }
            JAtom::Eq { .. } => false,
        })
    }
}

/// Release the object sort of every inert definer of `input.clauses` (module
/// documentation). `is_source` names the concepts with a source reading
/// (IRI-mapped names and query targets); they are never released.
pub fn release_inert_object_sorts(input: &mut JInput, is_source: impl Fn(&str) -> bool) -> Released {
    release_inert_object_sorts_in(
        &mut input.clauses,
        &input.cardinalities,
        &input.definers,
        &input.rules,
        is_source,
    )
}

/// [`release_inert_object_sorts`] over the parts of a frontend result that
/// the pass reads, for callers that hold a `FrontendResult` instead of the
/// clause file (`incremental_rules`). The clause set changes in place; the
/// records only decide which names are reserved.
pub(crate) fn release_inert_object_sorts_in(
    clause_set: &mut Vec<JClause>,
    cardinalities: &[CardMeta],
    definers: &[DefinerMeta],
    rules: &[JRule],
    is_source: impl Fn(&str) -> bool,
) -> Released {
    let clauses: &Vec<JClause> = clause_set;
    if !clauses
        .iter()
        .any(|c| c.head.iter().any(|a| matches!(a, JAtom::Concept { concept, .. } if concept == DATA_SORT)))
    {
        return Released::default();
    }
    let mut guards = Guards {
        object_concepts: HashSet::new(),
        object_domain: HashSet::new(),
        object_range: HashSet::new(),
        ground_concepts: Vec::new(),
        ground_roles: Vec::new(),
    };
    for clause in clauses {
        if clause.body.is_empty() && clause.head.len() == 1 {
            match &clause.head[0] {
                JAtom::Concept { concept, term: term @ JTerm::Ind { .. } } => {
                    guards.ground_concepts.push((concept, term));
                }
                JAtom::Role { role, source: source @ JTerm::Ind { .. }, target: target @ JTerm::Ind { .. } } => {
                    guards.ground_roles.push((role, source, target));
                }
                _ => {}
            }
        }
        if let Some(concept) = concept_sort_clause(clause) {
            guards.object_concepts.insert(concept);
        } else if let Some((role, domain)) = role_sort_clause(clause) {
            if domain {
                guards.object_domain.insert(role);
            } else {
                guards.object_range.insert(role);
            }
        }
    }
    // Names with a meaning outside the clauses.
    let mut reserved: HashSet<&str> = HashSet::new();
    for card in cardinalities {
        reserved.insert(&card.marker);
        reserved.insert(&card.filler);
    }
    for definer in definers {
        reserved.insert(&definer.marker);
        reserved.extend(definer.operands.iter().map(String::as_str));
    }
    for rule in rules {
        for atom in rule.body.iter().chain(&rule.head) {
            if let JRuleAtom::Class { concept, .. } = atom {
                reserved.insert(concept);
            }
        }
    }
    // Candidates: object-sorted internal definers carried by a relativized fact.
    let mut released: BTreeSet<&str> = BTreeSet::new();
    for clause in clauses {
        for atom in &clause.head {
            let JAtom::Concept { concept, term } = atom else { continue };
            if concept != DATA_SORT
                && guards.object_concepts.contains(concept.as_str())
                && clause.head.iter().any(|other| is_data(other, term))
                && super::cb_to_ht::is_internal(concept)
                && !concept.starts_with("__")
                && !reserved.contains(concept.as_str())
                && !is_source(concept)
            {
                released.insert(concept);
            }
        }
    }
    // Remove candidates that violate (B) or (H) until none does.
    loop {
        let mut failed: BTreeSet<&str> = BTreeSet::new();
        let pinned = guards.pinned(&released);
        for clause in clauses {
            if concept_sort_clause(clause).is_some() {
                continue;
            }
            for atom in &clause.body {
                if let JAtom::Concept { concept, term } = atom {
                    if released.contains(concept.as_str()) && !guards.guarded(clause, term, &released, &pinned) {
                        failed.insert(concept);
                    }
                }
            }
            for atom in &clause.head {
                if let JAtom::Concept { concept, term } = atom {
                    if released.contains(concept.as_str())
                        && !clause.head.iter().any(|other| is_data(other, term))
                        && !guards.guarded(clause, term, &released, &pinned)
                    {
                        failed.insert(concept);
                    }
                }
            }
        }
        if failed.is_empty() {
            break;
        }
        released.retain(|concept| !failed.contains(concept));
    }
    if released.is_empty() {
        return Released::default();
    }
    let released: BTreeSet<String> = released.into_iter().map(str::to_string).collect();
    let mut report = Released { concepts: released.iter().cloned().collect(), ..Released::default() };
    clause_set.retain(|clause| {
        let drop = concept_sort_clause(clause).is_some_and(|concept| released.contains(concept));
        report.sort_clauses += usize::from(drop);
        !drop
    });
    for clause in clause_set.iter_mut() {
        let released_terms: Vec<JTerm> = clause
            .head
            .iter()
            .filter_map(|atom| match atom {
                JAtom::Concept { concept, term } if released.contains(concept) => Some(term.clone()),
                _ => None,
            })
            .collect();
        if released_terms.is_empty() {
            continue;
        }
        let before = clause.head.len();
        clause.head.retain(|atom| !released_terms.iter().any(|term| is_data(atom, term)));
        report.facts += usize::from(clause.head.len() != before);
    }
    report
}

/// Concept names that something other than the clauses reads with a meaning
/// of its own: cardinality and definer records, rule atoms, source axioms,
/// and every name that is not a clausifier definer (`Q_`, `aux_`, `def_`),
/// which covers source names, query targets, built-in vocabulary, nominal
/// proxies, datatype ranges and the data sort itself. The Lean checker of the
/// release certificate rejects a release that touches one of them.
pub fn reserved_concepts(input: &JInput, is_source: impl Fn(&str) -> bool) -> BTreeSet<String> {
    fn concept_names(concept: &crate::frontend::syntax::Concept, out: &mut BTreeSet<String>) {
        use crate::frontend::syntax::Concept;
        match concept {
            Concept::Name(name) => {
                out.insert(name.clone());
            }
            Concept::Not(inner)
            | Concept::Exists(_, inner)
            | Concept::Forall(_, inner)
            | Concept::AtLeast(_, _, inner)
            | Concept::AtMost(_, _, inner) => concept_names(inner, out),
            Concept::And(set) | Concept::Or(set) => set.iter().for_each(|c| concept_names(c, out)),
            Concept::Top | Concept::Bottom | Concept::Nominal(_) | Concept::HasSelf(_) => {}
        }
    }
    let mut reserved = BTreeSet::new();
    for card in &input.cardinalities {
        reserved.insert(card.marker.clone());
        reserved.insert(card.filler.clone());
    }
    for definer in &input.definers {
        reserved.insert(definer.marker.clone());
        reserved.extend(definer.operands.iter().cloned());
    }
    for rule in &input.rules {
        for atom in rule.body.iter().chain(&rule.head) {
            if let JRuleAtom::Class { concept, .. } = atom {
                reserved.insert(concept.clone());
            }
        }
    }
    for axiom in &input.source_axioms {
        concept_names(&axiom.left, &mut reserved);
        concept_names(&axiom.right, &mut reserved);
    }
    for clause in &input.clauses {
        for atom in clause.body.iter().chain(&clause.head) {
            if let JAtom::Concept { concept, .. } = atom {
                let definer = ["Q_", "aux_", "def_"].iter().any(|prefix| concept.starts_with(prefix));
                if !definer || is_source(concept) {
                    reserved.insert(concept.clone());
                }
            }
        }
    }
    reserved
}

/// Numbering of the names of a release certificate.
#[derive(Default)]
struct CertIds {
    concepts: Vec<String>,
    concept_id: std::collections::HashMap<String, usize>,
    roles: Vec<String>,
    role_id: std::collections::HashMap<String, usize>,
    vars: std::collections::HashMap<String, usize>,
    inds: std::collections::HashMap<String, usize>,
    functions: std::collections::HashMap<String, usize>,
}

impl CertIds {
    fn concept(&mut self, name: &str) -> usize {
        if let Some(&id) = self.concept_id.get(name) {
            return id;
        }
        let id = self.concepts.len();
        self.concepts.push(name.to_string());
        self.concept_id.insert(name.to_string(), id);
        id
    }
    fn role(&mut self, name: &str) -> usize {
        if let Some(&id) = self.role_id.get(name) {
            return id;
        }
        let id = self.roles.len();
        self.roles.push(name.to_string());
        self.role_id.insert(name.to_string(), id);
        id
    }
    fn term(&mut self, term: &JTerm) -> serde_json::Value {
        fn next(map: &mut std::collections::HashMap<String, usize>, key: String) -> usize {
            let n = map.len();
            *map.entry(key).or_insert(n)
        }
        match term {
            JTerm::Var { name } => serde_json::json!({ "var": { "index": next(&mut self.vars, name.clone()) } }),
            JTerm::Ind { name } => {
                serde_json::json!({ "ind": { "index": next(&mut self.inds, format!("ind:{name}")) } })
            }
            JTerm::Aux { root, label } => serde_json::json!({
                "ind": { "index": next(&mut self.inds, format!("aux:{root}:{label:?}")) }
            }),
            JTerm::Fun { function, arg } => {
                let function = next(&mut self.functions, function.clone());
                let arg = self.term(arg);
                serde_json::json!({ "app": { "function": function, "arg": arg } })
            }
        }
    }
    fn atom(&mut self, atom: &JAtom) -> serde_json::Value {
        match atom {
            JAtom::Concept { concept, term } => {
                let concept = self.concept(concept);
                serde_json::json!({ "concept": { "concept": concept, "term": self.term(term) } })
            }
            JAtom::Role { role, source, target } => {
                let role = self.role(role);
                let source = self.term(source);
                let target = self.term(target);
                serde_json::json!({ "role": { "role": role, "source": source, "target": target } })
            }
            JAtom::Eq { left, right } => {
                let left = self.term(left);
                let right = self.term(right);
                serde_json::json!({ "eq": { "left": left, "right": right } })
            }
        }
    }
    fn clauses(&mut self, clauses: &[JClause]) -> Vec<serde_json::Value> {
        clauses
            .iter()
            .map(|clause| {
                let body: Vec<_> = clause.body.iter().map(|atom| self.atom(atom)).collect();
                let head: Vec<_> = clause.head.iter().map(|atom| self.atom(atom)).collect();
                serde_json::json!({ "body": body, "head": head })
            })
            .collect()
    }
}

/// The release certificate checked by `lean/RulesInertSortReleaseCheck.lean`
/// (`WireInertSortRelease`): the sorted clause set before the pass, the
/// released definers, the reserved concepts and the clause set the worker
/// reads. Lean recomputes the guard tables and the released clause set from
/// `original` and `released`, so nothing else in the document is trusted.
pub fn release_certificate(
    original: &[JClause],
    result: &[JClause],
    released: &[String],
    reserved: &BTreeSet<String>,
) -> serde_json::Value {
    let mut ids = CertIds::default();
    let data_sort = ids.concept(DATA_SORT);
    let original = ids.clauses(original);
    let result = ids.clauses(result);
    let released: Vec<usize> = released.iter().map(|name| ids.concept(name)).collect();
    let reserved: Vec<usize> = reserved.iter().map(|name| ids.concept(name)).collect();
    serde_json::json!({
        "version": 1,
        "data_sort": data_sort,
        "released": released,
        "reserved": reserved,
        "original": original,
        "result": result,
        "concept_names": ids.concepts,
        "role_names": ids.roles,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> JTerm {
        JTerm::Var { name: name.into() }
    }
    fn ind(name: &str) -> JTerm {
        JTerm::Ind { name: name.into() }
    }
    fn c(concept: &str, term: JTerm) -> JAtom {
        JAtom::Concept { concept: concept.into(), term }
    }
    fn r(role: &str, source: JTerm, target: JTerm) -> JAtom {
        JAtom::Role { role: role.into(), source, target }
    }
    fn cl(body: Vec<JAtom>, head: Vec<JAtom>) -> JClause {
        JClause { body, head }
    }
    fn input(clauses: Vec<JClause>) -> JInput {
        serde_json::from_value(serde_json::json!({ "clauses": [] }))
            .map(|mut i: JInput| {
                i.clauses = clauses;
                i
            })
            .unwrap()
    }
    const D: &str = DATA_SORT;

    /// `DataPropertyRange(p xsd:double)` under the sort pass, with `p` used on
    /// a named individual: the range definer `Q_1` is only read through `p`.
    fn range_clauses() -> Vec<JClause> {
        vec![
            cl(vec![], vec![c("Q_0", var("x"))]),
            cl(vec![c("Q_0", var("x"))], vec![c("Q_1", var("x")), c(D, var("x"))]),
            cl(vec![c("Q_1", var("x")), r("p", var("x"), var("y"))], vec![c("__dt__double", var("y"))]),
            cl(vec![c("Q_1", var("x")), c(D, var("x"))], vec![]),
            cl(vec![r("p", var("x"), var("y")), c(D, var("x"))], vec![]),
            cl(vec![r("p", var("x"), var("y"))], vec![c(D, var("y"))]),
            cl(vec![c("__nom__a", var("x")), c(D, var("x"))], vec![]),
            cl(vec![c("__nom__a", var("x"))], vec![c("Q_1", var("x"))]),
            cl(vec![], vec![c("__nom__a", ind("a"))]),
        ]
    }

    #[test]
    fn range_definer_read_only_through_its_data_property_is_released() {
        let mut i = input(range_clauses());
        let report = release_inert_object_sorts(&mut i, |_| false);
        assert_eq!(report, Released { concepts: vec!["Q_1".into()], facts: 1, sort_clauses: 1 });
        assert!(i.clauses.contains(&cl(vec![c("Q_0", var("x"))], vec![c("Q_1", var("x"))])));
        assert!(!i.clauses.contains(&cl(vec![c("Q_1", var("x")), c(D, var("x"))], vec![])));
        // The guard sort clauses stay.
        assert!(i.clauses.contains(&cl(vec![r("p", var("x"), var("y")), c(D, var("x"))], vec![])));
        assert!(i.clauses.contains(&cl(vec![c("__nom__a", var("x")), c(D, var("x"))], vec![])));
        assert_eq!(i.clauses.len(), range_clauses().len() - 1);
    }

    #[test]
    fn ground_fact_on_a_pinned_individual_needs_no_guard() {
        // The normaliser also writes the range definer as ground facts on
        // the individuals it applies to (ore_ont_7278: `→ Q_14(goodsSales)`).
        let mut clauses = range_clauses();
        clauses.push(cl(vec![], vec![c("Q_1", ind("a"))]));
        let mut i = input(clauses.clone());
        let report = release_inert_object_sorts(&mut i, |_| false);
        assert_eq!(report, Released { concepts: vec!["Q_1".into()], facts: 1, sort_clauses: 1 });
        // On an individual no unit fact pins, the sort clause is what keeps
        // `b` out of `D`, and it stays.
        clauses.push(cl(vec![], vec![c("Q_1", ind("b"))]));
        let mut i = input(clauses.clone());
        assert_eq!(release_inert_object_sorts(&mut i, |_| false), Released::default());
        assert!(i.clauses == clauses);
    }

    #[test]
    fn unguarded_body_occurrence_keeps_the_sort() {
        // `Q_1(x) → A(x)` would force the source class `A` on every data
        // element once `Q_1` held there.
        let mut clauses = range_clauses();
        clauses.push(cl(vec![c("Q_1", var("x"))], vec![c("A", var("x"))]));
        clauses.push(cl(vec![c("A", var("x")), c(D, var("x"))], vec![]));
        let mut i = input(clauses.clone());
        assert_eq!(release_inert_object_sorts(&mut i, |_| false), Released::default());
        assert!(i.clauses == clauses);
    }

    #[test]
    fn unguarded_head_occurrence_keeps_the_sort() {
        // `B(x) → Q_1(x)` with a polymorphic `B`: under the sort clause it
        // keeps `B` off data elements, which nothing else does.
        let mut clauses = range_clauses();
        clauses.push(cl(vec![c("B", var("x"))], vec![c("Q_1", var("x"))]));
        let mut i = input(clauses.clone());
        assert_eq!(release_inert_object_sorts(&mut i, |_| false), Released::default());
        assert!(i.clauses == clauses);
    }

    #[test]
    fn candidates_do_not_guard_each_other() {
        // `Q_2(x) ∧ Q_1(x) → A(x)`: each would be the other's only guard,
        // and a released concept is no guard, so neither is released.
        let mut clauses = range_clauses();
        clauses.push(cl(vec![c("Q_0", var("x"))], vec![c("Q_2", var("x")), c(D, var("x"))]));
        clauses.push(cl(vec![c("Q_2", var("x")), c(D, var("x"))], vec![]));
        clauses.push(cl(vec![c("Q_2", var("x")), c("Q_1", var("x"))], vec![c("A", var("x"))]));
        clauses.push(cl(vec![c("A", var("x")), c(D, var("x"))], vec![]));
        let mut i = input(clauses);
        assert_eq!(release_inert_object_sorts(&mut i, |_| false), Released::default());
    }

    #[test]
    fn source_and_reserved_names_keep_their_sort() {
        let mut i = input(range_clauses());
        assert_eq!(release_inert_object_sorts(&mut i, |name| name == "Q_1"), Released::default());
        let mut i = input(range_clauses());
        i.rules = vec![crate::json_io::JRule {
            body: vec![JRuleAtom::Class {
                concept: "Q_1".into(),
                term: crate::json_io::JRuleTerm::Var { name: "x".into() },
            }],
            head: vec![],
        }];
        assert_eq!(release_inert_object_sorts(&mut i, |_| false), Released::default());
    }

    /// Satisfiability of a function-free, equality-free clause set, by DPLL
    /// over its ground instances on the individuals (Herbrand's theorem).
    fn satisfiable(clauses: &[JClause]) -> bool {
        use std::collections::HashMap;
        let mut individuals: BTreeSet<String> = BTreeSet::new();
        let mut terms = |t: &JTerm| match t {
            JTerm::Ind { name } => {
                individuals.insert(name.clone());
            }
            JTerm::Var { .. } => {}
            _ => panic!("function-free clauses only"),
        };
        for clause in clauses {
            for atom in clause.body.iter().chain(&clause.head) {
                match atom {
                    JAtom::Concept { term, .. } => terms(term),
                    JAtom::Role { source, target, .. } => {
                        terms(source);
                        terms(target);
                    }
                    JAtom::Eq { .. } => panic!("equality-free clauses only"),
                }
            }
        }
        let individuals: Vec<String> = individuals.into_iter().collect();
        let mut ids: HashMap<String, usize> = HashMap::new();
        let mut ground: Vec<Vec<(usize, bool)>> = Vec::new();
        for clause in clauses {
            let mut vars: Vec<String> = Vec::new();
            for atom in clause.body.iter().chain(&clause.head) {
                let ts: Vec<&JTerm> = match atom {
                    JAtom::Concept { term, .. } => vec![term],
                    JAtom::Role { source, target, .. } => vec![source, target],
                    JAtom::Eq { .. } => unreachable!(),
                };
                for t in ts {
                    if let JTerm::Var { name } = t {
                        if !vars.contains(name) {
                            vars.push(name.clone());
                        }
                    }
                }
            }
            let mut assignment = vec![0usize; vars.len()];
            loop {
                let value = |t: &JTerm| match t {
                    JTerm::Ind { name } => name.clone(),
                    JTerm::Var { name } => individuals[assignment[vars.iter().position(|v| v == name).unwrap()]].clone(),
                    _ => unreachable!(),
                };
                let key = |atom: &JAtom| match atom {
                    JAtom::Concept { concept, term } => format!("{concept}({})", value(term)),
                    JAtom::Role { role, source, target } => format!("{role}({},{})", value(source), value(target)),
                    JAtom::Eq { .. } => unreachable!(),
                };
                let mut lits = Vec::new();
                for atom in &clause.body {
                    let n = ids.len();
                    lits.push((*ids.entry(key(atom)).or_insert(n), false));
                }
                for atom in &clause.head {
                    let n = ids.len();
                    lits.push((*ids.entry(key(atom)).or_insert(n), true));
                }
                ground.push(lits);
                let mut i = 0;
                while i < vars.len() {
                    assignment[i] += 1;
                    if assignment[i] < individuals.len() {
                        break;
                    }
                    assignment[i] = 0;
                    i += 1;
                }
                if i == vars.len() {
                    break;
                }
            }
        }
        fn dpll(clauses: &[Vec<(usize, bool)>], values: &mut Vec<Option<bool>>) -> bool {
            loop {
                let mut unit = None;
                for clause in clauses {
                    let mut open = None;
                    let mut count = 0;
                    let mut satisfied = false;
                    for &(v, sign) in clause {
                        match values[v] {
                            Some(x) if x == sign => satisfied = true,
                            Some(_) => {}
                            None => {
                                count += 1;
                                open = Some((v, sign));
                            }
                        }
                    }
                    if satisfied {
                        continue;
                    }
                    if count == 0 {
                        return false;
                    }
                    if count == 1 {
                        unit = open;
                        break;
                    }
                }
                match unit {
                    Some((v, sign)) => values[v] = Some(sign),
                    None => break,
                }
            }
            let Some(v) = values.iter().position(Option::is_none) else { return true };
            for choice in [false, true] {
                let mut next = values.clone();
                next[v] = Some(choice);
                if dpll(clauses, &mut next) {
                    return true;
                }
            }
            false
        }
        let mut values = vec![None; ids.len()];
        dpll(&ground, &mut values)
    }

    /// Small LCG, so the generated clause sets are reproducible.
    struct Lcg(u64);
    impl Lcg {
        fn below(&mut self, n: usize) -> usize {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((self.0 >> 33) as usize) % n
        }
    }

    /// A random sorted clause set in the shape the frontend emits: two range
    /// definers `Q_1`, `Q_2` behind relativized `⊤` facts, source classes
    /// `A`, `B`, a nominal proxy, a data property `p`, an object property `r`,
    /// a data value `v`, and a few random clauses over them.
    fn random_sorted(rng: &mut Lcg) -> Vec<JClause> {
        let (x, y) = (var("x"), var("y"));
        let mut s = vec![
            cl(vec![], vec![c("Q_0", x.clone())]),
            cl(vec![c("Q_0", x.clone())], vec![c("Q_1", x.clone()), c(D, x.clone())]),
            cl(vec![c("Q_0", x.clone())], vec![c("Q_2", x.clone()), c(D, x.clone())]),
            cl(vec![r("p", x.clone(), y.clone()), c(D, x.clone())], vec![]),
            cl(vec![r("p", x.clone(), y.clone())], vec![c(D, y.clone())]),
            cl(vec![r("r", x.clone(), y.clone()), c(D, x.clone())], vec![]),
            cl(vec![r("r", x.clone(), y.clone()), c(D, y.clone())], vec![]),
            cl(vec![c("__dt__x", x.clone())], vec![c(D, x.clone())]),
            cl(vec![], vec![c("__nom__a", ind("a"))]),
            cl(vec![], vec![c("__dt__x", ind("v"))]),
        ];
        for g in ["A", "B", "__nom__a", "Q_1", "Q_2"] {
            s.push(cl(vec![c(g, x.clone()), c(D, x.clone())], vec![]));
        }
        let subject = ["a", "b"][rng.below(2)];
        s.push(cl(vec![], vec![r("p", ind(subject), ind("v"))]));
        if rng.below(2) == 0 {
            s.push(cl(vec![], vec![r("r", ind("a"), ind("b"))]));
        }
        let concepts = ["Q_1", "Q_2", "A", "B", "__dt__x"];
        let atom = |rng: &mut Lcg, allow_roles: bool| -> JAtom {
            let terms = [var("x"), var("y"), ind("a"), ind("b"), ind("v")];
            let t = terms[rng.below(terms.len())].clone();
            if allow_roles && rng.below(3) == 0 {
                let (s, o) = if rng.below(2) == 0 { (var("x"), var("y")) } else { (var("y"), var("x")) };
                return r(["p", "r"][rng.below(2)], s, o);
            }
            c(concepts[rng.below(concepts.len())], t)
        };
        for _ in 0..(2 + rng.below(4)) {
            let body: Vec<JAtom> = (0..rng.below(3)).map(|_| atom(rng, true)).collect();
            let head: Vec<JAtom> = (0..rng.below(3)).map(|_| atom(rng, false)).collect();
            if body.is_empty() && head.is_empty() {
                continue;
            }
            s.push(cl(body, head));
        }
        s
    }

    /// The release without (B) and (H): every candidate loses its sort.
    fn release_unchecked(clauses: &[JClause]) -> Vec<JClause> {
        let released = ["Q_1", "Q_2"];
        let mut out: Vec<JClause> = clauses
            .iter()
            .filter(|clause| !concept_sort_clause(clause).is_some_and(|g| released.contains(&g)))
            .cloned()
            .collect();
        for clause in &mut out {
            let terms: Vec<JTerm> = clause
                .head
                .iter()
                .filter_map(|a| match a {
                    JAtom::Concept { concept, term } if released.contains(&concept.as_str()) => Some(term.clone()),
                    _ => None,
                })
                .collect();
            clause.head.retain(|a| !terms.iter().any(|t| is_data(a, t)));
        }
        out
    }

    #[test]
    fn release_preserves_satisfiability_and_its_conditions_are_needed() {
        let mut rng = Lcg(20261030);
        let (mut released, mut released_satisfiable, mut differs_unchecked) = (0, 0, 0);
        for _ in 0..3000 {
            let clauses = random_sorted(&mut rng);
            let mut i = input(clauses.clone());
            let report = release_inert_object_sorts(&mut i, |_| false);
            if !report.concepts.is_empty() {
                released += 1;
            }
            let before = satisfiable(&clauses);
            assert_eq!(before, satisfiable(&i.clauses), "release changed satisfiability: {report:?}");
            if before && !report.concepts.is_empty() {
                released_satisfiable += 1;
            }
            if before != satisfiable(&release_unchecked(&clauses)) {
                differs_unchecked += 1;
            }
        }
        eprintln!(
            "3000 random clause sets: released on {released} ({released_satisfiable} satisfiable), \
             unchecked release changes the verdict on {differs_unchecked}"
        );
        // The release applies on a share of the inputs, and dropping the
        // guard conditions would change the verdict on others.
        assert!(released > 300, "released on {released} inputs");
        assert!(released_satisfiable > 100, "released on {released_satisfiable} satisfiable inputs");
        assert!(differs_unchecked > 30, "unchecked release differs on {differs_unchecked} inputs");
    }

    #[test]
    fn unchecked_release_turns_a_consistent_input_inconsistent() {
        // `Q_1(x) → A(x)` reads the definer on the data value `v`: released
        // without (B), `Q_0(v) → Q_1(v) → A(v)` clashes with `A ⊓ D ⊑ ⊥`.
        let mut clauses = range_clauses();
        clauses.push(cl(vec![c("Q_1", var("x"))], vec![c("A", var("x"))]));
        clauses.push(cl(vec![c("A", var("x")), c(D, var("x"))], vec![]));
        clauses.push(cl(vec![], vec![r("p", ind("a"), ind("v"))]));
        assert!(satisfiable(&clauses));
        let unchecked: Vec<JClause> = release_unchecked(&clauses);
        assert!(!satisfiable(&unchecked));
        let mut i = input(clauses.clone());
        assert_eq!(release_inert_object_sorts(&mut i, |_| false), Released::default());
    }

    /// The Lean checker of the release certificate, from
    /// `KM_RULES_TEST_INERT_LEAN_CHECKER` (the rules certification gate sets
    /// it); `None` skips, unless `KM_REQUIRE_LEAN_CHECKERS` is set.
    fn lean_checker() -> Option<std::path::PathBuf> {
        match std::env::var_os("KM_RULES_TEST_INERT_LEAN_CHECKER") {
            Some(path) => Some(path.into()),
            None => {
                assert!(
                    std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
                    "KM_RULES_TEST_INERT_LEAN_CHECKER is required"
                );
                eprintln!("skipping: KM_RULES_TEST_INERT_LEAN_CHECKER is unset");
                None
            }
        }
    }

    fn lean_accepts(checker: &std::path::Path, document: &serde_json::Value, tag: &str) -> bool {
        let path = std::env::temp_dir().join(format!("km-rules-inert-test-{}-{tag}.json", std::process::id()));
        std::fs::write(&path, serde_json::to_vec(document).unwrap()).unwrap();
        let status = crate::lean_checker::run(checker, &path).unwrap().status;
        let _ = std::fs::remove_file(&path);
        assert!(status.code().is_some_and(|code| code <= 1), "checker failed to run: {status}");
        status.success()
    }

    #[test]
    fn lean_checker_accepts_the_release_and_rejects_unchecked_ones() {
        let Some(checker) = lean_checker() else { return };
        let mut rng = Lcg(20261030);
        let (mut accepted, mut rejected) = (0, 0);
        for round in 0..3000 {
            let clauses = random_sorted(&mut rng);
            let mut i = input(clauses.clone());
            let reserved = reserved_concepts(&i, |_| false);
            let report = release_inert_object_sorts(&mut i, |_| false);
            if !report.concepts.is_empty() {
                let document = release_certificate(&clauses, &i.clauses, &report.concepts, &reserved);
                assert!(lean_accepts(&checker, &document, &format!("{round}-ok")), "round {round}: rejected");
                accepted += 1;
            }
            // Releasing both candidates without (B) and (H): whenever that
            // changes satisfiability, `WireInertSortRelease.check_sound`
            // forbids acceptance.
            let unchecked = release_unchecked(&clauses);
            if satisfiable(&clauses) != satisfiable(&unchecked) {
                let released = vec!["Q_1".to_string(), "Q_2".to_string()];
                let document = release_certificate(&clauses, &unchecked, &released, &reserved);
                assert!(!lean_accepts(&checker, &document, &format!("{round}-bad")), "round {round}: accepted");
                rejected += 1;
            }
        }
        eprintln!("Lean accepted {accepted} releases and rejected {rejected} verdict-changing unchecked releases");
        assert!(accepted > 300 && rejected > 30);
    }

    #[test]
    fn lean_checker_rejects_a_tampered_or_reserved_release() {
        let Some(checker) = lean_checker() else { return };
        let clauses = range_clauses();
        let mut i = input(clauses.clone());
        let reserved = reserved_concepts(&i, |_| false);
        let report = release_inert_object_sorts(&mut i, |_| false);
        let document = release_certificate(&clauses, &i.clauses, &report.concepts, &reserved);
        assert!(lean_accepts(&checker, &document, "range"));
        // The worker input must be exactly the release of the original.
        let mut dropped = i.clauses.clone();
        dropped.pop();
        let document = release_certificate(&clauses, &dropped, &report.concepts, &reserved);
        assert!(!lean_accepts(&checker, &document, "dropped"));
        // A reserved name is never released.
        let mut with_q1: BTreeSet<String> = reserved.clone();
        with_q1.insert("Q_1".into());
        let document = release_certificate(&clauses, &i.clauses, &report.concepts, &with_q1);
        assert!(!lean_accepts(&checker, &document, "reserved"));
    }

    #[test]
    fn input_without_relativized_facts_is_unchanged() {
        let clauses = vec![
            cl(vec![], vec![c("Q_0", var("x"))]),
            cl(vec![c("Q_0", var("x"))], vec![c("Q_1", var("x"))]),
        ];
        let mut i = input(clauses.clone());
        assert_eq!(release_inert_object_sorts(&mut i, |_| false), Released::default());
        assert!(i.clauses == clauses);
    }
}
