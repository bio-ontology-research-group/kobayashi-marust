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
use crate::json_io::{JAtom, JClause, JInput, JRuleAtom, JTerm};

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
    release_with(input, is_source, Options { reserve_records: true, maximal: false })
}

/// The same release for the clause input of the nominal CB engine
/// (docs/NOMINALS-CB.md, "Inert object sorts in the nominal CB input
/// (2026-10-30)"). Two differences from the rule checker's pass:
///
/// * Cardinality and definer records do not reserve their names. The CB
///   engine reads only `input.clauses` (`cli::run_engine` builds the
///   `Reasoner` from the clauses alone), so a record carries no meaning there;
///   the names it reads with a meaning of their own are the source names, the
///   queries and the asserted markers, which the caller passes in `is_source`,
///   and the `__nom__` proxies and assertion markers of the nominal ABox,
///   which this function reserves. Rule atoms stay reserved.
/// * The fixpoint is maximal along mutual guards: when every failing candidate
///   fails only in clauses where another candidate on the same term would be a
///   guard once it is kept (`Q_0(x) ∧ Q_2(x) → ⊥` for the complementary
///   markers of `≤1 p` and `≥2 p`), one of them (the greatest name) is kept and
///   the others are re-checked, instead of keeping all of them. The loop ends
///   only when no candidate fails (B) or (H), so the module's model
///   correspondence holds for the final set exactly as for the rule checker's.
///
/// The caller must give the result only to workers that read nothing but the
/// clauses and report only names in `is_source`.
pub fn release_inert_object_sorts_for_cb(
    input: &mut JInput,
    is_source: impl Fn(&str) -> bool,
) -> Released {
    let mut abox_names: HashSet<String> = HashSet::new();
    for individual in &input.nominal_abox.individuals {
        abox_names.extend(individual.proxies.iter().cloned());
        abox_names.extend(individual.assertion_markers.iter().cloned());
    }
    release_with(
        input,
        |name| is_source(name) || abox_names.contains(name),
        Options { reserve_records: false, maximal: true },
    )
}

/// What [`eliminate_universal_definers`] removed.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Eliminated {
    /// The definers `Q` with a unit fact `→ Q(x)` that were eliminated, sorted.
    pub concepts: Vec<String>,
    /// Clauses dropped because their head holds an eliminated definer (the
    /// unit facts included).
    pub clauses: usize,
    /// Body atoms dropped.
    pub body_atoms: usize,
}

/// Eliminate every internal definer `Q` that holds everywhere: the clause
/// set has the unit fact `→ Q(x)` (empty body, one atom on a variable), so
/// every model interprets `Q` as the whole domain. Each body atom `Q(t)` is
/// then true and is dropped, and each clause with `Q(t)` in its head is true
/// and is dropped, the unit fact included (docs/NOMINALS-CB.md, "Inert
/// object sorts in the nominal CB input (2026-10-30)").
///
/// The result `S'` has the same models as the input `S` on every other name:
/// a model of `S` satisfies `S'` because each dropped body atom was true and
/// `S'` has no clause that `S` lacks a stronger form of; a model of `S'`
/// becomes a model of `S` by interpreting each eliminated `Q` as the whole
/// domain (a clause with `Q` in its head then holds, and a clause that lost
/// `Q` body atoms holds as its shortened form does). Names in `is_source`,
/// the nominal-ABox proxies and markers and rule atoms are never
/// eliminated. A definer is kept when dropping its body atoms would leave a
/// clause with an empty body and a role atom or a function term in its head,
/// a shape the frontend never emits. Clause sets with inverse roles are left
/// unchanged (a cost guard, see the body).
///
/// After [`release_inert_object_sorts_for_cb`], a released definer whose
/// relativized fact was `→ Q(x) ∨ D(x)` has the unit fact `→ Q(x)` and is
/// eliminated here; so is the `⊤` definer of an unqualified cardinality.
/// Like that pass, the result is only for workers that read nothing but the
/// clauses and report only names in `is_source`.
pub fn eliminate_universal_definers(
    input: &mut JInput,
    is_source: impl Fn(&str) -> bool,
) -> Eliminated {
    // Inverse roles: the elimination is exact there too, but it can cost.
    // On `⊤ ⊑ ≥2 u`, `⊤ ⊑ ∃r.{a}`, `{a} ⊑ ≤1 r⁻`
    // (tests/fixtures/top_nominal_data/probe_v7.ofn) dropping the `⊤` filler
    // from the inverse at-most clause took the CB engine from 0.06 s past
    // 150 s (nominals, inverse roles and number restrictions together are
    // where the Nom rule fires). Leave such clause sets unchanged.
    let inverse = input.rbox.iter().any(|row| row.first().map(String::as_str) == Some("inverse"))
        || input.clauses.iter().any(|clause| {
            clause.body.iter().chain(&clause.head).any(|atom| {
                matches!(atom, JAtom::Role { role, .. } if role.starts_with("__inv__"))
            })
        });
    if inverse {
        return Eliminated::default();
    }
    let mut reserved: HashSet<String> = HashSet::new();
    for individual in &input.nominal_abox.individuals {
        reserved.extend(individual.proxies.iter().cloned());
        reserved.extend(individual.assertion_markers.iter().cloned());
    }
    for rule in &input.rules {
        for atom in rule.body.iter().chain(&rule.head) {
            if let JRuleAtom::Class { concept, .. } = atom {
                reserved.insert(concept.clone());
            }
        }
    }
    let mut universal: BTreeSet<String> = BTreeSet::new();
    for clause in &input.clauses {
        if let ([], [JAtom::Concept { concept, term: JTerm::Var { .. } }]) =
            (clause.body.as_slice(), clause.head.as_slice())
        {
            if super::cb_to_ht::is_internal(concept)
                && !concept.starts_with("__")
                && concept != DATA_SORT
                && !reserved.contains(concept)
                && !is_source(concept)
            {
                universal.insert(concept.clone());
            }
        }
    }
    let is_universal = |atom: &JAtom, universal: &BTreeSet<String>| {
        matches!(atom, JAtom::Concept { concept, .. } if universal.contains(concept))
    };
    // Keep a definer whose elimination would leave an unconditional role or
    // Skolem head; repeat, since keeping one can change another clause's body.
    loop {
        let mut kept: Option<String> = None;
        for clause in &input.clauses {
            if clause.head.iter().any(|atom| is_universal(atom, &universal))
                || !clause.body.iter().any(|atom| is_universal(atom, &universal))
                || clause.body.iter().any(|atom| !is_universal(atom, &universal))
            {
                continue;
            }
            let unconditional_structure = clause.head.iter().any(|atom| match atom {
                JAtom::Concept { term, .. } => !matches!(term, JTerm::Var { .. } | JTerm::Ind { .. }),
                JAtom::Role { .. } | JAtom::Eq { .. } => true,
            });
            if unconditional_structure {
                if let Some(JAtom::Concept { concept, .. }) =
                    clause.body.iter().find(|atom| is_universal(atom, &universal))
                {
                    kept = Some(concept.clone());
                    break;
                }
            }
        }
        match kept {
            Some(concept) => {
                universal.remove(&concept);
            }
            None => break,
        }
    }
    if universal.is_empty() {
        return Eliminated::default();
    }
    let mut report = Eliminated { concepts: universal.iter().cloned().collect(), ..Eliminated::default() };
    input.clauses.retain(|clause| {
        let drop = clause.head.iter().any(|atom| is_universal(atom, &universal));
        report.clauses += usize::from(drop);
        !drop
    });
    for clause in &mut input.clauses {
        let before = clause.body.len();
        clause.body.retain(|atom| !is_universal(atom, &universal));
        report.body_atoms += before - clause.body.len();
    }
    report
}

struct Options {
    /// Cardinality markers and fillers and definer markers and operands keep
    /// their sorts (their records are read by the worker).
    reserve_records: bool,
    /// Keep one of a set of mutually guarding candidates instead of all.
    maximal: bool,
}

fn release_with(input: &mut JInput, is_source: impl Fn(&str) -> bool, options: Options) -> Released {
    let clauses = &input.clauses;
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
    if options.reserve_records {
        for card in &input.cardinalities {
            reserved.insert(&card.marker);
            reserved.insert(&card.filler);
        }
        for definer in &input.definers {
            reserved.insert(&definer.marker);
            reserved.extend(definer.operands.iter().map(String::as_str));
        }
    }
    for rule in &input.rules {
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
    // Only the clauses that mention a candidate can fail; candidates only
    // leave the set, so this list stays complete for every round.
    let relevant: Vec<&JClause> = clauses
        .iter()
        .filter(|clause| concept_sort_clause(clause).is_none())
        .filter(|clause| {
            clause.body.iter().chain(&clause.head).any(|atom| {
                matches!(atom, JAtom::Concept { concept, .. } if released.contains(concept.as_str()))
            })
        })
        .collect();
    // Remove candidates that violate (B) or (H) until none does.
    loop {
        let mut failed: BTreeSet<&str> = BTreeSet::new();
        let pinned = guards.pinned(&released);
        for &clause in &relevant {
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
        if options.maximal {
            // A failure is soft when the failing clause's body holds another
            // candidate on the same term that has a sort clause: keeping that
            // candidate would make it a guard. A concept with a hard failure
            // is kept at once; among soft failures only the greatest is kept.
            let mut hard: BTreeSet<&str> = BTreeSet::new();
            for &clause in &relevant {
                let soft = |own: &str, term: &JTerm| {
                    clause.body.iter().any(|atom| {
                        matches!(atom, JAtom::Concept { concept, term: t }
                            if t == term
                                && concept.as_str() != own
                                && released.contains(concept.as_str())
                                && guards.object_concepts.contains(concept.as_str()))
                    })
                };
                for atom in &clause.body {
                    if let JAtom::Concept { concept, term } = atom {
                        if failed.contains(concept.as_str())
                            && !guards.guarded(clause, term, &released, &pinned)
                            && !soft(concept, term)
                        {
                            hard.insert(concept.as_str());
                        }
                    }
                }
                for atom in &clause.head {
                    if let JAtom::Concept { concept, term } = atom {
                        if failed.contains(concept.as_str())
                            && !clause.head.iter().any(|other| is_data(other, term))
                            && !guards.guarded(clause, term, &released, &pinned)
                            && !soft(concept, term)
                        {
                            hard.insert(concept.as_str());
                        }
                    }
                }
            }
            if hard.is_empty() {
                let greatest = *failed.iter().next_back().expect("failed is non-empty");
                released.remove(greatest);
            } else {
                released.retain(|concept| !hard.contains(concept));
            }
            continue;
        }
        released.retain(|concept| !failed.contains(concept));
    }
    if released.is_empty() {
        return Released::default();
    }
    let released: BTreeSet<String> = released.into_iter().map(str::to_string).collect();
    let mut report = Released { concepts: released.iter().cloned().collect(), ..Released::default() };
    input.clauses.retain(|clause| {
        let drop = concept_sort_clause(clause).is_some_and(|concept| released.contains(concept));
        report.sort_clauses += usize::from(drop);
        !drop
    });
    for clause in &mut input.clauses {
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

    // ---- the nominal CB variant (`release_inert_object_sorts_for_cb`) ----

    /// The complementary markers of `≤1 p` (`Q_3`) and `≥2 p` (`Q_4`) of a
    /// negated data cardinality: `⊤ ⊑ ≤1 p ⊔ ≥2 p` relativized, with the
    /// disjointness clause between them. `Q_4` is read unguarded (as the
    /// existential of `≥2 p` is), `Q_3` only through `p`.
    fn complementary_marker_clauses() -> Vec<JClause> {
        let mut clauses = range_clauses();
        clauses.push(cl(vec![], vec![c("Q_3", var("x")), c("Q_4", var("x")), c(D, var("x"))]));
        clauses.push(cl(vec![c("Q_3", var("x")), c("Q_4", var("x"))], vec![]));
        clauses.push(cl(vec![c("Q_3", var("x")), c(D, var("x"))], vec![]));
        clauses.push(cl(vec![c("Q_4", var("x")), c(D, var("x"))], vec![]));
        clauses.push(cl(vec![c("Q_3", var("x")), r("p", var("x"), var("y")), r("p", var("x"), var("z"))], vec![c("B", var("y"))]));
        clauses.push(cl(vec![c("Q_4", var("x"))], vec![c("A", var("x"))]));
        clauses.push(cl(vec![c("A", var("x")), c(D, var("x"))], vec![]));
        clauses.push(cl(vec![c("B", var("x")), c(D, var("x"))], vec![]));
        clauses
    }

    fn with_cardinality_records(mut i: JInput) -> JInput {
        i.cardinalities = serde_json::from_value(serde_json::json!([
            {"marker": "Q_3", "min": false, "n": 1, "role": "p", "filler": "Q_0"},
            {"marker": "Q_4", "min": true, "n": 2, "role": "p", "filler": "Q_0"}
        ]))
        .unwrap();
        i
    }

    #[test]
    fn cb_release_frees_a_maximum_marker_kept_by_its_record_in_the_rule_checker() {
        let clauses = complementary_marker_clauses();
        // The rule checker reads the records: `Q_3` stays reserved.
        let mut i = with_cardinality_records(input(clauses.clone()));
        let rules = release_inert_object_sorts(&mut i, |name| !crate::orchestrate::cb_to_ht::is_internal(name));
        assert!(!rules.concepts.contains(&"Q_3".to_string()), "{rules:?}");
        // The CB engine reads only the clauses. `Q_4` is read unguarded
        // (`Q_4(x) → A(x)`), so it keeps its sort and guards `Q_3` in the
        // disjointness clause; `Q_3` is released and the `D` disjunct of the
        // complementary fact goes.
        let mut i = with_cardinality_records(input(clauses.clone()));
        let cb = release_inert_object_sorts_for_cb(&mut i, |name| !crate::orchestrate::cb_to_ht::is_internal(name));
        assert_eq!(cb.concepts, vec!["Q_1".to_string(), "Q_3".to_string()]);
        assert!(i.clauses.contains(&cl(vec![], vec![c("Q_3", var("x")), c("Q_4", var("x"))])));
        assert!(i.clauses.contains(&cl(vec![c("Q_4", var("x")), c(D, var("x"))], vec![])));
        assert!(!i.clauses.contains(&cl(vec![c("Q_3", var("x")), c(D, var("x"))], vec![])));
        assert_eq!(satisfiable(&clauses), satisfiable(&i.clauses));
    }

    #[test]
    fn cb_release_keeps_exactly_one_of_two_mutual_guards() {
        // The clauses of `candidates_do_not_guard_each_other`: the rule
        // checker's pass keeps both sorts; the CB variant keeps the greatest
        // (`Q_2`), which then guards `Q_1`.
        let mut clauses = range_clauses();
        clauses.push(cl(vec![c("Q_0", var("x"))], vec![c("Q_2", var("x")), c(D, var("x"))]));
        clauses.push(cl(vec![c("Q_2", var("x")), c(D, var("x"))], vec![]));
        clauses.push(cl(vec![c("Q_2", var("x")), c("Q_1", var("x"))], vec![c("A", var("x"))]));
        clauses.push(cl(vec![c("A", var("x")), c(D, var("x"))], vec![]));
        let mut i = input(clauses.clone());
        assert_eq!(release_inert_object_sorts(&mut i, |_| false), Released::default());
        let mut i = input(clauses.clone());
        let cb = release_inert_object_sorts_for_cb(&mut i, |_| false);
        assert_eq!(cb, Released { concepts: vec!["Q_1".into()], facts: 1, sort_clauses: 1 });
        assert!(i.clauses.contains(&cl(vec![c("Q_2", var("x")), c(D, var("x"))], vec![])));
        assert_eq!(satisfiable(&clauses), satisfiable(&i.clauses));
    }

    #[test]
    fn cb_release_reserves_the_nominal_abox_markers() {
        let mut i = input(range_clauses());
        i.nominal_abox = serde_json::from_value(serde_json::json!({
            "complete": true,
            "individuals": [{"individual": "a", "proxies": ["__nom__a"], "assertions": [], "assertion_markers": ["Q_1"]}]
        }))
        .unwrap();
        assert_eq!(release_inert_object_sorts_for_cb(&mut i, |_| false), Released::default());
        assert!(i.clauses == range_clauses());
    }

    /// Entailment of the source-level answers by DPLL: consistency, and for
    /// the source classes `A`, `B` satisfiability and `A ⊑ B`, `B ⊑ A` (a
    /// fresh individual `c` carries the query).
    fn answers(clauses: &[JClause]) -> Vec<bool> {
        let mut out = vec![satisfiable(clauses)];
        for (sub, sup) in [("A", None), ("B", None), ("A", Some("B")), ("B", Some("A"))] {
            let mut query = clauses.to_vec();
            query.push(cl(vec![], vec![c(sub, ind("c"))]));
            if let Some(sup) = sup {
                query.push(cl(vec![c(sup, ind("c"))], vec![]));
            }
            out.push(satisfiable(&query));
        }
        out
    }

    #[test]
    fn cb_release_preserves_source_answers_on_random_inputs() {
        let mut rng = Lcg(20261031);
        let (mut released, mut more_than_rules, mut eliminated) = (0, 0, 0);
        for _ in 0..2000 {
            let mut clauses = random_sorted(&mut rng);
            // Mutual guards between the two range definers, as the
            // complementary cardinality markers have them.
            if rng.below(2) == 0 {
                clauses.push(cl(vec![c("Q_1", var("x")), c("Q_2", var("x"))], vec![]));
            }
            let mut rules_input = input(clauses.clone());
            let rules = release_inert_object_sorts(&mut rules_input, |name| name == "A" || name == "B");
            let mut i = input(clauses.clone());
            let report = release_inert_object_sorts_for_cb(&mut i, |name| name == "A" || name == "B");
            if !report.concepts.is_empty() {
                released += 1;
            }
            if report.concepts.len() > rules.concepts.len() {
                more_than_rules += 1;
            }
            let expected = answers(&clauses);
            assert_eq!(expected, answers(&i.clauses), "release changed an answer: {report:?}");
            let gone = eliminate_universal_definers(&mut i, |name| name == "A" || name == "B");
            if !gone.concepts.is_empty() {
                eliminated += 1;
            }
            assert_eq!(expected, answers(&i.clauses), "elimination changed an answer: {gone:?}");
        }
        eprintln!(
            "2000 random clause sets: CB release on {released}, more than the rule checker's on \
             {more_than_rules}, universal definers eliminated on {eliminated}"
        );
        assert!(released > 200, "released on {released} inputs");
        assert!(eliminated > 200, "eliminated on {eliminated} inputs");
        assert!(more_than_rules > 20, "maximal fixpoint released more on {more_than_rules} inputs");
    }

    #[test]
    fn universal_definer_is_eliminated_from_bodies_and_heads() {
        // `→ Q_1(x)` (the `⊤` definer of an unqualified cardinality, or a
        // released range definer): its body atoms are true, and clauses with
        // it in the head are true.
        let clauses = vec![
            cl(vec![], vec![c("Q_1", var("x"))]),
            cl(vec![c("Q_1", var("y")), r("p", var("x"), var("y"))], vec![c("Q_2", var("x"))]),
            cl(vec![c("A", var("x"))], vec![c("Q_1", var("x")), c("B", var("x"))]),
            cl(vec![c("Q_1", var("x")), c("Q_2", var("x"))], vec![c("B", var("x"))]),
            cl(vec![], vec![r("p", ind("a"), ind("b"))]),
            cl(vec![c("B", ind("a"))], vec![]),
        ];
        let mut i = input(clauses.clone());
        let report = eliminate_universal_definers(&mut i, |name| name == "A" || name == "B");
        assert_eq!(report, Eliminated { concepts: vec!["Q_1".into()], clauses: 2, body_atoms: 2 });
        assert!(i.clauses.contains(&cl(vec![r("p", var("x"), var("y"))], vec![c("Q_2", var("x"))])));
        assert!(i.clauses.contains(&cl(vec![c("Q_2", var("x"))], vec![c("B", var("x"))])));
        // `p(a, b)` gives `Q_2(a)`, then `B(a)`, which clashes either way.
        assert!(!satisfiable(&clauses));
        assert!(!satisfiable(&i.clauses));
    }

    #[test]
    fn universal_definer_guarding_an_existential_is_kept() {
        // Dropping `Q_1(x)` from `Q_1(x) → p(x, f(x))` would leave an
        // unconditional Skolem head, a shape the frontend never emits.
        let f = JTerm::Fun { function: "f".into(), arg: Box::new(var("x")) };
        let clauses = vec![
            cl(vec![], vec![c("Q_1", var("x"))]),
            cl(vec![c("Q_1", var("x"))], vec![r("p", var("x"), f)]),
            cl(vec![c("Q_1", var("x")), c("A", var("x"))], vec![c("B", var("x"))]),
        ];
        let mut i = input(clauses.clone());
        assert_eq!(eliminate_universal_definers(&mut i, |_| false), Eliminated::default());
        assert!(i.clauses == clauses);
    }

    #[test]
    fn source_and_abox_names_are_never_eliminated() {
        let clauses = vec![
            cl(vec![], vec![c("Q_1", var("x"))]),
            cl(vec![c("Q_1", var("x"))], vec![c("B", var("x"))]),
        ];
        let mut i = input(clauses.clone());
        assert_eq!(eliminate_universal_definers(&mut i, |name| name == "Q_1"), Eliminated::default());
        let mut i = input(clauses.clone());
        i.nominal_abox = serde_json::from_value(serde_json::json!({
            "complete": true,
            "individuals": [{"individual": "a", "proxies": ["__nom__a"], "assertions": [], "assertion_markers": ["Q_1"]}]
        }))
        .unwrap();
        assert_eq!(eliminate_universal_definers(&mut i, |_| false), Eliminated::default());
        assert!(i.clauses == clauses);
    }

    #[test]
    fn universal_definers_stay_beside_inverse_roles() {
        let clauses = vec![
            cl(vec![], vec![c("Q_1", var("x"))]),
            cl(
                vec![c("Q_1", var("y")), c("Q_1", var("z")), c("Q_3", var("x")),
                     r("__inv__r", var("x"), var("y")), r("__inv__r", var("x"), var("z"))],
                vec![JAtom::Eq { left: var("y"), right: var("z") }],
            ),
        ];
        let mut i = input(clauses.clone());
        assert_eq!(eliminate_universal_definers(&mut i, |_| false), Eliminated::default());
        assert!(i.clauses == clauses);
        let mut i = input(clauses[..1].to_vec());
        assert_eq!(eliminate_universal_definers(&mut i, |_| false).concepts, vec!["Q_1".to_string()]);
    }
}
