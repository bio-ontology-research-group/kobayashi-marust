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
/// * When the clause set equates generated value successors
///   ([`equates_generated_values`]), a definer that guards a data role in a
///   body and whose relativized fact is disjunctive is not a candidate. The
///   fixpoint then starts from fewer candidates and ends, as before, only
///   when none fails (B) or (H); with no candidate left the input is
///   unchanged.
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
    let data_guards_sorted = equates_generated_values(&input.clauses);
    release_with(
        &mut input.clauses,
        &[],
        &[],
        &input.rules,
        |name| is_source(name) || abox_names.contains(name),
        Options { maximal: true, data_guards_sorted },
    )
}

/// The names [`release_inert_object_sorts_for_cb`] never releases, for its
/// certificate (`release_certificate`): every concept that is not an
/// internal definer, every name in `is_source`, the nominal-ABox proxies and
/// assertion markers, and rule atoms. Unlike [`reserved_concepts`] it does
/// not reserve record or source-axiom names, which the CB engine does not
/// read.
pub fn reserved_concepts_for_cb(input: &JInput, is_source: impl Fn(&str) -> bool) -> BTreeSet<String> {
    let mut reserved = BTreeSet::new();
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
    for clause in &input.clauses {
        for atom in clause.body.iter().chain(&clause.head) {
            if let JAtom::Concept { concept, .. } = atom {
                if !is_cb_definer(concept) || is_source(concept) {
                    reserved.insert(concept.clone());
                }
            }
        }
    }
    reserved
}

/// An internal definer name of the frontend (`Q_`, `aux_`, `def_`): the only
/// names the CB variants of the release and of the universal-definer
/// elimination may change. Every other concept is in
/// [`reserved_concepts_for_cb`].
pub(crate) fn is_cb_definer(concept: &str) -> bool {
    ["Q_", "aux_", "def_"].iter().any(|prefix| concept.starts_with(prefix))
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
///
/// Lean: `ContextCalculus.UniversalDefiner.eliminate` is this
/// transformation, and `models_iff` and `eliminate_equisatisfiable` prove the
/// correspondence above for any eliminated set whose members are unreserved
/// and have a unit fact; the guards below only shrink the set.
/// [`nominal_cb_input_certificate`] records the release and this pass for
/// the checker `nominal-cb-input-check`.
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
    let mut abox_names: HashSet<String> = HashSet::new();
    for individual in &input.nominal_abox.individuals {
        abox_names.extend(individual.proxies.iter().cloned());
        abox_names.extend(individual.assertion_markers.iter().cloned());
    }
    let mut reserved: HashSet<String> = abox_names.clone();
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
            // `is_cb_definer` and `is_source` together are the complement of
            // `reserved_concepts_for_cb` (with the ABox and rule names in
            // `reserved`), the reserved set of the Lean certificate
            // (`WireNominalCBInput`): its check requires every eliminated
            // definer to be unreserved. `is_internal` alone also admits
            // builtin vocabulary such as `owl:Thing`, which that set reserves.
            if super::cb_to_ht::is_internal(concept)
                && is_cb_definer(concept)
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
    // Fillers of an at-most asserted on an individual: the same cost as the
    // inverse case above. On open_r3602 (results/agents/2026-10-30/
    // r3-unannounced: `ClassAssertion(≤1 s, c)` with `s(a, a)`, `s(c, a)` and
    // `D ⊑ {a, b}`) dropping the `⊤` filler from `Q_3(x) ∧ Q_4(y0) ∧ Q_4(y1)
    // ∧ s(x, y0) ∧ s(x, y1) → y0 = y1`, `Q_3` the assertion marker of `c`,
    // took the forced nominals route from 4 s past 60 s: the equality then
    // fires on every pair of `s`-successors of `c` before their labels are
    // known. Keep a definer on an equality-head term whose clause body holds
    // a nominal proxy or an assertion marker, unless the term is a data
    // successor (`v(x, y0)` with `v(x, y) → D(y)`; seed m2047 asserts
    // `≤2 v` on `a` and takes 0.5 s with the filler eliminated, 2.1 s with
    // it kept). Fillers of TBox at-most clauses (`FunctionalObjectProperty`,
    // `≤n r` on a class) stay eliminable: on ORE 9800 one `⊤` filler sits in
    // 33 functional-role clauses and keeping it took the CB arm from 2.3 s
    // to 30 s.
    let data_roles = data_roles(&input.clauses);
    let asserted_filler = |clause: &JClause, concept: &str| {
        clause.head.iter().any(|head| matches!(head, JAtom::Eq { left, right }
            if clause.body.iter().any(|atom| {
                matches!(atom, JAtom::Concept { concept: c, term } if c == concept && (term == left || term == right))
            }) && !clause.body.iter().any(|atom| {
                matches!(atom, JAtom::Role { role, target, .. } if (target == left || target == right) && data_roles.contains(role.as_str()))
            })))
            && clause.body.iter().any(|atom| {
                matches!(atom, JAtom::Concept { concept: c, .. } if abox_names.contains(c) || c.starts_with("__nom__"))
            })
    };
    for clause in &input.clauses {
        universal.retain(|concept| !asserted_filler(clause, concept));
    }
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
    /// Keep one of a set of mutually guarding candidates instead of all.
    maximal: bool,
    /// Keep the sort of a definer that guards a data role in a body
    /// (`Q(t) ∧ p(t, y) → …`, `p` with `p(x, y) → D(y)`) when its relativized
    /// fact is disjunctive (`→ Q(t) ∨ R(t) ∨ D(t)`). A cost restriction that
    /// only shrinks the candidate set; the CB variant sets it when the clause
    /// set equates generated value successors
    /// ([`equates_generated_values`]).
    data_guards_sorted: bool,
}

/// Whether the clause set equates data elements that the CB engine creates:
/// it has the identity clause `V(y0) ∧ V(y1) → y0 = y1` of a value marker
/// `V` (one with `V(x) → D(x)`), and some clause puts `V` on a Skolem term,
/// `… → V(f(x))` (a `DataHasValue` in a positive position). Every such
/// successor, in every context, is then equal to every other.
///
/// A released definer holds on data elements too, so the released form
/// `→ Q(x) ∨ R(x)` of a relativized fact `→ Q(x) ∨ R(x) ∨ D(x)` is a live
/// disjunction at every data element, where the sorted form was true through
/// `D`. On the generated value successors the CB engine's equality rules copy
/// those disjunctions, and their consequences, between all of them when `Q`
/// also guards the data role (`Q(x) ∧ u(x, y) → …`): on the
/// hub-plus-data-values input of `tests/universal_role_and_top_data_range.rs`
/// the CB engine took 6 s on the released clause set and 0.3 s on the sorted
/// one, and 0.2 s on the released set without the identity clause
/// (docs/NOMINALS-CB.md, "Released disjunctive facts on generated values").
/// Released disjunctions on definers that do not read a data role stay cheap
/// there and are what the nominal seeds need (m2047: 0.4 s released, no
/// answer in 60 s with every disjunctive release withheld). Equations that
/// only an at-most restriction or a functional data property forces
/// (successors of one element) do not count.
/// Roles `p` with a range sort clause `p(x, y) → D(y)`: the data properties.
fn data_roles(clauses: &[JClause]) -> HashSet<&str> {
    clauses
        .iter()
        .filter_map(|clause| {
            let ([JAtom::Role { role, source, target }], [JAtom::Concept { concept, term }]) =
                (clause.body.as_slice(), clause.head.as_slice())
            else {
                return None;
            };
            (concept == DATA_SORT && term == target && source != target && matches!(target, JTerm::Var { .. }))
                .then_some(role.as_str())
        })
        .collect()
}

fn equates_generated_values(clauses: &[JClause]) -> bool {
    let mut data_concepts: HashSet<&str> = HashSet::new();
    for clause in clauses {
        let ([JAtom::Concept { concept: v, term: body_term }], [JAtom::Concept { concept, term }]) =
            (clause.body.as_slice(), clause.head.as_slice())
        else {
            continue;
        };
        if concept == DATA_SORT && v != DATA_SORT && body_term == term && matches!(term, JTerm::Var { .. }) {
            data_concepts.insert(v);
        }
    }
    let identities: HashSet<&str> = clauses
        .iter()
        .filter_map(|clause| {
            let (
                [JAtom::Concept { concept: a, term: ta }, JAtom::Concept { concept: b, term: tb }],
                [JAtom::Eq { left, right }],
            ) = (clause.body.as_slice(), clause.head.as_slice())
            else {
                return None;
            };
            let same_pair = (left == ta && right == tb) || (left == tb && right == ta);
            (a == b && ta != tb && same_pair && data_concepts.contains(a.as_str())).then_some(a.as_str())
        })
        .collect();
    !identities.is_empty()
        && clauses.iter().any(|clause| {
            clause.head.iter().any(|atom| {
                matches!(atom, JAtom::Concept { concept, term: JTerm::Fun { .. } } if identities.contains(concept.as_str()))
            })
        })
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
    release_with(
        clause_set,
        cardinalities,
        definers,
        rules,
        is_source,
        Options { maximal: false, data_guards_sorted: false },
    )
}

fn release_with(
    clause_set: &mut Vec<JClause>,
    cardinalities: &[CardMeta],
    definers: &[DefinerMeta],
    rules: &[JRule],
    is_source: impl Fn(&str) -> bool,
    options: Options,
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
    if options.data_guards_sorted {
        let data_roles = data_roles(clauses);
        let mut disjunctive: HashSet<&str> = HashSet::new();
        let mut data_guards: HashSet<&str> = HashSet::new();
        for clause in clauses {
            if clause.head.len() > 2 {
                for atom in &clause.head {
                    if let JAtom::Concept { concept, term } = atom {
                        if clause.head.iter().any(|other| is_data(other, term)) {
                            disjunctive.insert(concept);
                        }
                    }
                }
            }
            for atom in &clause.body {
                let JAtom::Concept { concept, term } = atom else { continue };
                if clause.body.iter().any(|other| {
                    matches!(other, JAtom::Role { role, source, .. } if source == term && data_roles.contains(role.as_str()))
                }) {
                    data_guards.insert(concept);
                }
            }
        }
        released.retain(|concept| !(disjunctive.contains(concept) && data_guards.contains(concept)));
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
                if !is_cb_definer(concept) || is_source(concept) {
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

/// The nominal CB input certificate checked by `lean/NominalCBInputCheck.lean`
/// (`WireNominalCBInput`, theorems `check_sound`, `check_consistent`,
/// `check_unsat` and `check_entails` in
/// `lean/ContextCalculus/UniversalDefinerElimination.lean`): the frontend's
/// clause set, the released definers, the eliminated definers, the reserved
/// concepts and the clause set the CB engine reads. Lean recomputes the
/// release and the elimination from `original`, `released` and `eliminated`
/// and compares the result, so nothing else in the document is trusted.
pub fn nominal_cb_input_certificate(
    original: &[JClause],
    result: &[JClause],
    released: &[String],
    eliminated: &[String],
    reserved: &BTreeSet<String>,
) -> serde_json::Value {
    let mut ids = CertIds::default();
    let data_sort = ids.concept(DATA_SORT);
    let original = ids.clauses(original);
    let result = ids.clauses(result);
    let released: Vec<usize> = released.iter().map(|name| ids.concept(name)).collect();
    let eliminated: Vec<usize> = eliminated.iter().map(|name| ids.concept(name)).collect();
    let reserved: Vec<usize> = reserved.iter().map(|name| ids.concept(name)).collect();
    serde_json::json!({
        "version": 1,
        "data_sort": data_sort,
        "released": released,
        "eliminated": eliminated,
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
        let status = crate::lean_checkers::run_document(checker, &path).unwrap().status;
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

    /// The hub-plus-data-values shape: the complement definer `Q_4` of
    /// `¬(u value 1)` sits in `→ Q_4(x) ∨ Q_6(x) ∨ D(x)` with `Q_6 ≡ ∃u.{1}`,
    /// whose unguarded existential keeps `Q_6` sorted.
    fn excluded_middle_with_a_value() -> Vec<JClause> {
        let (x, y) = (var("x"), var("y"));
        let v = "__dt__val__1";
        let g = JTerm::Fun { function: "g".into(), arg: Box::new(x.clone()) };
        vec![
            cl(vec![], vec![c("Q_4", x.clone()), c("Q_6", x.clone()), c(D, x.clone())]),
            cl(vec![c("Q_4", x.clone()), c("Q_6", x.clone())], vec![]),
            cl(vec![c("Q_6", x.clone())], vec![r("u", x.clone(), g)]),
            cl(vec![c("Q_4", x.clone()), r("u", x.clone(), y.clone())], vec![c("Q_5", y.clone())]),
            cl(vec![c("Q_4", x.clone()), c(D, x.clone())], vec![]),
            cl(vec![c("Q_6", x.clone()), c(D, x.clone())], vec![]),
            cl(vec![r("u", x.clone(), y.clone())], vec![c(D, y.clone())]),
            cl(vec![r("u", x.clone(), y.clone()), c(D, x.clone())], vec![]),
            cl(vec![c(v, x.clone())], vec![c(D, x.clone())]),
        ]
    }

    fn value_identity() -> JClause {
        let v = "__dt__val__1";
        cl(vec![c(v, var("y0")), c(v, var("y1"))], vec![JAtom::Eq { left: var("y0"), right: var("y1") }])
    }

    /// `Q_12 ⊑ ∃u.{1}`: the value on a Skolem successor.
    fn generated_value() -> Vec<JClause> {
        let f = JTerm::Fun { function: "f".into(), arg: Box::new(var("x")) };
        vec![
            cl(vec![c("Q_12", var("x"))], vec![r("u", var("x"), f.clone())]),
            cl(vec![c("Q_12", var("x"))], vec![c("__dt__val__1", f)]),
        ]
    }

    #[test]
    fn cb_release_keeps_a_disjunctive_data_guard_sorted_on_equated_generated_values() {
        // Without an equation between generated values `Q_4` is released.
        let mut i = input(excluded_middle_with_a_value());
        assert_eq!(release_inert_object_sorts_for_cb(&mut i, |_| false).concepts, vec!["Q_4".to_string()]);
        // The literal's identity clause and a value on a Skolem term: the
        // released fact `→ Q_4(x) ∨ Q_6(x)` would be a live disjunction on
        // every generated value, and they are all equal; `Q_4` guards `u`.
        let mut clauses = excluded_middle_with_a_value();
        clauses.push(value_identity());
        clauses.extend(generated_value());
        assert!(equates_generated_values(&clauses));
        let mut i = input(clauses.clone());
        assert_eq!(release_inert_object_sorts_for_cb(&mut i, |_| false), Released::default());
        assert!(i.clauses == clauses);
        // The identity alone (values only on individuals or in bodies), the
        // generated value alone, a functional data property and an equation
        // between nominals keep the full release.
        let functional = cl(
            vec![r("u", var("x"), var("y0")), r("u", var("x"), var("y1"))],
            vec![JAtom::Eq { left: var("y0"), right: var("y1") }],
        );
        let nominal = cl(vec![c("__nom__a", var("x"))], vec![JAtom::Eq { left: var("x"), right: ind("a") }]);
        for extra in [vec![value_identity()], generated_value(), vec![functional], vec![nominal]] {
            let mut clauses = excluded_middle_with_a_value();
            clauses.extend(extra);
            assert!(!equates_generated_values(&clauses));
            let mut i = input(clauses);
            assert_eq!(release_inert_object_sorts_for_cb(&mut i, |_| false).concepts, vec!["Q_4".to_string()]);
        }
    }

    #[test]
    fn cb_release_keeps_other_releases_on_equated_generated_values() {
        // A range definer's unit fact `→ Q_1(x) ∨ D(x)` and a disjunctive
        // fact on a definer that reads no data role (`→ A(x) ∨ Q_2(x) ∨ D(x)`,
        // the complement of a source class, seed m2047) are released as
        // without the equation.
        let mut clauses = range_clauses();
        clauses.push(cl(vec![], vec![c("A", var("x")), c("Q_2", var("x")), c(D, var("x"))]));
        clauses.push(cl(vec![c("A", var("x")), c("Q_2", var("x"))], vec![]));
        clauses.push(cl(vec![c("Q_2", var("x")), c(D, var("x"))], vec![]));
        clauses.push(cl(vec![c("A", var("x")), c(D, var("x"))], vec![]));
        clauses.push(cl(vec![c("__dt__val__1", var("x"))], vec![c(D, var("x"))]));
        let mut plain = input(clauses.clone());
        let plain = release_inert_object_sorts_for_cb(&mut plain, |name| name == "A");
        assert_eq!(plain.concepts, vec!["Q_1".to_string(), "Q_2".to_string()]);
        clauses.push(value_identity());
        clauses.extend(generated_value());
        assert!(equates_generated_values(&clauses));
        let mut i = input(clauses);
        assert_eq!(release_inert_object_sorts_for_cb(&mut i, |name| name == "A").concepts, plain.concepts);
    }

    #[test]
    fn data_guards_sorted_release_preserves_source_answers_on_random_inputs() {
        // The DPLL oracle has no equality, so this runs the restricted pass
        // directly instead of through an identity clause.
        let mut rng = Lcg(20261101);
        let (mut released, mut fewer) = (0, 0);
        for _ in 0..2000 {
            let mut clauses = random_sorted(&mut rng);
            if rng.below(2) == 0 {
                clauses.push(cl(vec![], vec![c("Q_1", var("x")), c("Q_2", var("x")), c(D, var("x"))]));
            }
            let is_source = |name: &str| name == "A" || name == "B";
            let mut full = clauses.clone();
            let all = release_with(&mut full, &[], &[], &[], is_source, Options { maximal: true, data_guards_sorted: false });
            let mut restricted = clauses.clone();
            let report = release_with(
                &mut restricted,
                &[],
                &[],
                &[],
                is_source,
                Options { maximal: true, data_guards_sorted: true },
            );
            if !report.concepts.is_empty() {
                released += 1;
            }
            if report.concepts.len() < all.concepts.len() {
                fewer += 1;
            }
            assert_eq!(answers(&clauses), answers(&restricted), "restricted release changed an answer: {report:?}");
        }
        eprintln!("2000 random clause sets: restricted release on {released}, fewer than the full release on {fewer}");
        assert!(released > 200, "released on {released} inputs");
        assert!(fewer > 5, "restriction applied on {fewer} inputs");
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
    fn universal_filler_of_an_asserted_at_most_is_kept() {
        let at_most = |subject: &str| {
            cl(
                vec![c("Q_1", var("y0")), c("Q_1", var("y1")), c(subject, var("x")),
                     r("s", var("x"), var("y0")), r("s", var("x"), var("y1"))],
                vec![JAtom::Eq { left: var("y0"), right: var("y1") }],
            )
        };
        let unit = cl(vec![], vec![c("Q_1", var("x"))]);
        // `ClassAssertion(≤1 s, c)` (open_r3602): `Q_3` is the assertion
        // marker of `c`, the filler stays.
        let clauses = vec![unit.clone(), at_most("Q_3")];
        let mut i = input(clauses.clone());
        i.nominal_abox = serde_json::from_value(serde_json::json!({
            "complete": true,
            "individuals": [{"individual": "c", "proxies": ["__nom__c"], "assertions": [], "assertion_markers": ["Q_3"]}]
        }))
        .unwrap();
        assert_eq!(eliminate_universal_definers(&mut i, |_| false), Eliminated::default());
        assert!(i.clauses == clauses);
        // The same clause under a nominal proxy keeps it too.
        let mut i = input(vec![unit.clone(), at_most("__nom__c")]);
        assert_eq!(eliminate_universal_definers(&mut i, |_| false), Eliminated::default());
        // A TBox at-most (`A ⊑ ≤1 s`, ORE 9800's functional roles) does not.
        let mut i = input(vec![unit.clone(), at_most("A")]);
        assert_eq!(eliminate_universal_definers(&mut i, |_| false).concepts, vec!["Q_1".to_string()]);
        // Nor an at-most on a data role (`s(x, y) → D(y)`; seed m2047).
        let mut i = input(vec![unit, at_most("__nom__c"), cl(vec![r("s", var("x"), var("y"))], vec![c(D, var("y"))])]);
        assert_eq!(eliminate_universal_definers(&mut i, |_| false).concepts, vec!["Q_1".to_string()]);
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

    #[test]
    fn builtin_vocabulary_is_never_eliminated() {
        // `owl:Thing` is internal (`cb_to_ht::is_internal`) but not a
        // frontend definer, so `reserved_concepts_for_cb` reserves it and the
        // Lean check of the nominal CB input would reject its elimination.
        let clauses = vec![
            cl(vec![], vec![c("owl:Thing", var("x"))]),
            cl(vec![c("owl:Thing", var("x")), c("A", var("x"))], vec![c("B", var("x"))]),
            cl(vec![], vec![c("Q_1", var("x"))]),
            cl(vec![c("Q_1", var("x")), c("B", var("x"))], vec![c("A", var("x"))]),
        ];
        let mut i = input(clauses.clone());
        let source = |name: &str| name == "A" || name == "B";
        let reserved = reserved_concepts_for_cb(&i, source);
        assert!(reserved.contains("owl:Thing") && !reserved.contains("Q_1"));
        assert_eq!(eliminate_universal_definers(&mut i, source).concepts, vec!["Q_1".to_string()]);
        assert!(i.clauses.contains(&clauses[0]) && i.clauses.contains(&clauses[1]));
    }

    /// The elimination without its gates: drop the named definers from every
    /// head (with the clause) and body.
    fn eliminate_unchecked(clauses: &[JClause], names: &[&str]) -> Vec<JClause> {
        let named = |atom: &JAtom| matches!(atom, JAtom::Concept { concept, .. } if names.contains(&concept.as_str()));
        clauses
            .iter()
            .filter(|clause| !clause.head.iter().any(named))
            .map(|clause| cl(clause.body.iter().filter(|atom| !named(atom)).cloned().collect(), clause.head.clone()))
            .collect()
    }

    /// The Lean checker of the nominal CB input certificate, from
    /// `KM_RULES_TEST_NOMINAL_CB_INPUT_LEAN_CHECKER` (the rules certification
    /// gate sets it); `None` skips, unless `KM_REQUIRE_LEAN_CHECKERS` is set.
    fn nominal_cb_input_checker() -> Option<std::path::PathBuf> {
        match std::env::var_os("KM_RULES_TEST_NOMINAL_CB_INPUT_LEAN_CHECKER") {
            Some(path) => Some(path.into()),
            None => {
                assert!(
                    std::env::var_os("KM_REQUIRE_LEAN_CHECKERS").is_none(),
                    "KM_RULES_TEST_NOMINAL_CB_INPUT_LEAN_CHECKER is required"
                );
                eprintln!("skipping: KM_RULES_TEST_NOMINAL_CB_INPUT_LEAN_CHECKER is unset");
                None
            }
        }
    }

    #[test]
    fn eliminated_definers_are_unreserved_and_universal() {
        // The two hypotheses of `elimConditions` (Lean): every eliminated
        // definer is outside `reserved_concepts_for_cb` and has a unit fact
        // `→ Q(x)` in the clause set the elimination reads.
        let mut rng = Lcg(20261031);
        let source = |name: &str| name == "A" || name == "B";
        let mut eliminated = 0;
        for _ in 0..2000 {
            let mut clauses = random_sorted(&mut rng);
            if rng.below(2) == 0 {
                clauses.push(cl(vec![c("Q_1", var("x")), c("Q_2", var("x"))], vec![]));
            }
            let mut i = input(clauses);
            let reserved = reserved_concepts_for_cb(&i, source);
            release_inert_object_sorts_for_cb(&mut i, source);
            let released = i.clauses.clone();
            let gone = eliminate_universal_definers(&mut i, source);
            for concept in &gone.concepts {
                assert!(!reserved.contains(concept), "{concept} is reserved");
                assert!(released.iter().any(|clause| clause.body.is_empty()
                    && matches!(clause.head.as_slice(), [JAtom::Concept { concept: q, term: JTerm::Var { .. } }] if q == concept)));
            }
            let names: Vec<&str> = gone.concepts.iter().map(String::as_str).collect();
            if !names.is_empty() {
                assert!(i.clauses == eliminate_unchecked(&released, &names));
                eliminated += 1;
            }
        }
        assert!(eliminated > 200, "eliminated on {eliminated} inputs");
    }

    #[test]
    fn lean_checker_accepts_the_nominal_cb_input_and_rejects_unchecked_ones() {
        let Some(checker) = nominal_cb_input_checker() else { return };
        let mut rng = Lcg(20261031);
        let source = |name: &str| name == "A" || name == "B";
        let (mut accepted, mut rejected) = (0, 0);
        for round in 0..2000 {
            let mut clauses = random_sorted(&mut rng);
            if rng.below(2) == 0 {
                clauses.push(cl(vec![c("Q_1", var("x")), c("Q_2", var("x"))], vec![]));
            }
            let mut i = input(clauses.clone());
            let reserved = reserved_concepts_for_cb(&i, source);
            let released = release_inert_object_sorts_for_cb(&mut i, source);
            let after_release = i.clauses.clone();
            let gone = eliminate_universal_definers(&mut i, source);
            if !released.concepts.is_empty() || !gone.concepts.is_empty() {
                let document =
                    nominal_cb_input_certificate(&clauses, &i.clauses, &released.concepts, &gone.concepts, &reserved);
                assert!(lean_accepts(&checker, &document, &format!("cb-{round}-ok")), "round {round}: rejected");
                accepted += 1;
            }
            // Eliminating `Q_2` whether or not it holds everywhere: whenever
            // that changes an answer, `check_entails` and its siblings forbid
            // acceptance.
            let unchecked = eliminate_unchecked(&after_release, &["Q_2"]);
            if answers(&clauses) != answers(&unchecked) {
                let document = nominal_cb_input_certificate(
                    &clauses,
                    &unchecked,
                    &released.concepts,
                    &["Q_2".to_string()],
                    &reserved,
                );
                assert!(!lean_accepts(&checker, &document, &format!("cb-{round}-bad")), "round {round}: accepted");
                rejected += 1;
            }
        }
        eprintln!("Lean accepted {accepted} nominal CB inputs and rejected {rejected} answer-changing eliminations");
        assert!(accepted > 300 && rejected > 30, "accepted {accepted}, rejected {rejected}");
    }

    #[test]
    fn lean_checker_rejects_a_tampered_nominal_cb_input() {
        let Some(checker) = nominal_cb_input_checker() else { return };
        let clauses = vec![
            cl(vec![], vec![c("Q_1", var("x"))]),
            cl(vec![c("Q_1", var("y")), r("p", var("x"), var("y"))], vec![c("Q_2", var("x"))]),
            cl(vec![c("A", var("x"))], vec![c("Q_1", var("x")), c("B", var("x"))]),
            cl(vec![c("Q_1", var("x")), c("Q_2", var("x"))], vec![c("B", var("x"))]),
        ];
        let source = |name: &str| name == "A" || name == "B";
        let mut i = input(clauses.clone());
        let reserved = reserved_concepts_for_cb(&i, source);
        let gone = eliminate_universal_definers(&mut i, source);
        assert_eq!(gone.concepts, vec!["Q_1".to_string()]);
        let document = nominal_cb_input_certificate(&clauses, &i.clauses, &[], &gone.concepts, &reserved);
        assert!(lean_accepts(&checker, &document, "cb-ok"));
        // The CB input must be exactly the elimination of the original.
        let mut dropped = i.clauses.clone();
        dropped.pop();
        let document = nominal_cb_input_certificate(&clauses, &dropped, &[], &gone.concepts, &reserved);
        assert!(!lean_accepts(&checker, &document, "cb-dropped"));
        // A reserved name is never eliminated.
        let mut with_q1 = reserved.clone();
        with_q1.insert("Q_1".into());
        let document = nominal_cb_input_certificate(&clauses, &i.clauses, &[], &gone.concepts, &with_q1);
        assert!(!lean_accepts(&checker, &document, "cb-reserved"));
        // A definer without a unit fact is never eliminated.
        let both = vec!["Q_1".to_string(), "Q_2".to_string()];
        let unchecked = eliminate_unchecked(&clauses, &["Q_1", "Q_2"]);
        let document = nominal_cb_input_certificate(&clauses, &unchecked, &[], &both, &reserved);
        assert!(!lean_accepts(&checker, &document, "cb-no-unit"));
    }
}
