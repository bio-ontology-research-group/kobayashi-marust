//! Object and data sorts for the nominal clause set.
//!
//! OWL 2 Direct Semantics interprets class expressions over the object domain
//! `Δ_I` and data ranges over the data domain `Δ_D`, with `Δ_I ∩ Δ_D = ∅`.
//! The clause set is one-sorted: a data value is an element of the same
//! domain as every object, carrying its `__dt__` concept. That is exact as
//! long as nothing forces a data value into object structure. Under nominal
//! clausification every empty-body fact `⊤ ⊑ C` (`owl:Thing ⊑ C`, which
//! should range over `Δ_I` only) is instantiated in the ground context at
//! every term, data values included, and the value's at-most-one clause
//! `v(z₁) ∧ v(z₂) → z₁ ≈ z₂` together with the excluded middle
//! `⊤ ⊑ ¬{v} ⊔ {v}` then makes every pair of ground terms (named
//! individuals, their Skolem successors, the universal-role hub) a merge
//! candidate, and the ground context explodes.
//!
//! This pass makes the two sorts explicit with one fresh marker concept
//! [`DATA_SORT`] (`D`, interpreted as `Δ_D`), linearly in the signature:
//!
//! * every data range `⊑ D`; every object-sorted concept `⊑ ¬D`;
//! * every role: domain `⊑ ¬D`; range `⊑ ¬D` for object roles and `⊑ D`
//!   for data roles;
//! * every class-level fact `⊤ ⊑ C` becomes `¬D ⊑ C`, i.e. `→ C(x) ∨ D(x)`:
//!   `owl:Thing` is `¬D`. The same applies to a clause whose body is only
//!   polymorphic or data-sorted concepts and whose head is object-sorted:
//!   the normaliser writes `⊤ ⊑ ∀p.R` of a `DataPropertyRange` as
//!   `Q_⊤(x) → Q(x)` once `⊤` has a definer, and `Q_⊤` also holds on data
//!   values (it is the `rdfs:Literal` filler), so without the `D(x)`
//!   disjunct the object-sorted `Q` would be forced on a value.
//!
//! Sorts fixed by OWL 2 Direct Semantics are never widened: source classes
//! and named individuals (`__nom__` proxies, and `→ O(a)` with `O ⊓ D ⊑ ⊥`
//! for every individual `a`) are objects; every data range, complement ranges
//! included (`¬R` is `Δ_D \ R`), is data; every source property has an
//! object domain, and a data (object) property a data (object) range. A
//! clause whose body admits a sort at a term where its head offers only
//! fixed sorts that do not admit it is relativized instead: `D(t)` joins the
//! head when the clause must not apply to data elements, and the body when
//! it must not apply to objects (the excluded middle `→ R(x) ∨ ¬R(x)` of a
//! data range becomes `D(x) → R(x) ∨ ¬R(x)`). The sort of every concept and role position is inferred from the
//! clause set itself (data ranges and data properties are data, source
//! classes and named individuals are objects, and atoms on one term share a
//! sort; a Skolem term `f(x)` and an individual denote the same element in
//! every clause), so the pass needs no provenance from the clausifier. A
//! concept used in both sorts (the `⊤` definer of an unqualified
//! cardinality) gets no sort clause and keeps its facts as they are.
//!
//! Before any clause is emitted, sort admissibility is closed under the
//! clause set: whenever the body of a clause admits a sort at a term and no
//! head atom on that term admits it, the head concepts (the definers first,
//! the seeded names only when no definer is there) are made to admit it,
//! and a role position in the same situation admits it too. A concept or
//! role position that admits both sorts gets no sort clause. The closure is
//! what guarantees that no sort clause can make a clause unsatisfiable for
//! an element the clause set allows in that sort; the `⊤`-axiom
//! relativization runs first so that `⊤ ⊑ C` keeps its exact reading
//! instead of turning `C` polymorphic.
//!
//! The exactness argument is in docs/NOMINALS-CB.md, "Object and data sorts".

use std::collections::{BTreeMap, BTreeSet};

use super::clauses::{clause, Atom, DLClause, Term};
use crate::fxhash::{FxHashMap, FxHashSet};

/// Marker concept interpreted as the data domain `Δ_D`.
pub const DATA_SORT: &str = "__data__";

/// Marker concept carried by every named individual; disjoint from
/// [`DATA_SORT`].
pub const OBJECT_SORT: &str = "__object__";

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

/// The sorts an element carrying a concept, or filling a role position, may
/// have. `Sort::Both` and `Sort::Unknown` admit both.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Admits {
    object: bool,
    data: bool,
}

impl Admits {
    const BOTH: Admits = Admits { object: true, data: true };

    fn from_sort(sort: Sort) -> Admits {
        match sort {
            Sort::Object => Admits { object: true, data: false },
            Sort::Data => Admits { object: false, data: true },
            Sort::Both | Sort::Unknown => Admits::BOTH,
        }
    }

    fn admits(self, sort: Sort) -> bool {
        match sort {
            Sort::Object => self.object,
            Sort::Data => self.data,
            Sort::Both | Sort::Unknown => true,
        }
    }

    /// Admit `sort` as well; `true` when that is new.
    fn add(&mut self, sort: Sort) -> bool {
        let before = *self;
        match sort {
            Sort::Object => self.object = true,
            Sort::Data => self.data = true,
            Sort::Both | Sort::Unknown => {}
        }
        *self != before
    }

    fn only(self) -> Option<Sort> {
        match (self.object, self.data) {
            (true, false) => Some(Sort::Object),
            (false, true) => Some(Sort::Data),
            _ => None,
        }
    }
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

/// Whether the encoding applies to this clause set, once the caller has
/// established nominal clausification and that the source has nominals or
/// individuals: the clause set carries a data value, a data range, or an
/// atom of a source data property. A data successor is an element of the
/// one-sorted domain whether or not a literal names it, and the `⊤` definer
/// of an unqualified data cardinality (`≥2 u` reifies `rdfs:Literal` as the
/// same definer as `owl:Thing`) carries every `⊤ ⊑ C` fact onto it; with
/// `⊤ ⊑ {a}` both `u`-successors would be merged with `a` and with each
/// other (docs/NOMINALS-CB.md, "Data successors without data values").
pub fn applies(tbox: &[DLClause], data_roles: &BTreeSet<String>) -> bool {
    has_data_values(tbox)
        || tbox.iter().any(|c| {
            c.body.iter().chain(c.head.iter()).any(|atom| match atom {
                Atom::Concept(name, _) => is_data_range(name),
                Atom::Role(name, ..) => data_roles.contains(name),
                Atom::Eq(..) => false,
            })
        })
}

/// Whether the clause set carries a data value (every `__dt__val__` concept
/// comes with its at-most-one clause).
pub fn has_data_values(tbox: &[DLClause]) -> bool {
    tbox.iter().any(|c| {
        c.body.iter().chain(c.head.iter()).any(|atom| {
            matches!(atom, Atom::Concept(name, _) if name.starts_with("__dt__val__"))
        })
    })
}

/// Interned view of the clause set: concept, role and term ids, and every
/// clause as id atoms. Terms are interned by value, so two equal terms of one
/// clause share an id exactly as they shared a key of the former
/// `BTreeMap<&Term, _>`; variables are still read per clause.
struct Index<'a> {
    concept_names: Vec<&'a str>,
    concept_ids: FxHashMap<&'a str, usize>,
    role_names: Vec<&'a str>,
    role_ids: FxHashMap<&'a str, usize>,
    terms: Vec<&'a Term>,
    term_ids: FxHashMap<&'a Term, usize>,
    is_var: Vec<bool>,
    clauses: Vec<IClause>,
}

#[derive(Clone, Copy)]
enum IAtom {
    Concept(usize, usize),
    Role(usize, usize, usize),
    Eq(usize, usize),
}

#[derive(Default)]
struct IClause {
    body: Vec<IAtom>,
    head: Vec<IAtom>,
}

impl IClause {
    fn atoms(&self) -> impl Iterator<Item = &IAtom> {
        self.body.iter().chain(self.head.iter())
    }
}

impl<'a> Index<'a> {
    fn new(tbox: &'a [DLClause]) -> Index<'a> {
        let mut index = Index {
            concept_names: Vec::new(),
            concept_ids: FxHashMap::default(),
            role_names: Vec::new(),
            role_ids: FxHashMap::default(),
            terms: Vec::new(),
            term_ids: FxHashMap::default(),
            is_var: Vec::new(),
            clauses: Vec::with_capacity(tbox.len()),
        };
        for c in tbox {
            let compiled = index.compile(c);
            index.clauses.push(compiled);
        }
        index
    }

    fn concept(&mut self, name: &'a str) -> usize {
        if let Some(&id) = self.concept_ids.get(name) {
            return id;
        }
        let id = self.concept_names.len();
        self.concept_names.push(name);
        self.concept_ids.insert(name, id);
        id
    }

    fn role(&mut self, name: &'a str) -> usize {
        if let Some(&id) = self.role_ids.get(name) {
            return id;
        }
        let id = self.role_names.len();
        self.role_names.push(name);
        self.role_ids.insert(name, id);
        id
    }

    fn term(&mut self, term: &'a Term) -> usize {
        if let Some(&id) = self.term_ids.get(term) {
            return id;
        }
        let id = self.terms.len();
        self.terms.push(term);
        self.term_ids.insert(term, id);
        self.is_var.push(matches!(term, Term::Var(_)));
        id
    }

    fn atom(&mut self, atom: &'a Atom) -> IAtom {
        match atom {
            Atom::Concept(name, t) => IAtom::Concept(self.concept(name), self.term(t)),
            Atom::Role(name, s, t) => IAtom::Role(self.role(name), self.term(s), self.term(t)),
            Atom::Eq(s, t) => IAtom::Eq(self.term(s), self.term(t)),
        }
    }

    fn compile(&mut self, c: &'a DLClause) -> IClause {
        IClause {
            body: c.body.iter().map(|a| self.atom(a)).collect(),
            head: c.head.iter().map(|a| self.atom(a)).collect(),
        }
    }
}

/// Inferred sorts, indexed like [`Index`]. Phase 1 and 2 of the inference
/// visit the clauses in their order and update in place, as before.
struct Sorts {
    /// Concept sort and whether it is a fixed seed.
    concepts: Vec<(Sort, bool)>,
    /// Role (domain, range) sorts.
    roles: Vec<(Sort, Sort)>,
    /// Structural sort of every Skolem term and individual (phase 1);
    /// `Unknown` for variables and for terms without evidence.
    terms: Vec<Sort>,
}

/// Term sorts of the clause being scanned: variables per clause, Skolem
/// terms and individuals across the clause set.
struct TermSorts<'s> {
    local: &'s mut Vec<Sort>,
    touched: &'s mut Vec<usize>,
    global: &'s mut Vec<Sort>,
    is_var: &'s [bool],
}

impl<'s> TermSorts<'s> {
    fn get(&self, term: usize) -> Sort {
        if self.is_var[term] { self.local[term] } else { self.global[term] }
    }

    /// Record definite evidence for `term`; indefinite evidence is ignored.
    fn join(&mut self, term: usize, sort: Sort) {
        if sort.definite() {
            if self.is_var[term] {
                if self.local[term] == Sort::Unknown {
                    self.touched.push(term);
                }
                self.local[term] = self.local[term].join(sort);
            } else {
                self.global[term] = self.global[term].join(sort);
            }
        }
    }

    fn clear(&mut self) {
        for &term in self.touched.iter() {
            self.local[term] = Sort::Unknown;
        }
        self.touched.clear();
    }
}

impl Sorts {
    fn infer(index: &Index, data_roles: &BTreeSet<String>) -> Sorts {
        let concepts: Vec<(Sort, bool)> = index
            .concept_names
            .iter()
            .map(|name| {
                if is_data_range(name) {
                    (Sort::Data, true)
                } else if is_source_concept(name) || name.starts_with("__nom__") {
                    (Sort::Object, true)
                } else {
                    (Sort::Unknown, false)
                }
            })
            .collect();
        let roles: Vec<(Sort, Sort)> = index
            .role_names
            .iter()
            .map(|name| {
                // Every property has an object domain; a data property has a
                // data range and every other source property an object
                // range. Internal roles learn their range from their fillers.
                let range = if data_roles.contains(*name) {
                    Sort::Data
                } else if is_source_role(name) {
                    Sort::Object
                } else {
                    Sort::Unknown
                };
                (Sort::Object, range)
            })
            .collect();
        let mut sorts = Sorts { concepts, roles, terms: Vec::new() };
        // Phase 1, structural evidence: a term's sort comes from the seeded
        // concepts on it and from the role positions it fills. A variable is
        // local to its clause; a Skolem term `f(x)` (one function per
        // definer) and an individual denote one element across the whole
        // clause set, so their evidence is kept globally. Definers and role
        // positions learn from that evidence; a definer that meets both sorts
        // is polymorphic (`Both`), and only definite sorts ever propagate.
        let term_count = index.terms.len();
        let mut global = vec![Sort::Unknown; term_count];
        let mut local = vec![Sort::Unknown; term_count];
        let mut touched: Vec<usize> = Vec::new();
        loop {
            let mut changed = false;
            for c in &index.clauses {
                let mut terms = TermSorts {
                    local: &mut local,
                    touched: &mut touched,
                    global: &mut global,
                    is_var: &index.is_var,
                };
                terms.clear();
                for atom in c.atoms() {
                    match *atom {
                        IAtom::Concept(name, t) => {
                            let (sort, fixed) = sorts.concepts[name];
                            if fixed {
                                terms.join(t, sort);
                            }
                        }
                        IAtom::Role(name, s, t) => {
                            let (domain, range) = sorts.roles[name];
                            terms.join(s, domain);
                            terms.join(t, range);
                        }
                        IAtom::Eq(..) => {}
                    }
                }
                for atom in c.atoms() {
                    if let IAtom::Eq(s, t) = *atom {
                        let joined = terms.get(s).join(terms.get(t));
                        terms.join(s, joined);
                        terms.join(t, joined);
                    }
                }
                for atom in c.atoms() {
                    match *atom {
                        IAtom::Concept(name, t) => {
                            let term_sort = terms.get(t);
                            if !term_sort.definite() {
                                continue;
                            }
                            let entry = &mut sorts.concepts[name];
                            if entry.1 {
                                continue;
                            }
                            let joined = entry.0.join(term_sort);
                            if joined != entry.0 {
                                entry.0 = joined;
                                changed = true;
                            }
                        }
                        IAtom::Role(name, s, t) => {
                            let (domain_sort, range_sort) = (terms.get(s), terms.get(t));
                            let entry = &mut sorts.roles[name];
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
                        IAtom::Eq(..) => {}
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
            for c in &index.clauses {
                for atom in c.atoms() {
                    if let IAtom::Concept(name, t) = *atom {
                        let structural =
                            if index.is_var[t] { Sort::Unknown } else { global[t] };
                        let mut sort = structural;
                        for other in c.atoms() {
                            if let IAtom::Concept(other_name, other_t) = *other {
                                if other_t == t {
                                    sort = sort.join(sorts.concepts[other_name].0);
                                }
                            }
                        }
                        if !sort.definite() {
                            continue;
                        }
                        let entry = &mut sorts.concepts[name];
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
        for (t, &is_var) in index.is_var.iter().enumerate() {
            if is_var {
                global[t] = Sort::Unknown;
            }
        }
        sorts.terms = global;
        sorts
    }
}

/// Apply the encoding in place. Returns the number of clauses added plus
/// the number of facts relativized. `data_roles` holds the clause-set names
/// of the source's data properties.
pub fn encode(tbox: &mut Vec<DLClause>, data_roles: &BTreeSet<String>) -> usize {
    encode_with_classes(tbox, data_roles, &[], &BTreeMap::new())
}

/// [`encode`], also placing every declared source class in the object sort,
/// including classes no clause mentions: an unconstrained class is still a
/// set of objects, and every relativized `⊤` fact must apply to it.
///
/// The passes and their visiting order are those of the map-keyed
/// implementation they replace (kept as `sorts_reference.rs` for the
/// differential tests); only lookups go through interned ids.
pub fn encode_with_classes(
    tbox: &mut Vec<DLClause>,
    data_roles: &BTreeSet<String>,
    declared: &[String],
    proxies: &BTreeMap<String, String>,
) -> usize {
    // Analysis on the input clause set; edits are collected and applied at
    // the end, so the clause set is borrowed for the whole analysis.
    let (relativized, head_d, body_d, mut added, count, object_only, known_proxies) = {
        let tbox_ref: &[DLClause] = tbox;
        let mut index = Index::new(tbox_ref);
        let sorts = Sorts::infer(&index, data_roles);
        let data_sort = index.concept(DATA_SORT);
        let concept_sort = |id: usize| -> Sort {
            sorts.concepts.get(id).map_or(Sort::Unknown, |entry| entry.0)
        };
        // Class-level facts: `⊤ ⊑ C` becomes `¬D ⊑ C`. A clause is class-level
        // when it mentions exactly one variable, its body is empty or consists
        // of polymorphic or data-sorted concept atoms only (nothing that pins
        // the element to the object domain), and every concept in its head is
        // object-sorted. Data-range-level, polymorphic and unresolved heads are
        // left as they are (see the module documentation), and so are ground
        // facts, whose individuals carry their own sort.
        let mut count = 0usize;
        // (clause index, variable) of every relativized fact.
        let mut relativized_vars: Vec<(usize, &Term)> = Vec::new();
        for (ci, c) in index.clauses.iter().enumerate() {
            let mut vars: Vec<&Term> = Vec::new();
            fn note<'t>(t: &'t Term, vars: &mut Vec<&'t Term>) {
                if let Some(v) = term_var(t) {
                    if !vars.contains(&v) {
                        vars.push(v);
                    }
                }
            }
            let mut object_level = !c.head.is_empty();
            for atom in &c.body {
                match *atom {
                    IAtom::Concept(name, t) => {
                        note(index.terms[t], &mut vars);
                        object_level &= matches!(concept_sort(name), Sort::Both | Sort::Data);
                    }
                    IAtom::Role(..) | IAtom::Eq(..) => object_level = false,
                }
            }
            for atom in &c.head {
                match *atom {
                    IAtom::Concept(name, t) => {
                        note(index.terms[t], &mut vars);
                        object_level &= concept_sort(name) == Sort::Object;
                    }
                    IAtom::Role(_, s, t) | IAtom::Eq(s, t) => {
                        note(index.terms[s], &mut vars);
                        note(index.terms[t], &mut vars);
                    }
                }
            }
            if !object_level || vars.len() != 1 {
                continue;
            }
            relativized_vars.push((ci, vars[0]));
            count += 1;
        }
        let relativized: Vec<(usize, usize)> =
            relativized_vars.iter().map(|&(ci, v)| (ci, index.term(v))).collect();
        // A relativized clause gains `D(v)` in its head; the admissibility
        // closure reads the clause in that form.
        for &(ci, v) in &relativized {
            index.clauses[ci].head.push(IAtom::Concept(data_sort, v));
        }
        // Admissibility, closed under the clause set (see the module
        // documentation). Sorts fixed by OWL 2 Direct Semantics are never
        // widened: source classes and `__nom__` proxies are objects, data ranges
        // (complement ranges included: `¬R` is `Δ_D \ R`) are data, every source property has an
        // object domain, a data property a data range and an object property an
        // object range. Only internal definers and internal roles widen. Where a
        // clause would force a fixed sort to admit the other one, the clause is
        // relativized instead (`head_d`: `D(t)` joins the head, restricting the
        // clause to object elements at `t`; `body_d`: `D(t)` joins the body,
        // restricting it to data elements).
        let fixed_concept = |id: usize| id == data_sort || sorts.concepts[id].1;
        let mut concept_adm: Vec<Admits> = (0..index.concept_names.len())
            .map(|id| {
                if id == data_sort {
                    Admits::from_sort(Sort::Data)
                } else {
                    Admits::from_sort(sorts.concepts[id].0)
                }
            })
            .collect();
        let fixed_role = |name: &str| is_source_role(name);
        let mut role_adm: Vec<(Admits, Admits)> = index
            .role_names
            .iter()
            .zip(sorts.roles.iter())
            .map(|(name, (domain, range))| {
                let (domain, range) = if fixed_role(name) {
                    let range = if data_roles.contains(*name) { Sort::Data } else { Sort::Object };
                    (Sort::Object, range)
                } else {
                    (*domain, *range)
                };
                (Admits::from_sort(domain), Admits::from_sort(range))
            })
            .collect();
        let fixed_role_id: Vec<bool> = index.role_names.iter().map(|name| fixed_role(name)).collect();
        // Per clause: its distinct terms in `Term` order, and which of them
        // the body mentions (the former `BTreeSet<&Term>` iteration).
        let term_lists: Vec<(Vec<usize>, Vec<usize>)> = index
            .clauses
            .iter()
            .map(|c| {
                let mut body_terms: Vec<usize> = Vec::new();
                for atom in &c.body {
                    match *atom {
                        IAtom::Concept(_, t) => body_terms.push(t),
                        IAtom::Role(_, s, t) | IAtom::Eq(s, t) => {
                            body_terms.push(s);
                            body_terms.push(t);
                        }
                    }
                }
                let mut terms = body_terms.clone();
                for atom in &c.head {
                    match *atom {
                        IAtom::Concept(_, t) => terms.push(t),
                        IAtom::Role(_, s, t) | IAtom::Eq(s, t) => {
                            terms.push(s);
                            terms.push(t);
                        }
                    }
                }
                body_terms.sort_unstable();
                body_terms.dedup();
                terms.sort_unstable_by(|&a, &b| index.terms[a].cmp(index.terms[b]));
                terms.dedup();
                (terms, body_terms)
            })
            .collect();
        let mut head_d: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        let mut body_d: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        let mut definers: Vec<usize> = Vec::new();
        let mut positions: Vec<(usize, bool)> = Vec::new();
        loop {
            let mut changed = false;
            for (ci, c) in index.clauses.iter().enumerate() {
                let (terms, body_terms) = &term_lists[ci];
                for &t in terms {
                    let is_var = index.is_var[t];
                    let structural = if is_var { Sort::Unknown } else { sorts.terms[t] };
                    // A Skolem term only the head mentions is created by the
                    // clause; its sort is whatever its structural evidence says.
                    if body_terms.binary_search(&t).is_err() && !is_var && !structural.definite() {
                        continue;
                    }
                    for sort in [Sort::Object, Sort::Data] {
                        // An individual is an object, a Skolem term has its
                        // structural sort.
                        if matches!(index.terms[t], Term::Ind(_)) && sort == Sort::Data {
                            continue;
                        }
                        if structural.definite() && structural != sort {
                            continue;
                        }
                        if sort == Sort::Object && body_d.get(&ci).is_some_and(|ts| ts.contains(&t)) {
                            continue;
                        }
                        if sort == Sort::Data && head_d.get(&ci).is_some_and(|ts| ts.contains(&t)) {
                            continue;
                        }
                        let body_admits = c.body.iter().all(|atom| match *atom {
                            IAtom::Concept(name, u) if u == t => concept_adm[name].admits(sort),
                            IAtom::Role(name, s, u) => {
                                (s != t || role_adm[name].0.admits(sort))
                                    && (u != t || role_adm[name].1.admits(sort))
                            }
                            _ => true,
                        });
                        if !body_admits {
                            continue;
                        }
                        let mut on_term = false;
                        let mut satisfied = false;
                        definers.clear();
                        positions.clear();
                        for atom in &c.head {
                            match *atom {
                                IAtom::Concept(name, u) if u == t => {
                                    on_term = true;
                                    satisfied |= concept_adm[name].admits(sort);
                                    if !fixed_concept(name) {
                                        definers.push(name);
                                    }
                                }
                                IAtom::Role(name, s, u) => {
                                    if s == t {
                                        on_term = true;
                                        satisfied |= role_adm[name].0.admits(sort);
                                        if !fixed_role_id[name] {
                                            positions.push((name, false));
                                        }
                                    }
                                    if u == t {
                                        on_term = true;
                                        satisfied |= role_adm[name].1.admits(sort);
                                        if !fixed_role_id[name] {
                                            positions.push((name, true));
                                        }
                                    }
                                }
                                IAtom::Eq(s, u) if s == t || u == t => {
                                    on_term = true;
                                    satisfied = true;
                                }
                                _ => {}
                            }
                        }
                        if !on_term || satisfied {
                            continue;
                        }
                        if !definers.is_empty() {
                            for &name in definers.iter() {
                                changed |= concept_adm[name].add(sort);
                            }
                        } else if !positions.is_empty() {
                            for &(name, range) in positions.iter() {
                                let entry = &mut role_adm[name];
                                changed |= if range { entry.1.add(sort) } else { entry.0.add(sort) };
                            }
                        } else {
                            // Only fixed sorts on `t`: relativize the clause.
                            let set = if sort == Sort::Data { &mut head_d } else { &mut body_d };
                            let ts = set.entry(ci).or_default();
                            if !ts.contains(&t) {
                                ts.push(t);
                                changed = true;
                            }
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        let x = Term::Var("x".to_string());
        let y = Term::Var("y".to_string());
        let d = |t: &Term| Atom::Concept(DATA_SORT.to_string(), t.clone());
        let mut added: Vec<DLClause> = Vec::new();
        // Sort clauses in name order (the former `BTreeMap<String, _>`).
        let mut concept_order: Vec<usize> = (0..index.concept_names.len()).collect();
        concept_order.sort_unstable_by(|&a, &b| index.concept_names[a].cmp(index.concept_names[b]));
        for &id in &concept_order {
            if id == data_sort {
                continue;
            }
            let atom = Atom::Concept(index.concept_names[id].to_string(), x.clone());
            match concept_adm[id].only() {
                Some(Sort::Data) => added.push(clause([atom], [d(&x)])),
                Some(Sort::Object) => added.push(clause([atom, d(&x)], [])),
                _ => {}
            }
        }
        let mut role_order: Vec<usize> = (0..index.role_names.len()).collect();
        role_order.sort_unstable_by(|&a, &b| index.role_names[a].cmp(index.role_names[b]));
        for &id in &role_order {
            let (domain, range) = role_adm[id];
            let atom = Atom::Role(index.role_names[id].to_string(), x.clone(), y.clone());
            match domain.only() {
                Some(Sort::Object) => added.push(clause([atom.clone(), d(&x)], [])),
                Some(Sort::Data) => added.push(clause([atom.clone()], [d(&x)])),
                _ => {}
            }
            match range.only() {
                Some(Sort::Object) => added.push(clause([atom.clone(), d(&y)], [])),
                Some(Sort::Data) => added.push(clause([atom.clone()], [d(&y)])),
                _ => {}
            }
        }
        for name in declared {
            if is_source_concept(name) && !index.concept_ids.contains_key(name.as_str()) {
                added.push(clause([Atom::Concept(name.clone(), x.clone()), d(&x)], []));
            }
        }
        // The individual pass below reads the edited clause set; keep what it
        // needs from the analysis: the object-only concepts among ground unit
        // heads, and which proxies the clause set mentions.
        let mut object_only: FxHashSet<String> = FxHashSet::default();
        for c in tbox_ref {
            if let [Atom::Concept(name, Term::Ind(_))] = c.head.as_slice() {
                if let Some(&id) = index.concept_ids.get(name.as_str()) {
                    if concept_adm[id].only() == Some(Sort::Object) {
                        object_only.insert(name.clone());
                    }
                }
            }
        }
        let known_proxies: FxHashSet<String> = proxies
            .values()
            .filter(|proxy| index.concept_ids.contains_key(proxy.as_str()))
            .cloned()
            .collect();
        // Owned edits, so the borrow of the clause set ends here.
        let to_terms = |set: BTreeMap<usize, Vec<usize>>| -> Vec<(usize, BTreeSet<Term>)> {
            set.into_iter()
                .map(|(ci, ts)| (ci, ts.into_iter().map(|t| index.terms[t].clone()).collect()))
                .collect()
        };
        let relativized: Vec<(usize, Term)> =
            relativized.into_iter().map(|(ci, v)| (ci, index.terms[v].clone())).collect();
        (relativized, to_terms(head_d), to_terms(body_d), added, count, object_only, known_proxies)
    };
    let mut count = count;
    let d = |t: &Term| Atom::Concept(DATA_SORT.to_string(), t.clone());
    for (ci, v) in &relativized {
        let c = &mut tbox[*ci];
        let body = std::mem::take(&mut c.body);
        let mut head = std::mem::take(&mut c.head);
        head.push(d(v));
        *c = clause(body, head);
    }
    for (ci, ts) in &head_d {
        let c = &mut tbox[*ci];
        let body = std::mem::take(&mut c.body);
        let mut head = std::mem::take(&mut c.head);
        head.extend(ts.iter().map(|t| d(t)));
        *c = clause(body, head);
        count += 1;
    }
    for (ci, ts) in &body_d {
        let c = &mut tbox[*ci];
        let mut body = std::mem::take(&mut c.body);
        let head = std::mem::take(&mut c.head);
        body.extend(ts.iter().map(|t| d(t)));
        *c = clause(body, head);
        count += 1;
    }
    let x = Term::Var("x".to_string());
    // Every named individual is an object. Most are already pinned by a
    // ground atom whose concept is object-only at the fixpoint or by a
    // source-property assertion (whose domain and range are fixed); the
    // rest get the ground fact `→ O(a)` over the fresh object marker `O`
    // ([`OBJECT_SORT`]) with `O ⊓ D ⊑ ⊥`. Pinned individuals get no extra
    // fact, so the typed native ABox views see no unrepresented ground
    // clause where none is needed. The ground `D(a) → ⊥` is avoided: the
    // nominal CB engine mishandles an empty-head clause whose only body
    // atom is ground.
    let mut individuals: BTreeSet<&str> = BTreeSet::new();
    let mut pinned: BTreeSet<&str> = BTreeSet::new();
    fn collect<'t>(t: &'t Term, out: &mut BTreeSet<&'t str>) {
        match t {
            Term::Ind(name) => {
                out.insert(name);
            }
            Term::Fun(_, inner) => collect(inner, out),
            Term::Var(_) | Term::Aux(..) => {}
        }
    }
    let fixed_role = |name: &str| is_source_role(name);
    for c in tbox.iter() {
        for atom in c.body.iter().chain(c.head.iter()) {
            match atom {
                Atom::Concept(_, t) => collect(t, &mut individuals),
                Atom::Role(_, s, t) | Atom::Eq(s, t) => {
                    collect(s, &mut individuals);
                    collect(t, &mut individuals);
                }
            }
        }
        if !c.body.is_empty() || c.head.len() != 1 {
            continue;
        }
        match &c.head[0] {
            Atom::Concept(name, Term::Ind(a)) => {
                // `D` is data-only; every other unit head was recorded.
                if name != DATA_SORT && object_only.contains(name) {
                    pinned.insert(a);
                }
            }
            Atom::Role(name, Term::Ind(a), Term::Ind(b)) if fixed_role(name) => {
                pinned.insert(a);
                if !data_roles.contains(name) {
                    pinned.insert(b);
                }
            }
            _ => {}
        }
    }
    let object = |t: &Term| Atom::Concept(OBJECT_SORT.to_string(), t.clone());
    // An unpinned individual with a nominal proxy `p` (the typed nominal
    // ABox's singleton concept of `a`) is pinned through it: `→ p(a)` is a
    // fact every consumer already represents (the native ABox view reads it
    // as the proxy of `a`), and `p ⊓ D ⊑ ⊥` is an ordinary TBox clause.
    // Only an individual without a proxy needs the fresh marker `O`.
    let mut marker_needed = false;
    let mut proxy_clauses: BTreeSet<&str> = BTreeSet::new();
    for name in individuals.difference(&pinned) {
        let a = Term::Ind(name.to_string());
        match proxies.get(*name) {
            Some(proxy) => {
                added.push(clause(Vec::new(), [Atom::Concept(proxy.clone(), a)]));
                if !known_proxies.contains(proxy) {
                    proxy_clauses.insert(proxy);
                }
            }
            None => {
                added.push(clause(Vec::new(), [object(&a)]));
                marker_needed = true;
            }
        }
    }
    for proxy in proxy_clauses {
        added.push(clause([Atom::Concept(proxy.to_string(), x.clone()), d(&x)], []));
    }
    if marker_needed {
        added.push(clause([object(&x), d(&x)], []));
    }
    count += added.len();
    tbox.extend(added);
    count
}

/// Sorts by name, for the tests.
#[cfg(test)]
struct Inferred {
    concepts: BTreeMap<String, Sort>,
    roles: BTreeMap<String, (Sort, Sort)>,
}

#[cfg(test)]
impl Inferred {
    fn concept(&self, name: &str) -> Sort {
        self.concepts.get(name).copied().unwrap_or(Sort::Unknown)
    }
}

#[cfg(test)]
fn infer_by_name(tbox: &[DLClause], data_roles: &BTreeSet<String>) -> Inferred {
    let index = Index::new(tbox);
    let sorts = Sorts::infer(&index, data_roles);
    Inferred {
        concepts: index.concept_names.iter().zip(&sorts.concepts)
            .map(|(name, entry)| (name.to_string(), entry.0)).collect(),
        roles: index.role_names.iter().zip(&sorts.roles)
            .map(|(name, entry)| (name.to_string(), *entry)).collect(),
    }
}

#[cfg(test)]
#[path = "sorts_reference.rs"]
mod reference;

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
        let sorts = infer_by_name(&tbox, &BTreeSet::from(["u".to_string()]));
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

    /// The concept of a `DataComplementOf` range is `Δ_D \ R`: it is placed
    /// in Δ_D, and its excluded middle `→ ¬R(x) ∨ R(x)` (from `datatypes`)
    /// is restricted to data elements (`D(x)` joins the body) instead of
    /// being instantiated at every object term, where it offered every value
    /// as a merge candidate (differential seeds 1, 78, 148).
    #[test]
    fn complement_range_concepts_are_data_and_their_excluded_middle_is_guarded() {
        const NOT_INT: &str = "__dt__c__DataComplementOf(xsd:integer)";
        const INT: &str = "__dt__integer";
        let mut tbox = vec![
            clause([c("Q_0", x()), r("u", x(), y())], [c(NOT_INT, y())]),
            clause([c("A", x())], [c("Q_0", x())]),
            clause([c("Q_1", x()), c(VAL, x())], []),
            fact([c(NOT_INT, x()), c(INT, x())]),
            clause([c(NOT_INT, x()), c(INT, x())], []),
            fact([c("__nom__o", Term::Ind("o".into()))]),
        ];
        let _ = encode(&mut tbox, &BTreeSet::from(["u".to_string()]));
        let dx = c(DATA_SORT, x());
        assert!(tbox.contains(&clause([c(INT, x())], [dx.clone()])));
        assert!(tbox.contains(&clause([c(NOT_INT, x())], [dx.clone()])));
        assert!(tbox.contains(&clause([dx.clone()], [c(NOT_INT, x()), c(INT, x())])));
        assert!(!tbox.contains(&fact([c(NOT_INT, x()), c(INT, x())])));
        assert!(tbox.contains(&clause([c("A", x()), dx.clone()], [])));
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
        let sorts = infer_by_name(&tbox, &BTreeSet::from(["u".to_string()]));
        assert_eq!(sorts.concept("Q_t"), Sort::Both);
        encode(&mut tbox, &BTreeSet::from(["u".to_string()]));
        assert!(tbox.contains(&fact([c("Q_t", x())])));
        assert!(!tbox.iter().any(|cl| cl.body.contains(&c("Q_t", x()))));
    }

    /// ore_ont_14321: `DataPropertyRange(uri anyURI)` is written as
    /// `Q_⊤(x) → Q_97(x)` with `Q_⊤` the shared `⊤` definer, which also
    /// holds on the `linkURI` value; `Q_97` is object-sorted (domain of
    /// `uri`). Without the `D(x)` disjunct the value would clash with
    /// `Q_97 ⊑ ¬D`, making `URLLink ⊑ ≥1 linkURI` unsatisfiable.
    #[test]
    fn a_top_definer_implication_with_an_object_head_is_relativized() {
        let mut tbox = vec![
            fact([c("Q_t", x())]),
            clause([c("Document", x())], [c("Q_t", x())]),
            clause([c("Q_72", x())], [r("linkURI", x(), fx("f"))]),
            clause([c("Q_72", x())], [c("Q_t", fx("f"))]),
            clause([c("URLLink", x())], [c("Q_72", x())]),
            clause([c("Q_97", x()), r("uri", x(), y())], [c("__dt__anyURI", y())]),
            clause([c("Q_t", x())], [c("Q_97", x())]),
            clause([c("V", x())], [c(VAL, fx("g"))]),
        ];
        let roles = BTreeSet::from(["linkURI".to_string(), "uri".to_string()]);
        let sorts = infer_by_name(&tbox, &roles);
        assert_eq!(sorts.concept("Q_t"), Sort::Both);
        assert_eq!(sorts.concept("Q_97"), Sort::Object);
        encode(&mut tbox, &roles);
        let dx = c(DATA_SORT, x());
        assert!(tbox.contains(&clause([c("Q_t", x())], [c("Q_97", x()), dx.clone()])));
        assert!(tbox.contains(&fact([c("Q_t", x())])));
        assert!(tbox.contains(&clause([c("Document", x())], [c("Q_t", x())])));
    }

    /// The coordinator's reproducer: `Has ≡ ≥1 d` reifies `⊤` as `Q_1`
    /// (data-sorted: its only structural evidence is the `d` successor),
    /// `DataPropertyRange(e string)` is `Q_1(x) → Q_7(x)` with `Q_7`
    /// object-sorted. The implication is relativized, `Q_7 ⊑ ¬D` stays, and
    /// the closure leaves `Q_1` alone (its fact holds on both sorts).
    #[test]
    fn a_data_sorted_top_definer_implication_is_relativized_and_the_range_definer_keeps_its_sort() {
        let mut tbox = vec![
            fact([c("Q_1", x())]),
            clause([c("Q_0", x())], [r("d", x(), fx("f"))]),
            clause([c("Q_0", x())], [c("Q_1", fx("f"))]),
            clause([c("Has", x())], [c("Q_0", x())]),
            clause([c("Q_1", x())], [c("Q_7", x())]),
            clause([c("Q_7", x()), r("e", x(), y())], [c("__dt__string", y())]),
            clause([c("V", x())], [c(VAL, fx("g"))]),
        ];
        let roles = BTreeSet::from(["d".to_string(), "e".to_string()]);
        let sorts = infer_by_name(&tbox, &roles);
        assert_eq!(sorts.concept("Q_1"), Sort::Data);
        assert_eq!(sorts.concept("Q_7"), Sort::Object);
        encode(&mut tbox, &roles);
        let dx = c(DATA_SORT, x());
        assert!(tbox.contains(&clause([c("Q_1", x())], [c("Q_7", x()), dx.clone()])));
        assert!(tbox.contains(&clause([c("Q_7", x()), dx.clone()], [])));
        assert!(tbox.contains(&fact([c("Q_1", x())])));
        assert!(!tbox.iter().any(|cl| cl.body == vec![c("Q_1", x())] && cl.head == vec![dx.clone()]));
    }

    /// The closure repairs a head the inference cannot: a data-sorted
    /// definer implied by a polymorphic one through a role-guarded clause
    /// must admit both sorts and then gets no `⊑ D` clause. A complement
    /// range is a data range like any other: its excluded middle
    /// `→ R(x) ∨ ¬R(x)` is restricted to data elements (`D(x)` joins the
    /// body), which is its two-sorted reading (`¬R` is `Δ_D \ R`).
    #[test]
    fn admissibility_closure_removes_clauses_instead_of_guessing() {
        let comp = "__dt__c__DataComplementOf(xsd:string)";
        let mut tbox = vec![
            fact([c("Q_t", x())]),
            clause([c("A", x())], [r("u", x(), fx("f"))]),
            clause([c("A", x())], [c("Q_t", fx("f"))]),
            clause([c("A", x())], [r("r", x(), fx("g"))]),
            clause([c("A", x())], [c("Q_t", fx("g"))]),
            // Q_t implies Q_d, whose only structural evidence is data-sorted.
            clause([c("Q_t", x())], [c("Q_d", x())]),
            clause([c("Q_d", x()), c(VAL, x())], []),
            fact([c("__dt__string", x()), c(comp, x())]),
        ];
        let roles = BTreeSet::from(["u".to_string()]);
        let sorts = infer_by_name(&tbox, &roles);
        assert_eq!(sorts.concept("Q_t"), Sort::Both);
        assert_eq!(sorts.concept("Q_d"), Sort::Data);
        encode(&mut tbox, &roles);
        let dx = c(DATA_SORT, x());
        assert!(!tbox.contains(&clause([c("Q_d", x())], [dx.clone()])));
        assert!(!tbox.iter().any(|cl| cl.body.contains(&c("Q_d", x())) && cl.body.contains(&dx)));
        assert!(tbox.contains(&clause([c("__dt__string", x())], [dx.clone()])));
        assert!(tbox.contains(&clause([c(comp, x())], [dx.clone()])));
        assert!(tbox.contains(&clause([dx.clone()], [c("__dt__string", x()), c(comp, x())])));
        assert!(tbox.contains(&clause([c("A", x()), dx.clone()], [])));
    }

    /// An individual with no object-pinning atom is pinned through its
    /// nominal proxy when it has one (a fact the typed native ABox view
    /// represents), and through the fresh marker `O` otherwise.
    #[test]
    fn unpinned_individuals_are_pinned_by_proxy_or_marker() {
        let a = || Term::Ind("a".into());
        let b = || Term::Ind("b".into());
        let mut tbox = vec![
            fact([c("Q_t", a())]),
            fact([c("Q_t", b())]),
            clause([c("V", x())], [c(VAL, fx("g"))]),
        ];
        let proxies = BTreeMap::from([("a".to_string(), "__nom__a".to_string())]);
        encode_with_classes(&mut tbox, &BTreeSet::new(), &[], &proxies);
        let dx = c(DATA_SORT, x());
        assert!(tbox.contains(&fact([c("__nom__a", a())])));
        assert!(tbox.contains(&clause([c("__nom__a", x()), dx.clone()], [])));
        assert!(!tbox.contains(&fact([c(OBJECT_SORT, a())])));
        assert!(tbox.contains(&fact([c(OBJECT_SORT, b())])));
        assert!(tbox.contains(&clause([c(OBJECT_SORT, x()), dx.clone()], [])));
    }

    #[test]
    fn gate_needs_a_data_value_range_or_data_property() {
        let none = BTreeSet::new();
        assert!(has_data_values(&fixture()));
        assert!(applies(&fixture(), &none));
        assert!(!has_data_values(&[clause([c("A", x())], [c("__dt__integer", fx("f"))])]));
        assert!(applies(&[clause([c("A", x())], [c("__dt__integer", fx("f"))])], &none));
        // `⊤ ⊑ ≥1 u` with no literal anywhere: the `u` atom opens the gate.
        let unvalued = [clause([c("Q_1", x())], [r("u", x(), fx("f"))])];
        assert!(!applies(&unvalued, &none));
        assert!(applies(&unvalued, &BTreeSet::from(["u".to_string()])));
        // Object roles and classes alone keep the clause set unchanged.
        assert!(!applies(&[clause([c("A", x())], [r("r", x(), fx("f"))])], &BTreeSet::from(["u".to_string()])));
    }

    /// m2197: `⊤ ⊑ ≥2 u` and `⊤ ⊑ {a}` with no data value. The `⊤` definer
    /// `Q_0` is also the `rdfs:Literal` filler of the cardinality, so
    /// `Q_0(x) → __nom__a(x)` held on both `u`-successors, merged them with
    /// `a` and with each other, and clashed with their inequality. The
    /// encoding relativizes the nominal fact (and the cardinality fact) to
    /// objects, and the `u` range puts both successors in `D`.
    #[test]
    fn top_nominal_with_unvalued_data_cardinality_is_relativized() {
        let a = || Term::Ind("a".into());
        let f0 = || fx("f_Q_1_0");
        let f1 = || fx("f_Q_1_1");
        let mut tbox = vec![
            fact([c("Q_0", x())]),
            clause([c("Q_1", x())], [r("u", x(), f0())]),
            clause([c("Q_1", x())], [c("Q_0", f0())]),
            clause([c("Q_1", x())], [r("u", x(), f1())]),
            clause([c("Q_1", x())], [c("Q_0", f1())]),
            clause([c("Q_1", x()), Atom::Eq(f0(), f1())], []),
            clause([c("Q_0", x())], [c("Q_1", x())]),
            clause([c("Q_0", x())], [c("__nom__a", x())]),
            fact([c("__nom__a", a())]),
            clause([c("__nom__a", x())], [Atom::Eq(x(), a())]),
        ];
        let roles = BTreeSet::from(["u".to_string()]);
        assert!(!has_data_values(&tbox));
        assert!(applies(&tbox, &roles));
        let sorts = infer_by_name(&tbox, &roles);
        assert_eq!(sorts.concept("Q_0"), Sort::Both);
        encode(&mut tbox, &roles);
        let dx = c(DATA_SORT, x());
        let dy = c(DATA_SORT, y());
        assert!(tbox.contains(&clause([c("Q_0", x())], [c("__nom__a", x()), dx.clone()])));
        assert!(tbox.contains(&clause([c("Q_0", x())], [c("Q_1", x()), dx.clone()])));
        assert!(tbox.contains(&clause([r("u", x(), y())], [dy])));
        assert!(tbox.contains(&clause([c("__nom__a", x()), dx.clone()], [])));
        assert!(tbox.contains(&fact([c("Q_0", x())])));
    }

    /// The indexed pass against the map-keyed reference (775223bf) on
    /// random clause sets over every kind of name and term: the same clause
    /// set, in the same order, and the same count.
    #[test]
    fn indexed_encoding_matches_the_reference() {
        let concepts = ["A", "B", "C", "Q_0", "Q_1", "Q_2", "Q_3", "__dt__integer", "__dt__boolean",
            VAL, "__dt__val__\"true\"^^xsd:boolean", "__nom__o", "__nom__p", "Thing", "__top__"];
        let roles = ["u", "w", "r", "s", "__inv__r", "__chain__0"];
        let mut state: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move |n: usize| -> usize {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state % n as u64) as usize
        };
        let data_roles = BTreeSet::from(["u".to_string(), "w".to_string()]);
        let declared: Vec<String> = ["A", "B", "D", "E"].iter().map(|s| s.to_string()).collect();
        let proxies: BTreeMap<String, String> = [("o", "__nom__o"), ("p", "__nom__p"), ("q", "__nom__q")]
            .iter().map(|(a, b)| (a.to_string(), b.to_string())).collect();
        for round in 0..3000 {
            let mut tbox: Vec<DLClause> = Vec::new();
            let size = 1 + next(12);
            for _ in 0..size {
                let mut term = |next: &mut dyn FnMut(usize) -> usize| match next(7) {
                    0 | 1 => x(),
                    2 => y(),
                    3 => fx("f"),
                    4 => fx("g"),
                    5 => Term::Ind(["o", "p", "q"][next(3)].into()),
                    _ => Term::Fun("h".into(), Box::new(y())),
                };
                let mut atom = |next: &mut dyn FnMut(usize) -> usize| match next(5) {
                    0 | 1 | 2 => c(concepts[next(concepts.len())], term(next)),
                    3 => r(roles[next(roles.len())], term(next), term(next)),
                    _ => Atom::Eq(term(next), term(next)),
                };
                let body: Vec<Atom> = (0..next(3)).map(|_| atom(&mut next)).collect();
                let head: Vec<Atom> = (0..next(3)).map(|_| atom(&mut next)).collect();
                tbox.push(clause(body, head));
            }
            let mut expected = tbox.clone();
            let want = reference::encode_with_classes(&mut expected, &data_roles, &declared, &proxies);
            let got = encode_with_classes(&mut tbox, &data_roles, &declared, &proxies);
            assert_eq!((got, &tbox), (want, &expected), "round {round}");
        }
    }

    #[test]
    fn indexed_encoding_matches_the_reference_on_the_fixtures() {
        let u = BTreeSet::from(["u".to_string()]);
        for tbox in [fixture()] {
            let mut expected = tbox.clone();
            let mut got = tbox.clone();
            let want = reference::encode(&mut expected, &u);
            assert_eq!(encode(&mut got, &u), want);
            assert_eq!(got, expected);
        }
    }
}
