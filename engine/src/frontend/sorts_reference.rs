//! The sort encoding as of 775223bf (v1.5.5 preview), kept verbatim as the
//! oracle for the indexed implementation in `sorts.rs` (tests only).
#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};

use crate::frontend::clauses::{clause, Atom, DLClause, Term};

/// Marker concept interpreted as the data domain `Δ_D`.
pub const DATA_SORT: &str = super::DATA_SORT;

/// Marker concept carried by every named individual; disjoint from
/// [`DATA_SORT`].
pub const OBJECT_SORT: &str = super::OBJECT_SORT;

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

struct Sorts {
    /// Concept sort and whether it is a fixed seed.
    concepts: BTreeMap<String, (Sort, bool)>,
    /// Role (domain, range) sorts.
    roles: BTreeMap<String, (Sort, Sort)>,
    /// Structural sort of every Skolem term and individual (phase 1).
    terms: BTreeMap<Term, Sort>,
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
        let mut sorts = Sorts { concepts, roles, terms: BTreeMap::new() };
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
        sorts.terms = global.into_iter().map(|(t, s)| (t.clone(), s)).collect();
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
    encode_with_classes(tbox, data_roles, &[], &BTreeMap::new())
}

/// [`encode`], also placing every declared source class in the object sort,
/// including classes no clause mentions: an unconstrained class is still a
/// set of objects, and every relativized `⊤` fact must apply to it.
pub fn encode_with_classes(
    tbox: &mut Vec<DLClause>,
    data_roles: &BTreeSet<String>,
    declared: &[String],
    proxies: &BTreeMap<String, String>,
) -> usize {
    let sorts = Sorts::infer(tbox, data_roles);
    let x = Term::Var("x".to_string());
    let y = Term::Var("y".to_string());
    let d = |t: &Term| Atom::Concept(DATA_SORT.to_string(), t.clone());
    let mut count = 0usize;
    // Class-level facts: `⊤ ⊑ C` becomes `¬D ⊑ C`. A clause is class-level
    // when it mentions exactly one variable, its body is empty or consists
    // of polymorphic or data-sorted concept atoms only (nothing that pins
    // the element to the object domain), and every concept in its head is
    // object-sorted. Data-range-level, polymorphic and unresolved heads are
    // left as they are (see the module documentation), and so are ground
    // facts, whose individuals carry their own sort.
    for c in tbox.iter_mut() {
        let mut vars: BTreeSet<&Term> = BTreeSet::new();
        let mut object_level = !c.head.is_empty();
        for atom in &c.body {
            match atom {
                Atom::Concept(name, t) => {
                    vars.extend(term_var(t));
                    object_level &= matches!(sorts.concept(name), Sort::Both | Sort::Data);
                }
                Atom::Role(..) | Atom::Eq(..) => object_level = false,
            }
        }
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
        let body = std::mem::take(&mut c.body);
        let mut head = std::mem::take(&mut c.head);
        head.push(d(&v));
        *c = clause(body, head);
        count += 1;
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
    let fixed_concept = |name: &str| name == DATA_SORT || sorts.concepts[name].1;
    let mut concept_adm: BTreeMap<String, Admits> = sorts
        .concepts
        .iter()
        .map(|(name, (sort, _))| (name.clone(), Admits::from_sort(*sort)))
        .collect();
    concept_adm.insert(DATA_SORT.to_string(), Admits::from_sort(Sort::Data));
    let fixed_role = |name: &str| is_source_role(name);
    let mut role_adm: BTreeMap<String, (Admits, Admits)> = sorts
        .roles
        .iter()
        .map(|(name, (domain, range))| {
            let (domain, range) = if fixed_role(name) {
                let range = if data_roles.contains(name) { Sort::Data } else { Sort::Object };
                (Sort::Object, range)
            } else {
                (*domain, *range)
            };
            (name.clone(), (Admits::from_sort(domain), Admits::from_sort(range)))
        })
        .collect();
    let mut head_d: BTreeMap<usize, BTreeSet<Term>> = BTreeMap::new();
    let mut body_d: BTreeMap<usize, BTreeSet<Term>> = BTreeMap::new();
    loop {
        let mut changed = false;
        for (index, c) in tbox.iter().enumerate() {
            let mut body_terms: BTreeSet<&Term> = BTreeSet::new();
            for atom in &c.body {
                match atom {
                    Atom::Concept(_, t) => {
                        body_terms.insert(t);
                    }
                    Atom::Role(_, s, t) | Atom::Eq(s, t) => {
                        body_terms.insert(s);
                        body_terms.insert(t);
                    }
                }
            }
            let mut terms: BTreeSet<&Term> = body_terms.clone();
            for atom in &c.head {
                match atom {
                    Atom::Concept(_, t) => {
                        terms.insert(t);
                    }
                    Atom::Role(_, s, t) | Atom::Eq(s, t) => {
                        terms.insert(s);
                        terms.insert(t);
                    }
                }
            }
            for t in terms {
                let structural = if matches!(t, Term::Var(_)) {
                    Sort::Unknown
                } else {
                    sorts.terms.get(t).copied().unwrap_or(Sort::Unknown)
                };
                // A Skolem term only the head mentions is created by the
                // clause; its sort is whatever its structural evidence says.
                if !body_terms.contains(t) && !matches!(t, Term::Var(_)) && !structural.definite() {
                    continue;
                }
                for sort in [Sort::Object, Sort::Data] {
                    // An individual is an object, a Skolem term has its
                    // structural sort.
                    if matches!(t, Term::Ind(_)) && sort == Sort::Data {
                        continue;
                    }
                    if structural.definite() && structural != sort {
                        continue;
                    }
                    if sort == Sort::Object && body_d.get(&index).is_some_and(|ts| ts.contains(t)) {
                        continue;
                    }
                    if sort == Sort::Data && head_d.get(&index).is_some_and(|ts| ts.contains(t)) {
                        continue;
                    }
                    let body_admits = c.body.iter().all(|atom| match atom {
                        Atom::Concept(name, u) if u == t => concept_adm[name].admits(sort),
                        Atom::Role(name, s, u) => {
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
                    let mut definers: Vec<&str> = Vec::new();
                    let mut positions: Vec<(&str, bool)> = Vec::new();
                    for atom in &c.head {
                        match atom {
                            Atom::Concept(name, u) if u == t => {
                                on_term = true;
                                satisfied |= concept_adm[name].admits(sort);
                                if !fixed_concept(name) {
                                    definers.push(name);
                                }
                            }
                            Atom::Role(name, s, u) => {
                                if s == t {
                                    on_term = true;
                                    satisfied |= role_adm[name].0.admits(sort);
                                    if !fixed_role(name) {
                                        positions.push((name, false));
                                    }
                                }
                                if u == t {
                                    on_term = true;
                                    satisfied |= role_adm[name].1.admits(sort);
                                    if !fixed_role(name) {
                                        positions.push((name, true));
                                    }
                                }
                            }
                            Atom::Eq(s, u) if s == t || u == t => {
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
                        for name in definers {
                            changed |= concept_adm.get_mut(name).expect("head concept").add(sort);
                        }
                    } else if !positions.is_empty() {
                        for (name, range) in positions {
                            let entry = role_adm.get_mut(name).expect("head role");
                            changed |= if range { entry.1.add(sort) } else { entry.0.add(sort) };
                        }
                    } else {
                        // Only fixed sorts on `t`: relativize the clause.
                        let set = if sort == Sort::Data { &mut head_d } else { &mut body_d };
                        changed |= set.entry(index).or_default().insert(t.clone());
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    for (index, ts) in &head_d {
        let c = &mut tbox[*index];
        let body = std::mem::take(&mut c.body);
        let mut head = std::mem::take(&mut c.head);
        head.extend(ts.iter().map(|t| d(t)));
        *c = clause(body, head);
        count += 1;
    }
    for (index, ts) in &body_d {
        let c = &mut tbox[*index];
        let mut body = std::mem::take(&mut c.body);
        let head = std::mem::take(&mut c.head);
        body.extend(ts.iter().map(|t| d(t)));
        *c = clause(body, head);
        count += 1;
    }
    let mut added: Vec<DLClause> = Vec::new();
    for (name, adm) in &concept_adm {
        if name == DATA_SORT {
            continue;
        }
        let atom = Atom::Concept(name.clone(), x.clone());
        match adm.only() {
            Some(Sort::Data) => added.push(clause([atom], [d(&x)])),
            Some(Sort::Object) => added.push(clause([atom, d(&x)], [])),
            _ => {}
        }
    }
    for (name, (domain, range)) in &role_adm {
        let atom = Atom::Role(name.clone(), x.clone(), y.clone());
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
        if is_source_concept(name) && !concept_adm.contains_key(name) {
            added.push(clause([Atom::Concept(name.clone(), x.clone()), d(&x)], []));
        }
    }
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
    fn collect<'a>(t: &'a Term, out: &mut BTreeSet<&'a str>) {
        match t {
            Term::Ind(name) => {
                out.insert(name);
            }
            Term::Fun(_, inner) => collect(inner, out),
            Term::Var(_) | Term::Aux(..) => {}
        }
    }
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
                if concept_adm.get(name).and_then(|adm| adm.only()) == Some(Sort::Object) {
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
                if !concept_adm.contains_key(proxy) {
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

