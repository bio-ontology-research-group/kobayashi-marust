//! DL-clause normal form (port of `moose.sroiq.dlclauses`) + conversion to the
//! engine JSON schema (`crate::json_io`).
//!
//! `DLClause` keeps `body`/`head` as sorted, de-duplicated `Vec<Atom>` — the
//! canonical form of the frozenset semantics of the Python `DLClause`
//! (unordered, de-duplicated). All constructions go through `clause`/`fact`/
//! `constraint`, which canonicalise, so derived `Eq`/`Ord`/`Hash` coincide
//! with set equality and iteration order matches the old `BTreeSet` exactly.
//! (A `BTreeSet` node allocates 11 `Atom` slots even for a 1–2 atom set,
//! which made the clause set the dominant memory cost on 3M-axiom
//! ontologies; an exact-size sorted Vec is ~5x smaller.)

use crate::json_io::{JAtom, JClause, JTerm};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Var(String),
    Ind(String),
    Aux(String, Vec<(String, i64)>),
    Fun(String, Box<Term>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Atom {
    Concept(String, Term),
    Role(String, Term, Term),
    Eq(Term, Term),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DLClause {
    pub body: Vec<Atom>,
    pub head: Vec<Atom>,
}

/// Canonicalise an atom list: sorted + de-duplicated, exact capacity.
fn canon<I: IntoIterator<Item = Atom>>(atoms: I) -> Vec<Atom> {
    let mut v: Vec<Atom> = atoms.into_iter().collect();
    v.sort();
    v.dedup();
    v.shrink_to_fit();
    v
}

/// Convenience constructors mirroring `dlc.X` / `dlc.Y`.
pub fn var_x() -> Term {
    Term::Var("x".to_string())
}
pub fn var_y() -> Term {
    Term::Var("y".to_string())
}

pub fn clause<B: IntoIterator<Item = Atom>, H: IntoIterator<Item = Atom>>(
    body: B,
    head: H,
) -> DLClause {
    DLClause {
        body: canon(body),
        head: canon(head),
    }
}

pub fn fact<H: IntoIterator<Item = Atom>>(head: H) -> DLClause {
    DLClause {
        body: Vec::new(),
        head: canon(head),
    }
}

pub fn constraint<B: IntoIterator<Item = Atom>>(body: B) -> DLClause {
    DLClause {
        body: canon(body),
        head: Vec::new(),
    }
}

/// KM_EMELIM — complementary-definer excluded-middle elimination (the CB
/// analogue of the HT-path `cb_to_ht.elim_complements`). A pair `⊤ ⊑ A ∨ B`
/// (empty body, two concepts over one term) together with `A ⊓ B ⊑ ⊥` (empty
/// head) entails `B ≡ ¬A`. The clausifier introduced B as a fresh definer for a
/// negation and then forced excluded middle as a disjunctive fact that fires on
/// every individual. Since the CB DL-clause form is positive (negation is
/// body/head position), `B ≡ ¬A` is applied by MOVING each occurrence of B to
/// the other side of `⊑` as A: a head B becomes a body A, a body B becomes a
/// head A. Dropping the two now-tautologous defining clauses, this is
/// model-preserving (sound + complete). The internal (definer) side is
/// eliminated so named/query concepts survive. Substitution is kept chain-free.
fn is_definer(s: &str) -> bool {
    s.starts_with("Q_") || s.starts_with("__") || s.starts_with("aux_") || s.starts_with("def_")
}

/// If `atoms` are exactly two distinct Concept atoms over the SAME term, return
/// their names (sorted); else None. (Matches the `⊤⊑A∨B` / `A⊓B⊑⊥` shape.)
fn two_concepts_same_term(atoms: &[Atom]) -> Option<(String, String)> {
    if atoms.len() != 2 {
        return None;
    }
    if let (Atom::Concept(a, ta), Atom::Concept(b, tb)) = (&atoms[0], &atoms[1]) {
        if ta == tb && a != b {
            return Some(if a <= b { (a.clone(), b.clone()) } else { (b.clone(), a.clone()) });
        }
    }
    None
}

pub fn elim_complements(tbox: Vec<DLClause>) -> (Vec<DLClause>, usize) {
    use std::collections::{HashMap, HashSet};
    let mut em: HashSet<(String, String)> = HashSet::new();
    let mut dj: HashSet<(String, String)> = HashSet::new();
    for c in &tbox {
        if c.body.is_empty() {
            if let Some(p) = two_concepts_same_term(&c.head) {
                em.insert(p);
            }
        }
        if c.head.is_empty() {
            if let Some(p) = two_concepts_same_term(&c.body) {
                dj.insert(p);
            }
        }
    }
    let pairs: Vec<(String, String)> = em.intersection(&dj).cloned().collect();
    if pairs.is_empty() {
        return (tbox, 0);
    }
    // elim -> keep  (elim ≡ ¬keep). Prefer eliminating the definer side.
    let mut sub: HashMap<String, String> = HashMap::new();
    let mut used: HashSet<String> = HashSet::new();
    for (a, b) in &pairs {
        let (elim, keep) = if is_definer(b) && !is_definer(a) {
            (b, a)
        } else if is_definer(a) && !is_definer(b) {
            (a, b)
        } else {
            (b, a) // both/neither definer: drop the lexicographically larger (b >= a)
        };
        if used.contains(elim) || used.contains(keep) {
            continue; // keep the substitution chain-free
        }
        sub.insert(elim.clone(), keep.clone());
        used.insert(elim.clone());
        used.insert(keep.clone());
    }
    if sub.is_empty() {
        return (tbox, 0);
    }
    let elim_pairs: HashSet<(String, String)> = sub
        .iter()
        .map(|(e, k)| if e <= k { (e.clone(), k.clone()) } else { (k.clone(), e.clone()) })
        .collect();
    let n = sub.len();
    let mut out: Vec<DLClause> = Vec::with_capacity(tbox.len());
    for c in tbox {
        // drop the defining `⊤⊑A∨B` / `A⊓B⊑⊥` clauses for eliminated pairs.
        if c.body.is_empty() {
            if let Some(p) = two_concepts_same_term(&c.head) {
                if elim_pairs.contains(&p) {
                    continue;
                }
            }
        }
        if c.head.is_empty() {
            if let Some(p) = two_concepts_same_term(&c.body) {
                if elim_pairs.contains(&p) {
                    continue;
                }
            }
        }
        let mut nb: Vec<Atom> = Vec::new();
        let mut nh: Vec<Atom> = Vec::new();
        for a in &c.body {
            match a {
                Atom::Concept(name, t) if sub.contains_key(name) => {
                    nh.push(Atom::Concept(sub[name].clone(), t.clone()))
                }
                _ => nb.push(a.clone()),
            }
        }
        for a in &c.head {
            match a {
                Atom::Concept(name, t) if sub.contains_key(name) => {
                    nb.push(Atom::Concept(sub[name].clone(), t.clone()))
                }
                _ => nh.push(a.clone()),
            }
        }
        out.push(clause(nb, nh));
    }
    (out, n)
}

// ---- conversion to JSON (port of rust_context._term_to_json etc.) ----

fn term_to_json(t: &Term) -> JTerm {
    match t {
        Term::Var(n) => JTerm::Var { name: n.clone() },
        Term::Ind(n) => JTerm::Ind { name: n.clone() },
        Term::Aux(root, label) => JTerm::Aux {
            root: root.clone(),
            label: label.clone(),
        },
        Term::Fun(f, arg) => JTerm::Fun {
            function: f.clone(),
            arg: Box::new(term_to_json(arg)),
        },
    }
}

fn atom_to_json(a: &Atom) -> JAtom {
    match a {
        Atom::Concept(c, t) => JAtom::Concept {
            concept: c.clone(),
            term: term_to_json(t),
        },
        Atom::Role(r, s, t) => JAtom::Role {
            role: r.clone(),
            source: term_to_json(s),
            target: term_to_json(t),
        },
        Atom::Eq(l, r) => JAtom::Eq {
            left: term_to_json(l),
            right: term_to_json(r),
        },
    }
}

/// Port of `rust_context._clause_to_json`.
pub fn clause_to_json(c: &DLClause) -> JClause {
    JClause {
        body: c.body.iter().map(atom_to_json).collect(),
        head: c.head.iter().map(atom_to_json).collect(),
    }
}
