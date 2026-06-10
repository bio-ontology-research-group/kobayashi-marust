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
