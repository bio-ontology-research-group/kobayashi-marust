//! Adapter: parse the JSON DL-clause input into the calculus representation,
//! run the disjunctive context-calculus `Engine`, and expose subsumptions,
//! derived clauses, and consistency.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::calc::*;
use crate::clause::OntologyClause;
use crate::engine::Engine;
use crate::json_io::{JAtom, JClause, JTerm};

fn short(name: &str) -> &str {
    name.rsplit(['#', '/']).next().unwrap_or(name)
}

/// Build the engine from input clauses.
pub struct Reasoner {
    engine: Engine,
}

struct Builder {
    sig: Sig,
    /// global function-symbol interner (function name -> f index >= 1)
    fn_id: HashMap<String, i32>,
    dropped: usize,
}

impl Builder {
    fn new() -> Builder {
        Builder {
            sig: Sig::default(),
            fn_id: HashMap::new(),
            dropped: 0,
        }
    }

    fn function(&mut self, name: &str) -> i32 {
        if let Some(&id) = self.fn_id.get(name) {
            return id;
        }
        let id = self.fn_id.len() as i32 + 1;
        self.fn_id.insert(name.to_string(), id);
        id
    }

    /// Map a JTerm to a calculus Term using a per-clause variable map.
    /// Returns None if the term is an unsupported individual/nominal/aux.
    fn term(&mut self, t: &JTerm, varmap: &mut HashMap<String, Term>) -> Option<Term> {
        match t {
            JTerm::Var { name } => {
                if name == "x" {
                    return Some(X);
                }
                if let Some(&v) = varmap.get(name) {
                    return Some(v);
                }
                // assign next neighbour variable z_i (i >= 1), i.e. ids -2, -3, ...
                let next = varmap.values().filter(|&&v| is_neighbour(v) && v != Y).count() as i32 + 1;
                let v = zvar(next);
                varmap.insert(name.clone(), v);
                Some(v)
            }
            JTerm::Fun { function, arg } => {
                // function terms must be f(x)
                match arg.as_ref() {
                    JTerm::Var { name } if name == "x" => {}
                    _ => return None,
                }
                Some(fterm(self.function(function)))
            }
            // individuals / nominal aux constants: unsupported in the ALCHIQ core
            JTerm::Ind { .. } | JTerm::Aux { .. } => None,
        }
    }

    fn atom_pred(&mut self, a: &JAtom, varmap: &mut HashMap<String, Term>) -> Option<Pred> {
        match a {
            JAtom::Concept { concept, term } => {
                let t = self.term(term, varmap)?;
                let iri = self.sig.concept(concept);
                if short(concept) == "Nothing" {
                    self.sig.bottom = Some(iri);
                }
                Some(Pred::Concept { iri, t })
            }
            JAtom::Role { role, source, target } => {
                let s = self.term(source, varmap)?;
                let t = self.term(target, varmap)?;
                let iri = self.sig.role(role);
                Some(Pred::Role { iri, s, t })
            }
            JAtom::Eq { .. } => None,
        }
    }

    fn atom_lit(&mut self, a: &JAtom, varmap: &mut HashMap<String, Term>) -> Option<Lit> {
        match a {
            JAtom::Eq { left, right } => {
                let l = self.term(left, varmap)?;
                let r = self.term(right, varmap)?;
                Some(Lit::eq(l, r))
            }
            _ => self.atom_pred(a, varmap).map(Lit::P),
        }
    }

    /// Parse a JClause to an OntologyClause; None if unsupported / non-normal.
    fn clause(&mut self, c: &JClause) -> Option<OntologyClause> {
        let mut varmap: HashMap<String, Term> = HashMap::new();
        let mut body: Vec<Pred> = Vec::new();
        // A body equality `a ≈ b` is a negative equality literal: the clause
        // `{a≈b} ∧ Γ → Δ` is logically `Γ → Δ ∨ a ≉ b`.  We move such body
        // equalities to the head as inequalities (this is how the normaliser
        // encodes the distinctness of number-restriction witnesses, e.g.
        // `{f_i ≈ f_j, Q} → ⊥` meaning `f_i ≠ f_j`).
        let mut body_ineqs: Vec<Lit> = Vec::new();
        for a in &c.body {
            match a {
                JAtom::Eq { left, right } => {
                    let l = self.term(left, &mut varmap)?;
                    let r = self.term(right, &mut varmap)?;
                    body_ineqs.push(Lit::ineq(l, r));
                }
                _ => {
                    let p = self.atom_pred(a, &mut varmap)?;
                    body.push(p);
                }
            }
        }
        // Normal-form requirement: every body *role* mentions the central
        // variable.  Body concepts may be on a neighbour variable (e.g. `C(y)`
        // in `R(x,y) ∧ C(y) -> D(x)`), which is guarded by a body role.  Only
        // role-chain / transitivity clauses with a `R(z_i, z_j)` body role
        // (no central variable) are out of the ALCHIQ clause normal form; they
        // require the role-automaton transformation, so we drop them soundly
        // and report the count.
        let normal = body.iter().all(|p| match p {
            Pred::Concept { .. } => true,
            Pred::Role { s, t, .. } => is_central(*s) || is_central(*t),
        });
        if !normal {
            return None;
        }
        let mut head: Vec<Lit> = body_ineqs;
        for a in &c.head {
            let l = self.atom_lit(a, &mut varmap)?;
            head.push(l);
        }
        Some(OntologyClause::new(body, head))
    }
}

impl Reasoner {
    pub fn new(input: &[JClause]) -> Reasoner {
        let mut b = Builder::new();
        let mut clauses: Vec<OntologyClause> = Vec::new();
        for c in input {
            match b.clause(c) {
                Some(oc) => clauses.push(oc),
                None => b.dropped += 1,
            }
        }
        let engine = Engine::new(b.sig, clauses, b.dropped);
        Reasoner { engine }
    }

    pub fn saturate(&mut self) {
        self.engine.run();
    }

    pub fn subsumptions(&self) -> BTreeMap<String, BTreeSet<String>> {
        let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (a, supers) in self.engine.subsumptions() {
            out.insert(a, supers.into_iter().collect());
        }
        out
    }

    pub fn emit_clauses(&self) -> Vec<JClause> {
        fn ax(name: &str) -> JAtom {
            JAtom::Concept {
                concept: name.to_string(),
                term: JTerm::Var { name: "x".to_string() },
            }
        }
        let mut out = Vec::new();
        for (a, supers) in self.engine.subsumptions() {
            for d in supers {
                if d == "owl:Nothing" {
                    out.push(JClause { body: vec![ax(&a)], head: vec![] });
                } else {
                    out.push(JClause { body: vec![ax(&a)], head: vec![ax(&d)] });
                }
            }
        }
        out
    }

    pub fn inconsistent(&self) -> bool {
        self.engine.inconsistent()
    }

    pub fn dropped_unsupported(&self) -> usize {
        self.engine.dropped_unsupported
    }

    pub fn num_contexts(&self) -> usize {
        self.engine.num_contexts()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json_io::{JAtom, JClause, JTerm};

    fn vx() -> JTerm {
        JTerm::Var { name: "x".into() }
    }
    fn vn(n: &str) -> JTerm {
        JTerm::Var { name: n.into() }
    }
    fn fx(f: &str) -> JTerm {
        JTerm::Fun {
            function: f.into(),
            arg: Box::new(vx()),
        }
    }
    fn c(name: &str, t: JTerm) -> JAtom {
        JAtom::Concept {
            concept: name.into(),
            term: t,
        }
    }
    fn r(name: &str, s: JTerm, t: JTerm) -> JAtom {
        JAtom::Role {
            role: name.into(),
            source: s,
            target: t,
        }
    }
    fn cl(body: Vec<JAtom>, head: Vec<JAtom>) -> JClause {
        JClause { body, head }
    }

    fn run(clauses: Vec<JClause>) -> Reasoner {
        let mut rr = Reasoner::new(&clauses);
        rr.saturate();
        rr
    }
    fn supers(rr: &Reasoner, a: &str) -> std::collections::BTreeSet<String> {
        rr.subsumptions().get(a).cloned().unwrap_or_default()
    }

    #[test]
    fn concept_hierarchy() {
        // A ⊑ B, B ⊑ C  ⟹  A ⊑ B, A ⊑ C
        let rr = run(vec![
            cl(vec![c("A", vx())], vec![c("B", vx())]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
        ]);
        assert!(supers(&rr, "A").contains("B"));
        assert!(supers(&rr, "A").contains("C"));
    }

    #[test]
    fn disjointness_unsat() {
        // A ⊑ B, A ⊑ C, B ⊓ C ⊑ ⊥  ⟹  A unsatisfiable
        let rr = run(vec![
            cl(vec![c("A", vx())], vec![c("B", vx())]),
            cl(vec![c("A", vx())], vec![c("C", vx())]),
            cl(vec![c("B", vx()), c("C", vx())], vec![]),
        ]);
        assert!(supers(&rr, "A").contains("owl:Nothing"));
    }

    #[test]
    fn disjunction_no_spurious_subsumption() {
        // A ⊑ B ⊔ C must NOT yield A ⊑ B or A ⊑ C (this was the soundness bug).
        let rr = run(vec![cl(vec![c("A", vx())], vec![c("B", vx()), c("C", vx())])]);
        assert!(!supers(&rr, "A").contains("B"));
        assert!(!supers(&rr, "A").contains("C"));
        assert!(!rr.inconsistent());
    }

    #[test]
    fn existential_subsumption() {
        // A ⊑ ∃R.B, B ⊑ C, ∃R.C ⊑ D  ⟹  A ⊑ D  (exercises Succ + Pred).
        let rr = run(vec![
            cl(vec![c("A", vx())], vec![r("R", vx(), fx("f"))]),
            cl(vec![c("A", vx())], vec![c("B", fx("f"))]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
            cl(vec![r("R", vx(), vn("y")), c("C", vn("y"))], vec![c("D", vx())]),
        ]);
        assert!(supers(&rr, "A").contains("D"), "expected A ⊑ D, got {:?}", supers(&rr, "A"));
    }

    #[test]
    fn factor_number_restriction_clash() {
        // Three pairwise-distinct witnesses f,g,h (head inequalities, encoded as
        // body equalities) together with the ≤2 conclusion "at least two of the
        // three coincide" (a head disjunction of equalities) is unsatisfiable.
        // Requires Factor + Eq/Ineq.
        let eqa = |a: JTerm, b: JTerm| JAtom::Eq { left: a, right: b };
        let rr = run(vec![
            // A -> f≈g ∨ f≈h ∨ g≈h
            cl(
                vec![c("A", vx())],
                vec![eqa(fx("f"), fx("g")), eqa(fx("f"), fx("h")), eqa(fx("g"), fx("h"))],
            ),
            // {A, f≈g} -> ⊥   (i.e. A -> f≉g)
            cl(vec![c("A", vx()), eqa(fx("f"), fx("g"))], vec![]),
            cl(vec![c("A", vx()), eqa(fx("f"), fx("h"))], vec![]),
            cl(vec![c("A", vx()), eqa(fx("g"), fx("h"))], vec![]),
        ]);
        assert!(
            supers(&rr, "A").contains("owl:Nothing"),
            "expected A unsatisfiable, got {:?}",
            supers(&rr, "A")
        );
    }

    #[test]
    fn role_hierarchy_and_domain() {
        // R ⊑ S, ∃S.⊤ ⊑ A, and B ⊑ ∃R.⊤  ⟹  B ⊑ A
        let rr = run(vec![
            cl(vec![r("R", vx(), vn("y"))], vec![r("S", vx(), vn("y"))]),
            cl(vec![r("S", vx(), vn("y"))], vec![c("A", vx())]),
            cl(vec![c("B", vx())], vec![r("R", vx(), fx("g"))]),
        ]);
        assert!(supers(&rr, "B").contains("A"), "expected B ⊑ A, got {:?}", supers(&rr, "B"));
    }
}
