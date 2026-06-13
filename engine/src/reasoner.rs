//! Adapter: parse the JSON DL-clause input into the calculus representation,
//! run the disjunctive context-calculus `Engine`, and expose subsumptions,
//! derived clauses, and consistency.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use rayon::prelude::*;

use crate::calc::*;
use crate::clause::OntologyClause;
use crate::engine::Engine;
use crate::json_io::{JAtom, JClause, JTerm};

fn short(name: &str) -> &str {
    name.rsplit(['#', '/']).next().unwrap_or(name)
}

/// Outcome of one branch of the Direction-B splitting search
/// (docs/DISJUNCTION-SPLITTING.md).
enum SplitBranch {
    /// The branch derived ⊥ — impossible under its decisions.
    Closed,
    /// A leaf model; the concept iris forced as `⊤ → B(x)` units in it.
    Open(BTreeSet<Iri>),
    /// A residual disjunction could not be split (a role/equality/successor
    /// disjunct, or the per-query node budget was exhausted): the driver falls
    /// back to the complete default engine for this query.
    Foreign,
}

/// Reasoner: parses input clauses, then classifies by running the verified
/// context-calculus `Engine` over disjoint chunks of the named query concepts
/// **in parallel** (rayon), merging the per-chunk results.  Each query's
/// subsumptions are independent of the others (the shared successor context is
/// only an optimisation), so chunked classification is sound and deterministic;
/// the engine core is unchanged.  Set `KM_THREADS=1` to force sequential mode.
pub struct Reasoner {
    sig0: Sig,
    clauses0: Vec<OntologyClause>,
    dropped: usize,
    subs: BTreeMap<String, BTreeSet<String>>,
    inconsistent: bool,
    num_ctx: usize,
}

struct Builder {
    sig: Sig,
    /// global function-symbol interner (function name -> f index >= 1)
    fn_id: HashMap<String, i32>,
    /// individual interner (name -> id >= 1); only populated in nominal mode
    ind_id: HashMap<String, i32>,
    /// KM_NOMINALS: accept individual terms (ALCHOIQ nominal rules,
    /// docs/NOMINALS-CB.md Phase 1). Off: clauses with individuals are
    /// dropped and counted, as before.
    nominals: bool,
    dropped: usize,
}

impl Builder {
    fn new() -> Builder {
        Builder {
            sig: Sig::default(),
            fn_id: HashMap::new(),
            ind_id: HashMap::new(),
            nominals: std::env::var_os("KM_NOMINALS").is_some(),
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

    fn individual(&mut self, name: &str) -> i32 {
        if let Some(&id) = self.ind_id.get(name) {
            return id;
        }
        let id = self.ind_id.len() as i32 + 1;
        self.ind_id.insert(name.to_string(), id);
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
            // individuals: accepted in nominal mode (ALCHOIQ rules,
            // docs/NOMINALS-CB.md Phase 1); otherwise unsupported and the
            // clause is dropped+counted as before. Aux constants stay
            // unsupported.
            JTerm::Ind { name } => {
                if self.nominals {
                    Some(ind_term(self.individual(name)))
                } else {
                    None
                }
            }
            JTerm::Aux { .. } => None,
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
        Reasoner {
            sig0: b.sig,
            clauses0: clauses,
            dropped: b.dropped,
            subs: BTreeMap::new(),
            inconsistent: false,
            num_ctx: 0,
        }
    }

    /// Desired worker count: `KM_THREADS` env if set (clamped >=1), else the
    /// machine's available parallelism.
    fn want_threads() -> usize {
        if let Ok(v) = std::env::var("KM_THREADS") {
            if let Ok(n) = v.trim().parse::<usize>() {
                return n.max(1);
            }
        }
        std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1)
    }

    fn build_engine(&self) -> Engine {
        Engine::new(self.sig0.clone(), self.clauses0.clone(), self.dropped)
    }

    fn absorb(&mut self, subs: Vec<(String, Vec<String>)>, inc: bool, nctx: usize) {
        if inc {
            self.inconsistent = true;
        }
        self.num_ctx += nctx;
        for (a, supers) in subs {
            let set = self.subs.entry(a).or_default();
            set.extend(supers);
        }
    }

    /// Direction B splitting recursion. A fresh engine per node gives branch
    /// isolation; `classify_assume` runs the ordered (tame) closure under the
    /// current decisions; a residual fact-disjunction with no satisfied disjunct
    /// is the next split point. A subsumer is forced iff it is a unit in EVERY
    /// open branch (the intersection); a query is unsatisfiable iff every branch
    /// closes. Sound by construction (proof by cases over an exhaustive
    /// disjunction); complete on the covered fragment (it falls back to the
    /// default engine on any disjunction it cannot split — `Foreign`).
    fn split_recurse(&self, query: Iri, decisions: &[Iri], budget: &mut usize) -> SplitBranch {
        if *budget == 0 {
            return SplitBranch::Foreign;
        }
        *budget -= 1;
        let mut e = self.build_engine();
        // Branch closures run under the tame ordered regime.
        set_branch_ordered(true);
        let cf = e.classify_assume(query, decisions);
        if cf.unsat {
            return SplitBranch::Closed;
        }
        if cf.foreign {
            return SplitBranch::Foreign;
        }
        let satisfied: std::collections::HashSet<Iri> =
            decisions.iter().copied().chain(cf.units.iter().copied()).collect();
        let pick = cf
            .disjunctions
            .iter()
            .find(|d| !d.iter().any(|l| satisfied.contains(l)))
            .cloned();
        match pick {
            // Leaf: no open disjunction left → a Horn-like branch in which the
            // ordered closure surfaces every forced unit.
            None => SplitBranch::Open(cf.units.into_iter().collect()),
            Some(d) => {
                let mut acc: Option<BTreeSet<Iri>> = None;
                for &li in &d {
                    let mut dd = decisions.to_vec();
                    dd.push(li);
                    match self.split_recurse(query, &dd, budget) {
                        SplitBranch::Foreign => return SplitBranch::Foreign,
                        SplitBranch::Closed => {}
                        SplitBranch::Open(s) => {
                            acc = Some(match acc {
                                None => s,
                                Some(a) => a.intersection(&s).copied().collect(),
                            });
                        }
                    }
                }
                match acc {
                    None => SplitBranch::Closed, // every disjunct closed
                    Some(s) => SplitBranch::Open(s),
                }
            }
        }
    }

    /// Direction B (`KM_SPLIT`) classification driver: split-classify each query,
    /// falling back to the default engine for queries whose closure carries a
    /// disjunction the propositional-on-x driver cannot split.
    fn saturate_split(&mut self, queries: &[Iri]) {
        // Global inconsistency (⊤ ⊑ ⊥), detected once via an empty-query run
        // under the complete (unordered) regime.
        set_branch_ordered(false);
        let inc = {
            let mut e = self.build_engine();
            e.run_for(&[]);
            e.inconsistent()
        };
        let node_budget: usize = std::env::var("KM_SPLIT_BUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(200_000);
        let mut subs: Vec<(String, Vec<String>)> = Vec::new();
        let mut fallback: Vec<Iri> = Vec::new();
        for &q in queries {
            let mut budget = node_budget;
            match self.split_recurse(q, &[], &mut budget) {
                SplitBranch::Foreign => fallback.push(q),
                SplitBranch::Closed => {
                    let a = self.sig0.concept_names[q as usize].clone();
                    subs.push((a, vec!["owl:Nothing".to_string()]));
                }
                SplitBranch::Open(set) => {
                    let a = self.sig0.concept_names[q as usize].clone();
                    let supers: Vec<String> = set
                        .into_iter()
                        .filter(|&i| i != q)
                        .map(|i| self.sig0.concept_names[i as usize].clone())
                        .collect();
                    subs.push((a, supers));
                }
            }
        }
        if std::env::var_os("KM_PROF").is_some() {
            eprintln!(
                "KM_PROF split: queries={} split_classified={} fallback={}",
                queries.len(),
                queries.len() - fallback.len(),
                fallback.len()
            );
        }
        self.absorb(subs, inc, 0);
        if !fallback.is_empty() {
            // Fallback queries run under the complete (unordered) regime.
            set_branch_ordered(false);
            let mut e = self.build_engine();
            e.run_for(&fallback);
            let (s, i, n) = (e.subsumptions(), e.inconsistent(), e.num_contexts());
            self.absorb(s, i, n);
        }
    }

    pub fn saturate(&mut self) {
        let mut queries = self.build_engine().named_queries();
        // KM_QUERIES: classify only the named subjects listed (comma-
        // separated internal names) — the certified-EL hybrid's residue path:
        // elc answers every subject its certificate determined, and the
        // context engine resolves just the leftovers (one root context each,
        // sound and complete per query independently of the subset).
        if let Ok(qs) = std::env::var("KM_QUERIES") {
            let want: std::collections::HashSet<&str> = qs.split(',').collect();
            queries.retain(|&iri| want.contains(self.sig0.concept_names[iri as usize].as_str()));
        }
        // Direction B (docs/DISJUNCTION-SPLITTING.md): split-classify when
        // KM_SPLIT is set. Gated, default OFF.
        if std::env::var_os("KM_SPLIT").is_some() {
            self.saturate_split(&queries);
            return;
        }
        let threads = Self::want_threads().min(queries.len().max(1));
        // Sequential path: one engine over all queries (preserves cross-query
        // context sharing -- fastest when single-threaded).
        if threads <= 1 || queries.len() <= 1 {
            let mut e = self.build_engine();
            e.run_for(&queries);
            let (subs, inc, n) = (e.subsumptions(), e.inconsistent(), e.num_contexts());
            self.absorb(subs, inc, n);
            return;
        }
        // Static-schedule escape hatch (A/B + debugging): the original
        // contiguous chunking — `threads` engines, one fixed slice of the query
        // list each. Kept reachable via KM_STATIC_SCHED so the dynamic scheduler
        // below can be compared against it without rebuilding.
        if std::env::var_os("KM_STATIC_SCHED").is_some() {
            let chunk_len = queries.len().div_ceil(threads);
            let chunks: Vec<&[Iri]> = queries.chunks(chunk_len).collect();
            let partials: Vec<(Vec<(String, Vec<String>)>, bool, usize)> = chunks
                .par_iter()
                .map(|chunk| {
                    let mut e = self.build_engine();
                    e.run_for(chunk);
                    (e.subsumptions(), e.inconsistent(), e.num_contexts())
                })
                .collect();
            for (subs, inc, n) in partials {
                self.absorb(subs, inc, n);
            }
            return;
        }
        // Dynamic work-stealing path (default): `threads` long-lived engines
        // drain a shared atomic cursor over the query list in guided-size grabs
        // (large early — low atomic contention and intra-engine cross-query
        // context sharing — shrinking to 1 near the tail for load balance). A
        // worker that finishes its grab immediately steals the next, so a single
        // heavy query or a *cluster* of heavy queries that the static scheduler
        // bins into one contiguous chunk (the measured ore_ont_12141 imbalance,
        // where the hard concepts were adjacent in the named ordering and one
        // chunk serialised the whole run) no longer idles the other workers.
        //
        // Each engine is independent (its own context graph), and a query's
        // subsumers do not depend on which other queries are co-classified
        // (run_for's contract), so the union of per-engine subsumptions is the
        // full, correct result for any partition. This is a pure scheduling
        // change: the derived set is partition-independent (confluent), so the
        // output matches the sequential path and no Lean re-certification is
        // needed.
        use std::sync::atomic::{AtomicUsize, Ordering};
        let n = queries.len();
        let cursor = AtomicUsize::new(0);
        let this: &Reasoner = self;
        let queries_ref: &[Iri] = &queries;
        let partials: std::sync::Mutex<Vec<(Vec<(String, Vec<String>)>, bool, usize)>> =
            std::sync::Mutex::new(Vec::with_capacity(threads));
        rayon::scope(|s| {
            for _ in 0..threads {
                s.spawn(|_| {
                    let mut e = this.build_engine();
                    let mut did_any = false;
                    loop {
                        let seen = cursor.load(Ordering::Relaxed);
                        if seen >= n {
                            break;
                        }
                        // Guided self-scheduling: grab ~1/(2·threads) of what is
                        // left, clamped to [1, 64].
                        let grab = ((n - seen) / (2 * threads)).clamp(1, 64);
                        let start = cursor.fetch_add(grab, Ordering::Relaxed);
                        if start >= n {
                            break;
                        }
                        let end = (start + grab).min(n);
                        e.run_for(&queries_ref[start..end]);
                        did_any = true;
                    }
                    if did_any {
                        let part = (e.subsumptions(), e.inconsistent(), e.num_contexts());
                        partials.lock().unwrap().push(part);
                    }
                });
            }
        });
        for (subs, inc, n) in partials.into_inner().unwrap() {
            self.absorb(subs, inc, n);
        }
    }

    pub fn subsumptions(&self) -> BTreeMap<String, BTreeSet<String>> {
        self.subs.clone()
    }

    pub fn emit_clauses(&self) -> Vec<JClause> {
        fn ax(name: &str) -> JAtom {
            JAtom::Concept {
                concept: name.to_string(),
                term: JTerm::Var { name: "x".to_string() },
            }
        }
        let mut out = Vec::new();
        for (a, supers) in &self.subs {
            for d in supers {
                if d == "owl:Nothing" {
                    out.push(JClause { body: vec![ax(a)], head: vec![] });
                } else {
                    out.push(JClause { body: vec![ax(a)], head: vec![ax(d)] });
                }
            }
        }
        out
    }

    pub fn inconsistent(&self) -> bool {
        self.inconsistent
    }

    pub fn dropped_unsupported(&self) -> usize {
        self.dropped
    }

    pub fn num_contexts(&self) -> usize {
        self.num_ctx
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
    fn min_cardinality_recognition() {
        // P ⊑ ∃r.J1, P ⊑ ∃r.J2, J1 ⊑ J, J2 ⊑ J, J1 ⊓ J2 ⊑ ⊥, ≥2 r.J ⊑ G
        // (recognition clause: r(x,y1) ∧ J(y1) ∧ r(x,y2) ∧ J(y2) → G(x) ∨ y1≈y2)
        // ⟹ P ⊑ G: the merged-witness disjunct dies via disjointness.
        let eqa = |a: JTerm, b: JTerm| JAtom::Eq { left: a, right: b };
        let rr = run(vec![
            cl(vec![c("P", vx())], vec![r("r", vx(), fx("f1"))]),
            cl(vec![c("P", vx())], vec![c("J1", fx("f1"))]),
            cl(vec![c("P", vx())], vec![r("r", vx(), fx("f2"))]),
            cl(vec![c("P", vx())], vec![c("J2", fx("f2"))]),
            cl(vec![c("J1", vx())], vec![c("J", vx())]),
            cl(vec![c("J2", vx())], vec![c("J", vx())]),
            cl(vec![c("J1", vx()), c("J2", vx())], vec![]),
            cl(
                vec![
                    r("r", vx(), vn("y1")),
                    c("J", vn("y1")),
                    r("r", vx(), vn("y2")),
                    c("J", vn("y2")),
                ],
                vec![c("G", vx()), eqa(vn("y1"), vn("y2"))],
            ),
        ]);
        assert!(supers(&rr, "P").contains("G"), "expected P ⊑ G, got {:?}", supers(&rr, "P"));
    }

    #[test]
    fn min_cardinality_recognition_three_witnesses() {
        // Same as min_cardinality_recognition but with three pairwise-disjoint
        // witnesses and a ≥3 recognition clause (3 equality disjuncts in the
        // head).  Pins the central-strategy fact-core fix: refuting the
        // disjuncts needs per-disjunct conditional refutations from the
        // successor context ([A1,A2]→⊥ etc.), which a union core (A1,A2,A3
        // asserted at once) cannot supply.
        let eqa = |a: JTerm, b: JTerm| JAtom::Eq { left: a, right: b };
        let mut clauses = vec![cl(
            vec![
                r("r", vx(), vn("y1")),
                c("J", vn("y1")),
                r("r", vx(), vn("y2")),
                c("J", vn("y2")),
                r("r", vx(), vn("y3")),
                c("J", vn("y3")),
            ],
            vec![
                c("G", vx()),
                eqa(vn("y1"), vn("y2")),
                eqa(vn("y1"), vn("y3")),
                eqa(vn("y2"), vn("y3")),
            ],
        )];
        for i in 1..=3 {
            let (ai, fi) = (format!("A{}", i), format!("f{}", i));
            clauses.push(cl(vec![c("P", vx())], vec![r("r", vx(), fx(&fi))]));
            clauses.push(cl(vec![c("P", vx())], vec![c(&ai, fx(&fi))]));
            clauses.push(cl(vec![c(&ai, vx())], vec![c("J", vx())]));
        }
        for i in 1..=3 {
            for j in (i + 1)..=3 {
                clauses.push(cl(
                    vec![c(&format!("A{}", i), vx()), c(&format!("A{}", j), vx())],
                    vec![],
                ));
            }
        }
        let rr = run(clauses);
        assert!(supers(&rr, "P").contains("G"), "expected P ⊑ G, got {:?}", supers(&rr, "P"));
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
