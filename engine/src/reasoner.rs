//! Adapter: parse the JSON DL-clause input into the calculus representation,
//! run the disjunctive context-calculus `Engine`, and expose subsumptions,
//! derived clauses, and consistency.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use rayon::prelude::*;

use crate::calc::*;
use crate::clause::OntologyClause;
use crate::engine::{Engine, PreparedOntology, RetainedInsertBoundary, RetainedInsertStats};
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
    incomplete: bool,
    num_ctx: usize,
    /// Present only when KM_CB_LIVE_STATE requests proof evidence. Certified
    /// emission must observe one complete engine, so this mode uses the exact
    /// sequential schedule and retains that engine until serialization.
    certificate_engine: Option<Box<Engine>>,
}

#[derive(Clone)]
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

/// Exact production parser state needed to bind a typed CB source to the same
/// symbols and normalized clauses that `Reasoner::new` consumes. Keeping this
/// adapter beside `Builder` prevents the certificate compiler from duplicating
/// interning, variable allocation, sorting, or equality handling.
pub(crate) struct CbProductionInput {
    pub(crate) concept_names: Vec<String>,
    pub(crate) role_names: Vec<String>,
    pub(crate) function_ids: HashMap<String, i32>,
    pub(crate) individual_ids: HashMap<String, i32>,
    pub(crate) clauses: Vec<OntologyClause>,
    pub(crate) dropped: usize,
}

pub(crate) fn cb_production_input(input: &[JClause]) -> CbProductionInput {
    let mut builder = Builder::new();
    let clauses = builder.clauses(input);
    CbProductionInput {
        concept_names: builder.sig.concept_names,
        role_names: builder.sig.role_names,
        function_ids: builder.fn_id,
        individual_ids: builder.ind_id,
        clauses,
        dropped: builder.dropped,
    }
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
                // The normalized frontend reserves `y` for the distinguished
                // predecessor/neighbour variable used by Succ/Pred. Further
                // variables start at z₁ below. Without this branch `y` was
                // accidentally allocated as z₁, leaving Y unused and making
                // the production ontology differ from both the calculus rules
                // and the certified source encoding.
                if name == "y" {
                    return Some(Y);
                }
                if let Some(&v) = varmap.get(name) {
                    return Some(v);
                }
                // assign next neighbour variable z_i (i >= 1), i.e. ids -2, -3, ...
                let next = varmap
                    .values()
                    .filter(|&&v| is_neighbour(v) && v != Y)
                    .count() as i32
                    + 1;
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
                // Only the canonical OWL vocabulary denotes bottom. A source
                // class in another namespace may legitimately have the local
                // name `Nothing`; treating that class as bottom makes ordinary
                // subclass axioms spuriously unsatisfiable.
                if concept == "owl:Nothing" || concept == "http://www.w3.org/2002/07/owl#Nothing" {
                    self.sig.bottom = Some(iri);
                }
                Some(Pred::Concept { iri, t })
            }
            JAtom::Role {
                role,
                source,
                target,
            } => {
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

    fn clauses(&mut self, input: &[JClause]) -> Vec<OntologyClause> {
        let mut clauses = Vec::with_capacity(input.len());
        for clause in input {
            match self.clause(clause) {
                Some(clause) => clauses.push(clause),
                None => self.dropped += 1,
            }
        }
        clauses
    }
}

fn has_internal_definer_disjunction(sig: &Sig, clauses: &[OntologyClause]) -> bool {
    clauses.iter().any(|clause| {
        let mut concepts = 0usize;
        let mut internal = false;
        for literal in &clause.head {
            if let Lit::P(Pred::Concept { iri, .. }) = literal {
                concepts += 1;
                internal |= sig.is_internal(*iri);
            }
        }
        concepts >= 2 && internal
    })
}

/// Omit a private definitional family from canonical query roots while leaving
/// its predicates in the ontology. Excluded concepts can still be derived as
/// supersumers of retained roots. This changes only which subject rows are
/// requested, not the fixpoint for any retained query. The prefix is matched
/// against the engine's internal concept names, before output-name remapping.
fn exclude_query_prefix(
    sig: &Sig,
    queries: &mut Vec<Iri>,
    prefix: &str,
    retained: &std::collections::HashSet<String>,
) {
    if prefix.is_empty() {
        return;
    }
    queries.retain(|&iri| {
        let name = &sig.concept_names[iri as usize];
        !name.starts_with(prefix) || retained.contains(name)
    });
}

/// A proof boundary encountered while attempting retained CB insertion.  The
/// ordinary fresh `Reasoner` remains an exact fallback for every case.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RetainedCbBoundary {
    UnsupportedClauses { dropped: usize },
    OrderingRouterChanged,
    Engine(RetainedInsertBoundary),
    IncompleteFixpoint,
}

/// A completed sequential CB engine whose context graph survives monotone
/// ontology insertions.  Updates are evaluated on a deep fork and committed
/// only after the resumed engine reaches a complete fixpoint, so a rejected or
/// resource-bounded revision leaves the live classification unchanged.
pub(crate) struct RetainedCbReasoner {
    builder: Builder,
    engine: Engine,
    internal_definer_disjunction: bool,
}

impl RetainedCbReasoner {
    pub(crate) fn available_for_current_route() -> bool {
        std::env::var_os("KM_SPLIT").is_none()
            && std::env::var_os("KM_ROOT_ORDERED").is_none()
            && std::env::var_os("KM_QUERIES").is_none()
    }

    pub(crate) fn new(input: &[JClause]) -> RetainedCbReasoner {
        let mut builder = Builder::new();
        let clauses = builder.clauses(input);
        let internal_definer_disjunction = has_internal_definer_disjunction(&builder.sig, &clauses);
        set_seq_order_auto(internal_definer_disjunction);
        let mut engine = Engine::new(builder.sig.clone(), clauses, builder.dropped);
        let queries = engine.named_queries();
        engine.run_for(&queries);
        RetainedCbReasoner {
            builder,
            engine,
            internal_definer_disjunction,
        }
    }

    pub(crate) fn dropped_unsupported(&self) -> usize {
        self.builder.dropped
    }

    pub(crate) fn incomplete(&self) -> bool {
        self.engine.incomplete()
    }

    pub(crate) fn subsumptions(&self) -> Vec<(String, Vec<String>)> {
        self.engine.subsumptions()
    }

    pub(crate) fn inconsistent(&self) -> bool {
        self.engine.inconsistent()
    }

    pub(crate) fn add_clauses(
        &mut self,
        additions: &[JClause],
    ) -> Result<RetainedInsertStats, RetainedCbBoundary> {
        let mut builder = self.builder.clone();
        let dropped_before = builder.dropped;
        let clauses = builder.clauses(additions);
        if builder.dropped != dropped_before {
            return Err(RetainedCbBoundary::UnsupportedClauses {
                dropped: builder.dropped - dropped_before,
            });
        }

        let next_internal = self.internal_definer_disjunction
            || has_internal_definer_disjunction(&builder.sig, &clauses);
        let ordering_forced = std::env::var_os("KM_SEQ_ORDER").is_some()
            || std::env::var_os("KM_NO_SEQ_ORDER").is_some();
        if !ordering_forced && next_internal != self.internal_definer_disjunction {
            return Err(RetainedCbBoundary::OrderingRouterChanged);
        }
        if let Some(boundary) = self.engine.retained_insert_boundary(&clauses) {
            return Err(RetainedCbBoundary::Engine(boundary));
        }

        set_seq_order_auto(next_internal);
        let mut candidate = self.engine.clone();
        let mut stats = candidate.insert_ontology_clauses_retained(builder.sig.clone(), clauses);
        let queries = candidate.named_queries();
        candidate.run_for(&queries);
        if candidate.incomplete() {
            set_seq_order_auto(self.internal_definer_disjunction);
            return Err(RetainedCbBoundary::IncompleteFixpoint);
        }
        let final_counts = candidate.retained_state_counts();
        stats.contexts_after = final_counts.contexts_after;
        stats.context_clauses_after = final_counts.context_clauses_after;
        stats.edges_after = final_counts.edges_after;
        self.builder = builder;
        self.engine = candidate;
        self.internal_definer_disjunction = next_internal;
        Ok(stats)
    }
}

impl Reasoner {
    pub fn new(input: &[JClause]) -> Reasoner {
        let mut b = Builder::new();
        let clauses = b.clauses(input);
        Reasoner {
            sig0: b.sig,
            clauses0: clauses,
            dropped: b.dropped,
            subs: BTreeMap::new(),
            inconsistent: false,
            incomplete: false,
            num_ctx: 0,
            certificate_engine: None,
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
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    }

    /// Finalize the ontology once per classification.  Every engine built from
    /// the result shares one clause arena, signature and nominal-certificate
    /// map, so the query-parallel paths below no longer hold one private copy of
    /// the (up to million-clause) ontology per worker thread.
    fn prepare(&self) -> PreparedOntology {
        Engine::prepare(self.sig0.clone(), self.clauses0.clone(), self.dropped)
    }

    pub(crate) fn absorb(
        &mut self,
        subs: Vec<(String, Vec<String>)>,
        inc: bool,
        incomplete: bool,
        nctx: usize,
    ) {
        if inc {
            self.inconsistent = true;
        }
        self.incomplete |= incomplete;
        self.num_ctx += nctx;
        for (a, supers) in subs {
            let set = self.subs.entry(a).or_default();
            set.extend(supers);
        }
    }

    /// Collapse named query concepts that the input clause set explicitly proves
    /// equivalent through a strongly connected component of unit implications:
    ///
    /// `A(x) -> B(x)` and `B(x) -> A(x)`.
    ///
    /// Classifying one representative is exact for every member because the
    /// every path is a valid subclass chain, and paths in both directions make
    /// the interpretations equal in every model. This is only query scheduling:
    /// the representative runs through the unchanged calculus, and
    /// `expand_mutual_unit_aliases` restores one output row per requested
    /// concept.
    fn collapse_mutual_unit_queries(&self, queries: &[Iri]) -> (Vec<Iri>, Vec<(Iri, Vec<Iri>)>) {
        if queries.len() < 2 || std::env::var_os("KM_NO_QUERY_EQUIV").is_some() {
            return (queries.to_vec(), Vec::new());
        }

        let query_set: HashSet<Iri> = queries.iter().copied().collect();
        let mut forward = vec![Vec::<Iri>::new(); self.sig0.concept_names.len()];
        let mut reverse = vec![Vec::<Iri>::new(); self.sig0.concept_names.len()];
        let mut edge_count = 0usize;
        for clause in &self.clauses0 {
            if clause.body.len() != 1 || clause.head.len() != 1 {
                continue;
            }
            let Pred::Concept { iri: from, t: bt } = clause.body[0] else {
                continue;
            };
            let Lit::P(Pred::Concept { iri: to, t: ht }) = clause.head[0] else {
                continue;
            };
            if bt == X
                && ht == X
                && from != to
                && query_set.contains(&from)
                && query_set.contains(&to)
            {
                forward[from as usize].push(to);
                reverse[to as usize].push(from);
                edge_count += 1;
            }
        }
        if edge_count == 0 {
            return (queries.to_vec(), Vec::new());
        }

        // Iterative Kosaraju avoids recursion depth proportional to a large
        // taxonomy chain. The first pass records postorder on the forward
        // graph; the reverse pass assigns each SCC its least stable signature
        // id as representative.
        let mut seen = vec![false; forward.len()];
        let mut finish = Vec::with_capacity(queries.len());
        for &start in queries {
            if seen[start as usize] {
                continue;
            }
            seen[start as usize] = true;
            let mut stack = vec![(start, 0usize)];
            while let Some((node, next)) = stack.last_mut() {
                if *next < forward[*node as usize].len() {
                    let target = forward[*node as usize][*next];
                    *next += 1;
                    if !seen[target as usize] {
                        seen[target as usize] = true;
                        stack.push((target, 0));
                    }
                } else {
                    finish.push(*node);
                    stack.pop();
                }
            }
        }

        let mut representative = vec![Iri::MAX; forward.len()];
        for &start in finish.iter().rev() {
            if representative[start as usize] != Iri::MAX {
                continue;
            }
            let mut component = Vec::new();
            let mut stack = vec![start];
            representative[start as usize] = start;
            while let Some(node) = stack.pop() {
                component.push(node);
                for &target in &reverse[node as usize] {
                    if representative[target as usize] == Iri::MAX {
                        representative[target as usize] = start;
                        stack.push(target);
                    }
                }
            }
            let root = component.iter().copied().min().unwrap_or(start);
            for member in component {
                representative[member as usize] = root;
            }
        }

        let mut members: BTreeMap<Iri, Vec<Iri>> = BTreeMap::new();
        for &query in queries {
            let root = representative[query as usize];
            members.entry(root).or_default().push(query);
        }
        let groups: Vec<(Iri, Vec<Iri>)> = members
            .into_iter()
            .filter(|(_, group)| group.len() > 1)
            .collect();
        if groups.is_empty() {
            return (queries.to_vec(), Vec::new());
        }
        let aliases: HashSet<Iri> = groups
            .iter()
            .flat_map(|(representative, group)| {
                group
                    .iter()
                    .copied()
                    .filter(move |member| member != representative)
            })
            .collect();
        let representatives = queries
            .iter()
            .copied()
            .filter(|query| !aliases.contains(query))
            .collect();
        (representatives, groups)
    }

    /// Restore output rows omitted by `collapse_mutual_unit_queries`.
    fn expand_mutual_unit_aliases(&mut self, groups: &[(Iri, Vec<Iri>)]) {
        for &(representative, ref members) in groups {
            let representative_name = self.sig0.concept_names[representative as usize].clone();
            let Some(representative_supers) = self.subs.get(&representative_name).cloned() else {
                continue;
            };
            for &member in members {
                if member == representative {
                    continue;
                }
                let member_name = self.sig0.concept_names[member as usize].clone();
                let mut supers = representative_supers.clone();
                // Engine output omits reflexive subsumption. Translating the
                // representative row to an alias therefore removes the alias
                // and adds the representative.
                supers.remove(&member_name);
                supers.insert(representative_name.clone());
                self.subs.insert(member_name, supers);
            }
        }
    }

    /// Direction B increment 2 splitting recursion. A fresh engine per node gives
    /// branch isolation; `classify_split_run` runs the ordered (tame) closure
    /// under the current per-core `decisions` (assumed disjunct facts, reproduced
    /// because cores are deterministic); a fact-disjunction in any chain-unique
    /// context with no already-assumed disjunct is the next split point. A
    /// subsumer is forced iff it is a query unit in EVERY open branch (the
    /// intersection); a query is unsatisfiable iff every branch closes. Sound by
    /// construction (proof by cases over an exhaustive disjunction, restricted to
    /// chain-unique contexts so a shared split is a single-element case analysis);
    /// it falls back to the complete default engine on any disjunction it cannot
    /// soundly split (`Foreign`).
    fn split_recurse(
        &self,
        prepared: &PreparedOntology,
        query: Iri,
        decisions: &HashMap<Vec<Pred>, Vec<Iri>>,
        budget: &mut usize,
    ) -> SplitBranch {
        if *budget == 0 {
            return SplitBranch::Foreign;
        }
        *budget -= 1;
        if std::env::var_os("KM_PROF").is_some() && *budget % 100 == 0 {
            eprintln!(
                "KM_PROF split node budget_left={} depth={}",
                *budget,
                decisions.len()
            );
        }
        let mut e = Engine::from_prepared(prepared);
        // Branch closures run under the tame ordered regime.
        set_branch_ordered(true);
        e.set_branch_decisions(decisions.clone());
        let cf = e.classify_split_run(query);
        if cf.unsat {
            return SplitBranch::Closed;
        }
        if cf.foreign {
            return SplitBranch::Foreign;
        }
        // Pick an undecided split point: a (core, disjuncts) for which we have
        // not already assumed one of the disjuncts in that core.
        let pick = cf
            .split_points
            .iter()
            .find(|(core, ds)| match decisions.get(core) {
                None => true,
                Some(assumed) => !ds.iter().any(|d| assumed.contains(d)),
            })
            .cloned();
        match pick {
            // Leaf: no open split point → every fact-disjunction is decided, so
            // the ordered closure surfaces every forced query unit.
            None => SplitBranch::Open(cf.units.into_iter().collect()),
            Some((core, ds)) => {
                let mut acc: Option<BTreeSet<Iri>> = None;
                for &d in &ds {
                    let mut dd = decisions.clone();
                    dd.entry(core.clone()).or_default().push(d);
                    match self.split_recurse(prepared, query, &dd, budget) {
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
    fn saturate_split(&mut self, prepared: &PreparedOntology, queries: &[Iri]) {
        // Global inconsistency (⊤ ⊑ ⊥), detected once via an empty-query run
        // under the complete (unordered) regime.
        set_branch_ordered(false);
        // The branch engines below (one per search node) share the caller's
        // finalized ontology instead of re-indexing and re-cloning the clause
        // set per node.
        let (inc, inc_incomplete) = {
            let mut e = Engine::from_prepared(prepared);
            e.run_for(&[]);
            (e.inconsistent(), e.incomplete())
        };
        let node_budget: usize = std::env::var("KM_SPLIT_BUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(200_000);
        let mut subs: Vec<(String, Vec<String>)> = Vec::new();
        let mut fallback: Vec<Iri> = Vec::new();
        for &q in queries {
            let mut budget = node_budget;
            let init: HashMap<Vec<Pred>, Vec<Iri>> = HashMap::new();
            match self.split_recurse(prepared, q, &init, &mut budget) {
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
        self.absorb(subs, inc, inc_incomplete, 0);
        if !fallback.is_empty() {
            // Fallback queries run under the complete (unordered) regime.
            set_branch_ordered(false);
            let mut e = Engine::from_prepared(prepared);
            e.run_for(&fallback);
            let (s, i, incomplete, n) = (
                e.subsumptions(),
                e.inconsistent(),
                e.incomplete(),
                e.num_contexts(),
            );
            self.absorb(s, i, incomplete, n);
        }
    }

    /// Direction A (`KM_ROOT_ORDERED`, docs/ROOT-ORDERED-RESOLUTION.md):
    /// classify under the ordered same-term concept regime (root contexts for
    /// mode 1, every context for mode 2), then restore the subsumption readout
    /// completeness that the bare total order loses with the complement-guard
    /// refutation residue readout. Single-threaded (the ordering mode is
    /// thread-local), gated, default OFF.
    ///
    /// Input augmentation: for every named concept `B`, a fresh internal
    /// concept `__notb__B` and the guard clause `B ⊓ NotB ⊑ ⊥`. The guards are
    /// jointly conservative — every model of the input extends to a model of
    /// the guarded input by interpreting each `NotB` as the complement of `B` —
    /// and inert outside refutation cores (`NotB` occurs in no head, so it is
    /// never derivable). Source names beginning with `__` are escaped to
    /// `km_src_` by the frontend registry, so `__notb__` cannot collide with a
    /// source class.
    fn saturate_root_ordered(&mut self, queries: &[Iri]) {
        let mut sig = self.sig0.clone();
        let mut clauses = self.clauses0.clone();
        let mut not_of: HashMap<Iri, Iri> = HashMap::new();
        let named: Vec<Iri> = (0..sig.concept_names.len() as Iri)
            .filter(|&i| !sig.is_internal(i) && !sig.is_nothing_concept(i))
            .collect();
        for b in named {
            let name = format!("__notb__{}", sig.concept_names[b as usize]);
            let nb = sig.concept(&name);
            clauses.push(OntologyClause::new(
                vec![
                    Pred::Concept { iri: b, t: X },
                    Pred::Concept { iri: nb, t: X },
                ],
                vec![],
            ));
            not_of.insert(b, nb);
        }
        let mut e = Engine::new(sig, clauses, self.dropped);
        e.run_for(queries);
        let repaired = e.ordered_residue_repair(&not_of);
        if std::env::var_os("KM_PROF").is_some() {
            eprintln!(
                "KM_PROF root-ordered: queries={} repaired_pairs={}",
                queries.len(),
                repaired.len()
            );
            for (q, b) in &repaired {
                eprintln!(
                    "KM_PROF root-ordered repair: {} ⊑ {}",
                    short(&self.sig0.concept_names[*q as usize]),
                    short(&self.sig0.concept_names[*b as usize])
                );
            }
        }
        let (subs, inc, incomplete, n) = (
            e.subsumptions(),
            e.inconsistent(),
            e.incomplete(),
            e.num_contexts(),
        );
        self.absorb(subs, inc, incomplete, n);
        for (q, b) in repaired {
            let a = self.sig0.concept_names[q as usize].clone();
            let bn = self.sig0.concept_names[b as usize].clone();
            self.subs.entry(a).or_default().insert(bn);
        }
    }

    /// `DISJ_INT >= 1`: does any clause head hold a disjunction (>= 2 concept
    /// literals) in which at least one concept is an internal (normaliser-
    /// introduced) definer? This is the routing feature for `KM_SEQ_ORDER`:
    /// only such ontologies benefit from the Sequoia definer ordering (see
    /// `calc::set_seq_order_auto`).
    pub fn has_internal_definer_disjunction(&self) -> bool {
        has_internal_definer_disjunction(&self.sig0, &self.clauses0)
    }

    pub fn saturate(&mut self) {
        self.saturate_inner(false);
    }

    /// Classify a one-shot input and release the converted source clauses once
    /// the immutable prepared ontology and query-equivalence groups have been
    /// built.  The CLI never saturates the same `Reasoner` twice, so retaining
    /// `clauses0` there only duplicates the (up to million-clause) ontology at
    /// the context-saturation peak.  Reusable library callers keep the normal
    /// `saturate` contract above.
    pub fn saturate_releasing_input(&mut self) {
        self.saturate_inner(true);
    }

    fn saturate_inner(&mut self, release_input: bool) {
        // Auto-route the Sequoia definer ordering before any saturation (the
        // parallel workers below all read the resulting global). Env overrides
        // win inside `set_seq_order_auto`.
        set_seq_order_auto(self.has_internal_definer_disjunction());
        // Finalize the ontology once. Every engine below (the sequential run,
        // each static chunk, each work-stealing worker) is built from this one
        // immutable copy, so the clause arena, signature and nominal
        // certificates exist once per classification rather than once per
        // worker thread. The query list also comes from it, which drops the
        // throw-away engine that used to be built just to enumerate queries.
        let prepared = self.prepare();
        let certified = std::env::var_os("KM_CB_LEAN_REQUIRED").is_some();
        let mut queries = if certified {
            prepared.certification_queries()
        } else {
            prepared.named_queries()
        };
        // KM_QUERIES: classify only the named subjects listed (comma-
        // separated internal names) — the certified-EL hybrid's residue path:
        // elc answers every subject its certificate determined, and the
        // context engine resolves just the leftovers (one root context each,
        // sound and complete per query independently of the subset).
        if let Ok(qs) = std::env::var("KM_QUERIES") {
            let want: std::collections::HashSet<&str> = qs.split(',').collect();
            queries.retain(|&iri| want.contains(self.sig0.concept_names[iri as usize].as_str()));
        }
        if let Ok(prefix) = std::env::var("KM_QUERY_EXCLUDE_PREFIX") {
            let retained = std::env::var_os("KM_QUERY_RETAIN_FILE")
                .map(|path| {
                    std::fs::read_to_string(&path).unwrap_or_else(|err| {
                        panic!(
                            "KM_QUERY_RETAIN_FILE {} cannot be read: {err}",
                            path.to_string_lossy()
                        )
                    })
                })
                .map(|text| text.lines().map(str::to_owned).collect())
                .unwrap_or_default();
            exclude_query_prefix(&self.sig0, &mut queries, &prefix, &retained);
        }
        // Direction B (docs/DISJUNCTION-SPLITTING.md): split-classify when
        // KM_SPLIT is set. Gated, default OFF.
        if std::env::var_os("KM_SPLIT").is_some() {
            self.saturate_split(&prepared, &queries);
            return;
        }
        // Direction A (docs/ROOT-ORDERED-RESOLUTION.md): ordered resolution in
        // root contexts (`KM_ROOT_ORDERED=1`) or every context
        // (`KM_ROOT_ORDERED=all`) with the refutation residue readout. Gated,
        // default OFF; tests select it via `set_root_ordered` on their thread.
        let rom = match std::env::var("KM_ROOT_ORDERED").ok().as_deref() {
            Some("all") | Some("2") => 2u8,
            Some(s) if !s.is_empty() && s != "0" => 1u8,
            _ => root_ordered_mode(),
        };
        if rom != 0 {
            set_root_ordered(rom);
            self.saturate_root_ordered(&queries);
            set_root_ordered(0);
            return;
        }
        // Alias restoration has no root context for the restored aliases.
        // Certified runs retain every query root until that post-processing
        // argument is represented in Lean.
        let (queries, mutual_unit_groups) = if certified {
            (queries, Vec::new())
        } else {
            self.collapse_mutual_unit_queries(&queries)
        };
        if release_input {
            self.clauses0.clear();
            self.clauses0.shrink_to_fit();
        }
        if std::env::var_os("KM_PROF").is_some() && !mutual_unit_groups.is_empty() {
            let aliases: usize = mutual_unit_groups
                .iter()
                .map(|(_, members)| members.len() - 1)
                .sum();
            eprintln!(
                "KM_PROF query-equivalence representatives={} aliases={} groups={}",
                queries.len(),
                aliases,
                mutual_unit_groups.len()
            );
        }
        let retain_certificate_engine = std::env::var_os("KM_CB_LIVE_STATE").is_some()
            || std::env::var_os("KM_CB_LEAN_REQUIRED").is_some();
        let threads = if retain_certificate_engine {
            1
        } else {
            Self::want_threads().min(queries.len().max(1))
        };
        // Sequential path: one engine over all queries (preserves cross-query
        // context sharing -- fastest when single-threaded).
        if threads <= 1 || queries.len() <= 1 {
            let mut e = Engine::from_prepared(&prepared);
            e.run_for(&queries);
            let (subs, inc, incomplete, n) = (
                e.subsumptions(),
                e.inconsistent(),
                e.incomplete(),
                e.num_contexts(),
            );
            self.absorb(subs, inc, incomplete, n);
            self.expand_mutual_unit_aliases(&mutual_unit_groups);
            if retain_certificate_engine {
                self.certificate_engine = Some(Box::new(e));
            }
            return;
        }
        // Exact nominal roots all communicate through one ground context.  A
        // long-lived work-stealing engine accumulates the conditional labels
        // of several non-contiguous query grabs; those clauses remain logically
        // separate, but multiply later ground r-Pred joins.  Konclude likewise
        // separates nominal-influenced saturation tasks from the completed base
        // nominal label.  Until KM can physically share that completed label,
        // use one fixed contiguous query slice per engine for nominal runs.  It
        // computes the same per-query fixpoints while bounding how many
        // influenced labels coexist in one ground context.
        //
        // KM_STATIC_SCHED selects this schedule for any mechanism.  The nominal
        // route selects it automatically; KM_NOMINAL_DYNAMIC restores the
        // general work-stealing scheduler for direct A/B measurements.
        let nominal_static = std::env::var_os("KM_NOMINALS").is_some()
            && std::env::var_os("KM_NOMINAL_DYNAMIC").is_none();
        if std::env::var_os("KM_STATIC_SCHED").is_some() || nominal_static {
            let chunk_len = queries.len().div_ceil(threads);
            let chunks: Vec<&[Iri]> = queries.chunks(chunk_len).collect();
            // Diagnostic scheduling gate: finish the inter-context message
            // fixpoint periodically instead of accumulating one queue over an
            // entire static worker slice. Reusing the same Engine preserves all
            // contexts and clauses; run_for merely reaches the same monotone,
            // confluent fixpoint earlier between root batches. Default is the
            // established one-shot schedule until real-ontology A/B evidence
            // establishes a useful batch size.
            let query_batch = std::env::var("KM_QUERY_BATCH")
                .ok()
                .and_then(|value| value.parse::<usize>().ok())
                .filter(|&value| value > 0);
            let partials: Vec<(Vec<(String, Vec<String>)>, bool, bool, usize)> = chunks
                .par_iter()
                .map(|chunk| {
                    let mut e = Engine::from_prepared(&prepared);
                    if let Some(batch) = query_batch {
                        for query_batch in chunk.chunks(batch) {
                            e.run_for(query_batch);
                        }
                    } else {
                        e.run_for(chunk);
                    }
                    (
                        e.subsumptions(),
                        e.inconsistent(),
                        e.incomplete(),
                        e.num_contexts(),
                    )
                })
                .collect();
            for (subs, inc, incomplete, n) in partials {
                self.absorb(subs, inc, incomplete, n);
            }
            self.expand_mutual_unit_aliases(&mutual_unit_groups);
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
        let prepared_ref: &PreparedOntology = &prepared;
        let queries_ref: &[Iri] = &queries;
        let partials: std::sync::Mutex<Vec<(Vec<(String, Vec<String>)>, bool, bool, usize)>> =
            std::sync::Mutex::new(Vec::with_capacity(threads));
        rayon::scope(|s| {
            for _ in 0..threads {
                s.spawn(|_| {
                    let mut engine = Engine::from_prepared(prepared_ref);
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
                        engine.run_for(&queries_ref[start..end]);
                        did_any = true;
                    }
                    if did_any {
                        let part = (
                            engine.subsumptions(),
                            engine.inconsistent(),
                            engine.incomplete(),
                            engine.num_contexts(),
                        );
                        partials.lock().unwrap().push(part);
                    }
                });
            }
        });
        for (subs, inc, incomplete, n) in partials.into_inner().unwrap() {
            self.absorb(subs, inc, incomplete, n);
        }
        self.expand_mutual_unit_aliases(&mutual_unit_groups);
    }

    pub fn subsumptions(&self) -> BTreeMap<String, BTreeSet<String>> {
        self.subs.clone()
    }

    /// Move the final classification out instead of cloning it. The map holds
    /// one owned `String` per subsumption pair, so on large outputs the clone
    /// in `subsumptions()` doubles the answer exactly at peak RSS (the full
    /// map, its clone, and the serialised bytes would coexist). End-of-run
    /// extraction paths use this; the reasoner's own map is left empty, so it
    /// can be taken once per run.
    pub fn take_subsumptions(&mut self) -> BTreeMap<String, BTreeSet<String>> {
        std::mem::take(&mut self.subs)
    }

    pub fn emit_clauses(&self) -> Vec<JClause> {
        fn ax(name: &str) -> JAtom {
            JAtom::Concept {
                concept: name.to_string(),
                term: JTerm::Var {
                    name: "x".to_string(),
                },
            }
        }
        let mut out = Vec::new();
        for (a, supers) in &self.subs {
            for d in supers {
                if d == "owl:Nothing" {
                    out.push(JClause {
                        body: vec![ax(a)],
                        head: vec![],
                    });
                } else {
                    out.push(JClause {
                        body: vec![ax(a)],
                        head: vec![ax(d)],
                    });
                }
            }
        }
        out
    }

    pub fn inconsistent(&self) -> bool {
        self.inconsistent
    }

    /// True when at least one worker hit a resource backstop before reaching
    /// its monotone fixpoint. The accumulated consequences are sound but must
    /// not be exposed as a complete classification.
    pub fn incomplete(&self) -> bool {
        self.incomplete
    }

    /// Write the deterministic snapshot of the single production engine kept
    /// for CB certification. Ordinary parallel classifications intentionally
    /// have no such snapshot: merging worker answers is exact, but it is not
    /// one context graph and cannot be represented as one terminal certificate.
    pub fn write_live_terminal_snapshot(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<(), String> {
        let snapshot = self.live_terminal_snapshot()?;
        let file = std::fs::File::create(path.as_ref()).map_err(|error| {
            format!(
                "cannot create CB live-state snapshot {}: {error}",
                path.as_ref().display()
            )
        })?;
        let mut writer = std::io::BufWriter::new(file);
        serde_json::to_writer(&mut writer, &snapshot)
            .map_err(|error| format!("cannot serialize CB live-state snapshot: {error}"))?;
        use std::io::Write;
        writer
            .write_all(b"\n")
            .map_err(|error| format!("cannot finish CB live-state snapshot: {error}"))?;
        writer
            .flush()
            .map_err(|error| format!("cannot flush CB live-state snapshot: {error}"))
    }

    /// Return the deterministic terminal snapshot retained for mandatory Lean
    /// checking.  Keeping this accessor on `Reasoner` ensures the certificate
    /// bundle is built from the same engine whose answer would be published.
    pub fn live_terminal_snapshot(&self) -> Result<crate::engine::CbLiveTerminalSnapshot, String> {
        let engine = self.certificate_engine.as_deref().ok_or_else(|| {
            "CB live-state evidence requires certified mode and a sequential production run"
                .to_string()
        })?;
        if engine.incomplete() {
            return Err("CB live-state emission refused an incomplete engine".to_string());
        }
        Ok(engine.live_terminal_snapshot())
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

    #[test]
    fn normalized_variables_use_the_calculus_reserved_namespace() {
        let mut builder = Builder::new();
        let mut variables = HashMap::new();
        assert_eq!(builder.term(&vn("x"), &mut variables), Some(X));
        assert_eq!(builder.term(&vn("y"), &mut variables), Some(Y));
        assert_eq!(builder.term(&vn("z"), &mut variables), Some(zvar(1)));
        assert_eq!(builder.term(&vn("w"), &mut variables), Some(zvar(2)));
        assert_eq!(builder.term(&vn("z"), &mut variables), Some(zvar(1)));
    }

    #[test]
    fn one_shot_saturation_releases_converted_input_after_preparation() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("B", vx())]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
        ];
        let mut retained = Reasoner::new(&clauses);
        retained.saturate();
        let mut released = Reasoner::new(&clauses);
        released.saturate_releasing_input();

        assert_eq!(released.subsumptions(), retained.subsumptions());
        assert!(released.clauses0.is_empty());
        assert!(!retained.clauses0.is_empty());
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
    fn private_query_prefix_filter_retains_predicates_as_conclusions() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("urn:km:private:P", vx())]),
            cl(vec![c("urn:km:private:P", vx())], vec![c("B", vx())]),
        ];
        let reasoner = Reasoner::new(&clauses);
        let prepared = reasoner.prepare();
        let mut queries = prepared.named_queries();
        exclude_query_prefix(
            &reasoner.sig0,
            &mut queries,
            "urn:km:private:",
            &std::collections::HashSet::new(),
        );
        assert_eq!(queries.len(), 2, "only A and B remain query roots");

        let mut engine = Engine::from_prepared(&prepared);
        engine.run_for(&queries);
        let rows: BTreeMap<_, BTreeSet<_>> = engine
            .subsumptions()
            .into_iter()
            .map(|(subject, supers)| (subject, supers.into_iter().collect()))
            .collect();
        assert!(rows["A"].contains("urn:km:private:P"));
        assert!(rows["A"].contains("B"));
        assert!(!rows.contains_key("urn:km:private:P"));
    }

    #[test]
    fn private_query_prefix_filter_can_retain_selected_roots() {
        let clauses = vec![cl(vec![c("urn:km:private:P", vx())], vec![c("B", vx())])];
        let reasoner = Reasoner::new(&clauses);
        let prepared = reasoner.prepare();
        let mut queries = prepared.named_queries();
        let retained = std::collections::HashSet::from(["urn:km:private:P".to_string()]);
        exclude_query_prefix(&reasoner.sig0, &mut queries, "urn:km:private:", &retained);
        assert!(queries
            .iter()
            .any(|&iri| { reasoner.sig0.concept_names[iri as usize] == "urn:km:private:P" }));
    }

    #[test]
    fn mutual_unit_queries_share_one_representative_and_restore_rows() {
        // A ≡ B, B ≡ C and C ⊑ D. The unit SCC forms one equivalence group.
        // Classification runs one root for the
        // group, then restores the exact non-reflexive row for every alias.
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("B", vx())]),
            cl(vec![c("B", vx())], vec![c("A", vx())]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
            cl(vec![c("C", vx())], vec![c("B", vx())]),
            cl(vec![c("C", vx())], vec![c("D", vx())]),
        ];
        let mut probe = Reasoner::new(&clauses);
        let queries = probe.prepare().named_queries();
        let (representatives, groups) = probe.collapse_mutual_unit_queries(&queries);
        assert_eq!(queries.len(), 4);
        assert_eq!(representatives.len(), 2, "A/B/C plus D need two roots");
        assert_eq!(groups.len(), 1);

        probe.saturate();
        assert_eq!(
            supers(&probe, "A"),
            ["B", "C", "D"].into_iter().map(String::from).collect()
        );
        assert_eq!(
            supers(&probe, "B"),
            ["A", "C", "D"].into_iter().map(String::from).collect()
        );
        assert_eq!(
            supers(&probe, "C"),
            ["A", "B", "D"].into_iter().map(String::from).collect()
        );
    }

    #[test]
    fn cyclic_unit_paths_collapse_without_direct_opposite_edges() {
        // No edge has its direct opposite, but A -> B -> C -> A proves all
        // three concepts equivalent. The SCC scheduler must see that proof.
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("B", vx())]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
            cl(vec![c("C", vx())], vec![c("A", vx())]),
            cl(vec![c("C", vx())], vec![c("D", vx())]),
        ];
        let mut probe = Reasoner::new(&clauses);
        let queries = probe.prepare().named_queries();
        let (representatives, groups) = probe.collapse_mutual_unit_queries(&queries);
        assert_eq!(representatives.len(), 2);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].1.len(), 3);

        probe.saturate();
        assert_eq!(
            supers(&probe, "A"),
            ["B", "C", "D"].into_iter().map(String::from).collect()
        );
        assert_eq!(
            supers(&probe, "B"),
            ["A", "C", "D"].into_iter().map(String::from).collect()
        );
        assert_eq!(
            supers(&probe, "C"),
            ["A", "B", "D"].into_iter().map(String::from).collect()
        );
    }

    #[test]
    fn one_way_unit_implications_do_not_collapse_queries() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("B", vx())]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
        ];
        let probe = Reasoner::new(&clauses);
        let queries = probe.prepare().named_queries();
        let (representatives, groups) = probe.collapse_mutual_unit_queries(&queries);
        assert_eq!(representatives, queries);
        assert!(groups.is_empty());
    }

    #[test]
    fn repeated_run_for_batches_match_one_shot_fixpoint() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![r("R", vx(), fx("f"))]),
            cl(vec![c("A", vx())], vec![c("B", fx("f"))]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
            cl(
                vec![r("R", vx(), vn("y")), c("C", vn("y"))],
                vec![c("D", vx())],
            ),
            cl(vec![c("E", vx())], vec![c("A", vx())]),
        ];
        let reasoner = Reasoner::new(&clauses);
        let prepared = reasoner.prepare();
        let queries = prepared.named_queries();

        let mut one_shot = Engine::from_prepared(&prepared);
        one_shot.run_for(&queries);
        let mut batched = Engine::from_prepared(&prepared);
        for batch in queries.chunks(2) {
            batched.run_for(batch);
        }

        assert_eq!(batched.subsumptions(), one_shot.subsumptions());
        assert_eq!(batched.inconsistent(), one_shot.inconsistent());
        assert_eq!(batched.incomplete(), one_shot.incomplete());
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
    fn direct_bottom_class_reported_unsat() {
        let rr = run(vec![
            cl(vec![c("C", vx())], vec![]),
            cl(vec![c("D", vx())], vec![c("C", vx())]),
            cl(vec![c("A", vx())], vec![c("B", vx())]),
        ]);
        assert!(supers(&rr, "C").contains("owl:Nothing"));
        assert!(supers(&rr, "D").contains("owl:Nothing"));
        assert!(!supers(&rr, "A").contains("owl:Nothing"));
        assert!(!supers(&rr, "B").contains("owl:Nothing"));
        assert!(supers(&rr, "A").contains("B"));
    }

    #[test]
    fn user_class_named_nothing_is_not_bottom() {
        let rr = run(vec![
            cl(vec![c("A", vx())], vec![c("Nothing", vx())]),
            cl(vec![c("B", vx())], vec![c("A", vx())]),
        ]);
        assert!(supers(&rr, "A").contains("Nothing"));
        assert!(supers(&rr, "B").contains("A"));
        assert!(!supers(&rr, "A").contains("owl:Nothing"));
        assert!(!supers(&rr, "B").contains("owl:Nothing"));
        assert!(!rr.inconsistent());
    }

    #[test]
    fn disjunction_no_spurious_subsumption() {
        // A ⊑ B ⊔ C must NOT yield A ⊑ B or A ⊑ C (this was the soundness bug).
        let rr = run(vec![cl(
            vec![c("A", vx())],
            vec![c("B", vx()), c("C", vx())],
        )]);
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
            cl(
                vec![r("R", vx(), vn("y")), c("C", vn("y"))],
                vec![c("D", vx())],
            ),
        ]);
        assert!(
            supers(&rr, "A").contains("D"),
            "expected A ⊑ D, got {:?}",
            supers(&rr, "A")
        );
    }

    #[test]
    fn take_subsumptions_moves_the_final_map_once() {
        // The moving accessor must return exactly the map the cloning accessor
        // returns (end-of-run extraction paths use it to avoid doubling the
        // answer at peak RSS), and it can only be taken once.
        let mut rr = run(vec![
            cl(vec![c("A", vx())], vec![c("B", vx())]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
        ]);
        let cloned = rr.subsumptions();
        let taken = rr.take_subsumptions();
        assert_eq!(cloned, taken);
        assert!(taken
            .get("A")
            .is_some_and(|s| s.contains("B") && s.contains("C")));
        assert!(rr.subsumptions().is_empty());
        assert!(rr.take_subsumptions().is_empty());
    }

    /// KM_ROOT_ORDERED test driver: select the mode on this thread (the
    /// gated driver is single-threaded, so the thread-local is authoritative)
    /// and classify. `saturate` resets the mode before returning.
    fn run_root_ordered(clauses: Vec<JClause>, mode: u8) -> Reasoner {
        let mut rr = Reasoner::new(&clauses);
        set_root_ordered(mode);
        rr.saturate();
        rr
    }

    /// The `KM_ORDERED_ALL` trap (calc.rs verdict): with `X` interned before
    /// `B`, the entailed named unit `B` is non-maximal behind the maximal `B`
    /// in `⊤ → X ∨ B`... precisely: from `A ⊑ X ⊔ B` and `X ⊑ B`, `B` is
    /// entailed, but under the total order `B` is maximal and unresolvable, so
    /// `X ⊑ B` never fires and `⊤ → B(x)` never surfaces. The refutation
    /// residue readout must recover it in both modes.
    #[test]
    fn root_ordered_recovers_trapped_named_unit() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("X", vx()), c("B", vx())]),
            cl(vec![c("X", vx())], vec![c("B", vx())]),
        ];
        for mode in [1u8, 2u8] {
            let rr = run_root_ordered(clauses.clone(), mode);
            assert!(
                supers(&rr, "A").contains("B"),
                "mode {}: expected A ⊑ B (trapped unit recovered), got {:?}",
                mode,
                supers(&rr, "A")
            );
            assert!(
                !supers(&rr, "A").contains("X"),
                "mode {}: A ⊑ X is not entailed, got {:?}",
                mode,
                supers(&rr, "A")
            );
            assert!(!rr.inconsistent());
        }
    }

    /// Same ontology with the opposite interning order (`B` before `X`): the
    /// maximal disjunct `X` IS resolvable, so ordered resolution consumes it
    /// directly and the unit surfaces without repair. Result must be identical.
    #[test]
    fn root_ordered_trap_other_interning_order() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("B", vx()), c("X", vx())]),
            cl(vec![c("X", vx())], vec![c("B", vx())]),
        ];
        for mode in [1u8, 2u8] {
            let rr = run_root_ordered(clauses.clone(), mode);
            assert!(supers(&rr, "A").contains("B"));
            assert!(!supers(&rr, "A").contains("X"));
        }
    }

    /// Trapped unit chained through a second named super: A ⊑ X ⊔ B, X ⊑ B,
    /// B ⊑ C entails A ⊑ B and A ⊑ C; under the order both are trapped
    /// (C maximal-unresolvable in ⊤ → X ∨ C) and both must be recovered.
    #[test]
    fn root_ordered_recovers_chained_trapped_units() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("X", vx()), c("B", vx())]),
            cl(vec![c("X", vx())], vec![c("B", vx())]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
        ];
        for mode in [1u8, 2u8] {
            let rr = run_root_ordered(clauses.clone(), mode);
            let s = supers(&rr, "A");
            assert!(s.contains("B") && s.contains("C"), "mode {mode}: got {s:?}");
            assert!(!s.contains("X"), "mode {mode}: got {s:?}");
        }
    }

    /// The soundness direction: a bare disjunction must not turn into a
    /// subsumption through the refutation readout (candidates that are not
    /// entailed must fail their refutation).
    #[test]
    fn root_ordered_no_spurious_subsumption() {
        let clauses = vec![cl(vec![c("A", vx())], vec![c("B", vx()), c("C", vx())])];
        for mode in [1u8, 2u8] {
            let rr = run_root_ordered(clauses.clone(), mode);
            assert!(!supers(&rr, "A").contains("B"));
            assert!(!supers(&rr, "A").contains("C"));
            assert!(!rr.inconsistent());
        }
    }

    /// Exclusive global disjunction (the live-family shape): ⊤ ⊑ P ⊔ N with
    /// P ⊓ N ⊑ ⊥ and A ⊑ P. Expect exactly A ⊑ P (never the sibling), and no
    /// inconsistency, in both modes.
    #[test]
    fn root_ordered_exclusive_global_disjunction() {
        let clauses = vec![
            cl(vec![], vec![c("P", vx()), c("N", vx())]),
            cl(vec![c("P", vx()), c("N", vx())], vec![]),
            cl(vec![c("A", vx())], vec![c("P", vx())]),
        ];
        for mode in [1u8, 2u8] {
            let rr = run_root_ordered(clauses.clone(), mode);
            let s = supers(&rr, "A");
            assert!(s.contains("P"), "mode {mode}: got {s:?}");
            assert!(!s.contains("N"), "mode {mode}: got {s:?}");
            assert!(!rr.inconsistent());
        }
    }

    /// Unsat query under the ordered regime: the ⊥ readout is order-robust.
    #[test]
    fn root_ordered_unsat_query() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("B", vx())]),
            cl(vec![c("A", vx())], vec![c("C", vx())]),
            cl(vec![c("B", vx()), c("C", vx())], vec![]),
        ];
        for mode in [1u8, 2u8] {
            let rr = run_root_ordered(clauses.clone(), mode);
            assert!(supers(&rr, "A").contains("owl:Nothing"), "mode {mode}");
        }
    }

    /// Disjunction over a successor (the historical KM_ORDERED_ALL probe,
    /// calc.rs + lean disjsucc): A ⊑ ∃R.Q, Q ⊑ C ⊔ D, C ⊑ E, D ⊑ E,
    /// ∃R.E ⊑ G ⟹ A ⊑ G. Mode 1 leaves successors on the complete
    /// incomparable regime; mode 2 orders them and must still export G via the
    /// disjunct-by-disjunct consumption chain (pred triggers sit at the bottom
    /// of the order).
    #[test]
    fn root_ordered_disjunction_over_successor() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![r("R", vx(), fx("f"))]),
            cl(vec![c("A", vx())], vec![c("Q", fx("f"))]),
            cl(vec![c("Q", vx())], vec![c("C", vx()), c("D", vx())]),
            cl(vec![c("C", vx())], vec![c("E", vx())]),
            cl(vec![c("D", vx())], vec![c("E", vx())]),
            cl(
                vec![r("R", vx(), vn("y")), c("E", vn("y"))],
                vec![c("G", vx())],
            ),
        ];
        for mode in [1u8, 2u8] {
            let rr = run_root_ordered(clauses.clone(), mode);
            assert!(
                supers(&rr, "A").contains("G"),
                "mode {}: expected A ⊑ G, got {:?}",
                mode,
                supers(&rr, "A")
            );
        }
    }

    /// End-to-end equivalence on a mixed ontology (disjunction + existential +
    /// disjointness + hierarchy): the ordered modes must produce exactly the
    /// default engine's subsumption map.
    #[test]
    fn root_ordered_matches_default_engine() {
        let clauses = vec![
            cl(vec![c("A", vx())], vec![c("X", vx()), c("B", vx())]),
            cl(vec![c("X", vx())], vec![c("B", vx())]),
            cl(vec![c("B", vx())], vec![c("C", vx())]),
            cl(vec![c("H", vx())], vec![r("R", vx(), fx("f"))]),
            cl(vec![c("H", vx())], vec![c("Q", fx("f"))]),
            cl(vec![c("Q", vx())], vec![c("C2", vx()), c("D2", vx())]),
            cl(vec![c("C2", vx())], vec![c("E", vx())]),
            cl(vec![c("D2", vx())], vec![c("E", vx())]),
            cl(
                vec![r("R", vx(), vn("y")), c("E", vn("y"))],
                vec![c("G", vx())],
            ),
            cl(vec![], vec![c("P", vx()), c("N", vx())]),
            cl(vec![c("P", vx()), c("N", vx())], vec![]),
            cl(vec![c("U", vx())], vec![c("P", vx())]),
            cl(vec![c("W", vx())], vec![c("B", vx())]),
            cl(vec![c("W", vx())], vec![c("N", vx())]),
        ];
        let base = run(clauses.clone());
        for mode in [1u8, 2u8] {
            let rr = run_root_ordered(clauses.clone(), mode);
            assert_eq!(
                rr.subsumptions(),
                base.subsumptions(),
                "mode {mode}: ordered readout differs from the default engine"
            );
            assert_eq!(rr.inconsistent(), base.inconsistent(), "mode {mode}");
        }
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
                vec![
                    eqa(fx("f"), fx("g")),
                    eqa(fx("f"), fx("h")),
                    eqa(fx("g"), fx("h")),
                ],
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
        assert!(
            supers(&rr, "P").contains("G"),
            "expected P ⊑ G, got {:?}",
            supers(&rr, "P")
        );
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
        assert!(
            supers(&rr, "P").contains("G"),
            "expected P ⊑ G, got {:?}",
            supers(&rr, "P")
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
        assert!(
            supers(&rr, "B").contains("A"),
            "expected B ⊑ A, got {:?}",
            supers(&rr, "B")
        );
    }

    #[test]
    fn incomplete_worker_state_is_sticky() {
        let mut rr = Reasoner::new(&[]);
        assert!(!rr.incomplete());
        rr.absorb(Vec::new(), false, true, 0);
        assert!(rr.incomplete());
        rr.absorb(Vec::new(), false, false, 0);
        assert!(rr.incomplete());
    }
}
