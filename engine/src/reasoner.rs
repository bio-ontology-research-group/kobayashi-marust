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
    incomplete: bool,
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
                if short(concept) == "Nothing" {
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
            incomplete: false,
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
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    }

    fn build_engine(&self) -> Engine {
        Engine::new(self.sig0.clone(), self.clauses0.clone(), self.dropped)
    }

    fn absorb(
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
        let mut e = self.build_engine();
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
        let (inc, inc_incomplete) = {
            let mut e = self.build_engine();
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
            match self.split_recurse(q, &init, &mut budget) {
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
            let mut e = self.build_engine();
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
        self.clauses0.iter().any(|c| {
            let mut nconc = 0usize;
            let mut has_internal = false;
            for l in &c.head {
                if let Lit::P(Pred::Concept { iri, .. }) = l {
                    nconc += 1;
                    if self.sig0.is_internal(*iri) {
                        has_internal = true;
                    }
                }
            }
            nconc >= 2 && has_internal
        })
    }

    pub fn saturate(&mut self) {
        // Auto-route the Sequoia definer ordering before any saturation (the
        // parallel workers below all read the resulting global). Env overrides
        // win inside `set_seq_order_auto`.
        set_seq_order_auto(self.has_internal_definer_disjunction());
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
        let threads = Self::want_threads().min(queries.len().max(1));
        // Sequential path: one engine over all queries (preserves cross-query
        // context sharing -- fastest when single-threaded).
        if threads <= 1 || queries.len() <= 1 {
            let mut e = self.build_engine();
            e.run_for(&queries);
            let (subs, inc, incomplete, n) = (
                e.subsumptions(),
                e.inconsistent(),
                e.incomplete(),
                e.num_contexts(),
            );
            self.absorb(subs, inc, incomplete, n);
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
            let partials: Vec<(Vec<(String, Vec<String>)>, bool, bool, usize)> = chunks
                .par_iter()
                .map(|chunk| {
                    let mut e = self.build_engine();
                    e.run_for(chunk);
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
        let partials: std::sync::Mutex<Vec<(Vec<(String, Vec<String>)>, bool, bool, usize)>> =
            std::sync::Mutex::new(Vec::with_capacity(threads));
        rayon::scope(|s| {
            for _ in 0..threads {
                s.spawn(|_| {
                    let mut engine = this.build_engine();
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
    }

    pub fn subsumptions(&self) -> BTreeMap<String, BTreeSet<String>> {
        self.subs.clone()
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
