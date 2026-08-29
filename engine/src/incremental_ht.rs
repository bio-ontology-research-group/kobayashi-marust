//! Exact incremental classification for the validated direct-clause HT arm.
//!
//! The adapter keeps three kinds of reusable evidence:
//!
//! * monotone verdicts (UNSAT under addition, SAT under deletion);
//! * clash-free completion-graph snapshots, replayed against monotone additions;
//! * signature-component dependencies, used to leave independent probes intact.
//!
//! Graphs are retained only for the global and per-class probes. Pair
//! countermodel probes keep their verdict but not another full graph, avoiding
//! quadratic graph retention.
//!
//! Every uncertain case runs a fresh complete HT probe. A failed model replay is
//! never interpreted as UNSAT, and a declined fresh probe aborts the transaction.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use crate::incremental::{IncrementalReasoningError, IncrementalResult};
use crate::json_io::{JAtom, JClause, JTerm};
use crate::orchestrate::cb_to_ht::{self, CardDefJson, HAtom, HtClause, NativeAboxJson, TInput};
use crate::tableau::hypertableau::{Ht, HtModelSnapshot};
use crate::tableau::{Atom, CLit, Clause, C, R};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum HtChangeKind {
    Addition,
    Removal,
    Replacement,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct HtDeltaStats {
    pub reused_probes: usize,
    pub resumed_models: usize,
    pub rebuilt_probes: usize,
    pub reused_edges: usize,
    pub new_edges: usize,
    pub reused_subsumptions: usize,
    pub new_subsumptions: usize,
}

#[derive(Clone)]
struct ProbeRecord {
    /// `true` means the probe seed is satisfiable.
    sat: bool,
    snapshot: Option<HtModelSnapshot>,
    root_label: BTreeSet<String>,
    snapshot_layout: u64,
}

impl ProbeRecord {
    fn edge_count(&self) -> usize {
        self.snapshot
            .as_ref()
            .map_or(0, HtModelSnapshot::edge_count)
    }
}

#[derive(Clone)]
struct CompiledHt {
    concepts: Vec<String>,
    roles: Vec<String>,
    clauses: Vec<HtClause>,
    queries: Vec<C>,
    number: bool,
    nominals: Vec<C>,
    native_abox: NativeAboxJson,
    card_defs: Vec<CardDefJson>,
    chains: Vec<(R, R, R)>,
    transitive: Vec<R>,
}

impl CompiledHt {
    fn instantiate(&self) -> Result<Ht, IncrementalReasoningError> {
        let mut clauses = Vec::with_capacity(self.clauses.len());
        for clause in &self.clauses {
            clauses.push(Clause::new(
                clause
                    .body
                    .iter()
                    .map(atom_of)
                    .collect::<Result<Vec<_>, _>>()?,
                clause
                    .head
                    .iter()
                    .map(atom_of)
                    .collect::<Result<Vec<_>, _>>()?,
            ));
        }
        let mut ht = Ht::new(clauses);
        ht.set_number(self.number);
        ht.set_nominals(self.nominals.clone());
        if self.native_abox.complete {
            let individuals = self
                .native_abox
                .individuals
                .iter()
                .map(|individual| {
                    Ok((
                        compact_concepts(&individual.proxies)?,
                        compact_concepts(&individual.assertions)?,
                    ))
                })
                .collect::<Result<Vec<_>, IncrementalReasoningError>>()?;
            let roles = self
                .native_abox
                .role_assertions
                .iter()
                .map(|&(role, source, target)| Ok((compact_role(role)?, source, target)))
                .collect::<Result<Vec<_>, IncrementalReasoningError>>()?;
            ht.set_native_abox(individuals, self.native_abox.different.clone(), roles);
        }
        if !self.chains.is_empty() || !self.transitive.is_empty() {
            ht.set_chains(self.chains.clone(), self.transitive.clone());
        }
        if !self.card_defs.is_empty() {
            let definitions = self
                .card_defs
                .iter()
                .map(|definition| {
                    Ok((
                        compact_concept(definition.marker)?,
                        definition.min,
                        definition.n,
                        compact_role(definition.role)?,
                        compact_concept(definition.filler)?,
                        definition.exact,
                    ))
                })
                .collect::<Result<Vec<_>, IncrementalReasoningError>>()?;
            ht.set_card_defs_raw(&definitions);
        }
        // These two paths change only worklist maintenance. They are already
        // differentially checked by the HT suite and make repeated probes viable.
        ht.set_fast_tableau();
        Ok(ht)
    }

    fn query_names(&self) -> Vec<String> {
        self.queries
            .iter()
            .filter_map(|&id| self.concepts.get(id as usize).cloned())
            .collect()
    }

    fn id_of(&self, name: &str) -> Option<C> {
        self.concepts
            .iter()
            .position(|candidate| candidate == name)
            .and_then(|id| C::try_from(id).ok())
    }

    fn name_of(&self, id: C) -> Option<&str> {
        self.concepts.get(id as usize).map(String::as_str)
    }

    fn stable_prefix_of(&self, next: &Self) -> bool {
        next.concepts.starts_with(&self.concepts)
            && next.roles.starts_with(&self.roles)
            && next.clauses.starts_with(&self.clauses)
            && self.number == next.number
            && self.nominals == next.nominals
            && self.native_abox == next.native_abox
            && self.card_defs == next.card_defs
            && self.chains == next.chains
            && self.transitive == next.transitive
    }
}

pub(crate) struct IncrementalHtClassifier {
    source_clauses: Vec<JClause>,
    compiled: CompiledHt,
    layout: u64,
    global: ProbeRecord,
    classes: BTreeMap<String, ProbeRecord>,
    pairs: BTreeMap<(String, String), ProbeRecord>,
    result: IncrementalResult,
}

impl IncrementalHtClassifier {
    pub(crate) fn new(clauses: &[JClause]) -> Result<Self, IncrementalReasoningError> {
        let compiled = compile_direct_ht(clauses)?;
        Self::from_compiled(clauses, compiled)
    }

    pub(crate) fn new_typed(
        clauses: &[JClause],
        input: TInput,
    ) -> Result<Self, IncrementalReasoningError> {
        let compiled = compile_typed_ht(input)?;
        Self::from_compiled(clauses, compiled)
    }

    fn from_compiled(
        clauses: &[JClause],
        compiled: CompiledHt,
    ) -> Result<Self, IncrementalReasoningError> {
        let layout = 0;
        let mut ht = compiled.instantiate()?;
        let global = fresh_probe(&mut ht, &[], &compiled, layout, true)?;
        let mut state = IncrementalHtClassifier {
            source_clauses: clauses.to_vec(),
            compiled,
            layout,
            global,
            classes: BTreeMap::new(),
            pairs: BTreeMap::new(),
            result: IncrementalResult {
                subsumptions: BTreeMap::new(),
                inconsistent: false,
                dropped: 0,
                unresolved: Vec::new(),
            },
        };
        state.classify_fresh_rest(&mut ht)?;
        Ok(state)
    }

    pub(crate) fn result(&self) -> IncrementalResult {
        self.result.clone()
    }

    pub(crate) fn pair_count(&self) -> usize {
        self.result.subsumptions.values().map(Vec::len).sum()
    }

    pub(crate) fn updated(
        &self,
        candidate: &[JClause],
        changed_clauses: &[JClause],
        kind: HtChangeKind,
    ) -> Result<(Self, HtDeltaStats), IncrementalReasoningError> {
        let compiled = compile_direct_ht(candidate)?;
        self.updated_compiled(candidate, changed_clauses, kind, compiled)
    }

    pub(crate) fn updated_typed(
        &self,
        candidate: &[JClause],
        changed_clauses: &[JClause],
        kind: HtChangeKind,
        input: TInput,
    ) -> Result<(Self, HtDeltaStats), IncrementalReasoningError> {
        let compiled = compile_typed_ht(input)?;
        self.updated_compiled(candidate, changed_clauses, kind, compiled)
    }

    fn updated_compiled(
        &self,
        candidate: &[JClause],
        changed_clauses: &[JClause],
        kind: HtChangeKind,
        compiled: CompiledHt,
    ) -> Result<(Self, HtDeltaStats), IncrementalReasoningError> {
        let layout = self.layout.wrapping_add(1);
        let resume_compatible =
            kind == HtChangeKind::Addition && self.compiled.stable_prefix_of(&compiled);
        let affected = affected_concepts(
            &self.source_clauses,
            candidate,
            changed_clauses,
            &compiled.query_names(),
        );
        let mut stats = HtDeltaStats::default();
        let mut ht = compiled.instantiate()?;

        let global = update_probe(
            Some(&self.global),
            &mut ht,
            &[],
            &compiled,
            self.layout,
            layout,
            kind,
            true,
            resume_compatible,
            true,
            &mut stats,
        )?;

        let mut next = IncrementalHtClassifier {
            source_clauses: candidate.to_vec(),
            compiled,
            layout,
            global,
            classes: BTreeMap::new(),
            pairs: BTreeMap::new(),
            result: IncrementalResult {
                subsumptions: BTreeMap::new(),
                inconsistent: false,
                dropped: 0,
                unresolved: Vec::new(),
            },
        };

        if !next.global.sat {
            next.result = result_from_probes(
                &next.compiled.query_names(),
                &next.global,
                &next.classes,
                &next.pairs,
            );
            finish_pair_stats(&self.result, &next.result, &mut stats);
            return Ok((next, stats));
        }

        let queries = next.compiled.query_names();
        for name in &queries {
            let id =
                next.compiled
                    .id_of(name)
                    .ok_or_else(|| IncrementalReasoningError::HtDeferred {
                        detail: format!("HT query {name} has no stable concept id"),
                    })?;
            let is_affected = affected.contains(name);
            let record = update_probe(
                self.classes.get(name),
                &mut ht,
                &[CLit::pos(id)],
                &next.compiled,
                self.layout,
                layout,
                kind,
                is_affected,
                resume_compatible,
                true,
                &mut stats,
            )?;
            next.classes.insert(name.clone(), record);
        }

        let satisfiable: BTreeSet<String> = next
            .classes
            .iter()
            .filter_map(|(name, probe)| probe.sat.then_some(name.clone()))
            .collect();
        for subject in &queries {
            let Some(class_probe) = next.classes.get(subject) else {
                continue;
            };
            if !class_probe.sat {
                continue;
            }
            for object in class_probe
                .root_label
                .iter()
                .filter(|object| *object != subject && satisfiable.contains(*object))
            {
                let Some(subject_id) = next.compiled.id_of(subject) else {
                    continue;
                };
                let Some(object_id) = next.compiled.id_of(object) else {
                    continue;
                };
                let key = (subject.clone(), object.clone());
                let is_affected = affected.contains(subject) || affected.contains(object);
                let record = update_probe(
                    self.pairs.get(&key),
                    &mut ht,
                    &[CLit::pos(subject_id), CLit::neg(object_id)],
                    &next.compiled,
                    self.layout,
                    layout,
                    kind,
                    is_affected,
                    resume_compatible,
                    false,
                    &mut stats,
                )?;
                next.pairs.insert(key, record);
            }
        }

        next.result = result_from_probes(&queries, &next.global, &next.classes, &next.pairs);
        finish_pair_stats(&self.result, &next.result, &mut stats);
        Ok((next, stats))
    }

    fn classify_fresh_rest(&mut self, ht: &mut Ht) -> Result<(), IncrementalReasoningError> {
        let queries = self.compiled.query_names();
        if !self.global.sat {
            self.result = result_from_probes(&queries, &self.global, &self.classes, &self.pairs);
            return Ok(());
        }

        for name in &queries {
            let id =
                self.compiled
                    .id_of(name)
                    .ok_or_else(|| IncrementalReasoningError::HtDeferred {
                        detail: format!("HT query {name} has no stable concept id"),
                    })?;
            let probe = fresh_probe(ht, &[CLit::pos(id)], &self.compiled, self.layout, true)?;
            self.classes.insert(name.clone(), probe);
        }

        let satisfiable: BTreeSet<String> = self
            .classes
            .iter()
            .filter_map(|(name, probe)| probe.sat.then_some(name.clone()))
            .collect();
        for subject in &queries {
            let Some(class_probe) = self.classes.get(subject) else {
                continue;
            };
            if !class_probe.sat {
                continue;
            }
            for object in class_probe
                .root_label
                .iter()
                .filter(|object| *object != subject && satisfiable.contains(*object))
            {
                let subject_id = self.compiled.id_of(subject).unwrap();
                let object_id = self.compiled.id_of(object).unwrap();
                let probe = fresh_probe(
                    ht,
                    &[CLit::pos(subject_id), CLit::neg(object_id)],
                    &self.compiled,
                    self.layout,
                    false,
                )?;
                self.pairs.insert((subject.clone(), object.clone()), probe);
            }
        }
        self.result = result_from_probes(&queries, &self.global, &self.classes, &self.pairs);
        Ok(())
    }
}

fn fresh_probe(
    ht: &mut Ht,
    seed: &[CLit],
    compiled: &CompiledHt,
    layout: u64,
    retain_snapshot: bool,
) -> Result<ProbeRecord, IncrementalReasoningError> {
    let (sat, snapshot) = if retain_snapshot {
        let Some(result) = ht.consistent_with_snapshot(seed) else {
            return Err(IncrementalReasoningError::HtDeferred {
                detail: "fresh HT probe reached an unsupported or incomplete boundary".into(),
            });
        };
        result
    } else {
        let Some(sat) = ht.consistent(seed) else {
            return Err(IncrementalReasoningError::HtDeferred {
                detail: "fresh HT probe reached an unsupported or incomplete boundary".into(),
            });
        };
        (sat, None)
    };
    Ok(record_from_snapshot(sat, snapshot, compiled, layout))
}

#[allow(clippy::too_many_arguments)]
fn update_probe(
    old: Option<&ProbeRecord>,
    ht: &mut Ht,
    seed: &[CLit],
    compiled: &CompiledHt,
    old_layout: u64,
    new_layout: u64,
    kind: HtChangeKind,
    affected: bool,
    resume_compatible: bool,
    retain_snapshot: bool,
    stats: &mut HtDeltaStats,
) -> Result<ProbeRecord, IncrementalReasoningError> {
    let Some(old) = old else {
        stats.rebuilt_probes += 1;
        return fresh_probe(ht, seed, compiled, new_layout, retain_snapshot);
    };

    if !affected {
        stats.reused_probes += 1;
        return Ok(old.clone());
    }

    match kind {
        HtChangeKind::Addition if !old.sat => {
            // UNSAT is monotone under axiom addition.
            stats.reused_probes += 1;
            return Ok(old.clone());
        }
        HtChangeKind::Removal if old.sat => {
            // The old model remains a model after constraints are removed.
            stats.reused_probes += 1;
            return Ok(old.clone());
        }
        HtChangeKind::Addition
            if resume_compatible && old.snapshot_layout == old_layout && old.snapshot.is_some() =>
        {
            let prior_edges = old.edge_count();
            if let Some(snapshot) =
                ht.resume_satisfiable_model(old.snapshot.as_ref().expect("checked above"))
            {
                let next_edges = snapshot.edge_count();
                stats.reused_probes += 1;
                stats.resumed_models += 1;
                stats.reused_edges += prior_edges.min(next_edges);
                stats.new_edges += next_edges.saturating_sub(prior_edges);
                return Ok(record_from_snapshot(
                    true,
                    Some(snapshot),
                    compiled,
                    new_layout,
                ));
            }
        }
        HtChangeKind::Addition | HtChangeKind::Removal | HtChangeKind::Replacement => {}
    }

    stats.rebuilt_probes += 1;
    fresh_probe(ht, seed, compiled, new_layout, retain_snapshot)
}

fn record_from_snapshot(
    sat: bool,
    snapshot: Option<HtModelSnapshot>,
    compiled: &CompiledHt,
    layout: u64,
) -> ProbeRecord {
    let root_label = snapshot
        .as_ref()
        .map(|snapshot| {
            snapshot
                .root_positive_label()
                .into_iter()
                .filter_map(|id| compiled.name_of(id).map(str::to_string))
                .collect()
        })
        .unwrap_or_default();
    ProbeRecord {
        sat,
        snapshot,
        root_label,
        snapshot_layout: layout,
    }
}

fn result_from_probes(
    queries: &[String],
    global: &ProbeRecord,
    classes: &BTreeMap<String, ProbeRecord>,
    pairs: &BTreeMap<(String, String), ProbeRecord>,
) -> IncrementalResult {
    let mut relation: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    if !global.sat {
        for query in queries {
            relation
                .entry(query.clone())
                .or_default()
                .insert("owl:Nothing".into());
        }
    } else {
        // Match the EL/CB classification contract: every queried named class is
        // present, including satisfiable leaf classes with no proper reported
        // superclass.
        for query in queries {
            relation.entry(query.clone()).or_default();
        }
        for (query, probe) in classes {
            if !probe.sat {
                relation
                    .entry(query.clone())
                    .or_default()
                    .insert("owl:Nothing".into());
            }
        }
        for ((subject, object), probe) in pairs {
            if !probe.sat {
                relation
                    .entry(subject.clone())
                    .or_default()
                    .insert(object.clone());
            }
        }
        transitive_close(&mut relation);
    }
    IncrementalResult {
        subsumptions: relation
            .into_iter()
            .map(|(subject, objects)| (subject, objects.into_iter().collect()))
            .collect(),
        inconsistent: !global.sat,
        dropped: 0,
        unresolved: Vec::new(),
    }
}

fn transitive_close(relation: &mut BTreeMap<String, BTreeSet<String>>) {
    loop {
        let snapshot = relation.clone();
        let mut changed = false;
        for objects in relation.values_mut() {
            let direct: Vec<String> = objects.iter().cloned().collect();
            for object in direct {
                if let Some(next) = snapshot.get(&object) {
                    for successor in next {
                        changed |= objects.insert(successor.clone());
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
}

fn finish_pair_stats(old: &IncrementalResult, new: &IncrementalResult, stats: &mut HtDeltaStats) {
    let old_pairs: BTreeSet<(String, String)> = old
        .subsumptions
        .iter()
        .flat_map(|(subject, objects)| {
            objects
                .iter()
                .map(move |object| (subject.clone(), object.clone()))
        })
        .collect();
    let new_pairs: BTreeSet<(String, String)> = new
        .subsumptions
        .iter()
        .flat_map(|(subject, objects)| {
            objects
                .iter()
                .map(move |object| (subject.clone(), object.clone()))
        })
        .collect();
    stats.reused_subsumptions = old_pairs.intersection(&new_pairs).count();
    stats.new_subsumptions = new_pairs.difference(&old_pairs).count();
}

fn compile_direct_ht(clauses: &[JClause]) -> Result<CompiledHt, IncrementalReasoningError> {
    for clause in clauses {
        if clause_is_global(clause) && clause.body.is_empty() && clause.head.is_empty() {
            // This is supported semantically (an immediate contradiction); keep
            // it. The check exists only to make the global dependency explicit.
        }
        for atom in clause.body.iter().chain(&clause.head) {
            match atom {
                JAtom::Concept { concept, term } => {
                    reject_term(term)?;
                    if short(concept).starts_with("__dt__") {
                        return unsupported("datatype concepts are outside direct incremental HT");
                    }
                }
                JAtom::Role {
                    role,
                    source,
                    target,
                } => {
                    reject_term(source)?;
                    reject_term(target)?;
                    let short = short(role);
                    if short.starts_with("__inv__")
                        || matches!(
                            short,
                            "topObjectProperty"
                                | "owl:topObjectProperty"
                                | "bottomObjectProperty"
                                | "owl:bottomObjectProperty"
                        )
                    {
                        return unsupported(
                            "inverse or builtin universal roles require orchestration side data",
                        );
                    }
                }
                JAtom::Eq { left, right } => {
                    reject_term(left)?;
                    reject_term(right)?;
                }
            }
        }
        let body_roles = clause
            .body
            .iter()
            .filter(|atom| matches!(atom, JAtom::Role { .. }))
            .count();
        let head_roles = clause
            .head
            .iter()
            .filter(|atom| matches!(atom, JAtom::Role { .. }))
            .count();
        if body_roles >= 2 && head_roles != 0 {
            return unsupported(
                "role-chain/transitivity updates require the typed RBox incremental contract",
            );
        }
    }

    let named: HashSet<String> = clauses
        .iter()
        .flat_map(|clause| clause.body.iter().chain(&clause.head))
        .filter_map(|atom| match atom {
            JAtom::Concept { concept, .. } => Some(concept.clone()),
            JAtom::Role { .. } | JAtom::Eq { .. } => None,
        })
        .collect();
    let tin = cb_to_ht::convert(clauses, None, &named, &[], &[], &[], false, &[], false);
    if tin.dropped != 0 {
        return unsupported(format!(
            "HT conversion dropped {} normalized clause(s)",
            tin.dropped
        ));
    }
    if !tin.fenced.is_empty() {
        let reasons = tin
            .fenced
            .iter()
            .map(|fence| fence.reason.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        return unsupported(format!("HT conversion raised route fence(s): {reasons}"));
    }
    if tin.inverse
        || !tin.nominals.is_empty()
        || !tin.chains.is_empty()
        || !tin.transitive.is_empty()
        || !tin.native_abox.is_empty()
        || !tin.card_defs.is_empty()
    {
        return unsupported(
            "direct incremental HT admits no inverse, nominal/ABox, chain, or side-cardinality state",
        );
    }
    if tin.concepts.len() > C::MAX as usize
        || tin.roles.len() > R::MAX as usize
        || tin.queries.iter().any(|&query| query > C::MAX as usize)
    {
        return unsupported("HT compact concept/role id space overflow");
    }

    Ok(CompiledHt {
        concepts: tin.concepts,
        roles: tin.roles,
        clauses: tin.clauses,
        queries: tin.queries.into_iter().map(|id| id as C).collect(),
        number: tin.number,
        nominals: Vec::new(),
        native_abox: NativeAboxJson::default(),
        card_defs: Vec::new(),
        chains: Vec::new(),
        transitive: Vec::new(),
    })
}

/// Compile an already route-validated production HT input without discarding
/// typed side state. The caller remains responsible for constructing this
/// `TInput` through the same source projection used by the batch route.
fn compile_typed_ht(input: TInput) -> Result<CompiledHt, IncrementalReasoningError> {
    if input.dropped != 0 {
        return unsupported(format!(
            "typed HT conversion dropped {} normalized clause(s)",
            input.dropped
        ));
    }
    if !input.fenced.is_empty() {
        let reasons = input
            .fenced
            .iter()
            .map(|fence| fence.reason.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        return unsupported(format!(
            "typed HT conversion raised route fence(s): {reasons}"
        ));
    }
    // The ordinary retained Ht probes do not implement the QO/SHIQ publication
    // guards. Those automatic variants need their own checked-state adapter.
    if input.inverse {
        return unsupported("typed incremental HT does not yet admit inverse-role publication");
    }
    if !input.native_abox.negative_role_assertions.is_empty() {
        return unsupported("typed incremental HT has no negative native-ABox role state");
    }
    if !input.native_abox.is_empty() && !input.native_abox.complete {
        return unsupported("typed incremental HT requires a complete native ABox");
    }
    if input.concepts.len() > C::MAX as usize || input.roles.len() > R::MAX as usize {
        return unsupported("typed HT compact concept/role id space overflow");
    }

    let queries = compact_concepts(&input.queries)?;
    let nominals = compact_concepts(&input.nominals)?;
    let chains = input
        .chains
        .iter()
        .map(|&(first, second, head)| {
            Ok((
                compact_role(first as usize)?,
                compact_role(second as usize)?,
                compact_role(head as usize)?,
            ))
        })
        .collect::<Result<Vec<_>, IncrementalReasoningError>>()?;
    let transitive = input
        .transitive
        .iter()
        .map(|&role| compact_role(role as usize))
        .collect::<Result<Vec<_>, IncrementalReasoningError>>()?;

    // Validate every typed id before a probe can mutate an Ht graph.
    for individual in &input.native_abox.individuals {
        let _ = compact_concepts(&individual.proxies)?;
        let _ = compact_concepts(&individual.assertions)?;
    }
    for &(role, source, target) in &input.native_abox.role_assertions {
        let _ = compact_role(role)?;
        if source >= input.native_abox.individuals.len()
            || target >= input.native_abox.individuals.len()
        {
            return unsupported("typed HT native-ABox individual id overflow");
        }
    }
    for &(left, right) in &input.native_abox.different {
        if left >= input.native_abox.individuals.len()
            || right >= input.native_abox.individuals.len()
        {
            return unsupported("typed HT native-ABox inequality id overflow");
        }
    }
    for definition in &input.card_defs {
        let _ = compact_concept(definition.marker)?;
        let _ = compact_role(definition.role)?;
        let _ = compact_concept(definition.filler)?;
    }

    Ok(CompiledHt {
        concepts: input.concepts,
        roles: input.roles,
        clauses: input.clauses,
        queries,
        number: input.number,
        nominals,
        native_abox: input.native_abox,
        card_defs: input.card_defs,
        chains,
        transitive,
    })
}

fn compact_concepts(ids: &[usize]) -> Result<Vec<C>, IncrementalReasoningError> {
    ids.iter().map(|&id| compact_concept(id)).collect()
}

fn compact_concept(id: usize) -> Result<C, IncrementalReasoningError> {
    C::try_from(id).map_err(|_| IncrementalReasoningError::HtDeferred {
        detail: "HT concept id overflow".into(),
    })
}

fn compact_role(id: usize) -> Result<R, IncrementalReasoningError> {
    R::try_from(id).map_err(|_| IncrementalReasoningError::HtDeferred {
        detail: "HT role id overflow".into(),
    })
}

fn atom_of(atom: &HAtom) -> Result<Atom, IncrementalReasoningError> {
    let concept = |id: usize| {
        C::try_from(id).map_err(|_| IncrementalReasoningError::HtDeferred {
            detail: "HT concept id overflow".into(),
        })
    };
    let role = |id: usize| {
        R::try_from(id).map_err(|_| IncrementalReasoningError::HtDeferred {
            detail: "HT role id overflow".into(),
        })
    };
    let var = |id: usize| {
        u32::try_from(id).map_err(|_| IncrementalReasoningError::HtDeferred {
            detail: "HT variable id overflow".into(),
        })
    };
    match atom {
        HAtom::Concept { neg, c, t } => Ok(Atom::Concept {
            lit: CLit {
                neg: *neg,
                c: concept(*c)?,
            },
            t: var(*t)?,
        }),
        HAtom::Role { r, s, t } => Ok(Atom::Role {
            r: role(*r)?,
            s: var(*s)?,
            t: var(*t)?,
        }),
        HAtom::Eq { s, t } => Ok(Atom::Eq {
            s: var(*s)?,
            t: var(*t)?,
        }),
        HAtom::Exist { r, neg, c, t } => Ok(Atom::Exists {
            r: role(*r)?,
            fil: CLit {
                neg: *neg,
                c: concept(*c)?,
            },
            t: var(*t)?,
        }),
    }
}

fn reject_term(term: &JTerm) -> Result<(), IncrementalReasoningError> {
    match term {
        JTerm::Var { .. } => Ok(()),
        JTerm::Fun { arg, .. } => reject_term(arg),
        JTerm::Ind { .. } | JTerm::Aux { .. } => {
            unsupported("ground individuals and auxiliary constants require typed HT side state")
        }
    }
}

fn unsupported<T>(detail: impl Into<String>) -> Result<T, IncrementalReasoningError> {
    Err(IncrementalReasoningError::RequestedBackendUnsupported {
        backend: crate::incremental::IncrementalBackend::Ht,
        detail: detail.into(),
    })
}

fn short(name: &str) -> &str {
    let after_hash = name.rsplit('#').next().unwrap_or(name);
    after_hash.rsplit('/').next().unwrap_or(after_hash)
}

fn is_top(name: &str) -> bool {
    matches!(
        name,
        "owl:Thing" | "http://www.w3.org/2002/07/owl#Thing" | "\u{22a4}"
    )
}

fn clause_is_global(clause: &JClause) -> bool {
    clause.body.is_empty()
        || clause
            .body
            .iter()
            .any(|atom| matches!(atom, JAtom::Concept { concept, .. } if is_top(concept)))
}

fn affected_concepts(
    old: &[JClause],
    new: &[JClause],
    changed: &[JClause],
    all_queries: &[String],
) -> BTreeSet<String> {
    if changed.iter().any(clause_is_global) {
        return all_queries.iter().cloned().collect();
    }
    let seeds: BTreeSet<String> = changed
        .iter()
        .flat_map(clause_symbols)
        .map(|symbol| symbol.key())
        .collect();
    if seeds.is_empty() {
        return all_queries.iter().cloned().collect();
    }

    let mut affected = BTreeSet::new();
    for clauses in [old, new] {
        let graph = dependency_graph(clauses);
        let mut queue: VecDeque<String> = seeds.iter().cloned().collect();
        let mut seen = HashSet::new();
        while let Some(symbol) = queue.pop_front() {
            if !seen.insert(symbol.clone()) {
                continue;
            }
            if let Some(concept) = symbol.strip_prefix("c\0") {
                affected.insert(concept.to_string());
            }
            if let Some(neighbours) = graph.get(&symbol) {
                queue.extend(neighbours.iter().cloned());
            }
        }
    }
    affected
}

#[derive(Clone)]
enum Symbol {
    Concept(String),
    Role(String),
    Function(String),
}

impl Symbol {
    fn key(&self) -> String {
        match self {
            Symbol::Concept(name) => format!("c\0{name}"),
            Symbol::Role(name) => format!("r\0{name}"),
            Symbol::Function(name) => format!("f\0{name}"),
        }
    }
}

fn dependency_graph(clauses: &[JClause]) -> HashMap<String, BTreeSet<String>> {
    let mut graph: HashMap<String, BTreeSet<String>> = HashMap::new();
    for clause in clauses {
        let symbols: Vec<String> = clause_symbols(clause)
            .into_iter()
            .map(|symbol| symbol.key())
            .collect();
        for symbol in &symbols {
            graph.entry(symbol.clone()).or_default();
        }
        if let Some(first) = symbols.first() {
            for symbol in symbols.iter().skip(1) {
                graph
                    .entry(first.clone())
                    .or_default()
                    .insert(symbol.clone());
                graph
                    .entry(symbol.clone())
                    .or_default()
                    .insert(first.clone());
            }
        }
    }
    graph
}

fn clause_symbols(clause: &JClause) -> Vec<Symbol> {
    let mut symbols = Vec::new();
    for atom in clause.body.iter().chain(&clause.head) {
        match atom {
            JAtom::Concept { concept, term } => {
                symbols.push(Symbol::Concept(concept.clone()));
                term_symbols(term, &mut symbols);
            }
            JAtom::Role {
                role,
                source,
                target,
            } => {
                symbols.push(Symbol::Role(role.clone()));
                term_symbols(source, &mut symbols);
                term_symbols(target, &mut symbols);
            }
            JAtom::Eq { left, right } => {
                term_symbols(left, &mut symbols);
                term_symbols(right, &mut symbols);
            }
        }
    }
    let mut seen = HashSet::new();
    symbols.retain(|symbol| seen.insert(symbol.key()));
    symbols
}

fn term_symbols(term: &JTerm, symbols: &mut Vec<Symbol>) {
    if let JTerm::Fun { function, arg } = term {
        symbols.push(Symbol::Function(function.clone()));
        term_symbols(arg, symbols);
    }
}

#[cfg(test)]
mod typed_tests {
    use super::*;
    use crate::orchestrate::cb_to_ht::{NativeIndividualJson, TInput};

    fn concept_clause(body: usize, head: usize) -> HtClause {
        HtClause {
            body: vec![HAtom::Concept {
                neg: false,
                c: body,
                t: 0,
            }],
            head: vec![HAtom::Concept {
                neg: false,
                c: head,
                t: 0,
            }],
        }
    }

    fn source_clause(body: &str, head: &str) -> JClause {
        let term = JTerm::Var { name: "x".into() };
        JClause {
            body: vec![JAtom::Concept {
                concept: body.into(),
                term: term.clone(),
            }],
            head: vec![JAtom::Concept {
                concept: head.into(),
                term,
            }],
        }
    }

    fn native_input(extra: bool) -> TInput {
        let mut input = TInput {
            concepts: vec!["A".into(), "B".into(), "__nom__a".into()],
            roles: vec![],
            clauses: vec![concept_clause(0, 1)],
            queries: vec![0, 1],
            nominals: vec![2],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![NativeIndividualJson {
                    proxies: vec![2],
                    assertions: vec![0],
                }],
                ..NativeAboxJson::default()
            },
            ..TInput::default()
        };
        if extra {
            input.concepts.extend(["X".into(), "Y".into()]);
            input.clauses.push(concept_clause(3, 4));
            input.queries.extend([3, 4]);
        }
        input
    }

    #[test]
    fn typed_native_abox_is_installed_and_classified() {
        let classifier =
            IncrementalHtClassifier::new_typed(&[source_clause("A", "B")], native_input(false))
                .unwrap();
        let result = classifier.result();
        assert!(!result.inconsistent);
        assert!(result
            .subsumptions
            .get("A")
            .is_some_and(|supers| supers.iter().any(|name| name == "B")));
    }

    #[test]
    fn typed_disconnected_addition_reuses_existing_probes() {
        let before = vec![source_clause("A", "B")];
        let classifier = IncrementalHtClassifier::new_typed(&before, native_input(false)).unwrap();
        let added = source_clause("X", "Y");
        let mut after = before;
        after.push(added.clone());
        let (_, stats) = classifier
            .updated_typed(&after, &[added], HtChangeKind::Addition, native_input(true))
            .unwrap();
        assert!(stats.reused_probes > 0);
    }

    #[test]
    fn incomplete_or_negative_native_abox_fails_closed() {
        let clauses = [source_clause("A", "B")];
        let mut incomplete = native_input(false);
        incomplete.native_abox.complete = false;
        assert!(IncrementalHtClassifier::new_typed(&clauses, incomplete).is_err());

        let mut negative = native_input(false);
        negative
            .native_abox
            .negative_role_assertions
            .push((0, 0, 0));
        assert!(IncrementalHtClassifier::new_typed(&clauses, negative).is_err());
    }
}
