//! Static proof that no value singleton can enter a completion-graph label.
//!
//! The native bridge consumes a value singleton `v(y1) ∧ v(y2) → y1 = y2` as
//! a scan-at-fixpoint merge (u02). Since 0520da9d the bridge does not install
//! the satisfiable expander cache when it consumes one, because a cache hit on
//! a data successor parks the finite cover that would choose `v`, and the merge
//! that the cover makes necessary never happens (`count_with_assertions_ok`).
//!
//! That argument needs a node that can carry `v`. When no node of any probe
//! can carry a positive `v`, the merge rule never fires: every probe runs
//! exactly as it runs without the singleton, and the cache keeps the locality
//! argument it has for singleton-free inputs. This module decides that case
//! with a least fixpoint over the bridge input. It over-approximates
//!
//! * `pos[c]` / `neg[c]`: concept `c` (resp. `¬c`) may occur in some label;
//! * `edge[r]`: some node may have an `r`-edge (in either direction).
//!
//! Every way the bridge can put a concept into a label or create an edge is a
//! rule below: probe seeds (each query positively and negatively), ABox seeds,
//! clause heads (a clause fires only when every positive body concept and every
//! body role may hold), source axioms in negation normal form (a sub-concept is
//! visited with its polarity; restrictions that need an edge are visited only
//! once the role may have one), definer markers expanded to their definitions
//! in the polarity they occur, cardinality markers, the choose rule of at-most
//! restrictions (both polarities of the filler), role domains and ranges, and
//! role chains. Inputs with rules, fenced clauses or the universal role are not
//! analysed (the cache stays off). The rules only ever add facts, so the
//! iteration terminates; if a singleton is still outside `pos`, no completion
//! graph of any probe contains it positively.
//!
//! `KM_HT_SINGLETON_INERT_AUDIT=1` checks the claim at run time: every
//! singleton fixpoint scan also verifies that no label holds a positive concept
//! outside `pos`, and the process exits with status 97 on a violation.

use crate::frontend::syntax::{Concept as SourceConcept, Role as SourceRole};
use crate::fxhash::{FxHashMap, FxHashSet};
use crate::json_io::{DefinerKind, SourceAxiomKind};
use crate::orchestrate::cb_to_ht::{HAtom, TInput};

/// The fixpoint result over `TInput.concepts` (indices `< tin.concepts.len()`)
/// and `TInput.roles`; names that only the source payload uses get extra ids.
pub(crate) struct LabelReach {
    pub pos: Vec<bool>,
    pub neg: Vec<bool>,
    pub edge: Vec<bool>,
}

struct Analyzer<'a> {
    concept_ids: FxHashMap<&'a str, usize>,
    role_ids: FxHashMap<&'a str, usize>,
    pos: Vec<bool>,
    neg: Vec<bool>,
    edge: Vec<bool>,
    changed: bool,
    universal: bool,
}

impl<'a> Analyzer<'a> {
    fn concept(&mut self, name: &'a str) -> usize {
        if let Some(&id) = self.concept_ids.get(name) {
            return id;
        }
        let id = self.pos.len();
        self.concept_ids.insert(name, id);
        self.pos.push(false);
        self.neg.push(false);
        id
    }
    fn role(&mut self, role: &'a SourceRole) -> Option<usize> {
        let name = match role {
            SourceRole::Name(name) | SourceRole::Inverse(name) => name.as_str(),
            SourceRole::Universal => {
                self.universal = true;
                return None;
            }
        };
        if let Some(&id) = self.role_ids.get(name) {
            return Some(id);
        }
        let id = self.edge.len();
        self.role_ids.insert(name, id);
        self.edge.push(false);
        Some(id)
    }
    fn set_pos(&mut self, c: usize) {
        if !self.pos[c] {
            self.pos[c] = true;
            self.changed = true;
        }
    }
    fn set_neg(&mut self, c: usize) {
        if !self.neg[c] {
            self.neg[c] = true;
            self.changed = true;
        }
    }
    fn set_signed(&mut self, c: usize, negated: bool) {
        if negated {
            self.set_neg(c)
        } else {
            self.set_pos(c)
        }
    }
    fn set_edge(&mut self, r: usize) {
        if !self.edge[r] {
            self.edge[r] = true;
            self.changed = true;
        }
    }

    /// Visit a source concept that is added to a label with `positive`
    /// polarity (NNF of the concept, or of its complement when negative).
    fn walk(&mut self, concept: &'a SourceConcept, positive: bool) {
        match concept {
            SourceConcept::Name(name) => {
                let c = self.concept(name);
                self.set_signed(c, !positive);
            }
            SourceConcept::Top | SourceConcept::Bottom | SourceConcept::Nominal(_) => {}
            SourceConcept::Not(inner) => self.walk(inner, !positive),
            SourceConcept::And(operands) | SourceConcept::Or(operands) => {
                for operand in operands {
                    self.walk(operand, positive);
                }
            }
            // ∃r.f, or ¬∀r.f = ∃r.¬f: creates an r-successor.
            SourceConcept::Exists(role, filler) if positive => {
                if let Some(r) = self.role(role) {
                    self.set_edge(r);
                }
                self.walk(filler, true);
            }
            SourceConcept::Forall(role, filler) if !positive => {
                if let Some(r) = self.role(role) {
                    self.set_edge(r);
                }
                self.walk(filler, false);
            }
            // ∀r.f, or ¬∃r.f = ∀r.¬f: acts on existing r-edges only.
            SourceConcept::Forall(role, filler) | SourceConcept::Exists(role, filler) => {
                let forall = matches!(concept, SourceConcept::Forall(..));
                if let Some(r) = self.role(role) {
                    if self.edge[r] {
                        self.walk(filler, forall);
                    }
                }
            }
            // ≥n r.f, or ¬≤n r.f = ≥(n+1) r.f: creates r-successors; the
            // choose rule may add f or ¬f to r-successors.
            SourceConcept::AtLeast(_, role, filler) if positive => {
                if let Some(r) = self.role(role) {
                    self.set_edge(r);
                }
                self.walk(filler, true);
                self.walk(filler, false);
            }
            SourceConcept::AtMost(_, role, filler) if !positive => {
                if let Some(r) = self.role(role) {
                    self.set_edge(r);
                }
                self.walk(filler, true);
                self.walk(filler, false);
            }
            SourceConcept::AtLeast(_, role, filler) | SourceConcept::AtMost(_, role, filler) => {
                if let Some(r) = self.role(role) {
                    if self.edge[r] {
                        self.walk(filler, true);
                        self.walk(filler, false);
                    }
                }
            }
            SourceConcept::HasSelf(role) => {
                if let Some(r) = self.role(role) {
                    if positive {
                        self.set_edge(r);
                    }
                }
            }
        }
    }

    /// Over-approximation: may `concept` hold on some node?
    fn may_hold(&mut self, concept: &'a SourceConcept) -> bool {
        match concept {
            SourceConcept::Name(name) => {
                let c = self.concept(name);
                self.pos[c]
            }
            SourceConcept::Bottom => false,
            SourceConcept::And(operands) => {
                let mut all = true;
                for operand in operands {
                    all &= self.may_hold(operand);
                }
                all
            }
            SourceConcept::Or(operands) => {
                let mut any = false;
                for operand in operands {
                    any |= self.may_hold(operand);
                }
                any
            }
            SourceConcept::Exists(role, _)
            | SourceConcept::AtLeast(_, role, _)
            | SourceConcept::HasSelf(role) => match self.role(role) {
                Some(r) => self.edge[r],
                None => true,
            },
            SourceConcept::Top
            | SourceConcept::Nominal(_)
            | SourceConcept::Not(_)
            | SourceConcept::Forall(..)
            | SourceConcept::AtMost(..) => true,
        }
    }
}

/// Least fixpoint of the label/edge rules described in the module docs, or
/// `None` when the input carries a channel the analysis does not model.
pub(crate) fn label_reach(tin: &TInput) -> Option<LabelReach> {
    if tin.rule_data_roles.is_some()
        || tin.rule_source_classes.is_some()
        || tin.rule_source_abox.is_some()
        || !tin.fenced.is_empty()
    {
        return None;
    }
    let concept_count = tin.concepts.len();
    let role_count = tin.roles.len();
    let mut a = Analyzer {
        concept_ids: tin.concepts.iter().enumerate().map(|(i, n)| (n.as_str(), i)).collect(),
        role_ids: tin.roles.iter().enumerate().map(|(i, n)| (n.as_str(), i)).collect(),
        pos: vec![false; concept_count],
        neg: vec![false; concept_count],
        edge: vec![false; role_count],
        changed: false,
        universal: false,
    };
    let in_concepts = |c: usize| c < concept_count;
    let in_roles = |r: usize| r < role_count;
    for clause in &tin.clauses {
        for atom in clause.body.iter().chain(clause.head.iter()) {
            let ok = match *atom {
                HAtom::Concept { c, .. } => in_concepts(c),
                HAtom::Role { r, .. } => in_roles(r),
                HAtom::Exist { r, c, .. } => in_roles(r) && in_concepts(c),
                HAtom::Eq { .. } => true,
            };
            if !ok {
                return None;
            }
        }
    }

    // Definitions that the bridge substitutes for definer markers.
    struct Definition {
        marker: usize,
        kind: DefinerKind,
        operands: Vec<usize>,
        role: Option<usize>,
    }
    let mut definitions: Vec<Definition> = Vec::with_capacity(tin.definers.len());
    for definer in &tin.definers {
        let marker = a.concept(&definer.marker);
        let operands = definer.operands.iter().map(|name| a.concept(name)).collect();
        let role = match &definer.role {
            Some(name) => match a.role_ids.get(name.as_str()) {
                Some(&r) => Some(r),
                None => {
                    let r = a.edge.len();
                    a.role_ids.insert(name.as_str(), r);
                    a.edge.push(false);
                    Some(r)
                }
            },
            None => None,
        };
        definitions.push(Definition { marker, kind: definer.kind, operands, role });
    }
    for card in &tin.card_defs {
        if !in_concepts(card.marker) || !in_concepts(card.filler) || !in_roles(card.role) {
            return None;
        }
    }
    for &(r, c) in tin.role_domains.iter().chain(tin.role_ranges.iter()) {
        if !in_roles(r) || !in_concepts(c) {
            return None;
        }
    }
    for &(left, right, sup) in &tin.chains {
        if !in_roles(left) || !in_roles(right) || !in_roles(sup) {
            return None;
        }
    }

    // Seeds. Every query is a probe subject and a candidate subsumer.
    for &q in &tin.queries {
        if !in_concepts(q) {
            return None;
        }
        a.set_pos(q);
        a.set_neg(q);
    }
    for &n in &tin.nominals {
        if !in_concepts(n) {
            return None;
        }
        a.set_pos(n);
    }
    for individual in &tin.nominal_abox.individuals {
        for proxy in &individual.proxies {
            let c = a.concept(proxy);
            a.set_pos(c);
        }
        for marker in &individual.assertion_markers {
            let c = a.concept(marker);
            a.set_pos(c);
        }
        for assertion in &individual.assertions {
            a.walk(assertion, true);
        }
    }
    for assertion in &tin.nominal_abox.role_assertions {
        let Some(&r) = a.role_ids.get(assertion.role.as_str()) else {
            return None;
        };
        a.set_edge(r);
    }
    for individual in &tin.native_abox.individuals {
        for &c in individual.proxies.iter().chain(individual.assertions.iter()) {
            if !in_concepts(c) {
                return None;
            }
            a.set_pos(c);
        }
    }
    for &(r, _, _) in &tin.native_abox.role_assertions {
        if !in_roles(r) {
            return None;
        }
        a.set_edge(r);
    }
    // Disjointness and the negative side of every axiom do not depend on a
    // trigger: `L ⊑ R` is `⊤ ⊑ ¬L ⊔ R`.
    loop {
        a.changed = false;
        for axiom in &tin.source_axioms {
            match axiom.kind {
                SourceAxiomKind::SubClass => {
                    a.walk(&axiom.left, false);
                    if a.may_hold(&axiom.left) {
                        a.walk(&axiom.right, true);
                    }
                }
                SourceAxiomKind::Equivalent => {
                    a.walk(&axiom.left, true);
                    a.walk(&axiom.left, false);
                    a.walk(&axiom.right, true);
                    a.walk(&axiom.right, false);
                }
                SourceAxiomKind::Disjoint => {
                    a.walk(&axiom.left, false);
                    a.walk(&axiom.right, false);
                }
            }
        }
        if a.universal {
            return None;
        }
        for clause in &tin.clauses {
            let fires = clause.body.iter().all(|atom| match *atom {
                HAtom::Concept { neg: false, c, .. } => a.pos[c],
                HAtom::Concept { neg: true, .. } | HAtom::Eq { .. } => true,
                HAtom::Role { r, .. } | HAtom::Exist { r, .. } => a.edge[r],
            });
            if !fires {
                continue;
            }
            let mut equality = false;
            for atom in &clause.head {
                match *atom {
                    HAtom::Concept { neg, c, .. } => a.set_signed(c, neg),
                    HAtom::Role { r, .. } => a.set_edge(r),
                    HAtom::Exist { r, neg, c, .. } => {
                        a.set_edge(r);
                        a.set_signed(c, neg);
                    }
                    HAtom::Eq { .. } => equality = true,
                }
            }
            if equality {
                // An at-most restriction: its choose rule may add the filler
                // or its complement to a successor.
                for atom in &clause.body {
                    if let HAtom::Concept { c, t, .. } = *atom {
                        let successor = clause.body.iter().any(|other| {
                            matches!(*other, HAtom::Role { s, t: target, .. } if target == t && s != t)
                        });
                        if successor {
                            a.set_pos(c);
                            a.set_neg(c);
                        }
                    }
                }
            }
        }
        for d in &definitions {
            for positive in [true, false] {
                let present = if positive { a.pos[d.marker] } else { a.neg[d.marker] };
                if !present {
                    continue;
                }
                let operand_sign = |p: bool| !p; // set_signed takes "negated"
                match d.kind {
                    DefinerKind::Top | DefinerKind::Bottom => {}
                    DefinerKind::Not => {
                        for &o in &d.operands {
                            a.set_signed(o, positive);
                        }
                    }
                    DefinerKind::And | DefinerKind::Or => {
                        for &o in &d.operands {
                            a.set_signed(o, operand_sign(positive));
                        }
                    }
                    DefinerKind::Exists | DefinerKind::Forall => {
                        let Some(r) = d.role else { continue };
                        let creates = (d.kind == DefinerKind::Exists) == positive;
                        if creates {
                            a.set_edge(r);
                        }
                        if creates || a.edge[r] {
                            for &o in &d.operands {
                                a.set_signed(o, operand_sign(positive));
                            }
                        }
                    }
                    DefinerKind::SelfRestriction | DefinerKind::NotSelf => {
                        let Some(r) = d.role else { continue };
                        if (d.kind == DefinerKind::SelfRestriction) == positive {
                            a.set_edge(r);
                        }
                    }
                    DefinerKind::AtLeast | DefinerKind::AtMost => {
                        let Some(r) = d.role else { continue };
                        if (d.kind == DefinerKind::AtLeast) == positive {
                            a.set_edge(r);
                        }
                        if a.edge[r] {
                            for &o in &d.operands {
                                a.set_pos(o);
                                a.set_neg(o);
                            }
                        }
                    }
                }
            }
        }
        for card in &tin.card_defs {
            if a.pos[card.marker] || a.neg[card.marker] {
                a.set_edge(card.role);
                a.set_pos(card.filler);
                a.set_neg(card.filler);
            }
        }
        for &(r, c) in tin.role_domains.iter().chain(tin.role_ranges.iter()) {
            if a.edge[r] {
                a.set_pos(c);
            }
        }
        for &(left, right, sup) in &tin.chains {
            if a.edge[left] || a.edge[right] {
                a.set_edge(sup);
            }
        }
        if !a.changed {
            break;
        }
    }
    Some(LabelReach { pos: a.pos, neg: a.neg, edge: a.edge })
}

/// True when no concept of `singletons` (indices into `tin.concepts`) can
/// occur positively in any label; returns the reach for the audit.
pub(crate) fn value_singletons_inert(tin: &TInput, singletons: &[usize]) -> Option<LabelReach> {
    if singletons.iter().any(|&c| c >= tin.concepts.len()) {
        return None;
    }
    let reach = label_reach(tin)?;
    singletons.iter().all(|&c| !reach.pos[c]).then_some(reach)
}

/// Audit state: arena tags of concepts the analysis proved never positive.
static AUDIT: std::sync::Mutex<Option<FxHashSet<i64>>> = std::sync::Mutex::new(None);

pub(crate) fn audit_enabled() -> bool {
    std::env::var_os("KM_HT_SINGLETON_INERT_AUDIT").is_some()
}

pub(crate) fn install_audit(tags: FxHashSet<i64>) {
    if let Ok(mut guard) = AUDIT.lock() {
        *guard = Some(tags);
    }
}

/// Exit with status 97 if a label holds a positive concept the analysis
/// excluded. Called from the singleton fixpoint scan when the audit is on.
pub(crate) fn audit_labels(
    calc_alg_context: &super::completion::context::CalculationAlgorithmContextBase,
    phantom: &[(usize, usize)],
) {
    let Ok(guard) = AUDIT.lock() else { return };
    let Some(excluded) = guard.as_ref() else { return };
    let ctx = calc_alg_context.process_context();
    for i in 0..ctx.node_count() {
        if phantom.iter().any(|&(lo, hi)| i >= lo && i < hi) {
            continue;
        }
        let node_id = super::process::NodeId::new(i as i64);
        let node = ctx.node(node_id);
        if node.has_merged_into_individual_node_id() {
            continue;
        }
        let label = node.reapply_con_label_set;
        if label.is_none() {
            continue;
        }
        let mut violation: Option<i64> = None;
        ctx.label_set_visit_stored_descriptors(label, |tag, descriptor, _| {
            if violation.is_none()
                && excluded.contains(&tag)
                && !descriptor.is_none()
                && !ctx.con_desc(descriptor).is_negated()
            {
                violation = Some(tag);
            }
        });
        if let Some(tag) = violation {
            eprintln!("SINGLETON-INERT-AUDIT-VIOLATION node={i} concept_tag={tag}");
            std::process::exit(97);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json_io::{DefinerMeta, SourceAxiomMeta};
    use crate::orchestrate::cb_to_ht::HtClause;

    const A: usize = 0;
    const BOOL: usize = 1;
    const TRUE: usize = 2;
    const FALSE: usize = 3;
    const Q: usize = 4;
    const U: usize = 0;

    fn c(c: usize, t: usize) -> HAtom {
        HAtom::Concept { neg: false, c, t }
    }
    fn nc(c: usize, t: usize) -> HAtom {
        HAtom::Concept { neg: true, c, t }
    }
    fn r(r: usize, s: usize, t: usize) -> HAtom {
        HAtom::Role { r, s, t }
    }
    fn cl(body: Vec<HAtom>, head: Vec<HAtom>) -> HtClause {
        HtClause { body, head }
    }

    /// A boolean data property `u` used only in its domain, range and
    /// functionality, the shape of ore_ont_9027.
    fn range_only() -> TInput {
        TInput {
            concepts: ["A", "__dt__boolean", "__dt__val__\"true\"^^xsd:boolean",
                "__dt__val__\"false\"^^xsd:boolean", "Q_0"]
                .iter().map(|s| s.to_string()).collect(),
            roles: vec!["u".to_string()],
            clauses: vec![
                cl(vec![r(U, 0, 1)], vec![c(BOOL, 1)]),
                cl(vec![r(U, 0, 1)], vec![c(A, 0)]),
                cl(vec![r(U, 0, 1), r(U, 0, 2)], vec![HAtom::Eq { s: 1, t: 2 }]),
                cl(vec![c(BOOL, 0)], vec![c(TRUE, 0), c(FALSE, 0)]),
                cl(vec![c(TRUE, 0), c(TRUE, 1)], vec![HAtom::Eq { s: 0, t: 1 }]),
                cl(vec![c(FALSE, 0), c(FALSE, 1)], vec![HAtom::Eq { s: 0, t: 1 }]),
            ],
            queries: vec![A],
            ..TInput::default()
        }
    }

    #[test]
    fn range_domain_and_functionality_leave_values_inert() {
        let tin = range_only();
        let reach = value_singletons_inert(&tin, &[TRUE, FALSE]).expect("inert");
        assert!(!reach.edge[U]);
        assert!(!reach.pos[BOOL]);
    }

    #[test]
    fn a_data_existential_makes_values_reachable() {
        let mut tin = range_only();
        tin.clauses.push(cl(vec![c(A, 0)], vec![HAtom::Exist { r: U, neg: false, c: BOOL, t: 0 }]));
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_none());
    }

    #[test]
    fn a_negated_universal_definer_creates_an_edge() {
        // Q resolves to ∀u.boolean; ¬Q in a head is ∃u.¬boolean.
        let mut tin = range_only();
        tin.definers.push(DefinerMeta {
            marker: "Q_0".into(),
            kind: DefinerKind::Forall,
            operands: vec!["__dt__boolean".into()],
            role: Some("u".into()),
            n: None,
        });
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_some());
        tin.clauses.push(cl(vec![c(A, 0)], vec![nc(Q, 0)]));
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_none());
    }

    #[test]
    fn an_underivable_existential_definer_stays_inert() {
        // Q ≡ ∃u.⊤ is derivable only from a u-edge (the domain recognition).
        let mut tin = range_only();
        tin.definers.push(DefinerMeta {
            marker: "Q_0".into(),
            kind: DefinerKind::Exists,
            operands: vec!["A".into()],
            role: Some("u".into()),
            n: None,
        });
        tin.clauses.push(cl(vec![c(Q, 0)], vec![HAtom::Exist { r: U, neg: false, c: A, t: 0 }]));
        tin.clauses.push(cl(vec![r(U, 0, 1)], vec![c(Q, 0)]));
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_some());
        tin.clauses.push(cl(vec![c(A, 0)], vec![c(Q, 0)]));
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_none());
    }

    #[test]
    fn source_axioms_follow_polarity() {
        use crate::frontend::syntax::{Concept, Role};
        let name = |n: &str| Concept::Name(n.to_string());
        let u = || Role::Name("u".to_string());
        let mut tin = range_only();
        tin.source_axioms = vec![
            SourceAxiomMeta {
                kind: SourceAxiomKind::SubClass,
                left: Concept::Exists(u(), Box::new(Concept::Top)),
                right: name("A"),
            },
            SourceAxiomMeta {
                kind: SourceAxiomKind::SubClass,
                left: Concept::Top,
                right: Concept::Forall(u(), Box::new(name("__dt__boolean"))),
            },
        ];
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_some());
        // `¬∀u.¬boolean ⊑ A` puts nothing on a node; `A ⊑ ¬∀u.¬boolean` does.
        tin.source_axioms.push(SourceAxiomMeta {
            kind: SourceAxiomKind::SubClass,
            left: Concept::Not(Box::new(Concept::Forall(u(), Box::new(Concept::Not(Box::new(name("__dt__boolean"))))))),
            right: name("A"),
        });
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_some());
        tin.source_axioms.push(SourceAxiomMeta {
            kind: SourceAxiomKind::SubClass,
            left: name("A"),
            right: Concept::Not(Box::new(Concept::Forall(u(), Box::new(Concept::Not(Box::new(name("__dt__boolean"))))))),
        });
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_none());
    }

    #[test]
    fn abox_data_edges_and_unmodelled_channels_keep_the_gate() {
        let mut tin = range_only();
        tin.native_abox.role_assertions.push((U, 0, 1));
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_none());
        let mut tin = range_only();
        tin.rule_data_roles = Some(vec![true]);
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_none());
        let mut tin = range_only();
        tin.source_axioms.push(SourceAxiomMeta {
            kind: SourceAxiomKind::SubClass,
            left: Concept::Name("A".into()),
            right: Concept::Forall(SourceRole::Universal, Box::new(Concept::Top)),
        });
        assert!(value_singletons_inert(&tin, &[TRUE, FALSE]).is_none());
    }

    use crate::frontend::syntax::Concept;
}
