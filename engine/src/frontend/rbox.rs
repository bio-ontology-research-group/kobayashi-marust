//! RBox extraction from the parsed functional-syntax tree.
//!
//! Direct port of `frontend.ofn_rbox`, `_plain_role`, `_plain_class`. Only the
//! `domain` / `range` records affect the emitted clause set (via
//! `preprocess.domain_range_clauses`); the other record kinds are produced for
//! parity with the Python list but are not consumed by `ofn_to_clauses`.

use std::collections::HashSet;

use super::iri::IriRegistry;
use super::sexpr::Node;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RboxRecord {
    Subrole(String, String),
    Domain(String, String),
    Range(String, String),
    Inverse(String, String),
    Fenced(String, String),
    /// Transitive role (KM_KEEP_CHAIN_AXIOMS side data).  Emitted for
    /// `TransitiveObjectProperty(R)` so cb_to_ht can populate the `transitive`
    /// TInput field for the Ht chain-unfolding.
    Transitive(String),
    /// Role chain R1∘R2⊑R (KM_KEEP_CHAIN_AXIOMS side data).  Emitted for
    /// `SubObjectPropertyOf(ObjectPropertyChain(R1 R2) R)` so cb_to_ht can
    /// populate the `chains` TInput field.  The raw chain axiom is filtered
    /// from the clause stream (it bloats cb_to_ht); the chain info rides the
    /// rbox instead.
    Chain(String, String, String),
    /// Arbitrary finite named-role chain. Existing consumers fail closed on
    /// its distinct row tag until they opt into certified decomposition.
    ChainN(Vec<String>, String),
}

/// RBox source nodes retained during the primary parse without consulting the
/// IRI registry. Replaying only these nodes after clausification preserves the
/// historical "all axiom names, then RBox names" assignment order while
/// avoiding a second tokenization and parse of the complete ontology.
#[derive(Default)]
pub struct RawRbox<'a> {
    nodes: Vec<Node<'a>>,
}

impl<'a> RawRbox<'a> {
    pub fn observe(&mut self, node: &Node<'a>) {
        let Node::List(head, _) = node else {
            return;
        };
        if matches!(
            *head,
            "SubObjectPropertyOf"
                | "ObjectPropertyDomain"
                | "ObjectPropertyRange"
                | "InverseObjectProperties"
                | "EquivalentObjectProperties"
                | "TransitiveObjectProperty"
                | "SymmetricObjectProperty"
                | "ReflexiveObjectProperty"
                | "IrreflexiveObjectProperty"
                | "InverseFunctionalObjectProperty"
                | "AsymmetricObjectProperty"
                | "DisjointObjectProperties"
        ) {
            self.nodes.push(node.clone());
        }
    }

    pub fn source_nodes(&self) -> impl Iterator<Item = &Node<'a>> {
        self.nodes.iter()
    }

    pub fn resolve(self, registry: &mut IriRegistry) -> Vec<RboxRecord> {
        let mut out = Vec::new();
        for node in &self.nodes {
            rbox_node(registry, node, &mut out);
        }
        out
    }
}

/// Serialize the typed Rust record into the legacy row format consumed by
/// `cb_to_ht` and the `km cb-to-ht` worker protocol.
pub fn to_row(record: &RboxRecord) -> Vec<String> {
    match record {
        RboxRecord::Subrole(sub, sup) => vec!["subrole".into(), sub.clone(), sup.clone()],
        RboxRecord::Domain(role, concept) => {
            vec!["domain".into(), role.clone(), concept.clone()]
        }
        RboxRecord::Range(role, concept) => {
            vec!["range".into(), role.clone(), concept.clone()]
        }
        RboxRecord::Inverse(left, right) => {
            vec!["inverse".into(), left.clone(), right.clone()]
        }
        RboxRecord::Fenced(reason, detail) => {
            vec!["fenced".into(), reason.clone(), detail.clone()]
        }
        RboxRecord::Transitive(role) => vec!["transitive".into(), role.clone()],
        RboxRecord::Chain(left, right, sup) => {
            vec!["chain".into(), left.clone(), right.clone(), sup.clone()]
        }
        RboxRecord::ChainN(body, sup) => {
            let mut row = Vec::with_capacity(body.len() + 2);
            row.push("chain-n".into());
            row.push(sup.clone());
            row.extend(body.iter().cloned());
            row
        }
    }
}

/// Port of `_plain_role`: named role -> Some(short); inverse/complex -> None.
fn plain_role(reg: &mut IriRegistry, node: &Node) -> Option<String> {
    match node {
        Node::Atom(s) => Some(reg.short(s)),
        _ => None,
    }
}

/// Port of `_plain_class`: named class -> Some(short); ⊤ -> Some(""); ⊥/complex
/// -> None.
fn plain_class(reg: &mut IriRegistry, node: &Node) -> Option<String> {
    match node {
        Node::Atom(s) => {
            let sh = reg.short(s);
            if sh == "owl:Thing" {
                Some(String::new())
            } else if sh == "owl:Nothing" {
                None
            } else {
                Some(sh)
            }
        }
        _ => None,
    }
}

fn strip_annotations<'a, 'n>(args: &'n [Node<'a>]) -> Vec<&'n Node<'a>> {
    args.iter()
        .filter(|a| a.head() != Some("Annotation"))
        .collect()
}

/// Port of one `ofn_rbox` loop iteration: append the RBox records of a single
/// `Ontology(...)` child to `out`. Called from the streaming side scan in
/// `ofn_to_clauses` (the old `ofn_rbox` materialised all nodes first).
pub fn rbox_node(reg: &mut IriRegistry, node: &Node, out: &mut Vec<RboxRecord>) {
    {
        let (head, args) = match node {
            Node::List(h, a) => (*h, a),
            _ => return,
        };
        let args = strip_annotations(args);
        match head {
            "SubObjectPropertyOf" => {
                let sub = args[0];
                let sup = args[1];
                let ssup = plain_role(reg, sup);
                if sub.head() == Some("ObjectPropertyChain") {
                    // KM_KEEP_CHAIN_AXIOMS: emit the chain as side data
                    // (Chain(r1, r2, sup)) so cb_to_ht can populate the TInput
                    // `chains` field for the Ht chain-unfolding. Binary rows
                    // retain the legacy shape. Longer named chains use the
                    // distinct `chain-n` source row and are compiled to
                    // certified binary clauses by the normalizer. Fall back to
                    // a fence only when a chain role is not plain.
                    let chain_args: Vec<&Node> = match sub {
                        Node::List(_, ca) => strip_annotations(ca),
                        _ => Vec::new(),
                    };
                    let roles: Option<Vec<String>> = chain_args
                        .iter()
                        .map(|role| plain_role(reg, role))
                        .collect();
                    if let (Some(roles), Some(rs)) = (roles, ssup) {
                        if let [r1, r2] = roles.as_slice() {
                            out.push(RboxRecord::Chain(r1.clone(), r2.clone(), rs));
                        } else {
                            out.push(RboxRecord::ChainN(roles, rs));
                        }
                    } else {
                        out.push(RboxRecord::Fenced(
                            "role-chain".to_string(),
                            format!("{:?} ⊑ {:?}", sub, sup),
                        ));
                    }
                } else if let (Some(rsub), Some(rsup)) = (plain_role(reg, sub), ssup) {
                    out.push(RboxRecord::Subrole(rsub, rsup));
                } else {
                    out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("SubObjectPropertyOf {:?} ⊑ {:?}", sub, sup),
                    ));
                }
            }
            "ObjectPropertyDomain" => {
                let r = plain_role(reg, args[0]);
                let d = plain_class(reg, args[1]);
                match (r, d) {
                    (None, _) => out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("domain of {:?}", args[0]),
                    )),
                    (Some(_), None) => out.push(RboxRecord::Fenced(
                        "complex-domain".to_string(),
                        format!("domain({:?}) = {:?}", args[0], args[1]),
                    )),
                    (Some(r), Some(d)) => {
                        if !d.is_empty() {
                            out.push(RboxRecord::Domain(r, d));
                        }
                    }
                }
            }
            "ObjectPropertyRange" => {
                let r = plain_role(reg, args[0]);
                let c = plain_class(reg, args[1]);
                match (r, c) {
                    (None, _) => out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("range of {:?}", args[0]),
                    )),
                    (Some(_), None) => out.push(RboxRecord::Fenced(
                        "complex-range".to_string(),
                        format!("range({:?}) = {:?}", args[0], args[1]),
                    )),
                    (Some(r), Some(c)) => {
                        if !c.is_empty() {
                            out.push(RboxRecord::Range(r, c));
                        }
                    }
                }
            }
            "InverseObjectProperties" => {
                let a = plain_role(reg, args[0]);
                let b = plain_role(reg, args[1]);
                match (a, b) {
                    (Some(a), Some(b)) => out.push(RboxRecord::Inverse(a, b)),
                    _ => out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("InverseObjectProperties {:?}", args),
                    )),
                }
            }
            "EquivalentObjectProperties" => {
                // Equivalent simple roles fold into pairwise both-way subrole
                // records (the subrole clause itself is emitted by `normalise`
                // from the AST `RoleInclusion`s; these records drive routing /
                // relevance / domain-range propagation). Any inverse member
                // fences the whole axiom to the CB engine.
                let roles: Vec<Option<String>> = args.iter().map(|a| plain_role(reg, a)).collect();
                if roles.iter().any(|r| r.is_none()) {
                    out.push(RboxRecord::Fenced(
                        "inverse-role".to_string(),
                        format!("EquivalentObjectProperties {:?}", args),
                    ));
                } else {
                    for k in 0..roles.len() {
                        for l in (k + 1)..roles.len() {
                            let a = roles[k].clone().unwrap();
                            let b = roles[l].clone().unwrap();
                            out.push(RboxRecord::Subrole(a.clone(), b.clone()));
                            out.push(RboxRecord::Subrole(b, a));
                        }
                    }
                }
            }
            "TransitiveObjectProperty" => {
                // Always retain this as RBox side data. Consumers decide
                // whether to compile it; dropping it here made that decision
                // depend on an environment variable during parsing.
                if let Some(r) = plain_role(reg, args[0]) {
                    out.push(RboxRecord::Transitive(r));
                }
            }
            "SymmetricObjectProperty" => {
                let r = plain_role(reg, args[0]).unwrap_or_else(|| format!("{:?}", args[0]));
                out.push(RboxRecord::Fenced("symmetric-role".to_string(), r));
            }
            "ReflexiveObjectProperty" => {
                // Reflexive roles are EL++ and handled natively by the EL
                // completion (self-edge seeding), so this record is EL-safe (see
                // `el_rbox_safe`). The frontend still emits the `[] -> R(x,x)`
                // fact that carries the semantics.
                let r = plain_role(reg, args[0]).unwrap_or_else(|| format!("{:?}", args[0]));
                out.push(RboxRecord::Fenced("reflexivity".to_string(), r));
            }
            "IrreflexiveObjectProperty" => {
                // Irreflexivity is the negative constraint `R(x,x) -> ⊥`, which EL
                // completion cannot express; keep it fenced to the CB engine.
                let r = plain_role(reg, args[0]).unwrap_or_else(|| format!("{:?}", args[0]));
                out.push(RboxRecord::Fenced("irreflexivity".to_string(), r));
            }
            "FunctionalObjectProperty" => {
                // in-fragment for SHQ, not fenced
            }
            "InverseFunctionalObjectProperty" => {
                let r = plain_role(reg, args[0]).unwrap_or_else(|| format!("{:?}", args[0]));
                out.push(RboxRecord::Fenced("inverse-functional".to_string(), r));
            }
            "AsymmetricObjectProperty" | "DisjointObjectProperties" => {
                out.push(RboxRecord::Fenced(
                    "role-constraint".to_string(),
                    head.to_string(),
                ));
            }
            _ => {}
        }
    }
}

/// Port of `el_route.rbox_el_safe`: the RBox is safe to hand to the EL
/// completion reasoner iff every record is `subrole`/`domain`/`range` (folded
/// into the clauses with full semantics) or a fenced `role-chain` (also folded
/// into NF7 by `normalise`). Inverse / symmetric / functional / etc. are only
/// handled by the context-engine trigger machinery and never reach the clauses,
/// so they make completion incomplete and force the CB fallback.
pub fn el_rbox_safe(records: &[RboxRecord]) -> bool {
    records.iter().all(|r| match r {
        RboxRecord::Subrole(..) | RboxRecord::Domain(..) | RboxRecord::Range(..) => true,
        RboxRecord::Fenced(reason, _) => reason == "role-chain" || reason == "reflexivity",
        RboxRecord::Inverse(..) => false,
        RboxRecord::Transitive(..) | RboxRecord::Chain(..) | RboxRecord::ChainN(..) => true,
    })
}

/// Like [`el_rbox_safe`], but additionally admits a *symmetric* or *inverse*
/// role record when the role(s) it names are inert for classification, i.e. not
/// in `relevant` (see `preprocess::concept_relevant_roles`). The inert
/// reverse-edge clauses are pruned separately by `prune_inert_role_bridges`, so
/// the clause set the EL fast path receives is pure EL and the dropped axiom
/// changes no named-concept subsumption. Every other record is judged exactly
/// as `el_rbox_safe` would, so an ontology with no symmetric/inverse records (or
/// with a relevant one) gets the identical routing decision as before.
pub fn el_rbox_safe_relaxed(records: &[RboxRecord], relevant: &HashSet<String>) -> bool {
    records.iter().all(|r| match r {
        RboxRecord::Subrole(..) | RboxRecord::Domain(..) | RboxRecord::Range(..) => true,
        RboxRecord::Fenced(reason, role) => {
            reason == "role-chain"
                || reason == "reflexivity"
                || (reason == "symmetric-role" && !relevant.contains(role))
        }
        RboxRecord::Inverse(r, s) => !relevant.contains(r) && !relevant.contains(s),
        RboxRecord::Transitive(..) | RboxRecord::Chain(..) | RboxRecord::ChainN(..) => true,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parse;

    fn registry_bytes(registry: &IriRegistry) -> Vec<u8> {
        let mut entries: Vec<_> = registry.owned_entries().collect();
        entries.sort_unstable();
        serde_json::to_vec(&entries).unwrap()
    }

    fn record_bytes(records: &[RboxRecord]) -> Vec<u8> {
        serde_json::to_vec(&records.iter().map(to_row).collect::<Vec<_>>()).unwrap()
    }

    #[test]
    fn arbitrary_named_chain_is_retained_without_changing_binary_rows() {
        let text = "Ontology(\
            SubObjectPropertyOf(ObjectPropertyChain(<r> <s>) <t>) \
            SubObjectPropertyOf(ObjectPropertyChain(<r> <s> <u>) <v>))";
        let mut registry = IriRegistry::new();
        parse::parse_axioms(&mut registry, text).unwrap();
        let mut records = Vec::new();
        parse::for_each_ontology_child(text, |node| {
            rbox_node(&mut registry, node, &mut records);
            Ok(())
        })
        .unwrap();
        let rows: Vec<Vec<String>> = records.iter().map(to_row).collect();
        assert_eq!(rows[0], ["chain", "r", "s", "t"]);
        assert_eq!(rows[1], ["chain-n", "v", "r", "s", "u"]);
    }

    #[test]
    fn retained_rbox_replay_matches_full_second_parse_bytes() {
        let text = "Ontology(\
            Declaration(Class(<http://decl.example#A>)) \
            SubObjectPropertyOf(<http://one.example#r> <http://one.example#s>) \
            SubObjectPropertyOf(ObjectPropertyChain(<http://one.example#r> <http://two.example#r>) <http://one.example#t>) \
            ObjectPropertyDomain(<http://one.example#r> <http://class.example#A>) \
            ObjectPropertyRange(ObjectInverseOf(<http://one.example#s>) ObjectIntersectionOf(<http://class.example#A> <http://class.example#B>)) \
            EquivalentObjectProperties(<http://one.example#r> <http://two.example#r> <http://three.example#r>) \
            InverseObjectProperties(<http://one.example#r> <http://one.example#s>) \
            TransitiveObjectProperty(<http://one.example#t>) \
            SymmetricObjectProperty(<http://one.example#s>) \
            ReflexiveObjectProperty(<http://one.example#r>) \
            IrreflexiveObjectProperty(<http://two.example#r>) \
            InverseFunctionalObjectProperty(<http://one.example#s>) \
            DisjointObjectProperties(<http://one.example#r> <http://one.example#s>))";

        let mut retained_registry = IriRegistry::new();
        let mut raw = RawRbox::default();
        parse::parse_axioms_observed(&mut retained_registry, text, |node| raw.observe(node))
            .unwrap();
        let retained = raw.resolve(&mut retained_registry);

        let mut legacy_registry = IriRegistry::new();
        parse::parse_axioms(&mut legacy_registry, text).unwrap();
        let mut legacy = Vec::new();
        parse::for_each_ontology_child(text, |node| {
            rbox_node(&mut legacy_registry, node, &mut legacy);
            Ok(())
        })
        .unwrap();

        assert_eq!(record_bytes(&retained), record_bytes(&legacy));
        assert_eq!(
            registry_bytes(&retained_registry),
            registry_bytes(&legacy_registry)
        );
    }
}
