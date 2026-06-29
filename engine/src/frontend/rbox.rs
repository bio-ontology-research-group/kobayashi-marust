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
            if sh == "owl:Thing" || sh == "Thing" {
                Some(String::new())
            } else if sh == "owl:Nothing" || sh == "Nothing" {
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
                    // `chains` field for the Ht chain-unfolding.  The raw chain
                    // axiom is filtered from the clause stream (it bloats
                    // cb_to_ht); the chain info rides the rbox.  Fall back to the
                    // fenced record when the chain roles are not plain.
                    let chain_args: Vec<&Node> = match sub {
                        Node::List(_, ca) => strip_annotations(ca),
                        _ => Vec::new(),
                    };
                    if chain_args.len() == 2
                        && std::env::var_os("KM_KEEP_CHAIN_AXIOMS").is_some()
                    {
                        if let (Some(r1), Some(r2), Some(rs)) =
                            (plain_role(reg, chain_args[0]), plain_role(reg, chain_args[1]), ssup)
                        {
                            out.push(RboxRecord::Chain(r1, r2, rs));
                        } else {
                            out.push(RboxRecord::Fenced(
                                "role-chain".to_string(),
                                format!("{:?} ⊑ {:?}", sub, sup),
                            ));
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
                // KM_KEEP_CHAIN_AXIOMS: emit as side data so cb_to_ht can
                // populate the TInput `transitive` field.  Not fenced (TBox
                // normalisation still handles it for the default path).
                if std::env::var_os("KM_KEEP_CHAIN_AXIOMS").is_some() {
                    if let Some(r) = plain_role(reg, args[0]) {
                        out.push(RboxRecord::Transitive(r));
                    }
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
        RboxRecord::Transitive(..) | RboxRecord::Chain(..) => true,
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
        RboxRecord::Transitive(..) | RboxRecord::Chain(..) => true,
    })
}
