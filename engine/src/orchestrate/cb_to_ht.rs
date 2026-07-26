//! Convert CB DL-clauses into HT-clauses (the tableau `TInput`). A faithful port
//! of `engine/py/cb_to_ht.py`: the only transform is *reverse Skolemization*
//! (a function symbol `f` from `Body → r(x,f(x))` + `Body → C_i(f(x))` becomes
//! the HT existential `Body → ∃r.fil(x)`), plus RBox edge clauses, the ≥n/≤n
//! slot/eq encodings, nominal fencing, the Horrocks-Sattler transitivity
//! propagation, and the `KM_HT_EMELIM` complementary-definer elimination.
//!
//! Byte-identity with the Python reference depends on two things, both preserved
//! here: concept/role ids are assigned in FIRST-SEEN (insertion) order, and the
//! HT-clauses are emitted in exactly the same pass order.

use std::collections::{HashMap, HashSet};

use crate::json_io::{JAtom, JClause, JRule, JRuleAtom, JRuleTerm, JTerm};

// ---------------------------------------------------------------------------
// KM_HT_RULES (Stage 2): ABox seeding + DL-safe rule firing
// ---------------------------------------------------------------------------
/// The O-guard concept asserted on every named individual node, so a rule
/// variable only ever binds to a named individual (DL-safety): firing a rule on
/// an anonymous ∃-successor is unsound.
const O_GUARD: &str = "__O__";

fn nom_of(ind: &str) -> String {
    format!("__nom__{}", ind)
}

/// A ground ABox fact recognised in the clause set (only when `ht_rules`). The
/// frontend emits assertions as ground clauses (`normalise.rs`): a
/// `ClassAssertion` as `⊤ → q(a)`, a `RoleAssertion` as `⊤ → r(a,b)`,
/// `SameIndividual` as `⊤ → a≈b`, `DifferentIndividuals` as `a≈b → ⊥`.
enum AboxFact {
    Concept(String, String),      // q(a)
    Role(String, String, String), // r(a,b)
    Same(String, String),         // a ≈ b
    Diff(String, String),         // a ≠ b  (recorded, not encoded — see below)
}

fn ind_name(t: &JTerm) -> Option<&str> {
    if let JTerm::Ind { name } = t {
        Some(name.as_str())
    } else {
        None
    }
}

/// Recognise a ground ABox fact (all terms individuals). Returns `None` for any
/// clause with a variable term — those are TBox/RBox clauses handled normally.
fn abox_fact(c: &JClause) -> Option<AboxFact> {
    if c.body.is_empty() && c.head.len() == 1 {
        return match &c.head[0] {
            JAtom::Concept { concept, term } => Some(AboxFact::Concept(
                concept.clone(),
                ind_name(term)?.to_string(),
            )),
            JAtom::Role {
                role,
                source,
                target,
            } => Some(AboxFact::Role(
                role.clone(),
                ind_name(source)?.to_string(),
                ind_name(target)?.to_string(),
            )),
            JAtom::Eq { left, right } => Some(AboxFact::Same(
                ind_name(left)?.to_string(),
                ind_name(right)?.to_string(),
            )),
        };
    }
    if c.head.is_empty() && c.body.len() == 1 {
        if let JAtom::Eq { left, right } = &c.body[0] {
            return Some(AboxFact::Diff(
                ind_name(left)?.to_string(),
                ind_name(right)?.to_string(),
            ));
        }
    }
    None
}

fn rule_term_name(t: &JRuleTerm) -> (bool, &str) {
    match t {
        JRuleTerm::Var { name } => (false, name.as_str()),
        JRuleTerm::Ind { name } => (true, name.as_str()),
    }
}

/// Build the HT clause for one DL-safe rule (`ht_rules` path). Each distinct rule
/// term gets a Subst index; every variable is O-guarded (`__O__(v)`) and every
/// `Ind(a)` term is pinned by `__nom__a(v)`, so the matcher only binds variables
/// to named individuals.
///
/// SameIndividual atoms ARE encoded (the fragment the frontend contract now
/// promises to fire):
///   - a *body* `SameAs(u, v)` guard unifies u and v onto ONE Subst variable
///     (both positions share a node). Sound: a single O-guarded node trivially
///     satisfies u ≈ v, and any binding where the two named individuals are the
///     same collapses onto that node (which then carries both `__nom__` pins).
///   - a *head* `SameAs(u, v)` conclusion emits `HAtom::Eq{u,v}` (the rule
///     derives the equality, which the tableau o-rule then merges).
/// A `DifferentIndividuals` atom has NO sound encoding in the fast Ht (it tracks
/// no node distinctness, so a body guard `u ≠ v` cannot be tested and a head
/// `u ≠ v` cannot be recorded). Such a rule is DEFERRED wholesale: `None` is
/// returned and the caller counts it as `dropped`. Dropping a rule from the
/// one-sided consistency precheck is sound (a lost constraint can lose an
/// inconsistency, never invent one). `None` is likewise returned for an empty
/// head. The second tuple element is the individual names the rule references
/// (so they are registered as nominal nodes). Concept/role ids are assigned in
/// `ids`.
fn build_rule_clause(
    rule: &JRule,
    ids: &mut Ids,
    oguard: usize,
) -> Option<(HtClause, Vec<String>)> {
    type Key = (bool, String);
    let key = |t: &JRuleTerm| -> Key {
        let (is_ind, name) = rule_term_name(t);
        (is_ind, name.to_string())
    };
    // Union-find over rule terms; a body `SameAs` unifies its two terms. A body
    // `DifferentIndividuals` defers the whole rule (no sound distinctness here).
    fn find(parent: &mut HashMap<Key, Key>, k: Key) -> Key {
        match parent.get(&k).cloned() {
            Some(p) if p != k => {
                let root = find(parent, p);
                parent.insert(k, root.clone());
                root
            }
            _ => k,
        }
    }
    let mut parent: HashMap<Key, Key> = HashMap::new();
    for a in &rule.body {
        match a {
            JRuleAtom::Same { left, right } => {
                let ra = find(&mut parent, key(left));
                let rb = find(&mut parent, key(right));
                if ra != rb {
                    parent.insert(ra, rb);
                }
            }
            JRuleAtom::Diff { .. } => return None, // no sound distinctness encoding
            _ => {}
        }
    }
    // Resolve every term to its canonical (unified) root up front, so `vget`
    // never mutates the union-find while `conv` holds it.
    let mut canon: HashMap<Key, usize> = HashMap::new();
    let mut next_var = 0usize;
    let mut ind_vars: Vec<(usize, String)> = Vec::new();
    let mut all_vars: Vec<usize> = Vec::new();
    let mut vget = |t: &JRuleTerm| -> usize {
        let root = find(&mut parent, key(t));
        let v = if let Some(&v) = canon.get(&root) {
            v
        } else {
            let v = next_var;
            next_var += 1;
            canon.insert(root, v);
            v
        };
        if !all_vars.contains(&v) {
            all_vars.push(v);
        }
        // pin every `Ind(a)` occurrence, regardless of which side of a SameAs it
        // sits on, so `SameAs(x, a)` still pins x's shared variable to `__nom__a`.
        let (is_ind, name) = rule_term_name(t);
        if is_ind && !ind_vars.iter().any(|(vv, n)| *vv == v && n == name) {
            ind_vars.push((v, name.to_string()));
        }
        v
    };
    let mut conv = |atoms: &[JRuleAtom], ids: &mut Ids, is_head: bool| -> Option<Vec<HAtom>> {
        let mut out = Vec::new();
        for a in atoms {
            match a {
                JRuleAtom::Class { concept, term } => {
                    out.push(HAtom::Concept {
                        neg: false,
                        c: ids.cid(concept),
                        t: vget(term),
                    });
                }
                JRuleAtom::Role {
                    role,
                    source,
                    target,
                } => {
                    let s = vget(source);
                    let t = vget(target);
                    out.push(HAtom::Role {
                        r: ids.rid(role),
                        s,
                        t,
                    });
                }
                JRuleAtom::Same { left, right } => {
                    // Register both terms (variable assignment + `__nom__` pins);
                    // a body guard emits no atom (already unified via `canon`), a
                    // head conclusion emits the equality.
                    let l = vget(left);
                    let r = vget(right);
                    if is_head {
                        out.push(HAtom::Eq { s: l, t: r });
                    }
                }
                JRuleAtom::Diff { .. } => return None, // deferred (see doc comment)
            }
        }
        Some(out)
    };
    let mut body = conv(&rule.body, ids, false)?;
    let head = conv(&rule.head, ids, true)?;
    if head.is_empty() {
        return None;
    }
    for &v in &all_vars {
        body.push(HAtom::Concept {
            neg: false,
            c: oguard,
            t: v,
        });
    }
    let mut inds: Vec<String> = Vec::new();
    for (v, a) in &ind_vars {
        let na = ids.cid(&nom_of(a));
        body.push(HAtom::Concept {
            neg: false,
            c: na,
            t: *v,
        });
        inds.push(a.clone());
    }
    Some((HtClause { body, head }, inds))
}

// ---------------------------------------------------------------------------
// output (TInput) types
// ---------------------------------------------------------------------------
#[derive(serde::Serialize, serde::Deserialize, Clone, Debug, PartialEq, Eq, Hash)]
#[serde(tag = "k")]
pub enum HAtom {
    #[serde(rename = "c")]
    Concept { neg: bool, c: usize, t: usize },
    #[serde(rename = "r")]
    Role { r: usize, s: usize, t: usize },
    #[serde(rename = "eq")]
    Eq { s: usize, t: usize },
    #[serde(rename = "e")]
    Exist {
        r: usize,
        neg: bool,
        c: usize,
        t: usize,
    },
}

#[derive(serde::Serialize, serde::Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct HtClause {
    pub body: Vec<HAtom>,
    pub head: Vec<HAtom>,
}

#[derive(serde::Serialize, serde::Deserialize, Clone)]
pub struct Fenced {
    pub reason: String,
    pub detail: String,
}

/// KM_HT_CARD: a first-class number restriction in the TInput, resolved to HT
/// concept/role ids. `min` ⇒ `≥n role.filler`, else `≤n role.filler`. The HT
/// worker (`run_json`) installs these via `set_card_defs_raw`; the clausal
/// `⋁ Eq` pigeonhole for each marker is dropped from `clauses`.
#[derive(serde::Serialize, serde::Deserialize, Clone)]
pub struct CardDefJson {
    pub marker: usize,
    pub min: bool,
    pub n: u32,
    pub role: usize,
    pub filler: usize,
}

/// Numeric, independently validated named-individual state consumed by the
/// fast hypertableau.  Indices in `different`/role assertions refer to
/// `individuals`; concept and role values use this TInput's id tables.
#[derive(serde::Serialize, serde::Deserialize, Clone, Debug, Default, PartialEq, Eq)]
#[serde(default)]
pub struct NativeAboxJson {
    pub complete: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub individuals: Vec<NativeIndividualJson>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub different: Vec<(usize, usize)>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub role_assertions: Vec<(usize, usize, usize)>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub negative_role_assertions: Vec<(usize, usize, usize)>,
}

impl NativeAboxJson {
    pub fn is_empty(&self) -> bool {
        !self.complete
            && self.individuals.is_empty()
            && self.different.is_empty()
            && self.role_assertions.is_empty()
            && self.negative_role_assertions.is_empty()
    }
}

#[derive(serde::Serialize, serde::Deserialize, Clone, Debug, Default, PartialEq, Eq)]
#[serde(default)]
pub struct NativeIndividualJson {
    /// Every proxy denotes this same singleton and is seeded on one root.
    pub proxies: Vec<usize>,
    /// Positive normalized concept markers for source ClassAssertions.
    pub assertions: Vec<usize>,
}

#[derive(serde::Serialize, serde::Deserialize, Default, Clone)]
#[serde(default)]
pub struct TInput {
    pub concepts: Vec<String>,
    pub roles: Vec<String>,
    pub clauses: Vec<HtClause>,
    pub queries: Vec<usize>,
    pub dropped: usize,
    pub fenced: Vec<Fenced>,
    pub inverse: bool,
    pub number: bool,
    /// A normalized-RBox recheck that every first-class number role is in a
    /// component disjoint from inverse/symmetric and non-simple roles. This
    /// does not remove inverse semantics: their two swapped role clauses stay
    /// in `clauses`. It only proves that the missing SHOIQ NN/NI rule has no
    /// number-role premise for this input.
    #[serde(default, skip_serializing_if = "is_false")]
    pub inverse_cardinality_role_separable: bool,
    pub nominals: Vec<usize>,
    /// Auditable source payload retained for the native Konclude bridge.
    #[serde(
        default,
        skip_serializing_if = "crate::json_io::NominalAboxMeta::is_empty"
    )]
    pub nominal_abox: crate::json_io::NominalAboxMeta,
    /// Numeric exact payload for the fast Ht.  Produced only after independent
    /// name/id/coverage validation of `nominal_abox`.
    #[serde(default, skip_serializing_if = "NativeAboxJson::is_empty")]
    pub native_abox: NativeAboxJson,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub card_defs: Vec<CardDefJson>,
    /// Detected role chains `(R1, R2, R)` for `R1∘R2⊑R` (KM_KEEP_CHAIN_AXIOMS).
    /// Populated from the raw chain axioms, which are EXCLUDED from `clauses`
    /// (they bloat cb_to_ht's cardinality/disjunction expansion).  Consumed by
    /// the Ht chain-unfolding (`ht_chain_unfolding_clauses`) and the QoSat
    /// fprop chain-unfolding for the faithful Konclude role-automaton port.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub chains: Vec<(usize, usize, usize)>,
    /// Transitive roles (KM_KEEP_CHAIN_AXIOMS), from the raw `R∘R⊑R` axioms.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub transitive: Vec<usize>,
    /// Source RBox object-property domains `(role, concept)`. The DL-clause
    /// copies alone cannot distinguish these axioms from clausifier-generated
    /// guarded class rules. The Konclude bridge uses this provenance to fill
    /// `CRole::domainLinker` exactly.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub role_domains: Vec<(usize, usize)>,
    /// Source RBox object-property ranges `(role, concept)`, paired with
    /// [`TInput::role_domains`] for exact native `CRole` construction.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub role_ranges: Vec<(usize, usize)>,
    /// Fresh-concept structural definitions retained by the frontend. The
    /// bridge resolves these markers to native signed SOME/ALL/AND/OR concepts
    /// when triggered absorption is enabled.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub definers: Vec<crate::json_io::DefinerMeta>,
    /// Normalized source TBox. The bridge absorbs this before clausification,
    /// matching Konclude's preprocessing boundary.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub source_axioms: Vec<crate::json_io::SourceAxiomMeta>,
}

fn is_false(value: &bool) -> bool {
    !*value
}

/// Resolve and validate the frontend's typed ABox against a converted TInput.
/// The function is intentionally fail closed: it installs no partial native
/// state, and a nominal-bearing incomplete payload adds a route fence.
pub fn install_nominal_abox(tin: &mut TInput, meta: &crate::json_io::NominalAboxMeta) -> bool {
    use std::collections::{HashMap, HashSet};

    tin.nominal_abox = meta.clone();
    let has_nominal_input = !meta.individuals.is_empty()
        || !meta.different.is_empty()
        || !meta.role_assertions.is_empty()
        || !meta.negative_role_assertions.is_empty()
        || !tin.nominals.is_empty();

    // Resolve against scratch vectors.  Nothing semantic is installed until
    // every name, index, and coverage invariant has passed.
    let resolved = (|| -> Result<
        (
            NativeAboxJson,
            Vec<String>,
            Vec<String>,
            Vec<HtClause>,
            Vec<usize>,
        ),
        String,
    > {
        if !meta.complete || !meta.unsupported.is_empty() {
            return Err(if meta.unsupported.is_empty() {
                "frontend ABox coverage certificate is false".into()
            } else {
                meta.unsupported.join("; ")
            });
        }

        let mut concepts = tin.concepts.clone();
        let mut roles = tin.roles.clone();
        let mut concept_ids: HashMap<String, usize> = concepts
            .iter()
            .cloned()
            .enumerate()
            .map(|(id, name)| (name, id))
            .collect();
        let mut role_ids: HashMap<String, usize> = roles
            .iter()
            .cloned()
            .enumerate()
            .map(|(id, name)| (name, id))
            .collect();
        let mut individual_ids = HashMap::new();
        let mut proxy_owner = HashMap::new();
        let mut native = NativeAboxJson::default();

        for entry in &meta.individuals {
            if entry.individual.is_empty() {
                return Err("empty individual name".into());
            }
            if entry.proxies.is_empty() {
                return Err(format!("individual {} has no proxy", entry.individual));
            }
            if entry.assertions.len() != entry.assertion_markers.len() {
                return Err(format!(
                    "individual {} has {} assertion(s) but {} marker(s)",
                    entry.individual,
                    entry.assertions.len(),
                    entry.assertion_markers.len()
                ));
            }
            if individual_ids.contains_key(entry.individual.as_str()) {
                return Err(format!("duplicate individual {}", entry.individual));
            }
            let index = native.individuals.len();
            individual_ids.insert(entry.individual.as_str(), index);

            let mut proxies = Vec::new();
            for proxy in &entry.proxies {
                if proxy.is_empty() {
                    return Err(format!("individual {} has an empty proxy", entry.individual));
                }
                if proxy_owner
                    .insert(proxy.as_str(), entry.individual.as_str())
                    .is_some_and(|owner| owner != entry.individual.as_str())
                {
                    return Err(format!("proxy {proxy} belongs to multiple individuals"));
                }
                let id = match concept_ids.get(proxy) {
                    Some(&id) => id,
                    None => {
                        let id = concepts.len();
                        concepts.push(proxy.clone());
                        concept_ids.insert(proxy.clone(), id);
                        id
                    }
                };
                proxies.push(id);
            }
            proxies.sort_unstable();
            proxies.dedup();

            let mut assertions = Vec::new();
            for marker in &entry.assertion_markers {
                // Assertion markers come from normalized clauses/definers;
                // unlike a proxy, an absent marker cannot be manufactured.
                let Some(&id) = concept_ids.get(marker) else {
                    return Err(format!(
                        "ClassAssertion marker {marker} for {} is unresolved",
                        entry.individual
                    ));
                };
                assertions.push(id);
            }
            assertions.sort_unstable();
            assertions.dedup();
            native
                .individuals
                .push(NativeIndividualJson { proxies, assertions });
        }

        for (left, right) in &meta.different {
            let pair = (
                *individual_ids
                    .get(left.as_str())
                    .ok_or_else(|| format!("DifferentIndividuals left {left} is unresolved"))?,
                *individual_ids
                    .get(right.as_str())
                    .ok_or_else(|| format!("DifferentIndividuals right {right} is unresolved"))?,
            );
            native.different.push(pair);
        }

        fn resolve_roles(
            assertions: &[crate::json_io::NominalRoleAssertionMeta],
            individual_ids: &HashMap<&str, usize>,
            role_ids: &mut HashMap<String, usize>,
            roles: &mut Vec<String>,
        ) -> Result<Vec<(usize, usize, usize)>, String> {
            let mut out = Vec::with_capacity(assertions.len());
            for assertion in assertions {
                if is_universal_object_role(&assertion.role) {
                    return Err(format!(
                        "builtin object role {} is outside native ABox",
                        assertion.role
                    ));
                }
                let source = *individual_ids.get(assertion.source.as_str()).ok_or_else(|| {
                    format!("role assertion source {} is unresolved", assertion.source)
                })?;
                let target = *individual_ids.get(assertion.target.as_str()).ok_or_else(|| {
                    format!("role assertion target {} is unresolved", assertion.target)
                })?;
                let role = match role_ids.get(&assertion.role) {
                    Some(&role) => role,
                    None => {
                        // A role occurring only negatively has no clause
                        // occurrence.  The typed source name authorizes this
                        // otherwise empty role id.
                        let role = roles.len();
                        roles.push(assertion.role.clone());
                        role_ids.insert(assertion.role.clone(), role);
                        role
                    }
                };
                out.push((role, source, target));
            }
            Ok(out)
        }
        native.role_assertions = resolve_roles(
            &meta.role_assertions,
            &individual_ids,
            &mut role_ids,
            &mut roles,
        )?;
        native.negative_role_assertions = resolve_roles(
            &meta.negative_role_assertions,
            &individual_ids,
            &mut role_ids,
            &mut roles,
        )?;

        // A negative ground role assertion is exactly the guarded clash clause
        // {a}(x) ∧ R(x,y) ∧ {b}(y) -> ⊥.  Ordinary subrole/inverse/chain edge
        // propagation therefore makes the constraint apply to derived edges too.
        let mut negative_clauses = Vec::new();
        for &(role, source, target) in &native.negative_role_assertions {
            let source_proxy = *native.individuals[source]
                .proxies
                .first()
                .ok_or_else(|| "negative assertion source has no proxy".to_string())?;
            let target_proxy = *native.individuals[target]
                .proxies
                .first()
                .ok_or_else(|| "negative assertion target has no proxy".to_string())?;
            negative_clauses.push(HtClause {
                body: vec![
                    HAtom::Concept {
                        neg: false,
                        c: source_proxy,
                        t: 0,
                    },
                    HAtom::Role {
                        r: role,
                        s: 0,
                        t: 1,
                    },
                    HAtom::Concept {
                        neg: false,
                        c: target_proxy,
                        t: 1,
                    },
                ],
                head: Vec::new(),
            });
        }

        let mut nominals = tin.nominals.clone();
        let mut seen_nominals: HashSet<usize> = nominals.iter().copied().collect();
        for individual in &native.individuals {
            for &proxy in &individual.proxies {
                if seen_nominals.insert(proxy) {
                    nominals.push(proxy);
                }
            }
        }
        nominals.sort_unstable();
        nominals.dedup();
        native.complete = true;
        Ok((native, concepts, roles, negative_clauses, nominals))
    })();

    match resolved {
        Ok((native, concepts, roles, negative_clauses, nominals)) => {
            tin.concepts = concepts;
            tin.roles = roles;
            tin.clauses.extend(negative_clauses);
            tin.nominals = nominals;
            tin.native_abox = native;
            true
        }
        Err(detail) => {
            if has_nominal_input
                && !tin
                    .fenced
                    .iter()
                    .any(|fence| fence.reason == "incomplete-nominal-abox")
            {
                tin.fenced.push(Fenced {
                    reason: "incomplete-nominal-abox".into(),
                    detail,
                });
            }
            false
        }
    }
}

// ---------------------------------------------------------------------------
// name helpers (mirror cb_to_ht.short / is_internal / is_bottom)
// ---------------------------------------------------------------------------
fn short(n: &str) -> &str {
    let after_hash = n.rsplit('#').next().unwrap_or(n);
    after_hash.rsplit('/').next().unwrap_or(after_hash)
}
pub(crate) fn is_bottom(n: &str) -> bool {
    let s = short(n);
    s == "Nothing" || s == "owl:Nothing"
}
pub(crate) fn is_internal(n: &str) -> bool {
    let s = short(n);
    s.starts_with("Q_")
        || s.starts_with("__")
        || s.starts_with("aux_")
        || s.starts_with("def_")
        || (is_reserved_vocabulary_curie(s) && s != "Nothing" && s != "owl:Nothing")
}

/// True for OWL/RDF/RDFS/XSD/XML builtin vocabulary written in CURIE form
/// (`owl:Thing`, `rdfs:Literal`, `xsd:integer`, …).
///
/// The bridge's classification universe uses [`is_internal`] to drop synthetic
/// frontend markers and builtin vocabulary. It previously treated ANY name
/// containing a `:` as internal, but a real class localname may legitimately
/// contain a colon (URN class IRIs like `urn:example:Foo` for which `short`
/// strips no `#`/`/`, or colon-bearing fragments like `#Part:Whole`). Matching
/// every colon silently excluded such a class from the universe, so no
/// subsumption `X ⊑ ThatClass` was ever emitted and the drop was not counted as
/// unsound or incomplete. Konclude never approximates this away, and the
/// frontend's own internal-name predicate (`iri::reserved_internal_prefix`) is
/// prefix-based, not colon-based. Match only the reserved vocabulary prefixes,
/// which are exactly the builtins the heuristic intends to exclude.
fn is_reserved_vocabulary_curie(s: &str) -> bool {
    matches!(
        s.split_once(':'),
        Some(("owl" | "rdf" | "rdfs" | "xsd" | "xml", _))
    )
}

fn is_universal_object_role(role: &str) -> bool {
    matches!(
        short(role),
        "topObjectProperty"
            | "owl:topObjectProperty"
            | "bottomObjectProperty"
            | "owl:bottomObjectProperty"
    )
}

/// Recheck the source-profile certificate against the exact normalized inputs
/// handed to the HT converter. The check is deliberately conservative:
/// subroles and equivalences are treated as undirected dependencies, every
/// role in a chain component is rejected for cardinality, and any inline
/// `ObjectInverseOf` (`__inv__`) or malformed RBox row declines.
///
/// This is not an "inert inverse" test. Every accepted inverse pair is still
/// compiled below into both swapped-orientation role clauses. The certificate
/// only establishes that a number restriction cannot apply to an inverse,
/// inverse-connected, chained, or transitive role. Under that condition the
/// SHOQ o/number rules and the inverse-aware SHIQ blocking compose without the
/// otherwise-required Konclude NN/NI nominal-predecessor rule.
fn normalized_inverse_cardinality_role_separable(
    clauses: &[JClause],
    rbox: Option<&[Vec<String>]>,
    cardinalities: &[crate::json_io::CardMeta],
) -> bool {
    if cardinalities.is_empty()
        || cardinalities
            .iter()
            .any(|cardinality| is_universal_object_role(&cardinality.role))
        || clauses.iter().any(|clause| {
            clause.body.iter().chain(clause.head.iter()).any(|atom| {
                matches!(atom, JAtom::Role { role, .. }
                if short(role).starts_with("__inv__") || is_universal_object_role(role))
            })
        })
    {
        return false;
    }

    // CardMeta is deliberately optional for source FunctionalObjectProperty
    // (normalise.rs emits it only under KM_HT_CARD_FN). Recover every clausal
    // number role as well: a functional / inverse-functional / ≤n clause has
    // an Eq head and its counted roles in the body. An Eq-head without a role
    // is outside this certificate (e.g. ground equality) and fails closed.
    let mut number_roles: HashSet<&str> = cardinalities
        .iter()
        .map(|cardinality| cardinality.role.as_str())
        .collect();
    for clause in clauses {
        if clause
            .head
            .iter()
            .any(|atom| matches!(atom, JAtom::Eq { .. }))
        {
            let mut saw_role = false;
            for role in clause.body.iter().filter_map(|atom| match atom {
                JAtom::Role { role, .. } => Some(role.as_str()),
                _ => None,
            }) {
                saw_role = true;
                number_roles.insert(role);
            }
            if !saw_role {
                return false;
            }
        }
    }

    let Some(rbox) = rbox else {
        return false;
    };
    let mut dependencies: HashMap<&str, HashSet<&str>> = HashMap::new();
    let mut inverse_roles: HashSet<&str> = HashSet::new();
    let mut non_simple_roles: HashSet<&str> = HashSet::new();
    let mut saw_inverse = false;
    let mut invalid = false;

    fn connect<'a>(
        left: &'a str,
        right: &'a str,
        dependencies: &mut HashMap<&'a str, HashSet<&'a str>>,
    ) {
        dependencies.entry(left).or_default().insert(right);
        dependencies.entry(right).or_default().insert(left);
    }
    for axiom in rbox {
        match axiom.first().map(String::as_str) {
            Some("inverse") if axiom.len() == 3 => {
                let left = axiom[1].as_str();
                let right = axiom[2].as_str();
                if is_universal_object_role(left) || is_universal_object_role(right) {
                    invalid = true;
                    continue;
                }
                inverse_roles.insert(left);
                inverse_roles.insert(right);
                connect(left, right, &mut dependencies);
                saw_inverse = true;
            }
            Some("subrole") if axiom.len() == 3 => {
                if is_universal_object_role(&axiom[1]) || is_universal_object_role(&axiom[2]) {
                    invalid = true;
                    continue;
                }
                connect(&axiom[1], &axiom[2], &mut dependencies);
            }
            Some("chain") if axiom.len() == 4 => {
                let roles = [axiom[1].as_str(), axiom[2].as_str(), axiom[3].as_str()];
                if roles.iter().any(|role| is_universal_object_role(role)) {
                    invalid = true;
                    continue;
                }
                for role in roles {
                    non_simple_roles.insert(role);
                    connect(roles[0], role, &mut dependencies);
                }
            }
            Some("transitive") if axiom.len() == 2 => {
                if is_universal_object_role(&axiom[1]) {
                    invalid = true;
                    continue;
                }
                non_simple_roles.insert(axiom[1].as_str());
            }
            Some("domain" | "range") if axiom.len() == 3 => {
                if is_universal_object_role(&axiom[1]) {
                    invalid = true;
                }
                // These clauses are emitted exactly below. They connect a role
                // to a class label, not two role components, so they do not
                // create an NN/NI number-role premise.
            }
            Some("fenced") if axiom.len() >= 3 && axiom[1].as_str() == "symmetric-role" => {
                let role = axiom[2].as_str();
                if is_universal_object_role(role) {
                    invalid = true;
                    continue;
                }
                inverse_roles.insert(role);
                saw_inverse = true;
            }
            // These shapes either combine inverse and number directly or are
            // not represented by the exact first-class RBox machinery.
            Some("fenced") | Some(_) | None => invalid = true,
        }
    }
    if invalid || !saw_inverse {
        return false;
    }

    let mut seen: HashSet<&str> = HashSet::new();
    let mut pending: Vec<&str> = number_roles.into_iter().collect();
    while let Some(role) = pending.pop() {
        if !seen.insert(role) {
            continue;
        }
        if short(role).starts_with("__inv__")
            || is_universal_object_role(role)
            || inverse_roles.contains(role)
            || non_simple_roles.contains(role)
        {
            return false;
        }
        if let Some(neighbours) = dependencies.get(role) {
            pending.extend(neighbours.iter().copied());
        }
    }
    true
}

// ===========================================================================
// KM_ROLE_AUTOMATON: ∃R.C reachability closure over named classes.
//
// Konclude compiles transitive roles + role chains + the sub-role hierarchy
// into a per-role automaton and propagates `∃R.C` through it at runtime via
// a per-node per-role reapply queue that re-fires on every newly-created edge
// (incl. generated successors) — CRoleChainAutomataTransformationPreProcess +
// applyALLRule.  KM's shared-filler QoSat model cannot fire that forward push
// across a shared/generated successor soundly (the r-Succ gap), so the marker
// `__trans__R__C` that propagates `∃R.C ⊑ D` consumers up a transitive R never
// reaches the root on chain-composed routes (ore_ont_14817: 71 missing
// `X ⊑ ∃develops_from.UBERON_0000926` subsumptions).
//
// This pass closes that gap with a SOUND, FINITE preprocessing closure over
// named classes, mirroring what Konclude's automaton derives at runtime:
//   - transitivity of R:     A ⊑ ∃R.B ∧ B ⊑ ∃R.C  ⟹  A ⊑ ∃R.C
//   - chain R1∘R2 ⊑ R:       A ⊑ ∃R1.B ∧ B ⊑ ∃R2.C  ⟝  A ⊑ ∃R.C
//   - sub-role S ⊑ R:        A ⊑ ∃S.C  ⟝  A ⊑ ∃R.C
// Each derived `A ⊑ ∃R.C` is emitted as marker-seed + consumer clauses using
// the existing `__trans__R__C` predicate name, so the in-engine propagation
// rides the SAME predicate (monotone, sound).  Named-to-named only (finite).
// ===========================================================================
fn role_automaton_exist_reachability(
    ht: &[HtClause],
    ids: &mut Ids,
    inverse_pairs: &[(String, String)],
) -> Vec<HtClause> {
    use std::collections::{HashMap, HashSet};
    let nc = ids.con_names.len();
    let nr = ids.rol_names.len();

    // -- detect transitive roles + chains from the rbox + marker clauses --
    // Transitivity is not a raw `R∘R⊑R` clause (filtered by the frontend
    // `is_chain_axiom`); it lives as the marker-propagation clause
    // `R(x,y) ∧ __trans__R__C(y) → __trans__R__C(x)`.  Re-detect it: every
    // `__trans__R__…` marker name names a transitive role R.  Chains are the
    // `__chain__S__…` / `__cmpp__S__P` / `__cmpc__S__P` markers (the frontend
    // `chain_clauses` / `transitive_chain_compose_clauses` emission), but
    // those encode the chain's CONSUMER side, not the (R1,R2,R) triple — so
    // for the chain join we instead scan the 2-role-body/1-role-head clauses
    // that survived (the frontend emits those for non-transitive chains).
    let mut trans: HashSet<usize> = HashSet::new();
    let mut chains: Vec<(usize, usize, usize)> = Vec::new(); // (r1,r2,r)
    let mut sub_super: HashMap<usize, Vec<usize>> = HashMap::new();
    // transitive roles from marker names
    for (i, n) in ids.con_names.iter().enumerate() {
        if let Some(rest) = n.strip_prefix("__trans__") {
            // format: __trans__R__C  (R is the role name, C the filler)
            if let Some(idx) = rest.find("__") {
                let rname = &rest[..idx];
                if let Some(&rid) = ids.rol_id.get(rname) {
                    trans.insert(rid);
                }
            }
        }
    }
    // chains + sub-roles from the clause set
    for c in ht {
        let rb: Vec<&HAtom> = c
            .body
            .iter()
            .filter(|a| matches!(a, HAtom::Role { .. }))
            .collect();
        if c.body.len() == 2
            && c.head.len() == 1
            && matches!(c.body[0], HAtom::Role { .. })
            && matches!(c.body[1], HAtom::Role { .. })
            && matches!(c.head[0], HAtom::Role { .. })
        {
            if let (
                HAtom::Role {
                    r: r1,
                    s: r1s,
                    t: r1t,
                },
                HAtom::Role {
                    r: r2,
                    s: r2s,
                    t: r2t,
                },
                HAtom::Role {
                    r: hr,
                    s: hs,
                    t: ht_,
                },
            ) = (rb[0], rb[1], &c.head[0])
            {
                let (fr, fs, sr, st) = if r1t == r2s {
                    (*r1, *r1s, *r2, *r2t)
                } else if r2t == r1s {
                    (*r2, *r2s, *r1, *r1t)
                } else {
                    continue;
                };
                if *hs == fs && *ht_ == st && fs != st && !(fr == sr && sr == *hr) {
                    chains.push((fr, sr, *hr));
                }
            }
            continue;
        }
        // sub-role S⊑R: body=[Role S x y], head=[Role R x y]
        if c.body.len() == 1
            && c.head.len() == 1
            && matches!(c.body[0], HAtom::Role { .. })
            && matches!(c.head[0], HAtom::Role { .. })
        {
            if let (
                HAtom::Role {
                    r: sr,
                    s: ss,
                    t: st,
                },
                HAtom::Role {
                    r: hr,
                    s: hs,
                    t: ht_,
                },
            ) = (rb[0], &c.head[0])
            {
                if *ss == *hs && *st == *ht_ && *ss != *st && sr != hr {
                    sub_super.entry(*sr).or_default().push(*hr);
                }
            }
        }
    }
    if trans.is_empty() && chains.is_empty() {
        return Vec::new();
    }
    if std::env::var_os("KM_HT_STATS").is_some() {
        eprintln!(
            "cb_to_ht [role-automaton] trans={} chains={} subroles={} nc={} nr={}",
            trans.len(),
            chains.len(),
            sub_super.len(),
            nc,
            nr
        );
    }

    // -- concept subsumption graph (A ⊑ B from A(x)→B(x) concept-only clauses) --
    // used to resolve the absorbed definer chains around ∃R.C.
    let mut sub: HashMap<usize, Vec<usize>> = HashMap::new();
    for c in ht {
        if c.body.len() == 1
            && c.head.len() == 1
            && matches!(
                c.body[0],
                HAtom::Concept {
                    neg: false,
                    t: 0,
                    ..
                }
            )
            && matches!(
                c.head[0],
                HAtom::Concept {
                    neg: false,
                    t: 0,
                    ..
                }
            )
        {
            if let (HAtom::Concept { c: a, .. }, HAtom::Concept { c: b, .. }) =
                (&c.body[0], &c.head[0])
            {
                if a != b {
                    sub.entry(*a).or_default().push(*b);
                }
            }
        }
    }
    // transitive closure of subsumption (per-start BFS; nc is bounded by named set)
    let sub_close = |start: usize| -> HashSet<usize> {
        let mut out = HashSet::new();
        let mut st = vec![start];
        while let Some(u) = st.pop() {
            for &v in sub.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
                if out.insert(v) {
                    st.push(v);
                }
            }
        }
        out
    };
    // reverse subsumption graph (subclasses): rsub[B] = {A : A ⊑ B}.  Used to
    // resolve the named sources `A ⊑* D` of an absorbed exists-introducer `D ⊑ ∃R.F`.
    let mut rsub: HashMap<usize, Vec<usize>> = HashMap::new();
    for (&a, sups) in sub.iter() {
        for &b in sups {
            rsub.entry(b).or_default().push(a);
        }
    }
    let rsub_close = |start: usize| -> HashSet<usize> {
        let mut out = HashSet::new();
        let mut st = vec![start];
        while let Some(u) = st.pop() {
            for &v in rsub.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
                if out.insert(v) {
                    st.push(v);
                }
            }
        }
        out
    };
    // super-role closure (reflexive-transitive)
    let super_close = |r: usize| -> HashSet<usize> {
        let mut out = HashSet::new();
        out.insert(r);
        let mut st = vec![r];
        while let Some(u) = st.pop() {
            for &v in sub_super.get(&u).map(|x| x.as_slice()).unwrap_or(&[]) {
                if out.insert(v) {
                    st.push(v);
                }
            }
        }
        out
    };

    // -- ∃R.C introducers: A ⊑ ∃R.C, resolving definer chains --
    // An exists-head clause `D(x) → ∃R.F(x)` where D is a definer reachable
    // from a named A (A ⊑* D), and F is a definer reaching named Cs (F ⊑* C).
    // Collect (A_named, R, C_named) for every named A that ⊑* D and named C ⊑* F.
    // exists-head clauses: body=[Concept D t:0], head contains Exist{r,c,t:0}
    let mut exists_heads: Vec<(usize, usize, usize)> = Vec::new(); // (D, R, F)
    for c in ht {
        if c.body.len() != 1
            || !matches!(
                c.body[0],
                HAtom::Concept {
                    neg: false,
                    t: 0,
                    ..
                }
            )
        {
            continue;
        }
        if let HAtom::Concept { c: d, .. } = c.body[0] {
            for h in &c.head {
                if let HAtom::Exist {
                    r,
                    neg: false,
                    c: f,
                    t: 0,
                } = h
                {
                    exists_heads.push((d, *r, *f));
                }
            }
        }
    }
    // For each exists-head (D,R,F): the named sources A with A ⊑* D, and named
    // fillers C with F ⊑* C.  Cache the closures.
    let mut src_cache: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut fil_cache: HashMap<usize, Vec<usize>> = HashMap::new();
    let named_sources = |d: usize, sc: &mut HashMap<usize, Vec<usize>>| -> Vec<usize> {
        // named A with A ⊑* D  (A is a subclass of D, reflexive): reverse
        // closure of D.  Includes D itself when D is named.
        if let Some(v) = sc.get(&d) {
            return v.clone();
        }
        let mut cls = rsub_close(d);
        cls.insert(d);
        let mut named: Vec<usize> = cls
            .into_iter()
            .filter(|&c| c < nc && !is_internal(&ids.con_names[c]))
            .collect();
        named.sort_unstable();
        named.dedup();
        sc.insert(d, named.clone());
        named
    };
    let named_fillers = |f: usize, fc: &mut HashMap<usize, Vec<usize>>| -> Vec<usize> {
        // named C with F ⊑* C  (C is a superclass of F, reflexive): forward
        // closure of F.  Includes F itself when F is named (reflexive ⊑).
        if let Some(v) = fc.get(&f) {
            return v.clone();
        }
        let mut cls = sub_close(f);
        cls.insert(f);
        let mut named: Vec<usize> = cls
            .into_iter()
            .filter(|&c| c < nc && !is_internal(&ids.con_names[c]))
            .collect();
        named.sort_unstable();
        named.dedup();
        fc.insert(f, named.clone());
        named
    };
    // intros: (A, R, C) for named A,C.  Also keep the (A,R,Fdef) form for the
    // chain join (the join is over the FILLER being a source of the next hop;
    // the named filler is the resolution target).
    let mut intros: HashSet<(usize, usize, usize)> = HashSet::new(); // (A, R, Cnamed)
                                                                     // by_rf for the fixpoint: (R, Cnamed) -> {Anamed}.  Use named throughout so
                                                                     // the closure is finite and the join is sound (A⊑∃R1.Bnamed, Bnamed⊑∃R2.C).
    let mut by_rf: HashMap<(usize, usize), HashSet<usize>> = HashMap::new();
    let mut _dbg_eh = 0u64;
    let mut _dbg_src0 = 0u64;
    for (d, r, f) in &exists_heads {
        _dbg_eh += 1;
        let srcs = named_sources(*d, &mut src_cache);
        if srcs.is_empty() {
            _dbg_src0 += 1;
        }
        let fils = named_fillers(*f, &mut fil_cache);
        for &a in &srcs {
            for &c in &fils {
                intros.insert((a, *r, c));
                by_rf.entry((*r, c)).or_default().insert(a);
            }
        }
    }
    if std::env::var_os("KM_HT_STATS").is_some() {
        eprintln!(
            "cb_to_ht [role-automaton] exists_heads={} src0={} intros0={}",
            _dbg_eh,
            _dbg_src0,
            intros.len()
        );
    }

    // -- ∃R.C consumers: ∃R.C ⊑ D — role-body + filler-concept-on-y clauses --
    // body=[Role R x y, Concept C y], head=[Concept D x].  Resolve definer
    // fillers: a consumer with filler-def F covers every named C ⊑* F.  And
    // sub-role: ∃S.C ⊑ D also covers ∃R.C ⊑ D when S ⊑* R.
    // (R, Cnamed) -> [Dnamed]
    let mut consumers: HashMap<(usize, usize), Vec<usize>> = HashMap::new();
    for c in ht {
        let rb: Vec<&HAtom> = c
            .body
            .iter()
            .filter(|a| matches!(a, HAtom::Role { .. }))
            .collect();
        if rb.len() != 1 || c.head.is_empty() {
            continue;
        }
        if let HAtom::Role { r, s: rs, t: rt } = rb[0] {
            if *rs != 0 || *rt == 0 {
                continue;
            }
            // single filler concept on y (=rt)
            let mut fil: Option<usize> = None;
            for a in &c.body {
                if let HAtom::Concept {
                    neg: false,
                    c: cc,
                    t,
                } = a
                {
                    if *t == *rt {
                        if fil.is_none() {
                            fil = Some(*cc);
                        } else {
                            fil = None;
                            break;
                        }
                    }
                }
            }
            let fdef = match fil {
                Some(f) => f,
                None => continue,
            };
            // head concepts on x (=0): named Ds
            let mut ds: Vec<usize> = Vec::new();
            for h in &c.head {
                if let HAtom::Concept {
                    neg: false,
                    c: cc,
                    t: 0,
                } = h
                {
                    if *cc < nc && !is_internal(&ids.con_names[*cc]) {
                        ds.push(*cc);
                    }
                }
            }
            if ds.is_empty() {
                continue;
            }
            // resolve filler: named Cs with C ⊑* fdef  (fdef is a definer above C)
            // NOTE: sub_close(fdef) gives concepts fdef subsumes; a named C with
            // C ⊑* fdef means fdef is in sub_close(C).  We need the reverse.  But
            // in the absorbed form the filler definer F satisfies F ⊑ C (F reaches
            // the named filler downward), so named_fillers(fdef) = sub_close(fdef)
            // filtered to named — that is what the exists side uses too.  Use the
            // same resolution for consistency.
            let fils = named_fillers(fdef, &mut fil_cache);
            for cf in fils {
                consumers
                    .entry((*r, cf))
                    .or_default()
                    .extend(ds.iter().copied());
            }
        }
    }

    // -- role-automaton two-step routes per super-role R --
    // (R1, R2) with R1∘R2 ⊑ U and U ⊑* R  ⟹  route for R.
    let mut two_step: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
    for (r1, r2, u) in &chains {
        for sup in super_close(*u) {
            two_step.entry(sup).or_default().push((*r1, *r2));
        }
    }
    for r in &trans {
        two_step.entry(*r).or_default().push((*r, *r));
    }

    // -- fixpoint closure --
    let mut changed = true;
    let mut iters = 0u32;
    while changed {
        changed = false;
        iters += 1;
        if iters > 2000 {
            break;
        }
        let snapshot = by_rf.clone();
        // two-step: A ⊑ ∃R1.B ∧ B ⊑ ∃R2.C ⟹ A ⊑ ∃R.C
        for (r, routes) in &two_step {
            for (r1, r2) in routes {
                // Bs with B ⊑ ∃R2.C: keys (R2, C) in snapshot
                let r2_cs: Vec<(usize, usize)> = snapshot
                    .keys()
                    .filter(|(rr, _)| rr == r2)
                    .cloned()
                    .collect();
                for (_, c) in r2_cs {
                    let bs = match snapshot.get(&(*r2, c)) {
                        Some(s) => s.iter().copied().collect::<Vec<_>>(),
                        None => continue,
                    };
                    for b in bs {
                        if let Some(as_) = snapshot.get(&(*r1, b)) {
                            for &a in as_ {
                                let set = by_rf.entry((*r, c)).or_default();
                                if set.insert(a) {
                                    intros.insert((a, *r, c));
                                    changed = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        // sub-role: A ⊑ ∃S.C ∧ S ⊑ R ⟹ A ⊑ ∃R.C
        for (s, sups) in &sub_super {
            for r in sups {
                let s_cs: Vec<(usize, usize)> =
                    snapshot.keys().filter(|(rr, _)| rr == s).cloned().collect();
                for (_, c) in s_cs {
                    let as_ = match snapshot.get(&(*s, c)) {
                        Some(s2) => s2.iter().copied().collect::<Vec<_>>(),
                        None => continue,
                    };
                    for a in as_ {
                        let set = by_rf.entry((*r, c)).or_default();
                        if set.insert(a) {
                            intros.insert((a, *r, c));
                            changed = true;
                        }
                    }
                }
            }
        }
    }

    // -- emit marker-seed + consumer clauses --
    // marker name __trans__R__C  (id allocated via ids.cid, mirroring the
    // frontend transitivity_clauses name so the predicates coincide when both
    // fire).  The marker propagates via the existing in-engine clauses; here
    // we only SEED it on each named A that R-reaches C, and fan out consumers.
    let _ = inverse_pairs; // (inverse not needed; the role automaton is forward)
    let _ = nr;
    let mut out = Vec::new();
    let mut marker_cache: HashMap<(usize, usize), usize> = HashMap::new();
    let mut emitted: HashSet<(usize, usize, usize)> = HashSet::new();
    for (a, r, c) in &intros {
        if !emitted.insert((*a, *r, *c)) {
            continue;
        }
        let mid = *marker_cache.entry((*r, *c)).or_insert_with(|| {
            ids.cid(&format!(
                "__trans__{}__{}",
                ids.rol_names[*r], ids.con_names[*c]
            ))
        });
        // seed: A(x) → marker(x)
        out.push(HtClause {
            body: vec![HAtom::Concept {
                neg: false,
                c: *a,
                t: 0,
            }],
            head: vec![HAtom::Concept {
                neg: false,
                c: mid,
                t: 0,
            }],
        });
        // consumers: marker(x) → D(x) for each D with ∃R.C ⊑ D (incl. sub-role)
        let mut ds: Vec<usize> = Vec::new();
        if let Some(v) = consumers.get(&(*r, *c)) {
            ds.extend(v.iter().copied());
        }
        for (s, sups) in &sub_super {
            if sups.iter().any(|rr| rr == r) {
                if let Some(v) = consumers.get(&(*s, *c)) {
                    ds.extend(v.iter().copied());
                }
            }
        }
        ds.sort_unstable();
        ds.dedup();
        for d in ds {
            out.push(HtClause {
                body: vec![HAtom::Concept {
                    neg: false,
                    c: mid,
                    t: 0,
                }],
                head: vec![HAtom::Concept {
                    neg: false,
                    c: d,
                    t: 0,
                }],
            });
        }
    }
    out
}

fn term_is_fun(t: &JTerm) -> bool {
    matches!(t, JTerm::Fun { .. })
}
/// `f(x)` only (arg must be var x); else None.
fn fun_sym(t: &JTerm) -> Option<&str> {
    if let JTerm::Fun { function, arg } = t {
        if let JTerm::Var { name } = arg.as_ref() {
            if name == "x" {
                return Some(function);
            }
        }
    }
    None
}
fn atom_has_fun(a: &JAtom) -> bool {
    match a {
        JAtom::Concept { term, .. } => term_is_fun(term),
        JAtom::Role { source, target, .. } => term_is_fun(source) || term_is_fun(target),
        JAtom::Eq { .. } => true, // treat as non-ALC
    }
}
/// f(x) ≈ g(x) between two Skolem function terms -> (f, g), else None.
fn eq_fun_pair(a: &JAtom) -> Option<(String, String)> {
    if let JAtom::Eq { left, right } = a {
        if let (Some(fi), Some(fj)) = (fun_sym(left), fun_sym(right)) {
            return Some((fi.to_string(), fj.to_string()));
        }
    }
    None
}

/// KM_HT_CARD: is `c` part of the clausal cardinality expansion the frontend
/// `define` emitted for a card marker (now represented first-class in
/// `card_defs`)? Matches the three shapes `define` produces (`normalise.rs`):
///   (1) `≥n` Skolem intro: body `[Concept(m,x)]` (m ∈ `min_markers`), head has a
///       function term (`m → role(x,f_i(x))` / `m → filler(f_i(x))`);
///   (2) `≥n` distinctness: empty head, body carries an `m` concept (m ∈
///       `min_markers`) and an `Eq(f_i,f_j)` between Skolem terms;
///   (3) `≤n` definitional: non-empty all-`Eq` head, body carries an `m` concept
///       (m ∈ `max_markers`) — the `⋁ Eq` pigeonhole.
/// Each marker is fresh and used only by its own restriction, so these shapes
/// never alias a non-cardinality clause (the `≥n` recognition Horn/`∨ Eq` clause
/// and the `q ∨ NQ` excluded middle keep an `m` concept in the HEAD, not matched).
fn card_drop(
    c: &JClause,
    min_markers: &std::collections::HashSet<String>,
    max_markers: &std::collections::HashSet<String>,
) -> bool {
    let body_has = |set: &std::collections::HashSet<String>| -> bool {
        c.body.iter().any(|a| matches!(a,
            JAtom::Concept { concept, term: JTerm::Var { name } } if name == "x" && set.contains(concept)))
    };
    // (1) ≥n Skolem intro.
    if c.head.iter().any(atom_has_fun) {
        let single_min = c.body.len() == 1
            && matches!(&c.body[0],
                JAtom::Concept { concept, term: JTerm::Var { name } } if name == "x" && min_markers.contains(concept));
        if single_min {
            return true;
        }
    }
    // (2) ≥n distinctness.
    if c.head.is_empty() && body_has(min_markers) && c.body.iter().any(|a| eq_fun_pair(a).is_some())
    {
        return true;
    }
    // (3) ≤n definitional pigeonhole.
    if !c.head.is_empty()
        && c.head.iter().all(|a| matches!(a, JAtom::Eq { .. }))
        && body_has(max_markers)
    {
        return true;
    }
    false
}

/// KM_HT_CARD_DROP_EM (experimental): does `c` match the `⊤ → Q ∨ NQ`
/// excluded-middle RECOGNITION clause emitted for a card marker? Shape: empty
/// body, head is a disjunction of `Concept(_, x)` atoms, at least one of whose
/// concepts is a fresh card marker (`min`/`max`). Card markers are fresh `Q_`
/// names used only by their own restriction, so a genuine ontology covering
/// disjunction (`⊤ ⊑ A ⊔ B` over named classes) never matches.
fn em_recognition_drop(
    c: &JClause,
    min_markers: &std::collections::HashSet<String>,
    max_markers: &std::collections::HashSet<String>,
) -> bool {
    if !c.body.is_empty() || c.head.len() < 2 {
        return false;
    }
    let all_concept_x = c.head.iter().all(|a| {
        matches!(a,
        JAtom::Concept { term: JTerm::Var { name }, .. } if name == "x")
    });
    if !all_concept_x {
        return false;
    }
    c.head.iter().any(|a| matches!(a,
        JAtom::Concept { concept, .. } if min_markers.contains(concept) || max_markers.contains(concept)))
}

/// KM_HT_CARD_GUARD_EM (experimental, Konclude/HermiT lazy unfolding of
/// recognition): rather than dropping the `⊤ → Q ∨ NQ` cardinality-RECOGNITION
/// excluded middle (which loses recognition completeness), GUARD it by the real
/// (non-marker) concepts that co-occur with Q in the bodies that CONSUME Q. A
/// node can only contribute to a recognition derivation `Q ⊓ g1 ⊓ … → H` when it
/// already carries the real triggers g1…; emitting `g1 ⊓ … → Q ∨ NQ` fires the
/// branch only there instead of on every node. Sound because the ≤n/≥n SEMANTICS
/// are enforced first-class by `card_defs`, independent of the recognition
/// markers; the excluded middle is pure recognition. Complete because the guard
/// uses only the real co-triggers (a SUPERSET of when the full marker-bearing
/// body holds), so the branch fires wherever a recognition could fire. Markers
/// never alias real classes (fresh `Q_`), so a genuine covering disjunction is
/// untouched. NOTE: gives no reduction when the triggers are UBIQUITOUS in a
/// dense cardinality model (every molecule node is a CarbonAtom — ore_ont_10019
/// still does not converge); for those the deterministic propagation recognition
/// is required. Kept (gated, inert) for the onts where triggers are sparse.
fn guard_em_transform(
    clauses: &[JClause],
    min_markers: &std::collections::HashSet<String>,
    max_markers: &std::collections::HashSet<String>,
) -> Vec<JClause> {
    let is_marker = |c: &str| min_markers.contains(c) || max_markers.contains(c);
    // marker -> distinct real-concept guard sets harvested from its consumer bodies.
    let mut guards: HashMap<String, Vec<Vec<String>>> = HashMap::new();
    for c in clauses {
        let body_markers: Vec<&String> = c
            .body
            .iter()
            .filter_map(|a| match a {
                JAtom::Concept {
                    concept,
                    term: JTerm::Var { name },
                } if name == "x" && is_marker(concept) => Some(concept),
                _ => None,
            })
            .collect();
        if body_markers.is_empty() {
            continue;
        }
        let mut g: Vec<String> = c
            .body
            .iter()
            .filter_map(|a| match a {
                JAtom::Concept {
                    concept,
                    term: JTerm::Var { name },
                } if name == "x" && !is_marker(concept) => Some(concept.clone()),
                _ => None,
            })
            .collect();
        // Skip the marker's OWN expansion clauses (body = just the marker, e.g.
        // `Q → ∃r.F` / `Q ∧ (f_i=f_j) → ⊥`): no real co-trigger, downstream of the
        // split, not recognition consumers. Their empty guard would force the
        // unguarded fallback and defeat the transform.
        if g.is_empty() {
            continue;
        }
        g.sort();
        g.dedup();
        for m in body_markers {
            let e = guards.entry(m.clone()).or_default();
            if !e.contains(&g) {
                e.push(g.clone());
            }
        }
    }
    let mut out: Vec<JClause> = Vec::with_capacity(clauses.len());
    for c in clauses {
        if !em_recognition_drop(c, min_markers, max_markers) {
            out.push(c.clone());
            continue;
        }
        let mut gsets: Vec<Vec<String>> = Vec::new();
        let mut any_consumer = false;
        for a in &c.head {
            if let JAtom::Concept { concept, .. } = a {
                if let Some(gs) = guards.get(concept) {
                    any_consumer = true;
                    for g in gs {
                        if !gsets.contains(g) {
                            gsets.push(g.clone());
                        }
                    }
                }
            }
        }
        if !any_consumer {
            // recognition marker never consumed in any body ⇒ the split is dead.
            continue;
        }
        if gsets.iter().any(|g| g.is_empty()) {
            out.push(c.clone());
            continue;
        }
        for g in &gsets {
            let body: Vec<JAtom> = g
                .iter()
                .map(|cn| JAtom::Concept {
                    concept: cn.clone(),
                    term: JTerm::Var {
                        name: "x".to_string(),
                    },
                })
                .collect();
            out.push(JClause {
                body,
                head: c.head.clone(),
            });
        }
    }
    out
}

// ---------------------------------------------------------------------------
// id registries (first-seen order)
// ---------------------------------------------------------------------------
struct Ids {
    con_names: Vec<String>,
    con_id: HashMap<String, usize>,
    rol_names: Vec<String>,
    rol_id: HashMap<String, usize>,
}
impl Ids {
    fn new() -> Ids {
        Ids {
            con_names: Vec::new(),
            con_id: HashMap::new(),
            rol_names: Vec::new(),
            rol_id: HashMap::new(),
        }
    }
    fn cid(&mut self, n: &str) -> usize {
        if let Some(&i) = self.con_id.get(n) {
            return i;
        }
        let i = self.con_names.len();
        self.con_names.push(n.to_string());
        self.con_id.insert(n.to_string(), i);
        i
    }
    fn rid(&mut self, n: &str) -> usize {
        if let Some(&i) = self.rol_id.get(n) {
            return i;
        }
        let i = self.rol_names.len();
        self.rol_names.push(n.to_string());
        self.rol_id.insert(n.to_string(), i);
        i
    }
}

fn mk_varmap() -> HashMap<String, usize> {
    let mut m = HashMap::new();
    m.insert("x".to_string(), 0);
    m
}
fn vnum(vm: &mut HashMap<String, usize>, name: &str) -> usize {
    if let Some(&v) = vm.get(name) {
        return v;
    }
    let nv = vm.values().copied().max().map(|m| m + 1).unwrap_or(0);
    vm.insert(name.to_string(), nv);
    nv
}

struct ExjRec {
    body: Vec<JAtom>,
    role: Option<String>,
    fillers: Vec<String>,
    ok: bool,
}

/// insertion-ordered multimap (role name -> concept list), mirroring Python dict
struct OrderedMM {
    keys: Vec<String>,
    vals: HashMap<String, Vec<String>>,
}
impl OrderedMM {
    fn new() -> OrderedMM {
        OrderedMM {
            keys: Vec::new(),
            vals: HashMap::new(),
        }
    }
    fn push(&mut self, k: &str, v: &str) {
        if !self.vals.contains_key(k) {
            self.keys.push(k.to_string());
            self.vals.insert(k.to_string(), Vec::new());
        }
        self.vals.get_mut(k).unwrap().push(v.to_string());
    }
    fn get(&self, k: &str) -> &[String] {
        self.vals.get(k).map(|v| v.as_slice()).unwrap_or(&[])
    }
    fn iter(&self) -> impl Iterator<Item = (&String, &Vec<String>)> {
        self.keys
            .iter()
            .map(move |k| (k, self.vals.get(k).unwrap()))
    }
}

// ---------------------------------------------------------------------------
// convert
// ---------------------------------------------------------------------------
pub fn convert(
    clauses: &[JClause],
    rbox: Option<&[Vec<String>]>,
    named: &std::collections::HashSet<String>,
    cardinalities: &[crate::json_io::CardMeta],
    definers: &[crate::json_io::DefinerMeta],
    source_axioms: &[crate::json_io::SourceAxiomMeta],
    card_enabled: bool,
    rules: &[JRule],
    ht_rules: bool,
) -> TInput {
    let mut ids = Ids::new();
    let mut dropped: usize = 0;
    let mut ht: Vec<HtClause> = Vec::new();
    // KM_HT_RULES: ground ABox facts intercepted in pass 1 (so they are not
    // dropped as un-clausifiable ground clauses), seeded as nominal nodes below.
    let mut abox_facts: Vec<AboxFact> = Vec::new();

    // The rule machinery (ABox-as-nominal seeding + DL-safe rule firing + the
    // emelim suppression that keeps the rule's complementary markers intact) is
    // active ONLY when the ontology actually carries DL-safe rules. Gating on
    // `!rules.is_empty()` (not on `ht_rules` alone) makes `ht_rules` INERT on
    // every rule-free ontology: no ABox reseeding, and emelim still runs exactly
    // as before. So `ht_rules` can default-on with zero blast radius outside the
    // SWRL onts (2669/15516), where firing the rules is strictly more correct
    // (they are DL-safe Horn — sound — and reveal a real inconsistency the gold
    // reasoner misses; HermiT agrees. See docs/CONTESTED-GOLD.md).
    let rules_active = ht_rules && !rules.is_empty();

    // KM_HT_CARD: the frontend tagged each `≥n`/`≤n` restriction with a `CardMeta`.
    // Install the Konclude first-class number rule (built below into `card_defs`)
    // and DROP exactly the clausal pigeonhole the frontend emitted for those
    // markers, so each restriction reaches the HT via a single representation.
    // Only do the card transform when the ont is in the card-ROUTABLE fragment
    // (the same guard `race::spawn_ht`'s `card_candidate` uses): no datatype (no
    // concrete-domain oracle in the Ht). Nominals ARE allowed — the fast Ht carries
    // the SHOQ o-rule (`process_nominals`, which merges through the same `merge_into`
    // as the ≤n rule, i.e. Konclude `mergeIndividual`), so SHOQ number onts fold
    // correctly with the first-class card rules (ore_ont_9540: 66/66 gold-exact,
    // 46252→64 nodes). Datatype onts still keep the clausal `⋁ Eq` pigeonhole and
    // route elsewhere (QO / shoq / CB) — dropping it + emitting `card_defs` the other
    // routes cannot consume would lose the cardinality (or panic the QO apply_head).
    let card_routable = !clauses.iter().any(|c| {
        c.body.iter().chain(c.head.iter()).any(|a| {
            matches!(a, JAtom::Concept { concept, .. }
                if short(concept).starts_with("__dt__"))
        })
    });
    // The card transform must fire ONLY when the ont will actually take the card
    // route. Inverse-free inputs use the established SHOQ path. A named-RBox
    // inverse input is admitted only after the normalized role-separation check
    // below proves that no number role is inverse-connected or non-simple; all
    // inverse clauses remain present and the worker uses inverse-aware blocking.
    // Every other inverse+number input keeps its clausal pigeonhole and emits no
    // `card_defs`, so QO/CB cannot silently lose the cardinality.
    let has_inverse_rbox = rbox
        .map(|rb| {
            rb.iter()
                .any(|ax| ax.first().map(String::as_str) == Some("inverse"))
        })
        .unwrap_or(false);
    // Inverse roles used INSIDE a concept expression (`ObjectInverseOf` in
    // `∃R⁻.C` / `∀R⁻.C` / `≥n R⁻.C` / `≤n R⁻.C`, or `SubObjectPropertyOf(_, R⁻)`)
    // NEVER surface as an RBox `inverse` axiom: the frontend clausifies them into
    // `__inv__R` bridge clauses (`normalise.rs::link_inverse`, the sole producer
    // of `__inv__` role names), which stay in the ordinary clause set. So
    // `has_inverse_rbox` above is blind to them, and a number restriction over
    // such a role would look inverse-free here. That is unsound: `card_active`
    // would drop the clausal `⋁ Eq` pigeonhole and emit first-class `card_defs`,
    // yet `inverse_pairs` stays empty (so `tin.inverse=false`) and the ont would
    // reach the INVERSE-BLIND fast-Ht card/ALCQ arm, which has no double blocking
    // (SHIQ needs inverse-aware blocking). Detect the `__inv__` roles and fold
    // them into the inverse signal so the card transform fails closed (keeps the
    // pigeonhole, emits no `card_defs` → CB/QO handles it) and the
    // `inverse+number(SHIQ)` fence below arms. Precise + fail-closed: `__inv__`
    // is frontend-internal, so a genuine inverse-free cardinality ont (the
    // validated 9540/7499 SHOQ/SHQ number route) is untouched.
    let has_concept_inverse = clauses.iter().any(|c| {
        c.body
            .iter()
            .chain(c.head.iter())
            .any(|a| matches!(a, JAtom::Role { role, .. } if short(role).starts_with("__inv__")))
    });
    let has_inverse = has_inverse_rbox || has_concept_inverse;
    let inverse_cardinality_role_separable = has_inverse_rbox
        && !has_concept_inverse
        && normalized_inverse_cardinality_role_separable(clauses, rbox, cardinalities);
    let card_active = !cardinalities.is_empty()
        && card_enabled
        && card_routable
        && (!has_inverse || inverse_cardinality_role_separable);
    let mut min_markers: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut max_markers: std::collections::HashSet<String> = std::collections::HashSet::new();
    if card_active {
        for cm in cardinalities {
            if cm.min {
                min_markers.insert(cm.marker.clone());
            } else {
                max_markers.insert(cm.marker.clone());
            }
        }
    }

    // KM_HT_CARD_DROP_EM: read once (not per-clause); inert unless card is active.
    // KM_HT_CARD_RECOG also drops the clausal `⊤→Q∨NQ` excluded middle — the
    // deterministic propagation recognition (`card_recog_step` in the HT) replaces
    // it, so the per-node branch must not remain.
    let drop_em = card_active
        && (std::env::var_os("KM_HT_CARD_DROP_EM").is_some()
            || std::env::var_os("KM_NO_HT_CARD_RECOG").is_none());

    // KM_HT_CARD_GUARD_EM: rewrite the `⊤ → Q ∨ NQ` recognition splits into
    // guarded form before pass 1 (the sound, lazy-unfolding form of DROP_EM).
    // Inert unless card is active and the flag is set.
    let guard_em = card_active && std::env::var_os("KM_HT_CARD_GUARD_EM").is_some();
    let guarded_storage: Vec<JClause>;
    let clauses: &[JClause] = if guard_em {
        guarded_storage = guard_em_transform(clauses, &min_markers, &max_markers);
        &guarded_storage
    } else {
        clauses
    };

    // exj as an insertion-ordered map: f -> ExjRec
    let mut exj_order: Vec<String> = Vec::new();
    let mut exj: HashMap<String, ExjRec> = HashMap::new();

    let mut passthrough: Vec<JClause> = Vec::new();
    let mut eq_clauses: Vec<JClause> = Vec::new();
    let mut distinct_pairs: Vec<(String, String)> = Vec::new();

    // ---- pass 1: collect existential-introduction clauses by function symbol ----
    // KM_KEEP_CHAIN_AXIOMS: detect role chains (R1∘R2⊑R) and transitive roles
    // (R∘R⊑R) from the raw axioms, store as side data (`chains`/`transitive`),
    // and EXCLUDE the raw axioms from the clause set.  Keeping them in the
    // clause set bloats cb_to_ht's cardinality/disjunction expansion (14817:
    // +33 7-body-3-eq clauses + 13 global disjunctions → QoSat cascade).  The
    // chain info is consumed by the Ht chain-unfolding (ht_chain_unfolding_
    // clauses) and the QoSat fprop chain-unfolding — the faithful Konclude
    // role-automaton port. Enabled for the trigger/bridge production route;
    // otherwise it remains explicitly opt-in.
    let keep_chains = std::env::var_os("KM_KEEP_CHAIN_AXIOMS").is_some()
        || std::env::var_os("KM_TRIGGER_ABSORB").is_some();
    let mut detected_chains: Vec<(usize, usize, usize)> = Vec::new();
    let mut detected_transitive: Vec<usize> = Vec::new();
    if keep_chains {
        for c in clauses {
            let body = &c.body;
            let head = &c.head;
            if body.len() != 2 || head.len() != 1 {
                continue;
            }
            // 2 role-body + 1 role-head
            let roles: Vec<(&str, &crate::json_io::JTerm, &crate::json_io::JTerm)> = body
                .iter()
                .filter_map(|a| match a {
                    crate::json_io::JAtom::Role {
                        role,
                        source,
                        target,
                    } => Some((role.as_str(), source, target)),
                    _ => None,
                })
                .collect();
            if roles.len() != 2 {
                continue;
            }
            if let crate::json_io::JAtom::Role {
                role: hr,
                source: hs,
                target: ht,
            } = &head[0]
            {
                let (r1n, r1s, r1t) = roles[0];
                let (r2n, r2s, r2t) = roles[1];
                // orient: first.target == second.source (middle)
                let (fr, fs, sr, st) = if r1t == r2s {
                    (r1n, r1s, r2n, r2t)
                } else if r2t == r1s {
                    (r2n, r2s, r1n, r1t)
                } else {
                    continue;
                };
                // head source = first.source, head target = second.target
                if hs == fs && ht == st && fs != st {
                    let r1id = ids.rid(fr);
                    let r2id = ids.rid(sr);
                    let hrid = ids.rid(hr);
                    if r1id == r2id && r2id == hrid {
                        // R∘R⊑R (transitive)
                        if !detected_transitive.contains(&hrid) {
                            detected_transitive.push(hrid);
                        }
                    } else {
                        detected_chains.push((r1id, r2id, hrid));
                    }
                }
            }
        }
    }
    for c in clauses {
        // KM_KEEP_CHAIN_AXIOMS: skip the raw chain/transitive axioms (detected
        // above as side data; keeping them in the clause set bloats cb_to_ht).
        if keep_chains
            && c.body.len() == 2
            && c.head.len() == 1
            && c.body
                .iter()
                .all(|a| matches!(a, crate::json_io::JAtom::Role { .. }))
            && matches!(c.head[0], crate::json_io::JAtom::Role { .. })
        {
            continue;
        }
        if rules_active {
            if let Some(f) = abox_fact(c) {
                abox_facts.push(f);
                continue;
            }
        }
        // KM_HT_CARD: drop the clausal cardinality expansion the frontend emitted
        // for a card marker (the `≥n` Skolem successors + distinctness, and the
        // `≤n` Eq-head). The first-class rule in `card_defs` replaces it.
        if card_active && card_drop(c, &min_markers, &max_markers) {
            continue;
        }
        // KM_HT_CARD_DROP_EM (experimental, gated): also drop the clausal
        // `⊤ → Q ∨ NQ` excluded-middle RECOGNITION clause for a card marker. This
        // clause fires in EVERY context (empty body) and forces every node to branch
        // on every cardinality definer — the source of the disjunction-search
        // non-convergence on qualified-cardinality onts (ore_ont_10019: 10 such
        // splits × ~330 nodes). The first-class `card_defs` ≥n/≤n rules already
        // enforce the cardinality on the nodes that carry the role; this experiment
        // measures whether dropping the global per-node recognition branch lets the
        // search converge (and how much recognition completeness it costs vs HermiT).
        if drop_em && em_recognition_drop(c, &min_markers, &max_markers) {
            continue;
        }
        let mut head_funs: Vec<String> = Vec::new();
        for a in &c.head {
            match a {
                JAtom::Concept { term, .. } => {
                    if let Some(f) = fun_sym(term) {
                        if !head_funs.iter().any(|x| x == f) {
                            head_funs.push(f.to_string());
                        }
                    }
                }
                JAtom::Role { source, target, .. } => {
                    for t in [source, target] {
                        if let Some(f) = fun_sym(t) {
                            if !head_funs.iter().any(|x| x == f) {
                                head_funs.push(f.to_string());
                            }
                        }
                    }
                }
                JAtom::Eq { .. } => {}
            }
        }
        if !head_funs.is_empty() {
            if c.body.iter().any(atom_has_fun) || head_funs.len() != 1 {
                dropped += 1;
                continue;
            }
            let f = head_funs.pop().unwrap();
            if !exj.contains_key(&f) {
                exj_order.push(f.clone());
                exj.insert(
                    f.clone(),
                    ExjRec {
                        body: c.body.clone(),
                        role: None,
                        fillers: Vec::new(),
                        ok: true,
                    },
                );
            }
            let rec = exj.get_mut(&f).unwrap();
            for a in &c.head {
                match a {
                    JAtom::Role {
                        role,
                        source,
                        target,
                    } if fun_sym(target) == Some(f.as_str()) => {
                        let src_is_x = matches!(source, JTerm::Var { name } if name == "x");
                        if src_is_x {
                            if rec.role.is_some() && rec.role.as_deref() != Some(role.as_str()) {
                                rec.ok = false;
                            }
                            rec.role = Some(role.clone());
                        } else {
                            rec.ok = false;
                        }
                    }
                    JAtom::Concept { concept, term } if fun_sym(term) == Some(f.as_str()) => {
                        rec.fillers.push(concept.clone());
                    }
                    _ => {
                        rec.ok = false;
                    }
                }
            }
            continue;
        }
        // ---- no head function symbols ----
        let body_eq_pairs: Vec<(String, String)> = c.body.iter().filter_map(eq_fun_pair).collect();
        if !body_eq_pairs.is_empty() && c.head.is_empty() {
            distinct_pairs.extend(body_eq_pairs);
        } else if c.body.iter().any(atom_has_fun) {
            dropped += 1;
        } else if c
            .head
            .iter()
            .chain(c.body.iter())
            .any(|a| matches!(a, JAtom::Eq { .. }))
        {
            eq_clauses.push(c.clone());
        } else {
            passthrough.push(c.clone());
        }
    }

    let mut funcs_needing_slot: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for (fi, fj) in &distinct_pairs {
        funcs_needing_slot.insert(fi.clone());
        funcs_needing_slot.insert(fj.clone());
    }

    // ---- parse the RBox ----
    let mut fenced: Vec<Fenced> = Vec::new();
    let mut subrole_pairs: Vec<(String, String)> = Vec::new();
    let mut inverse_pairs: Vec<(String, String)> = Vec::new();
    let mut domains = OrderedMM::new();
    let mut ranges = OrderedMM::new();
    if let Some(rb) = rbox {
        for ax in rb {
            match ax.first().map(String::as_str) {
                Some("subrole") => subrole_pairs.push((ax[1].clone(), ax[2].clone())),
                Some("inverse") => inverse_pairs.push((ax[1].clone(), ax[2].clone())),
                Some("domain") => domains.push(&ax[1], &ax[2]),
                Some("range") => ranges.push(&ax[1], &ax[2]),
                Some("transitive") => {
                    let role = ids.rid(&ax[1]);
                    if !detected_transitive.contains(&role) {
                        detected_transitive.push(role);
                    }
                }
                Some("chain") => {
                    let chain = (ids.rid(&ax[1]), ids.rid(&ax[2]), ids.rid(&ax[3]));
                    if !detected_chains.contains(&chain) {
                        detected_chains.push(chain);
                    }
                }
                Some("fenced") if ax.get(1).map(String::as_str) == Some("symmetric-role") => {
                    // Konclude represents a symmetric role as its own inverse.
                    // The frontend's reverse-edge clause already carries the
                    // same semantics; retain it in the production RBox too so
                    // the bridge is not rejected merely by this metadata tag.
                    inverse_pairs.push((ax[2].clone(), ax[2].clone()));
                }
                Some("fenced") => fenced.push(Fenced {
                    reason: ax[1].clone(),
                    detail: ax[2].clone(),
                }),
                _ => fenced.push(Fenced {
                    reason: "unknown-rbox".into(),
                    detail: format!("{:?}", ax),
                }),
            }
        }
    }

    // reflexive-transitive super-role closure
    let super_roles = |r: &str| -> Vec<String> {
        let mut seen: Vec<String> = vec![r.to_string()];
        let mut frontier: Vec<String> = vec![r.to_string()];
        while let Some(cur) = frontier.pop() {
            for (sub, sup) in &subrole_pairs {
                if *sub == cur && !seen.iter().any(|s| s == sup) {
                    seen.push(sup.clone());
                    frontier.push(sup.clone());
                }
            }
        }
        seen
    };

    // ---- emit existentials ----
    for f in &exj_order {
        let rec = &exj[f];
        if !rec.ok || rec.role.is_none() || rec.fillers.is_empty() {
            dropped += 1;
            continue;
        }
        let mut vm = mk_varmap();
        let mut bod: Vec<HAtom> = Vec::new();
        let mut bad = false;
        for a in &rec.body {
            match a {
                JAtom::Concept {
                    concept,
                    term: JTerm::Var { name },
                } => {
                    let v = vnum(&mut vm, name);
                    bod.push(HAtom::Concept {
                        neg: false,
                        c: ids.cid(concept),
                        t: v,
                    });
                }
                JAtom::Role {
                    role,
                    source: JTerm::Var { name: sn },
                    target: JTerm::Var { name: tn },
                } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    bod.push(HAtom::Role {
                        r: ids.rid(role),
                        s,
                        t,
                    });
                }
                _ => bad = true,
            }
        }
        if bad {
            dropped += 1;
            continue;
        }
        let mut fillers = rec.fillers.clone();
        if funcs_needing_slot.contains(f) {
            fillers.push(format!("__slot__{}", f));
        }
        let fil = if fillers.len() == 1 && !is_bottom(&fillers[0]) {
            ids.cid(&fillers[0])
        } else {
            let dname = format!("def_exfil_{}", f);
            let fil = ids.cid(&dname);
            for cn in &fillers {
                if is_bottom(cn) {
                    ht.push(HtClause {
                        body: vec![HAtom::Concept {
                            neg: false,
                            c: ids.cid(&dname),
                            t: 0,
                        }],
                        head: vec![],
                    });
                } else {
                    let cc = ids.cid(cn);
                    ht.push(HtClause {
                        body: vec![HAtom::Concept {
                            neg: false,
                            c: ids.cid(&dname),
                            t: 0,
                        }],
                        head: vec![HAtom::Concept {
                            neg: false,
                            c: cc,
                            t: 0,
                        }],
                    });
                }
            }
            fil
        };
        let role = rec.role.as_ref().unwrap();
        let rrole = ids.rid(role);
        ht.push(HtClause {
            body: bod.clone(),
            head: vec![HAtom::Exist {
                r: rrole,
                neg: false,
                c: fil,
                t: 0,
            }],
        });
        // domain-obligation propagation
        for sup in super_roles(role) {
            let ds: Vec<String> = domains.get(&sup).to_vec();
            for d in ds {
                let dc = ids.cid(&d);
                ht.push(HtClause {
                    body: bod.clone(),
                    head: vec![HAtom::Concept {
                        neg: false,
                        c: dc,
                        t: 0,
                    }],
                });
            }
        }
    }

    // slot disjointness
    for (fi, fj) in &distinct_pairs {
        let ci = ids.cid(&format!("__slot__{}", fi));
        let cj = ids.cid(&format!("__slot__{}", fj));
        ht.push(HtClause {
            body: vec![
                HAtom::Concept {
                    neg: false,
                    c: ci,
                    t: 0,
                },
                HAtom::Concept {
                    neg: false,
                    c: cj,
                    t: 0,
                },
            ],
            head: vec![],
        });
    }

    // ---- passthrough (function-free) clauses ----
    for c in &passthrough {
        let mut vm = mk_varmap();
        let mut bod: Vec<HAtom> = Vec::new();
        let mut hed: Vec<HAtom> = Vec::new();
        let mut bad = false;
        for a in &c.body {
            match a {
                JAtom::Concept {
                    concept,
                    term: JTerm::Var { name },
                } => {
                    let v = vnum(&mut vm, name);
                    bod.push(HAtom::Concept {
                        neg: false,
                        c: ids.cid(concept),
                        t: v,
                    });
                }
                JAtom::Role {
                    role,
                    source: JTerm::Var { name: sn },
                    target: JTerm::Var { name: tn },
                } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    bod.push(HAtom::Role {
                        r: ids.rid(role),
                        s,
                        t,
                    });
                }
                _ => bad = true,
            }
        }
        for a in &c.head {
            match a {
                JAtom::Concept {
                    concept,
                    term: JTerm::Var { name },
                } => {
                    if is_bottom(concept) {
                        continue;
                    }
                    let v = vnum(&mut vm, name);
                    hed.push(HAtom::Concept {
                        neg: false,
                        c: ids.cid(concept),
                        t: v,
                    });
                }
                JAtom::Role {
                    role,
                    source: JTerm::Var { name: sn },
                    target: JTerm::Var { name: tn },
                } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    hed.push(HAtom::Role {
                        r: ids.rid(role),
                        s,
                        t,
                    });
                }
                _ => bad = true,
            }
        }
        if bad {
            dropped += 1;
            continue;
        }
        ht.push(HtClause {
            body: bod,
            head: hed,
        });
    }

    // ---- eq clauses (≤n / functional / inverse-functional) ----
    // Semantic feature bit, independent of whether the optional first-class
    // `card_defs` encoding is selected. The equality scan below additionally
    // covers source functional/inverse-functional properties for which the
    // frontend does not necessarily emit CardMeta.
    let mut number = !cardinalities.is_empty();
    for c in &eq_clauses {
        let mut vm = mk_varmap();
        let mut bod: Vec<HAtom> = Vec::new();
        let mut hed: Vec<HAtom> = Vec::new();
        let mut bad = false;
        for a in &c.body {
            match a {
                JAtom::Concept {
                    concept,
                    term: JTerm::Var { name },
                } => {
                    let v = vnum(&mut vm, name);
                    bod.push(HAtom::Concept {
                        neg: false,
                        c: ids.cid(concept),
                        t: v,
                    });
                }
                JAtom::Role {
                    role,
                    source: JTerm::Var { name: sn },
                    target: JTerm::Var { name: tn },
                } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    bod.push(HAtom::Role {
                        r: ids.rid(role),
                        s,
                        t,
                    });
                }
                JAtom::Eq {
                    left: JTerm::Var { name: ln },
                    right: JTerm::Var { name: rn },
                } => {
                    let s = vnum(&mut vm, ln);
                    let t = vnum(&mut vm, rn);
                    bod.push(HAtom::Eq { s, t });
                }
                _ => bad = true,
            }
        }
        for a in &c.head {
            match a {
                JAtom::Eq {
                    left: JTerm::Var { name: ln },
                    right: JTerm::Var { name: rn },
                } => {
                    let s = vnum(&mut vm, ln);
                    let t = vnum(&mut vm, rn);
                    hed.push(HAtom::Eq { s, t });
                }
                JAtom::Concept {
                    concept,
                    term: JTerm::Var { name },
                } => {
                    if is_bottom(concept) {
                        continue;
                    }
                    let v = vnum(&mut vm, name);
                    hed.push(HAtom::Concept {
                        neg: false,
                        c: ids.cid(concept),
                        t: v,
                    });
                }
                JAtom::Role {
                    role,
                    source: JTerm::Var { name: sn },
                    target: JTerm::Var { name: tn },
                } => {
                    let s = vnum(&mut vm, sn);
                    let t = vnum(&mut vm, tn);
                    hed.push(HAtom::Role {
                        r: ids.rid(role),
                        s,
                        t,
                    });
                }
                _ => bad = true,
            }
        }
        if bad {
            dropped += 1;
            continue;
        }
        if hed.iter().any(|h| matches!(h, HAtom::Eq { .. })) {
            number = true;
        }
        ht.push(HtClause {
            body: bod,
            head: hed,
        });
    }

    // ---- KM_HT_RULES: seed the ABox as named nominal nodes + fire DL-safe rules ----
    // Each named individual `a` becomes a nominal concept `__nom__a` (collected as a
    // nominal below, so the tableau seeds one root carrying it; the o-rule keeps all
    // `__nom__a` carriers identified). ABox facts attach to that node:
    //   q(a)      ⇒ {a} ⊑ q              : __nom__a(x) → q(x)
    //   r(a,b)    ⇒ {a} ⊑ ∃r.{b}         : __nom__a(x) → ∃r.__nom__b(x)
    //   a ≈ b     ⇒ {a} ⊑ {b}, {b} ⊑ {a} : the two nodes merge via the o-rule
    //   a ≠ b     ⇒ dropped (sound: losing a distinctness can never INVENT a clash;
    //              encoding it as a tableau distinct-edge is left to a later increment)
    // Every named node also carries the O-guard `__O__`, and every rule variable is
    // guarded by `__O__` so it only binds to a named individual (DL-safety): firing
    // over an anonymous ∃-successor would be unsound.
    if rules_active {
        use std::collections::BTreeSet;
        let mut individuals: BTreeSet<String> = BTreeSet::new();
        let mut note = |ind: &str, individuals: &mut BTreeSet<String>| {
            individuals.insert(ind.to_string());
        };
        for f in &abox_facts {
            match f {
                AboxFact::Concept(q, a) => {
                    note(a, &mut individuals);
                    let na = ids.cid(&nom_of(a));
                    let qc = ids.cid(q);
                    if is_bottom(q) {
                        ht.push(HtClause {
                            body: vec![HAtom::Concept {
                                neg: false,
                                c: na,
                                t: 0,
                            }],
                            head: vec![],
                        });
                    } else {
                        ht.push(HtClause {
                            body: vec![HAtom::Concept {
                                neg: false,
                                c: na,
                                t: 0,
                            }],
                            head: vec![HAtom::Concept {
                                neg: false,
                                c: qc,
                                t: 0,
                            }],
                        });
                    }
                }
                AboxFact::Role(r, a, b) => {
                    note(a, &mut individuals);
                    note(b, &mut individuals);
                    let na = ids.cid(&nom_of(a));
                    let nb = ids.cid(&nom_of(b));
                    let rr = ids.rid(r);
                    ht.push(HtClause {
                        body: vec![HAtom::Concept {
                            neg: false,
                            c: na,
                            t: 0,
                        }],
                        head: vec![HAtom::Exist {
                            r: rr,
                            neg: false,
                            c: nb,
                            t: 0,
                        }],
                    });
                }
                AboxFact::Same(a, b) => {
                    note(a, &mut individuals);
                    note(b, &mut individuals);
                    let na = ids.cid(&nom_of(a));
                    let nb = ids.cid(&nom_of(b));
                    ht.push(HtClause {
                        body: vec![HAtom::Concept {
                            neg: false,
                            c: na,
                            t: 0,
                        }],
                        head: vec![HAtom::Concept {
                            neg: false,
                            c: nb,
                            t: 0,
                        }],
                    });
                    ht.push(HtClause {
                        body: vec![HAtom::Concept {
                            neg: false,
                            c: nb,
                            t: 0,
                        }],
                        head: vec![HAtom::Concept {
                            neg: false,
                            c: na,
                            t: 0,
                        }],
                    });
                }
                AboxFact::Diff(a, b) => {
                    note(a, &mut individuals);
                    note(b, &mut individuals);
                    let _ = ids.cid(&nom_of(a));
                    let _ = ids.cid(&nom_of(b));
                }
            }
        }
        // rule clauses: every variable carries an `__O__` guard; an `Ind(a)` term is
        // additionally pinned by `__nom__a`. SameIndividual atoms fire (body guard
        // = variable identification, head = derived equality); a DifferentIndividuals
        // atom has no sound fast-Ht encoding, so its rule is DEFERRED wholesale and
        // counted in `dropped` (sound: a lost constraint never invents an inconsistency).
        let oguard = ids.cid(O_GUARD);
        for rule in rules {
            match build_rule_clause(rule, &mut ids, oguard) {
                Some((cl, inds)) => {
                    for a in &inds {
                        note(a, &mut individuals);
                    }
                    ht.push(cl);
                }
                None => dropped += 1,
            }
        }
        // Mark every named node with the O-guard: __nom__a(x) → __O__(x).
        for a in &individuals {
            let na = ids.cid(&nom_of(a));
            ht.push(HtClause {
                body: vec![HAtom::Concept {
                    neg: false,
                    c: na,
                    t: 0,
                }],
                head: vec![HAtom::Concept {
                    neg: false,
                    c: oguard,
                    t: 0,
                }],
            });
        }
    }

    // ---- RBox edge clauses ----
    for (sub, sup) in &subrole_pairs {
        let rs = ids.rid(sub);
        let rp = ids.rid(sup);
        ht.push(HtClause {
            body: vec![HAtom::Role { r: rs, s: 0, t: 1 }],
            head: vec![HAtom::Role { r: rp, s: 0, t: 1 }],
        });
    }
    for (a, b) in &inverse_pairs {
        let ra = ids.rid(a);
        let rb = ids.rid(b);
        ht.push(HtClause {
            body: vec![HAtom::Role { r: ra, s: 0, t: 1 }],
            head: vec![HAtom::Role { r: rb, s: 1, t: 0 }],
        });
        ht.push(HtClause {
            body: vec![HAtom::Role { r: rb, s: 0, t: 1 }],
            head: vec![HAtom::Role { r: ra, s: 1, t: 0 }],
        });
    }
    let mut role_domains = Vec::new();
    let mut role_ranges = Vec::new();
    {
        let dom_keys: Vec<(String, Vec<String>)> = domains
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        for (r, ds) in dom_keys {
            let rr = ids.rid(&r);
            for d in ds {
                let dc = ids.cid(&d);
                role_domains.push((rr, dc));
                ht.push(HtClause {
                    body: vec![HAtom::Role { r: rr, s: 0, t: 1 }],
                    head: vec![HAtom::Concept {
                        neg: false,
                        c: dc,
                        t: 0,
                    }],
                });
            }
        }
        let ran_keys: Vec<(String, Vec<String>)> =
            ranges.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        for (r, cs) in ran_keys {
            let rr = ids.rid(&r);
            for cc in cs {
                let c1 = ids.cid(&cc);
                role_ranges.push((rr, c1));
                ht.push(HtClause {
                    body: vec![HAtom::Role { r: rr, s: 0, t: 1 }],
                    head: vec![HAtom::Concept {
                        neg: false,
                        c: c1,
                        t: 1,
                    }],
                });
            }
        }
    }

    // ---- nominals ----
    let mut nom_names: Vec<String> = ids
        .con_names
        .iter()
        .filter(|n| short(n).starts_with("__nom__"))
        .cloned()
        .collect();
    nom_names.sort();
    nom_names.dedup();
    let mut nominal_ids: Vec<usize> = nom_names.iter().map(|n| ids.con_id[n]).collect();

    // The SHOI/SHOIQ fence protects the CLASSIFICATION consumers (the fast Ht
    // has no sound nominal+inverse completion). It must not unseat the
    // rule-route ABox seeds: their only consumer is the KM_RULES_CONSISTENCY
    // check, which acts solely on a derived clash (every tableau step is a
    // sound consequence, so a clash is real regardless of the fragment), and
    // a "consistent" verdict merely falls through to normal classification.
    // Clearing the seeds here leaves the tableau rootless and turns a real
    // rule-induced inconsistency into a silent fall-through (the 2669/15516
    // regression).
    if !nominal_ids.is_empty()
        && !inverse_pairs.is_empty()
        && !rules_active
        && !(card_active && inverse_cardinality_role_separable)
    {
        fenced.push(Fenced {
            reason: "nominal+inverse(SHOI/SHOIQ)".into(),
            detail: format!(
                "{} nominal(s) together with inverse roles",
                nominal_ids.len()
            ),
        });
        nominal_ids = Vec::new();
    }
    // Arm the SHIQ fence for BOTH inverse encodings: the RBox `inverse`/symmetric
    // pairs (`inverse_pairs`) and concept-position `ObjectInverseOf` roles
    // (`has_concept_inverse`, the `__inv__` bridge clauses). Without the second
    // disjunct a `≤n R⁻.C` ontology whose card transform was already refused above
    // still has `inverse_pairs` empty, so it would fall through to the
    // inverse-blind `ht_routable` fast Ht (which ignores `tin.inverse` bridges)
    // instead of the Konclude bridge / CB that handle inverse+number soundly.
    if (!inverse_pairs.is_empty() || has_concept_inverse)
        && number
        && !(card_active && inverse_cardinality_role_separable)
    {
        fenced.push(Fenced {
            reason: "inverse+number(SHIQ)".into(),
            detail: "inverse roles together with number restrictions".into(),
        });
    }

    // ---- transitivity: Horrocks-Sattler universal propagation ----
    if std::env::var_os("KM_HT_NO_TRANS_ENC").is_none() {
        let mut transitive_roles: std::collections::HashSet<usize> =
            std::collections::HashSet::new();
        for c in &ht {
            let rb: Vec<&HAtom> = c
                .body
                .iter()
                .filter(|a| matches!(a, HAtom::Role { .. }))
                .collect();
            let rh: Vec<&HAtom> = c
                .head
                .iter()
                .filter(|a| matches!(a, HAtom::Role { .. }))
                .collect();
            if c.body.len() == 2 && rb.len() == 2 && c.head.len() == 1 && rh.len() == 1 {
                if let (
                    HAtom::Role {
                        r: r1,
                        s: r1s,
                        t: r1t,
                    },
                    HAtom::Role {
                        r: r2,
                        s: r2s,
                        t: r2t,
                    },
                    HAtom::Role {
                        r: hr,
                        s: hs,
                        t: ht_,
                    },
                ) = (rb[0], rb[1], rh[0])
                {
                    let endpoints = if r1t == r2s {
                        Some((*r1s, *r2t))
                    } else if r2t == r1s {
                        Some((*r2s, *r1t))
                    } else {
                        None
                    };
                    if r1 == r2 && r2 == hr {
                        if let Some((start, end)) = endpoints {
                            if *hs == start && *ht_ == end && start != end {
                                transitive_roles.insert(*hr);
                            }
                        }
                    }
                }
            }
        }
        if !transitive_roles.is_empty() {
            let mut extra: Vec<HtClause> = Vec::new();
            let mut seen: std::collections::HashSet<(usize, usize)> =
                std::collections::HashSet::new();
            for c in &ht {
                let rb: Vec<&HAtom> = c
                    .body
                    .iter()
                    .filter(|a| matches!(a, HAtom::Role { .. }))
                    .collect();
                let cb: Vec<&HAtom> = c
                    .body
                    .iter()
                    .filter(|a| matches!(a, HAtom::Concept { .. }))
                    .collect();
                let ch: Vec<&HAtom> = c
                    .head
                    .iter()
                    .filter(|a| matches!(a, HAtom::Concept { .. }))
                    .collect();
                if c.body.len() == 2 && rb.len() == 1 && cb.len() == 1 {
                    if let (HAtom::Role { r, s: rs, t: rt }, HAtom::Concept { neg, c: uc, t: ut }) =
                        (rb[0], cb[0])
                    {
                        let any_ch_at_rt = ch
                            .iter()
                            .any(|cc| matches!(cc, HAtom::Concept { t, .. } if t == rt));
                        if transitive_roles.contains(r) && !*neg && ut == rs && any_ch_at_rt {
                            let key = (*r, *uc);
                            if !seen.contains(&key) {
                                seen.insert(key);
                                extra.push(HtClause {
                                    body: vec![
                                        HAtom::Role {
                                            r: *r,
                                            s: *rs,
                                            t: *rt,
                                        },
                                        HAtom::Concept {
                                            neg: false,
                                            c: *uc,
                                            t: *rs,
                                        },
                                    ],
                                    head: vec![HAtom::Concept {
                                        neg: false,
                                        c: *uc,
                                        t: *rt,
                                    }],
                                });
                            }
                        }
                    }
                }
            }
            ht.extend(extra);
        }
    }

    // ---- queries ----
    let mut queries: Vec<usize> = Vec::new();

    // ---- KM_ROLE_AUTOMATON: ∃R.C reachability closure over named classes ----
    // (see engine/src/frontend/preprocess.rs::role_automaton_reachability_clauses
    // for the full rationale; this is the post-cb_to_ht form that can see the
    // Exist atoms the clausifier's absorption produced).  Gated, additive,
    // default OFF.
    if std::env::var_os("KM_ROLE_AUTOMATON").is_some() {
        let extra = role_automaton_exist_reachability(&ht, &mut ids, &inverse_pairs);
        if !extra.is_empty() {
            if std::env::var_os("KM_HT_STATS").is_some() {
                eprintln!(
                    "cb_to_ht [role-automaton] +{} reachability clauses",
                    extra.len()
                );
            }
            ht.extend(extra);
        }
    }

    for (i, n) in ids.con_names.iter().enumerate() {
        if (named.contains(n) || !is_internal(n)) && !is_bottom(n) {
            queries.push(i);
        }
    }
    queries.sort();
    queries.dedup();

    // ---- KM_HT_CARD: resolve the first-class number restrictions to ids ----
    let mut card_defs: Vec<CardDefJson> = Vec::new();
    if card_active {
        for cm in cardinalities {
            card_defs.push(CardDefJson {
                marker: ids.cid(&cm.marker),
                min: cm.min,
                n: cm.n,
                role: ids.rid(&cm.role),
                filler: ids.cid(&cm.filler),
            });
        }
    }

    // ---- complementary-definer elimination (default ON) ----
    // Sound+complete since the completeness guard in elim_complements (never folds
    // a consequence-bearing pair that is not independently derivable). Opt out with
    // KM_NO_HT_EMELIM. Disabled under KM_HT_CARD: the `q`/`NQ` recognition markers
    // are a complementary pair (`⊤⊑q∨NQ`, `q⊓NQ⊑⊥`) that emelim would fold, which
    // would drop the NQ concept that carries the `≥(n+1)` recognition card_def.
    if card_defs.is_empty() && !rules_active && std::env::var_os("KM_NO_HT_EMELIM").is_none() {
        let (out, n_elim) = elim_complements(ht, &ids.con_names);
        ht = out;
        if std::env::var_os("KM_HT_STATS").is_some() {
            eprintln!(
                "cb_to_ht [emelim] eliminated {} complementary pairs",
                n_elim
            );
        }
    }

    // Konclude's implication absorber works over signed literals. EMELIM makes
    // those signs explicit by replacing an eliminated complement marker with
    // the retained concept at the opposite polarity. Normalize them into the
    // DL-clause orientation that the bridge can index: a negative head literal
    // becomes a positive body trigger, and a negative body literal becomes a
    // positive head literal. This is propositional literal movement, hence
    // logically equivalent and independent of the completion calculus.
    if std::env::var_os("KM_TRIGGER_ABSORB").is_some() {
        let (out, moved, dropped_tautologies) =
            normalize_signed_trigger_clauses(ht, definers, &ids.con_names);
        ht = out;
        if std::env::var_os("KM_HT_STATS").is_some() {
            eprintln!(
                "cb_to_ht [trigger-absorb] definers={} moved={} tautologies={}",
                definers.len(),
                moved,
                dropped_tautologies
            );
        }
    }

    nominal_ids.sort();
    nominal_ids.dedup();
    TInput {
        concepts: ids.con_names,
        roles: ids.rol_names,
        clauses: ht,
        queries,
        dropped,
        fenced,
        inverse: !inverse_pairs.is_empty(),
        number,
        inverse_cardinality_role_separable,
        nominals: nominal_ids,
        nominal_abox: crate::json_io::NominalAboxMeta::default(),
        native_abox: NativeAboxJson::default(),
        card_defs,
        chains: detected_chains,
        transitive: detected_transitive,
        role_domains,
        role_ranges,
        definers: definers.to_vec(),
        source_axioms: source_axioms.to_vec(),
    }
}

fn normalize_signed_trigger_clauses(
    ht: Vec<HtClause>,
    _definers: &[crate::json_io::DefinerMeta],
    _con_names: &[String],
) -> (Vec<HtClause>, usize, usize) {
    let mut out = Vec::with_capacity(ht.len());
    let mut moved = 0usize;
    let mut dropped_tautologies = 0usize;
    for cl in ht {
        let mut body = Vec::with_capacity(cl.body.len() + cl.head.len());
        let mut head = Vec::with_capacity(cl.body.len() + cl.head.len());
        for atom in cl.body {
            match atom {
                HAtom::Concept { neg: true, c, t } => {
                    head.push(HAtom::Concept { neg: false, c, t });
                    moved += 1;
                }
                other => body.push(other),
            }
        }
        for atom in cl.head {
            match atom {
                HAtom::Concept { neg: true, c, t } => {
                    body.push(HAtom::Concept { neg: false, c, t });
                    moved += 1;
                }
                other => head.push(other),
            }
        }
        body.sort_by_key(hatom_sort_key);
        body.dedup();
        head.sort_by_key(hatom_sort_key);
        head.dedup();
        if body.iter().any(|a| head.contains(a)) {
            dropped_tautologies += 1;
            continue;
        }
        out.push(HtClause { body, head });
    }
    (out, moved, dropped_tautologies)
}

fn hatom_sort_key(a: &HAtom) -> (u8, usize, usize, usize, bool) {
    match a {
        HAtom::Concept { neg, c, t } => (0, *c, *t, 0, *neg),
        HAtom::Role { r, s, t } => (1, *r, *s, *t, false),
        HAtom::Eq { s, t } => (2, *s, *t, 0, false),
        HAtom::Exist { r, neg, c, t } => (3, *r, *c, *t, *neg),
    }
}

#[cfg(test)]
mod native_abox_install_tests {
    use super::*;
    use crate::frontend::syntax::Concept;
    use crate::json_io::{NominalAboxMeta, NominalIndividualMeta, NominalRoleAssertionMeta};

    fn individual(name: &str, proxy: &str, marker: Option<&str>) -> NominalIndividualMeta {
        NominalIndividualMeta {
            individual: name.into(),
            proxies: vec![proxy.into()],
            assertions: marker
                .map(|name| vec![Concept::Name(name.into())])
                .unwrap_or_default(),
            assertion_markers: marker.map(|name| vec![name.into()]).unwrap_or_default(),
        }
    }

    #[test]
    fn complete_typed_abox_installs_numeric_roots_edges_and_negative_guard() {
        let mut tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: Vec::new(),
            clauses: vec![HtClause {
                body: vec![HAtom::Concept {
                    neg: false,
                    c: 0,
                    t: 0,
                }],
                head: vec![HAtom::Concept {
                    neg: false,
                    c: 1,
                    t: 0,
                }],
            }],
            ..TInput::default()
        };
        let role = NominalRoleAssertionMeta {
            role: "r".into(),
            source: "a".into(),
            target: "b".into(),
        };
        let meta = NominalAboxMeta {
            complete: true,
            individuals: vec![
                individual("a", "__nom__a", Some("A")),
                individual("b", "__nom__b", Some("B")),
            ],
            different: vec![("a".into(), "b".into())],
            role_assertions: vec![role.clone()],
            negative_role_assertions: vec![role],
            unsupported: Vec::new(),
        };

        assert!(install_nominal_abox(&mut tin, &meta));
        assert!(tin.native_abox.complete);
        assert_eq!(tin.native_abox.individuals.len(), 2);
        assert_eq!(tin.native_abox.different, vec![(0, 1)]);
        assert_eq!(tin.native_abox.role_assertions, vec![(0, 0, 1)]);
        assert_eq!(tin.native_abox.negative_role_assertions, vec![(0, 0, 1)]);
        assert_eq!(tin.nominals.len(), 2);
        assert_eq!(tin.roles, vec!["r"]);
        assert!(matches!(
            tin.clauses.last(),
            Some(HtClause { body, head })
                if head.is_empty()
                    && matches!(
                        body.as_slice(),
                        [
                            HAtom::Concept { neg: false, c: 2, t: 0 },
                            HAtom::Role { r: 0, s: 0, t: 1 },
                            HAtom::Concept { neg: false, c: 3, t: 1 }
                        ]
                    )
        ));
    }

    #[test]
    fn failed_install_rolls_back_every_semantic_vector_and_adds_only_a_fence() {
        let sentinel = HtClause {
            body: Vec::new(),
            head: vec![HAtom::Concept {
                neg: false,
                c: 0,
                t: 0,
            }],
        };
        let mut tin = TInput {
            concepts: vec!["A".into(), "__nom__existing".into()],
            roles: vec!["r".into()],
            clauses: vec![sentinel],
            nominals: vec![1],
            native_abox: NativeAboxJson {
                complete: true,
                individuals: vec![NativeIndividualJson {
                    proxies: vec![1],
                    assertions: Vec::new(),
                }],
                ..NativeAboxJson::default()
            },
            ..TInput::default()
        };
        let before_concepts = tin.concepts.clone();
        let before_roles = tin.roles.clone();
        let before_nominals = tin.nominals.clone();
        let before_clause_count = tin.clauses.len();
        let before_native = tin.native_abox.clone();
        let meta = NominalAboxMeta {
            complete: true,
            individuals: vec![individual("a", "__nom__new", Some("missing-marker"))],
            ..NominalAboxMeta::default()
        };

        assert!(!install_nominal_abox(&mut tin, &meta));
        assert_eq!(tin.concepts, before_concepts);
        assert_eq!(tin.roles, before_roles);
        assert_eq!(tin.nominals, before_nominals);
        assert_eq!(tin.clauses.len(), before_clause_count);
        assert_eq!(tin.native_abox, before_native);
        assert_eq!(tin.fenced.len(), 1);
        assert_eq!(tin.fenced[0].reason, "incomplete-nominal-abox");
    }

    #[test]
    fn duplicate_proxy_ownership_fails_closed_without_partial_install() {
        let mut tin = TInput::default();
        let meta = NominalAboxMeta {
            complete: true,
            individuals: vec![
                individual("a", "__nom__shared", None),
                individual("b", "__nom__shared", None),
            ],
            ..NominalAboxMeta::default()
        };
        assert!(!install_nominal_abox(&mut tin, &meta));
        assert!(tin.concepts.is_empty());
        assert!(tin.nominals.is_empty());
        assert!(tin.native_abox.is_empty());
        assert_eq!(tin.fenced[0].reason, "incomplete-nominal-abox");
    }
}

// ---------------------------------------------------------------------------
// KM_HT_EMELIM: complementary-definer excluded-middle elimination (B ≡ ¬A)
// ---------------------------------------------------------------------------
/// If `atoms` are ALL positive concept atoms over a single variable, return
/// their concept ids; else None.
fn pos_concepts(atoms: &[HAtom]) -> Option<Vec<usize>> {
    let mut out = Vec::new();
    let mut var: Option<usize> = None;
    for a in atoms {
        match a {
            HAtom::Concept { neg: false, c, t } => {
                match var {
                    None => var = Some(*t),
                    Some(v) if v != *t => return None,
                    _ => {}
                }
                out.push(*c);
            }
            _ => return None,
        }
    }
    Some(out)
}

fn sub_atom(a: &HAtom, sub: &HashMap<usize, usize>) -> HAtom {
    if let HAtom::Concept { neg, c, t } = a {
        if let Some(&k) = sub.get(c) {
            return HAtom::Concept {
                neg: !*neg,
                c: k,
                t: *t,
            };
        }
    }
    a.clone()
}

pub fn elim_complements(ht: Vec<HtClause>, con_names: &[String]) -> (Vec<HtClause>, usize) {
    use std::collections::HashSet;
    // `em` keeps INSERTION order (Python dict) — order decides which substitution
    // wins under the chain-free `used` guard, so it must not be sorted.
    let mut em: Vec<(usize, usize)> = Vec::new();
    let mut em_seen: HashSet<(usize, usize)> = HashSet::new();
    let mut dj: HashSet<(usize, usize)> = HashSet::new();
    let mut protected: HashSet<usize> = HashSet::new();
    // Concepts that appear in the body of a clause with a NON-EMPTY head, i.e. a
    // concept that drives a forward consequence. For a complementary pair B≡¬A,
    // both A and B are only ever *derived* through the excluded-middle ⊤⊑A∨B (or a
    // clash); dropping that disjunction (what folding does) therefore loses any
    // consequence keyed on the dropped side. BUT if that side is *independently*
    // derivable — it is the sole atom of some Horn head `X ⊑ B` (or `⊤ ⊑ B`) — then
    // its consequence still fires without the disjunction, so folding stays
    // complete. So a pair is unsafe to fold only when a member BOTH drives a
    // consequence (`body_drives`) AND is not Horn-derivable (`head_horn`). This is
    // the completeness fix for the live ∀+⊔ family: it keeps 5303's
    // `¬Q ⊑ ∃hasComponentPart.Q17` pair unfolded (¬Q is only born of the excluded
    // middle) while still folding the disjunction-family onts whose folded side is
    // Horn-derivable (12141/541/9024), which EMELIM legitimately classifies clean.
    let mut body_drives: HashSet<usize> = HashSet::new();
    let mut head_horn: HashSet<usize> = HashSet::new();
    let pair = |v: &[usize]| -> (usize, usize) {
        let (a, b) = (v[0], v[1]);
        if a <= b {
            (a, b)
        } else {
            (b, a)
        }
    };
    for c in &ht {
        let head_nonempty = !c.head.is_empty();
        for a in c.body.iter().chain(c.head.iter()) {
            if let HAtom::Exist { c: fc, .. } = a {
                protected.insert(*fc);
            }
        }
        if head_nonempty {
            for a in &c.body {
                if let HAtom::Concept { c: bc, .. } = a {
                    body_drives.insert(*bc);
                }
            }
        }
        // Horn-derivable: the concept is the single atom of this clause's head.
        if c.head.len() == 1 {
            if let HAtom::Concept { c: hc, .. } = c.head[0] {
                head_horn.insert(hc);
            }
        }
        if c.body.is_empty() {
            if let Some(h) = pos_concepts(&c.head) {
                if h.len() == 2 && h[0] != h[1] {
                    let p = pair(&h);
                    if em_seen.insert(p) {
                        em.push(p);
                    }
                }
            }
        }
        if c.head.is_empty() {
            if let Some(b) = pos_concepts(&c.body) {
                if b.len() == 2 && b[0] != b[1] {
                    dj.insert(pair(&b));
                }
            }
        }
    }
    let pairs: Vec<(usize, usize)> = em.into_iter().filter(|p| dj.contains(p)).collect();
    if pairs.is_empty() {
        return (ht, 0);
    }
    let internal = |i: usize| -> bool { is_internal(&con_names[i]) };
    let mut sub: HashMap<usize, usize> = HashMap::new();
    let mut used: HashSet<usize> = HashSet::new();
    for p in pairs {
        let (a, b) = p; // canonical a<=b == Python sorted(p) -> (a,b)
                        // Completeness: keep the excluded-middle ⊤⊑A∨B unfolded if a side both
                        // drives a consequence and is NOT independently (Horn) derivable — then
                        // dropping the disjunction would silence that consequence. A consequence
                        // whose side is Horn-derivable survives the drop, so that pair still folds.
        let unsafe_a = body_drives.contains(&a) && !head_horn.contains(&a);
        let unsafe_b = body_drives.contains(&b) && !head_horn.contains(&b);
        if unsafe_a || unsafe_b {
            continue;
        }
        let (elim, keep) = if internal(b) && !internal(a) {
            (b, a)
        } else if internal(a) && !internal(b) {
            (a, b)
        } else {
            (b, a) // both internal/named: drop the larger id (b, since a<=b)
        };
        if protected.contains(&elim) {
            continue;
        }
        if used.contains(&elim) || used.contains(&keep) {
            continue;
        }
        sub.insert(elim, keep);
        used.insert(elim);
        used.insert(keep);
    }
    if sub.is_empty() {
        return (ht, 0);
    }
    let elim_pairs: HashSet<(usize, usize)> = sub
        .iter()
        .map(|(&e, &k)| if e <= k { (e, k) } else { (k, e) })
        .collect();
    let mut out: Vec<HtClause> = Vec::new();
    for c in &ht {
        if c.body.is_empty() {
            if let Some(h) = pos_concepts(&c.head) {
                if h.len() == 2 && elim_pairs.contains(&pair(&h)) {
                    continue;
                }
            }
        }
        if c.head.is_empty() {
            if let Some(b) = pos_concepts(&c.body) {
                if b.len() == 2 && elim_pairs.contains(&pair(&b)) {
                    continue;
                }
            }
        }
        out.push(HtClause {
            body: c.body.iter().map(|a| sub_atom(a, &sub)).collect(),
            head: c.head.iter().map(|a| sub_atom(a, &sub)).collect(),
        });
    }
    let n = sub.len();
    (out, n)
}

#[cfg(test)]
mod trigger_absorb_tests {
    use super::*;

    #[test]
    fn is_internal_excludes_markers_and_builtins_but_keeps_colon_localname_classes() {
        // Frontend synthetic markers stay internal.
        for marker in ["Q_5", "__trans__R__C", "aux_1", "def_2"] {
            assert!(is_internal(marker), "{marker} should be internal");
        }
        // Builtin OWL/RDF/RDFS/XSD/XML vocabulary in CURIE form stays internal.
        for builtin in [
            "owl:Thing",
            "rdfs:Literal",
            "rdf:type",
            "xsd:integer",
            "xml:lang",
        ] {
            assert!(is_internal(builtin), "{builtin} should be internal");
        }
        // Bottom is handled by `is_bottom`, not `is_internal` — behaviour
        // preserved from the pre-fix predicate.
        assert!(!is_internal("owl:Nothing"));
        assert!(!is_internal("Nothing"));

        // Ordinary named classes are not internal.
        assert!(!is_internal("http://example.org/onto#Foo"));
        assert!(!is_internal("Foo"));

        // Regression: a REAL named class whose localname legitimately contains a
        // colon must NOT be dropped from the classification universe. The old
        // `s.contains(':')` heuristic silently excluded these, emitting no
        // subsumption for them and flagging neither unsound nor incomplete.
        assert!(
            !is_internal("http://example.org/onto#Part:Whole"),
            "colon-bearing fragment class must be kept"
        );
        assert!(
            !is_internal("urn:example:Foo"),
            "URN class IRI must be kept"
        );
        assert!(
            !is_internal("myprefix:MyClass"),
            "non-reserved CURIE class must be kept"
        );
    }

    #[test]
    fn convert_preserves_rbox_domain_range_provenance() {
        let rbox = vec![
            vec!["domain".into(), "r".into(), "D".into()],
            vec!["range".into(), "r".into(), "E".into()],
        ];
        let named = std::collections::HashSet::from(["D".to_string(), "E".to_string()]);
        let tin = convert(&[], Some(&rbox), &named, &[], &[], &[], false, &[], false);
        let role = tin.roles.iter().position(|name| name == "r").unwrap();
        let domain = tin.concepts.iter().position(|name| name == "D").unwrap();
        let range = tin.concepts.iter().position(|name| name == "E").unwrap();

        assert_eq!(tin.role_domains, vec![(role, domain)]);
        assert_eq!(tin.role_ranges, vec![(role, range)]);
    }

    #[test]
    fn signed_literals_move_to_trigger_orientation() {
        let input = vec![HtClause {
            body: vec![
                HAtom::Concept {
                    neg: true,
                    c: 0,
                    t: 0,
                },
                HAtom::Concept {
                    neg: false,
                    c: 1,
                    t: 0,
                },
            ],
            head: vec![
                HAtom::Concept {
                    neg: true,
                    c: 2,
                    t: 0,
                },
                HAtom::Concept {
                    neg: false,
                    c: 3,
                    t: 0,
                },
            ],
        }];
        let (out, moved, dropped) = normalize_signed_trigger_clauses(input, &[], &Vec::new());
        assert_eq!(moved, 2);
        assert_eq!(dropped, 0);
        assert_eq!(out.len(), 1);
        assert!(out[0].body.contains(&HAtom::Concept {
            neg: false,
            c: 2,
            t: 0
        }));
        assert!(out[0].head.contains(&HAtom::Concept {
            neg: false,
            c: 0,
            t: 0
        }));
    }

    #[test]
    fn rule_abox_seeds_survive_the_inverse_fence() {
        // Regression: threading the rbox into the rules-consistency conversion
        // armed the SHOI classification fence, which cleared the ABox nominal
        // seeds and left the consistency tableau rootless (2669/15516 lost
        // their 0.17 s inconsistent verdict). The seeds must survive an
        // inverse-declaring rbox whenever the rule machinery is active.
        let (clauses, rules, named) = rule_kb(true);
        let rbox = vec![vec!["inverse".into(), "partOf".into(), "hasPart".into()]];
        let tin = convert(
            &clauses,
            Some(&rbox),
            &named,
            &[],
            &[],
            &[],
            false,
            &rules,
            true,
        );
        assert!(
            !tin.nominals.is_empty(),
            "ABox seeds must survive the nominal+inverse fence on the rules route"
        );
        assert!(
            !tin.fenced
                .iter()
                .any(|f| f.reason.contains("nominal+inverse")),
            "the classification fence must not fire on rule-seeded nominals"
        );
        assert!(!rules_verdict(&tin), "rule-induced clash must be detected");
    }

    #[test]
    fn consistent_rule_ontology_reports_consistent() {
        // The fall-through case: a satisfiable DL-safe rule ontology must get
        // a "consistent" verdict so classify proceeds to normal taxonomy work.
        let (clauses, rules, named) = rule_kb(false);
        let rbox = vec![vec!["inverse".into(), "partOf".into(), "hasPart".into()]];
        let tin = convert(
            &clauses,
            Some(&rbox),
            &named,
            &[],
            &[],
            &[],
            false,
            &rules,
            true,
        );
        assert!(!tin.nominals.is_empty());
        assert!(rules_verdict(&tin));
    }

    #[test]
    fn classification_nominals_stay_fenced_with_inverse() {
        // Without active rules the SHOI fence must keep clearing nominals:
        // the fast-Ht classification path has no sound nominal+inverse
        // completion, and that contract is unchanged by the rules fix.
        use crate::json_io::{JAtom, JTerm};
        let clauses = vec![crate::json_io::JClause {
            body: vec![JAtom::Concept {
                concept: "__nom__a".into(),
                term: JTerm::Var { name: "X".into() },
            }],
            head: vec![JAtom::Concept {
                concept: "A".into(),
                term: JTerm::Var { name: "X".into() },
            }],
        }];
        let rbox = vec![vec!["inverse".into(), "partOf".into(), "hasPart".into()]];
        let named = std::collections::HashSet::from(["A".to_string()]);
        let tin = convert(
            &clauses,
            Some(&rbox),
            &named,
            &[],
            &[],
            &[],
            false,
            &[],
            true,
        );
        assert!(tin.nominals.is_empty());
        assert!(tin
            .fenced
            .iter()
            .any(|f| f.reason == "nominal+inverse(SHOI/SHOIQ)"));
    }

    #[test]
    fn separated_inverse_cardinality_keeps_exact_rbox_and_card_defs() {
        use crate::json_io::{CardMeta, JAtom, JClause, JTerm};
        let variable = || JTerm::Var { name: "x".into() };
        let clauses = vec![JClause {
            body: vec![JAtom::Concept {
                concept: "__nom__a".into(),
                term: variable(),
            }],
            head: vec![JAtom::Concept {
                concept: "A".into(),
                term: variable(),
            }],
        }];
        let rbox = vec![
            vec!["inverse".into(), "i".into(), "j".into()],
            vec!["subrole".into(), "i".into(), "k".into()],
            vec!["transitive".into(), "k".into()],
            vec!["domain".into(), "i".into(), "D".into()],
            vec!["range".into(), "j".into(), "E".into()],
        ];
        let cards = vec![CardMeta {
            marker: "Q_card".into(),
            min: false,
            n: 2,
            role: "p".into(),
            filler: "C".into(),
        }];
        let named = std::collections::HashSet::from([
            "A".to_string(),
            "C".to_string(),
            "D".to_string(),
            "E".to_string(),
        ]);
        let tin = convert(
            &clauses,
            Some(&rbox),
            &named,
            &cards,
            &[],
            &[],
            true,
            &[],
            false,
        );

        assert!(tin.inverse_cardinality_role_separable);
        assert!(tin.inverse, "the inverse flag must remain live");
        assert_eq!(tin.card_defs.len(), 1);
        assert!(!tin.nominals.is_empty(), "the SHOQ o-rule must remain live");
        assert!(
            tin.fenced.is_empty(),
            "certified composition must be routable"
        );

        let i = tin.roles.iter().position(|role| role == "i").unwrap();
        let j = tin.roles.iter().position(|role| role == "j").unwrap();
        let has_inverse_clause = |from: usize, to: usize| {
            tin.clauses.iter().any(|clause| {
                matches!(
                    (clause.body.as_slice(), clause.head.as_slice()),
                    (
                        [HAtom::Role { r, s: 0, t: 1 }],
                        [HAtom::Role { r: head_r, s: 1, t: 0 }]
                    ) if *r == from && *head_r == to
                )
            })
        };
        assert!(has_inverse_clause(i, j));
        assert!(has_inverse_clause(j, i));
        assert_eq!(tin.role_domains.len(), 1, "domain provenance remains exact");
        assert_eq!(tin.role_ranges.len(), 1, "range provenance remains exact");
    }

    #[test]
    fn normalized_inverse_cardinality_certificate_fails_closed() {
        use crate::json_io::CardMeta;
        let cards = vec![CardMeta {
            marker: "Q_card".into(),
            min: false,
            n: 1,
            role: "p".into(),
            filler: "C".into(),
        }];
        let cases = vec![
            vec![vec!["inverse".into(), "p".into(), "j".into()]],
            vec![
                vec!["inverse".into(), "i".into(), "j".into()],
                vec!["subrole".into(), "p".into(), "i".into()],
            ],
            vec![
                vec!["inverse".into(), "i".into(), "j".into()],
                // EquivalentObjectProperties(p,i) is serialized as both
                // subrole directions; one dependency edge already suffices.
                vec!["subrole".into(), "p".into(), "i".into()],
                vec!["subrole".into(), "i".into(), "p".into()],
            ],
            vec![
                vec!["inverse".into(), "i".into(), "j".into()],
                vec!["chain".into(), "p".into(), "r".into(), "s".into()],
            ],
            vec![
                vec!["inverse".into(), "i".into(), "j".into()],
                vec!["transitive".into(), "p".into()],
            ],
            vec![
                vec!["inverse".into(), "i".into(), "j".into()],
                vec!["fenced".into(), "inverse-functional".into(), "r".into()],
            ],
        ];
        for rbox in cases {
            assert!(
                !normalized_inverse_cardinality_role_separable(&[], Some(&rbox), &cards),
                "unsafe normalized RBox was certified: {rbox:?}"
            );
        }
        let separated = vec![
            vec!["inverse".into(), "i".into(), "j".into()],
            vec!["domain".into(), "i".into(), "D".into()],
            vec!["range".into(), "j".into(), "E".into()],
        ];
        assert!(normalized_inverse_cardinality_role_separable(
            &[],
            Some(&separated),
            &cards
        ));
        assert!(normalized_inverse_cardinality_role_separable(
            &[le1_over("functional_but_separate")],
            Some(&separated),
            &cards
        ));
        assert!(
            !normalized_inverse_cardinality_role_separable(
                &[le1_over("i")],
                Some(&separated),
                &cards
            ),
            "Eq-head functionality on an inverse role must be detected even without CardMeta"
        );
        assert!(!normalized_inverse_cardinality_role_separable(
            &[inv_bridge()],
            Some(&separated),
            &cards
        ));
    }

    /// A synthetic DL-safe rule KB mirroring the 2669/15516 core: an asserted
    /// `KeyAttr(a)`, a rule `KeyAttr(x) → NonKeyAttr(x)`, and (when `unsat`)
    /// the disjointness `KeyAttr ⊓ NonKeyAttr ⊑ ⊥`.
    fn rule_kb(
        unsat: bool,
    ) -> (
        Vec<crate::json_io::JClause>,
        Vec<crate::json_io::JRule>,
        std::collections::HashSet<String>,
    ) {
        use crate::json_io::{JAtom, JClause, JRule, JRuleAtom, JRuleTerm, JTerm};
        let vx = || JTerm::Var { name: "X".into() };
        let mut clauses = vec![
            // ClassAssertion(KeyAttr a): the ground clause the frontend keeps
            // in the clause set when rules are present.
            JClause {
                body: vec![],
                head: vec![JAtom::Concept {
                    concept: "KeyAttr".into(),
                    term: JTerm::Ind { name: "a".into() },
                }],
            },
            // RoleAssertion(partOf a b) so the seeded graph has a role edge.
            JClause {
                body: vec![],
                head: vec![JAtom::Role {
                    role: "partOf".into(),
                    source: JTerm::Ind { name: "a".into() },
                    target: JTerm::Ind { name: "b".into() },
                }],
            },
        ];
        if unsat {
            clauses.push(JClause {
                body: vec![
                    JAtom::Concept {
                        concept: "KeyAttr".into(),
                        term: vx(),
                    },
                    JAtom::Concept {
                        concept: "NonKeyAttr".into(),
                        term: vx(),
                    },
                ],
                head: vec![],
            });
        }
        let rules = vec![JRule {
            body: vec![JRuleAtom::Class {
                concept: "KeyAttr".into(),
                term: JRuleTerm::Var { name: "x".into() },
            }],
            head: vec![JRuleAtom::Class {
                concept: "NonKeyAttr".into(),
                term: JRuleTerm::Var { name: "x".into() },
            }],
        }];
        let named =
            std::collections::HashSet::from(["KeyAttr".to_string(), "NonKeyAttr".to_string()]);
        (clauses, rules, named)
    }

    /// Run the exact production consistency verdict on a converted TInput:
    /// serialise over the worker wire format and call the same entry the
    /// `KM_RULES_CONSISTENCY` tableau worker uses.
    fn rules_verdict(tin: &TInput) -> bool {
        let wire = serde_json::to_string(tin).expect("serialise TInput");
        let inp: crate::tableau::TInput = serde_json::from_str(&wire).expect("parse TInput");
        let clauses = crate::tableau::clauses_of_tinput(&inp);
        crate::tableau::rules_consistency_verdict(&inp, clauses).expect("consistency verdict")
    }

    #[test]
    fn signed_normalization_drops_tautology() {
        let input = vec![HtClause {
            body: vec![HAtom::Concept {
                neg: false,
                c: 0,
                t: 0,
            }],
            head: vec![HAtom::Concept {
                neg: false,
                c: 0,
                t: 0,
            }],
        }];
        let (out, moved, dropped) = normalize_signed_trigger_clauses(input, &[], &Vec::new());
        assert!(out.is_empty());
        assert_eq!(moved, 0);
        assert_eq!(dropped, 1);
    }

    // ---- concept-position inverse (ObjectInverseOf / __inv__) SHIQ fence ----
    // The frontend clausifies inverse roles used inside concept expressions into
    // `__inv__R` bridge clauses (normalise.rs::link_inverse), which never reach the
    // RBox. A number restriction over such a role is SHIQ, but the RBox-only
    // inverse guard cannot see it, so the card transform and the inverse+number
    // fence must key off the `__inv__` roles too, failing closed off the
    // inverse-blind fast Ht.
    use crate::json_io::{CardMeta, JAtom, JClause, JTerm};

    fn vx() -> JTerm {
        JTerm::Var { name: "x".into() }
    }
    fn vy() -> JTerm {
        JTerm::Var { name: "y".into() }
    }
    fn vy2() -> JTerm {
        JTerm::Var { name: "y2".into() }
    }
    /// The link_inverse bridge clause `R(x,y) -> __inv__R(y,x)`.
    fn inv_bridge() -> JClause {
        JClause {
            body: vec![JAtom::Role {
                role: "R".into(),
                source: vx(),
                target: vy(),
            }],
            head: vec![JAtom::Role {
                role: "__inv__R".into(),
                source: vy(),
                target: vx(),
            }],
        }
    }
    /// A `≤1 role.C`-style pigeonhole `role(x,y) ∧ role(x,y2) -> y≈y2` (Eq head,
    /// which sets `number`).
    fn le1_over(role: &str) -> JClause {
        JClause {
            body: vec![
                JAtom::Role {
                    role: role.into(),
                    source: vx(),
                    target: vy(),
                },
                JAtom::Role {
                    role: role.into(),
                    source: vx(),
                    target: vy2(),
                },
            ],
            head: vec![JAtom::Eq {
                left: vy(),
                right: vy2(),
            }],
        }
    }

    #[test]
    fn concept_position_inverse_disables_card_transform() {
        // A `≤1` restriction over an inverse role (__inv__R) must NOT be lifted to
        // first-class card_defs: the resulting ont would look inverse-free and
        // reach the inverse-blind card arm. Fail closed → keep the pigeonhole.
        let card = vec![CardMeta {
            marker: "Q_card".into(),
            min: false,
            n: 1,
            role: "__inv__R".into(),
            filler: "C".into(),
        }];
        let named = std::collections::HashSet::new();
        let tin = convert(
            &[inv_bridge()],
            None,
            &named,
            &card,
            &[],
            &[],
            true,
            &[],
            false,
        );
        assert!(
            tin.card_defs.is_empty(),
            "concept-position inverse must fail closed: no first-class card_defs"
        );
    }

    #[test]
    fn plain_role_cardinality_still_uses_card_transform() {
        // Control: an inverse-FREE cardinality ont keeps the validated first-class
        // card route (no regression to 9540/7499-style SHQ/SHOQ number onts).
        let card = vec![CardMeta {
            marker: "Q_card".into(),
            min: false,
            n: 1,
            role: "R".into(),
            filler: "C".into(),
        }];
        let filler_intro = JClause {
            body: vec![JAtom::Concept {
                concept: "A".into(),
                term: vx(),
            }],
            head: vec![JAtom::Concept {
                concept: "B".into(),
                term: vx(),
            }],
        };
        let named = std::collections::HashSet::new();
        let tin = convert(
            &[filler_intro],
            None,
            &named,
            &card,
            &[],
            &[],
            true,
            &[],
            false,
        );
        assert!(
            !tin.card_defs.is_empty(),
            "inverse-free cardinality must keep the first-class card_defs route"
        );
        assert!(
            tin.number,
            "CardMeta must set the semantic number feature independently of Eq-clause retention"
        );
    }

    #[test]
    fn concept_position_inverse_with_number_arms_the_shiq_fence() {
        // __inv__R bridge + a ≤1 Eq-head over it: number is set and the
        // inverse+number(SHIQ) fence must arm even though inverse_pairs is empty.
        let named = std::collections::HashSet::new();
        let tin = convert(
            &[inv_bridge(), le1_over("__inv__R")],
            None,
            &named,
            &[],
            &[],
            &[],
            false,
            &[],
            false,
        );
        assert!(tin.number, "the ≤1 Eq-head must set the number flag");
        assert!(
            !tin.inverse,
            "concept-position inverse is bridge-clause only, so tin.inverse stays false"
        );
        assert!(
            tin.fenced
                .iter()
                .any(|f| f.reason == "inverse+number(SHIQ)"),
            "concept-position inverse + number must arm the SHIQ fence"
        );
    }

    #[test]
    fn plain_number_restriction_is_not_shiq_fenced() {
        // Control: inverse-free ALCQ number restrictions must stay unfenced so the
        // sound fast-Ht/card route is not needlessly declined.
        let named = std::collections::HashSet::new();
        let tin = convert(
            &[le1_over("R")],
            None,
            &named,
            &[],
            &[],
            &[],
            false,
            &[],
            false,
        );
        assert!(tin.number);
        assert!(
            !tin.fenced.iter().any(|f| f.reason.contains("SHIQ")),
            "inverse-free number restrictions must not arm the SHIQ fence"
        );
    }
}

#[cfg(test)]
mod rule_clause_tests {
    //! Encoding contract for DL-safe rule → HT clauses (`build_rule_clause`):
    //! SameIndividual atoms fire (body = unification, head = derived equality);
    //! DifferentIndividuals atoms defer the whole rule (no sound distinctness).
    use super::*;

    fn var(n: &str) -> JRuleTerm {
        JRuleTerm::Var {
            name: n.to_string(),
        }
    }
    fn ind(n: &str) -> JRuleTerm {
        JRuleTerm::Ind {
            name: n.to_string(),
        }
    }
    fn class(c: &str, t: JRuleTerm) -> JRuleAtom {
        JRuleAtom::Class {
            concept: c.to_string(),
            term: t,
        }
    }
    fn role(r: &str, s: JRuleTerm, t: JRuleTerm) -> JRuleAtom {
        JRuleAtom::Role {
            role: r.to_string(),
            source: s,
            target: t,
        }
    }
    fn build(rule: &JRule) -> Option<(HtClause, Vec<String>)> {
        let mut ids = Ids::new();
        let oguard = ids.cid(O_GUARD);
        build_rule_clause(rule, &mut ids, oguard)
    }

    #[test]
    fn body_same_guard_unifies_its_two_terms() {
        // Body: r(x,y) ∧ SameAs(x,y); Head: D(x). The guard forces x = y, so the
        // role edge must land on ONE variable (s == t).
        let rule = JRule {
            body: vec![
                role("r", var("x"), var("y")),
                JRuleAtom::Same {
                    left: var("x"),
                    right: var("y"),
                },
            ],
            head: vec![class("D", var("x"))],
        };
        let (cl, _) = build(&rule).expect("SameAs body rule fires");
        let edge = cl
            .body
            .iter()
            .find_map(|a| match a {
                HAtom::Role { s, t, .. } => Some((*s, *t)),
                _ => None,
            })
            .expect("role edge present");
        assert_eq!(
            edge.0, edge.1,
            "SameAs(x,y) must unify the two terms onto one variable"
        );
        // No stray Eq atom in a body-guard-only rule.
        assert!(!cl.body.iter().any(|a| matches!(a, HAtom::Eq { .. })));
        assert!(!cl.head.iter().any(|a| matches!(a, HAtom::Eq { .. })));
    }

    #[test]
    fn head_same_derives_an_equality() {
        // Body: C(x) ∧ C(y); Head: SameAs(x,y). x and y stay distinct variables
        // (no body guard); the head concludes the equality as an Eq atom.
        let rule = JRule {
            body: vec![class("C", var("x")), class("C", var("y"))],
            head: vec![JRuleAtom::Same {
                left: var("x"),
                right: var("y"),
            }],
        };
        let (cl, _) = build(&rule).expect("SameAs head rule fires");
        let eq = cl
            .head
            .iter()
            .find_map(|a| match a {
                HAtom::Eq { s, t } => Some((*s, *t)),
                _ => None,
            })
            .expect("head equality present");
        assert_ne!(
            eq.0, eq.1,
            "distinct body variables remain distinct in the derived equality"
        );
    }

    #[test]
    fn different_individuals_atom_defers_the_rule() {
        // A Diff guard has no sound fast-Ht encoding, so the whole rule is
        // deferred (dropped, counted). Body and head positions both defer.
        let body_diff = JRule {
            body: vec![
                role("r", var("x"), var("y")),
                JRuleAtom::Diff {
                    left: var("x"),
                    right: var("y"),
                },
            ],
            head: vec![class("D", var("x"))],
        };
        assert!(
            build(&body_diff).is_none(),
            "body DifferentIndividuals defers the rule"
        );

        let head_diff = JRule {
            body: vec![class("C", var("x")), class("C", var("y"))],
            head: vec![JRuleAtom::Diff {
                left: var("x"),
                right: var("y"),
            }],
        };
        assert!(
            build(&head_diff).is_none(),
            "head DifferentIndividuals defers the rule"
        );
    }

    #[test]
    fn same_as_individual_pins_the_shared_variable_to_the_nominal() {
        // Body: SameAs(x, a) ∧ C(x); Head: D(x). x is pinned to individual a, so
        // `a` is registered and the shared variable carries the `__nom__a` guard.
        let rule = JRule {
            body: vec![
                JRuleAtom::Same {
                    left: var("x"),
                    right: ind("a"),
                },
                class("C", var("x")),
            ],
            head: vec![class("D", var("x"))],
        };
        let (cl, inds) = build(&rule).expect("SameAs(x,a) rule fires");
        assert!(
            inds.contains(&"a".to_string()),
            "individual a is registered as a nominal node"
        );
        // the C(x), D(x), __nom__a, and __O__ all sit on the same single variable.
        let vars: std::collections::HashSet<usize> = cl
            .body
            .iter()
            .chain(cl.head.iter())
            .filter_map(|a| match a {
                HAtom::Concept { t, .. } => Some(*t),
                _ => None,
            })
            .collect();
        assert_eq!(vars.len(), 1, "x unified with a onto one variable");
    }

    #[test]
    fn pure_class_role_rule_is_unchanged_by_the_union_find() {
        // Regression: a rule with no Same/Diff must encode exactly as before —
        // one variable per distinct term, one role edge, an O-guard per variable.
        let rule = JRule {
            body: vec![role("r", var("x"), var("y")), class("C", var("x"))],
            head: vec![class("D", var("y"))],
        };
        let (cl, inds) = build(&rule).expect("pure rule fires");
        assert!(inds.is_empty());
        let edge = cl
            .body
            .iter()
            .find_map(|a| match a {
                HAtom::Role { s, t, .. } => Some((*s, *t)),
                _ => None,
            })
            .expect("role edge present");
        assert_ne!(
            edge.0, edge.1,
            "distinct terms x,y stay distinct without a SameAs guard"
        );
    }
}
