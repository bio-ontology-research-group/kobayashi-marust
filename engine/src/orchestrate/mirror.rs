//! Certified private negative-existential mirror route.
//!
//! Some ontologies carry a large family of *private* negative definitions
//!
//! ```text
//! N_F ≡ ¬∃R.F
//! ```
//!
//! where every `N_F` occurs in no other logical axiom. Each such definition is
//! a top-level disjunction (`⊤ ⊑ N_F ⊔ ∃R.F`), so a family of tens of thousands
//! of them defeats the disjunctive context calculus outright. Removing the
//! definitions leaves a positive fragment that classifies in seconds.
//!
//! This module detects that shape, certifies every premise the decomposition
//! needs, classifies the *positive projection* instead of the source, and
//! reconstructs the exact original public taxonomy. It is preprocessing and
//! orchestration only: the CB derivation rules are untouched, and every
//! classification it performs is an ordinary `km classify` of an ordinary
//! ontology. If any premise fails the route returns `None` and the caller
//! classifies the source exactly as before — the route never approximates.
//!
//! # The decomposition
//!
//! Write `P_F` for a fresh name with `P_F ≡ ∃R.F`, so `N_F ≡ ¬P_F`. Removing
//! the private definitions is conservative over the base signature and adding
//! the fresh `P_F` is conservative again, so the projection settles the base
//! and proxy relations exactly. The four regions of the original public
//! taxonomy then come from separate arguments:
//!
//! * **base → base** is the projection restricted to base names.
//! * **negative → negative** is the *reversed* proxy hierarchy, because
//!   `P_F ⊑ P_G` iff `¬P_G ⊑ ¬P_F` iff `N_G ⊑ N_F`.
//! * **base → negative** is empty: `A ⊑ N_F` iff `A ⊓ ∃R.F` is unsatisfiable,
//!   and premise [`Premise::NoMirrorRoleLeftExistential`] makes a proxy's
//!   derived set disjoint from every concept that can take part in a
//!   multi-premise inference, so a base class and a proxy can never jointly
//!   fire a conjunction or reach a disjointness root.
//! * **negative → base** is empty for satisfiable non-top base targets by the
//!   isolated-element argument: with no top GCI, no reflexive or universal
//!   role, no ABox and no nominal, any model extends with a fresh element that
//!   has no role edge and no base membership, so it inhabits every `N_F` while
//!   staying outside every base class.
//!
//! Semantic top and bottom are handled exactly rather than assumed away:
//! `P_F ≡ ⊥` makes `N_F ≡ ⊤` (every satisfiable public class falls below it),
//! and the same premises that give the isolated element prove no named class is
//! equivalent to `⊤`, so no `N_F` is unsatisfiable.
//!
//! # Scale
//!
//! The proxies are never classified as query roots wholesale — one root per
//! private definition is exactly the cost the route exists to avoid. Instead
//! the projection carries the *neighbour slice* of each definition, the target
//! half `∃R.F ⊑ P_F`, which derives proxy membership on the successor side
//! without creating a root, and proxy-to-proxy subsumption is reconstructed by
//! existential monotonicity and role composition from the exact filler
//! taxonomy. Only the inverse-relevant definitions — those whose filler is
//! conjunction-defined through a role inverse to the mirror role, the one shape
//! that can produce a proxy consequence no monotonicity argument reaches — also
//! carry the source half and stay query roots.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::frontend::sexpr::{Node, Parser};

use super::tmpfile::TempPath;
use super::{Classification, Config, OrchestrateError};

/// Namespace of the fresh positive proxies. Reserved to this route; a source
/// ontology that already uses it is refused rather than silently shadowed.
pub const PROXY_IRI_PREFIX: &str = "urn:km:mirror-proxy:";
/// The engine-internal spelling of `PROXY_IRI_PREFIX` (`IriRegistry::short`
/// keeps everything after the first colon of a `urn:` IRI). `Reasoner`'s
/// `KM_QUERY_EXCLUDE_PREFIX` filter matches internal names, not IRIs.
const PROXY_INTERNAL_PREFIX: &str = "km:mirror-proxy:";

/// The arm the projections are classified with. `ht_bridge` is the Konclude
/// bridge: sound and complete on this fragment, and it produces no answer at
/// all rather than an incomplete one, which is what makes a refusal detectable.
const PROJECTION_ROUTE: &str = "ht_bridge";

const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";
const OWL_TOP_ROLE: &str = "http://www.w3.org/2002/07/owl#topObjectProperty";
const OWL_BOTTOM_ROLE: &str = "http://www.w3.org/2002/07/owl#bottomObjectProperty";

// ---------------------------------------------------------------------------
// premises
// ---------------------------------------------------------------------------

/// Every structural premise the reconstruction depends on. A failure is a
/// verdict of *unsupported*, never an approximation: the caller falls through
/// to the ordinary classify path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Premise {
    /// The document could not be read as OWL functional syntax.
    Parse(String),
    /// `owl:imports` is unresolved.
    Imports,
    /// ABox axioms, individuals, datatypes, data properties, or SWRL rules.
    NotPureTbox(String),
    /// A reflexive role: the isolated-element model extension is unsound.
    ReflexiveRole(String),
    /// The universal role: the isolated element would gain edges.
    UniversalRole,
    /// No exact negative-existential mirror definition was found.
    NoMirrors,
    /// A negative name is used outside its own definition.
    NegativeNotPrivate(String),
    /// A complement occurs outside exactly one mirror definition.
    ComplementOutsideMirror(String),
    /// A negative mirror lacks a declaration.
    UndeclaredNegative(String),
    /// Two mirror definitions share a negative name.
    DuplicateMirror(String),
    /// The residual TBox leaves the positive EL + named-disjointness fragment.
    NotPositiveResidual(String),
    /// A top GCI (`⊤ ⊑ C`), which breaks the isolated-element argument.
    TopGci,
    /// An axiom kind the certificate does not model.
    UnsupportedAxiom(String),
    /// A mirror role, or a super-role of one, occurs in a left-position
    /// existential or a domain axiom, so a proxy could acquire base
    /// supersumers. Both the zero-cross argument and the monotonicity
    /// reconstruction depend on this being impossible.
    NoMirrorRoleLeftExistential(String),
    /// A mirror role is functional or inverse-functional, so two proxy
    /// successors could merge and manufacture a cross-region clash.
    MirrorRoleCardinality(String),
    /// A role tied to a mirror role through the role hierarchy or an inverse
    /// carries a constraint that changes what `∃R.F` denotes or which edges a
    /// model has: a domain or range axiom (a range on `R` makes the proxy
    /// `∃R.(F ⊓ Range)`, and a domain on `R⁻` is the same thing), symmetry
    /// (which adds the back edge), asymmetry or irreflexivity (which can make a
    /// proxy unsatisfiable), or a property disjointness. Reconstruction from
    /// the filler taxonomy alone is then no longer exact.
    MirrorRoleConstraint { role: String, constraint: String },
    /// A mirror role is composed by a role chain other than its own
    /// transitivity, so existential composition is not `F ⊑ ∃R.G`.
    MirrorRoleComposed(String),
    /// Two distinct mirror roles are comparable, so `∃R_F.F ⊑ ∃R_G.G` does not
    /// reduce to the same-role case.
    ComparableMirrorRoles(String, String),
    /// A proxy could fall below a conjunction operand, conclusion, or
    /// disjointness root, so base-to-negative emptiness is not certified.
    ZeroCrossTrigger(String),
    /// The reserved proxy namespace is already in use.
    ProxyNamespaceInUse(String),
    /// The projection classified inconsistent, so the source is not the
    /// consistent positive fragment the reconstruction assumes.
    ProjectionInconsistent,
    /// The two projection classifications disagree on the base taxonomy: the
    /// pair relation, or the unsatisfiable base classes.
    BaseTaxonomyDisagreement(String),
    /// The selected inverse-relevant proxies produced no rows at all, so the
    /// query-root selection did not take effect.
    SelectedProxiesNotClassified,
    /// The projection reported a public name the source never declared.
    UnknownProjectedName(String),
}

impl std::fmt::Display for Premise {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Premise::Parse(m) => write!(f, "functional-syntax parse: {m}"),
            Premise::Imports => write!(f, "owl:imports is not resolved"),
            Premise::NotPureTbox(m) => write!(f, "not a pure TBox: {m}"),
            Premise::ReflexiveRole(r) => write!(f, "reflexive role: {r}"),
            Premise::UniversalRole => write!(f, "universal role in a logical axiom"),
            Premise::NoMirrors => write!(f, "no exact negative-existential mirror definition"),
            Premise::NegativeNotPrivate(n) => write!(f, "negative mirror is not private: {n}"),
            Premise::ComplementOutsideMirror(m) => {
                write!(f, "complement outside exactly one mirror definition: {m}")
            }
            Premise::UndeclaredNegative(n) => write!(f, "negative mirror is not declared: {n}"),
            Premise::DuplicateMirror(n) => write!(f, "negative has multiple definitions: {n}"),
            Premise::NotPositiveResidual(m) => write!(f, "non-positive residual axiom: {m}"),
            Premise::TopGci => write!(f, "top GCI is not permitted"),
            Premise::UnsupportedAxiom(m) => write!(f, "unsupported axiom: {m}"),
            Premise::NoMirrorRoleLeftExistential(r) => {
                write!(
                    f,
                    "mirror role in a left-position existential or domain: {r}"
                )
            }
            Premise::MirrorRoleCardinality(r) => write!(f, "mirror role has cardinality: {r}"),
            Premise::MirrorRoleConstraint { role, constraint } => {
                write!(f, "mirror-related role {role} carries {constraint}")
            }
            Premise::MirrorRoleComposed(r) => write!(f, "mirror role is chain-composed: {r}"),
            Premise::ComparableMirrorRoles(a, b) => {
                write!(f, "comparable mirror roles: {a} and {b}")
            }
            Premise::ZeroCrossTrigger(m) => write!(f, "zero-cross premise fails: {m}"),
            Premise::ProxyNamespaceInUse(n) => write!(f, "reserved proxy namespace in use: {n}"),
            Premise::ProjectionInconsistent => write!(f, "positive projection is inconsistent"),
            Premise::BaseTaxonomyDisagreement(m) => {
                write!(f, "projection base taxonomies disagree: {m}")
            }
            Premise::SelectedProxiesNotClassified => {
                write!(f, "selected proxy query roots produced no rows")
            }
            Premise::UnknownProjectedName(n) => write!(f, "undeclared projected name: {n}"),
        }
    }
}

// ---------------------------------------------------------------------------
// detection
// ---------------------------------------------------------------------------

/// The frontend's identity for an entity token: `IriRegistry::short` strips the
/// angle brackets of a full IRI and otherwise keys on the token as written, so
/// `<ex:A>` and `ex:A` name the same class and a prefixed name never needs
/// expanding. Using the same key here is what keeps the projection's declared
/// universe and the classifier's output IRIs in step for every spelling OWL
/// functional syntax allows.
fn entity_key(token: &str) -> String {
    let raw = token.trim();
    raw.strip_prefix('<')
        .and_then(|s| s.strip_suffix('>'))
        .unwrap_or(raw)
        .to_string()
}

/// `entity_key` plus the frontend's builtin canonicalisation: both spellings of
/// `owl:Thing` and `owl:Nothing` are the semantic constants, never source
/// classes (`iri::owl_builtin_class`).
fn class_key(token: &str) -> ClassRef {
    let raw = entity_key(token);
    match raw.as_str() {
        "owl:Thing" | OWL_THING => ClassRef::Top,
        "owl:Nothing" | OWL_NOTHING => ClassRef::Bottom,
        _ => ClassRef::Iri(raw),
    }
}

/// A class position: the two OWL builtins are semantic constants, everything
/// else is a source IRI.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum ClassRef {
    Top,
    Bottom,
    Iri(String),
}

/// One private definition `negative ≡ ¬∃role.filler` and the fresh positive
/// proxy that replaces it.
#[derive(Debug, Clone)]
pub struct Mirror {
    pub negative: String,
    pub proxy: String,
    pub role: String,
    filler: ClassRef,
    /// The proxy also carries the source half and stays a query root.
    selected: bool,
}

/// The certified fragment: what the source is, and everything the projection
/// and the reconstruction need.
#[derive(Debug)]
pub struct Fragment {
    mirrors: Vec<Mirror>,
    /// Declared source classes, excluding the OWL builtins.
    declared: BTreeSet<String>,
    /// Declared classes that are not negative mirrors.
    base: BTreeSet<String>,
    /// `negative` keyed by proxy IRI.
    negative_of_proxy: HashMap<String, String>,
    /// Proxies keyed by filler, in mirror order.
    proxies_of_filler: HashMap<ClassRef, Vec<usize>>,
    /// The single mirror role, or the set when several are used.
    mirror_roles: BTreeSet<String>,
    /// Mirror roles that are transitive (so `∃R.∃R.C ⊑ ∃R.C` for that role).
    transitive_mirror_roles: BTreeSet<String>,
    selected_proxies: BTreeSet<String>,
}

impl Fragment {
    pub fn mirrors(&self) -> &[Mirror] {
        &self.mirrors
    }
    pub fn selected_count(&self) -> usize {
        self.selected_proxies.len()
    }
}

/// Prefix map plus the raw facts one streaming pass over the document
/// collects. Everything here is checked before a projection is written.
struct Scan {
    declared_classes: BTreeSet<String>,
    /// class IRI -> number of logical axioms mentioning it
    occurrences: HashMap<String, u32>,
    /// negative IRI -> (role, filler)
    mirrors: BTreeMap<String, (String, ClassRef)>,
    complement_axioms: usize,
    complements: usize,
    /// role -> super-roles (`SubObjectPropertyOf` and `EquivalentObjectProperties`)
    super_roles: HashMap<String, BTreeSet<String>>,
    /// role -> inverse roles
    inverse_roles: HashMap<String, BTreeSet<String>>,
    transitive: HashSet<String>,
    functional: HashSet<String>,
    /// role -> the constraint kinds it carries that a mirror role must not
    /// have: domain, range, symmetry, asymmetry, irreflexivity, or property
    /// disjointness.
    role_constraints: BTreeMap<String, BTreeSet<&'static str>>,
    /// roles that appear as the target of a role chain of length >= 2
    chain_targets: HashSet<String>,
    /// roles carrying a left-position existential (`∃R.C ⊑ D`) or a domain axiom
    left_existential_roles: HashSet<String>,
    /// (role, filler-IRI) of every head-position existential over a *named*
    /// class; used to find the inverse-relevant mirrors.
    head_existentials: HashSet<(String, String)>,
    /// class IRIs conjunction-defined through an existential, keyed by the
    /// existential's role: `F ≡ … ⊓ ∃S.C …`.
    inverse_definable: HashMap<String, BTreeSet<String>>,
    /// Every trigger expression: conjunction operands, conjunction conclusions,
    /// and named disjointness roots. Named ones by IRI, anonymous ones as
    /// `(role, filler)` existential shapes.
    named_triggers: BTreeSet<String>,
    existential_triggers: BTreeSet<(String, ClassRef)>,
}

impl Scan {
    fn new() -> Scan {
        Scan {
            declared_classes: BTreeSet::new(),
            occurrences: HashMap::new(),
            mirrors: BTreeMap::new(),
            complement_axioms: 0,
            complements: 0,
            super_roles: HashMap::new(),
            inverse_roles: HashMap::new(),
            transitive: HashSet::new(),
            functional: HashSet::new(),
            role_constraints: BTreeMap::new(),
            chain_targets: HashSet::new(),
            left_existential_roles: HashSet::new(),
            head_existentials: HashSet::new(),
            inverse_definable: HashMap::new(),
            named_triggers: BTreeSet::new(),
            existential_triggers: BTreeSet::new(),
        }
    }

    fn class_ref(&self, node: &Node) -> Result<ClassRef, Premise> {
        let atom = node
            .as_atom()
            .ok_or_else(|| Premise::NotPositiveResidual(serialize(node)))?;
        Ok(class_key(atom))
    }

    /// A named object property. `ObjectInverseOf` and the two builtin roles are
    /// refused: the certificate is stated over named roles only.
    fn role_iri(&self, node: &Node) -> Result<String, Premise> {
        let atom = node
            .as_atom()
            .ok_or_else(|| Premise::UnsupportedAxiom(serialize(node)))?;
        let name = entity_key(atom);
        if name == "owl:topObjectProperty" || name == OWL_TOP_ROLE {
            return Err(Premise::UniversalRole);
        }
        if name == "owl:bottomObjectProperty" || name == OWL_BOTTOM_ROLE {
            return Err(Premise::UnsupportedAxiom(name));
        }
        Ok(name)
    }

    /// Positive EL over the source signature: a named class (or `owl:Thing`),
    /// a conjunction, or an existential over a named role. `owl:Nothing` is
    /// excluded — a bottom constructor would break the isolated element.
    fn positive_el(&self, node: &Node) -> Result<(), Premise> {
        match node {
            Node::Atom(_) => match self.class_ref(node)? {
                ClassRef::Bottom => Err(Premise::NotPositiveResidual(serialize(node))),
                _ => Ok(()),
            },
            Node::List("ObjectIntersectionOf", args) => {
                if args.is_empty() {
                    return Err(Premise::NotPositiveResidual(serialize(node)));
                }
                for a in args {
                    self.positive_el(a)?;
                }
                Ok(())
            }
            Node::List("ObjectSomeValuesFrom", args) if args.len() == 2 => {
                self.role_iri(&args[0])?;
                self.positive_el(&args[1])
            }
            other => Err(Premise::NotPositiveResidual(serialize(other))),
        }
    }

    /// `⊤` up to conjunction: an axiom side that is semantically top would be a
    /// top GCI in disguise.
    fn semantic_top(&self, node: &Node) -> bool {
        match node {
            Node::Atom(_) => matches!(self.class_ref(node), Ok(ClassRef::Top)),
            Node::List("ObjectIntersectionOf", args) => args.iter().all(|a| self.semantic_top(a)),
            _ => false,
        }
    }

    /// Record every class named anywhere in one logical axiom (once per axiom,
    /// matching an OWLAPI signature walk).
    fn note_occurrences(&mut self, node: &Node) {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        collect_atoms(node, &mut |tok| {
            if let ClassRef::Iri(iri) = class_key(tok) {
                seen.insert(iri);
            }
        });
        for iri in seen {
            *self.occurrences.entry(iri).or_insert(0) += 1;
        }
    }

    /// Walk a class expression in a *body* (subclass) position, recording the
    /// roles of its existentials. A mirror role reached here would let a proxy
    /// acquire base supersumers.
    fn note_left_existentials(&mut self, node: &Node) -> Result<(), Premise> {
        match node {
            Node::List("ObjectIntersectionOf", args) => {
                for a in args {
                    self.note_left_existentials(a)?;
                }
                Ok(())
            }
            Node::List("ObjectSomeValuesFrom", args) if args.len() == 2 => {
                let role = self.role_iri(&args[0])?;
                self.left_existential_roles.insert(role);
                self.note_left_existentials(&args[1])
            }
            _ => Ok(()),
        }
    }

    /// Walk a class expression in a *head* (superclass) position, recording the
    /// `(role, named filler)` existentials that create successors.
    fn note_head_existentials(&mut self, node: &Node) -> Result<(), Premise> {
        match node {
            Node::List("ObjectIntersectionOf", args) => {
                for a in args {
                    self.note_head_existentials(a)?;
                }
                Ok(())
            }
            Node::List("ObjectSomeValuesFrom", args) if args.len() == 2 => {
                let role = self.role_iri(&args[0])?;
                if let Ok(ClassRef::Iri(filler)) = self.class_ref(&args[1]) {
                    self.head_existentials.insert((role, filler));
                }
                self.note_head_existentials(&args[1])
            }
            _ => Ok(()),
        }
    }

    /// Record every trigger position of one conjunction GCI: the operands and
    /// the conclusion. The zero-cross premise asks whether a proxy can fall
    /// below any of them.
    fn note_triggers(&mut self, node: &Node) -> Result<(), Premise> {
        match node {
            Node::Atom(_) => {
                if let ClassRef::Iri(iri) = self.class_ref(node)? {
                    self.named_triggers.insert(iri);
                }
                Ok(())
            }
            Node::List("ObjectIntersectionOf", args) => {
                for a in args {
                    self.note_triggers(a)?;
                }
                Ok(())
            }
            Node::List("ObjectSomeValuesFrom", args) if args.len() == 2 => {
                let role = self.role_iri(&args[0])?;
                let filler = self.class_ref(&args[1]).unwrap_or(ClassRef::Top);
                self.existential_triggers.insert((role, filler));
                Ok(())
            }
            other => Err(Premise::NotPositiveResidual(serialize(other))),
        }
    }

    fn note_constraint(&mut self, role: &str, constraint: &'static str) {
        self.role_constraints
            .entry(role.to_string())
            .or_default()
            .insert(constraint);
    }

    /// `F ≡ … ⊓ ∃S.C …`: remember `F` under `S`. A mirror whose filler is
    /// inverse-definable this way can gain a proxy consequence through the
    /// predecessor edge, so it is classified exactly instead of derived.
    fn note_inverse_definable(&mut self, defined: &ClassRef, expression: &Node) {
        let ClassRef::Iri(name) = defined else {
            return;
        };
        let Node::List("ObjectIntersectionOf", args) = expression else {
            return;
        };
        for operand in args {
            if let Node::List("ObjectSomeValuesFrom", ex) = operand {
                if ex.len() == 2 {
                    if let Ok(role) = self.role_iri(&ex[0]) {
                        self.inverse_definable
                            .entry(role)
                            .or_default()
                            .insert(name.clone());
                    }
                }
            }
        }
    }
}

/// One top-level document item.
enum Item<'a, 'b> {
    Header(&'a str, &'b [Node<'a>]),
    Axiom(&'b Node<'a>),
}

/// Stream the document: every non-`Ontology` top-level node whole, and every
/// child of `Ontology(...)` one at a time. Mirrors
/// `parse::for_each_ontology_child` but also exposes the prefix declarations,
/// which the route needs to resolve prefixed names.
fn walk<'a, F>(text: &'a str, mut f: F) -> Result<(), Premise>
where
    F: FnMut(Item<'a, '_>) -> Result<(), Premise>,
{
    let perr = |e: String| Premise::Parse(e);
    let mut p = Parser::new(text);
    while p.peek().is_some() {
        let head = p.next_tok().unwrap();
        if head == "(" {
            return Err(perr("unexpected (".to_string()));
        }
        if p.peek() != Some("(") {
            continue; // bare atom at top level
        }
        p.next_tok();
        if head == "Ontology" {
            while p.peek() != Some(")") {
                if p.peek().is_none() {
                    return Err(perr("unexpected end of input".to_string()));
                }
                let node = p.parse().map_err(perr)?;
                f(Item::Axiom(&node))?;
            }
            p.next_tok();
        } else {
            let mut args = Vec::new();
            while p.peek() != Some(")") {
                if p.peek().is_none() {
                    return Err(perr("unexpected end of input".to_string()));
                }
                args.push(p.parse().map_err(perr)?);
            }
            p.next_tok();
            f(Item::Header(head, &args))?;
        }
    }
    Ok(())
}

fn collect_atoms(node: &Node, f: &mut impl FnMut(&str)) {
    match node {
        Node::Atom(s) => f(s),
        Node::List(_, args) => {
            for a in args {
                collect_atoms(a, f);
            }
        }
    }
}

/// Re-serialise a parsed node back to functional syntax. Token slices are
/// copied verbatim, so prefixed names keep working against the copied `Prefix`
/// declarations.
fn serialize(node: &Node) -> String {
    let mut out = Vec::new();
    write_node(&mut out, node).expect("serialise into Vec");
    String::from_utf8(out).unwrap_or_default()
}

fn write_node<W: Write>(w: &mut W, node: &Node) -> std::io::Result<()> {
    match node {
        Node::Atom(s) => w.write_all(s.as_bytes()),
        Node::List(h, args) => {
            w.write_all(h.as_bytes())?;
            w.write_all(b"(")?;
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    w.write_all(b" ")?;
                }
                write_node(w, a)?;
            }
            w.write_all(b")")
        }
    }
}

/// `EquivalentClasses(N ObjectComplementOf(ObjectSomeValuesFrom(R F)))` in
/// either argument order, with `N`, `R` and `F` all named.
fn exact_mirror(scan: &Scan, args: &[Node]) -> Option<(String, String, ClassRef)> {
    if args.len() != 2 {
        return None;
    }
    for (name, expression) in [(&args[0], &args[1]), (&args[1], &args[0])] {
        let Ok(ClassRef::Iri(negative)) = scan.class_ref(name) else {
            continue;
        };
        let Node::List("ObjectComplementOf", inner) = expression else {
            continue;
        };
        if inner.len() != 1 {
            continue;
        }
        let Node::List("ObjectSomeValuesFrom", ex) = &inner[0] else {
            continue;
        };
        if ex.len() != 2 {
            continue;
        }
        let (Ok(role), Ok(filler)) = (scan.role_iri(&ex[0]), scan.class_ref(&ex[1])) else {
            continue;
        };
        return Some((negative, role, filler));
    }
    None
}

fn count_complements(node: &Node) -> usize {
    match node {
        Node::Atom(_) => 0,
        Node::List(h, args) => {
            let here = usize::from(*h == "ObjectComplementOf");
            here + args.iter().map(count_complements).sum::<usize>()
        }
    }
}

/// A declaration node's entity kind and name, if it declares one.
fn declaration_entity<'a>(args: &'a [Node<'a>]) -> Option<(&'a str, &'a str)> {
    let Node::List(kind, inner) = args.first()? else {
        return None;
    };
    Some((kind, inner.first()?.as_atom()?))
}

/// Detect and certify the fragment. `Ok(None)` means the ontology does not
/// carry the shape at all; `Err` names the premise that failed.
pub fn detect(text: &str) -> Result<Option<Fragment>, Premise> {
    // Cheap refusal: without a complement there is no mirror family, and the
    // streaming pass below is pure cost on every other ontology.
    if !text.contains("ObjectComplementOf") {
        return Ok(None);
    }
    let mut scan = Scan::new();
    let mut saw_mirror = false;
    walk(text, |item| match item {
        // Prefix declarations need no interpretation: entity identity follows
        // the frontend, which keys on the token as written. They are copied
        // verbatim into the projections so every spelling keeps resolving.
        Item::Header(..) => Ok(()),
        Item::Axiom(node) => scan_axiom(&mut scan, node, &mut saw_mirror),
    })?;

    if scan.mirrors.is_empty() {
        return Ok(None);
    }
    finish(scan)
}

/// One source axiom: validate its shape and record what the certificate needs.
fn scan_axiom(scan: &mut Scan, node: &Node, saw_mirror: &mut bool) -> Result<(), Premise> {
    let (head, args) = match node {
        Node::List(h, a) => (*h, a.as_slice()),
        // The ontology IRI / version IRI children.
        Node::Atom(_) => return Ok(()),
    };
    match head {
        "Import" => return Err(Premise::Imports),
        "Declaration" => {
            let Some((kind, token)) = declaration_entity(args) else {
                return Err(Premise::UnsupportedAxiom(serialize(node)));
            };
            match kind {
                "Class" => {
                    if let ClassRef::Iri(iri) = class_key(token) {
                        if iri.starts_with(PROXY_IRI_PREFIX) {
                            return Err(Premise::ProxyNamespaceInUse(iri));
                        }
                        scan.declared_classes.insert(iri);
                    }
                }
                "ObjectProperty" | "AnnotationProperty" => {}
                other => {
                    return Err(Premise::NotPureTbox(format!("declared {other}")));
                }
            }
            return Ok(());
        }
        "Annotation"
        | "AnnotationAssertion"
        | "SubAnnotationPropertyOf"
        | "AnnotationPropertyDomain"
        | "AnnotationPropertyRange" => return Ok(()),
        _ => {}
    }

    // From here the axiom is logical: every class it names counts as an
    // occurrence, and its complements must sit inside a mirror definition.
    let complements = count_complements(node);
    if complements > 0 {
        scan.complements += complements;
        scan.complement_axioms += 1;
    }

    match head {
        "EquivalentClasses" => {
            if let Some((negative, role, filler)) = exact_mirror(scan, args) {
                if complements != 1 {
                    return Err(Premise::ComplementOutsideMirror(format!(
                        "{complements} in the definition of {negative}"
                    )));
                }
                if scan
                    .mirrors
                    .insert(negative.clone(), (role, filler))
                    .is_some()
                {
                    return Err(Premise::DuplicateMirror(negative));
                }
                *saw_mirror = true;
                scan.note_occurrences(node);
                return Ok(());
            }
            if complements != 0 {
                return Err(Premise::ComplementOutsideMirror(format!(
                    "inexact equivalence {}",
                    serialize(node)
                )));
            }
            for a in args {
                if scan.semantic_top(a) {
                    return Err(Premise::TopGci);
                }
                scan.positive_el(a)?;
            }
            // Every ordered pair of an equivalence is both a body and a head.
            for a in args {
                scan.note_left_existentials(a)?;
                scan.note_head_existentials(a)?;
            }
            for (index, left) in args.iter().enumerate() {
                if !matches!(left, Node::List("ObjectIntersectionOf", _)) {
                    continue;
                }
                for (other, right) in args.iter().enumerate() {
                    if other == index {
                        continue;
                    }
                    scan.note_triggers(left)?;
                    scan.note_triggers(right)?;
                }
            }
            for a in args {
                if let Ok(defined) = scan.class_ref(a) {
                    for other in args {
                        if !std::ptr::eq(a, other) {
                            scan.note_inverse_definable(&defined, other);
                        }
                    }
                }
            }
            scan.note_occurrences(node);
        }
        "SubClassOf" if args.len() == 2 => {
            if complements != 0 {
                return Err(Premise::ComplementOutsideMirror(format!(
                    "subclass axiom {}",
                    serialize(node)
                )));
            }
            if scan.semantic_top(&args[0]) {
                return Err(Premise::TopGci);
            }
            scan.positive_el(&args[0])?;
            scan.positive_el(&args[1])?;
            scan.note_left_existentials(&args[0])?;
            scan.note_head_existentials(&args[1])?;
            if matches!(&args[0], Node::List("ObjectIntersectionOf", _)) {
                scan.note_triggers(&args[0])?;
                scan.note_triggers(&args[1])?;
            }
            scan.note_occurrences(node);
        }
        "DisjointClasses" => {
            if args.len() < 2 {
                return Err(Premise::UnsupportedAxiom(serialize(node)));
            }
            for a in args {
                match scan.class_ref(a)? {
                    ClassRef::Iri(iri) => {
                        scan.named_triggers.insert(iri);
                    }
                    _ => return Err(Premise::NotPositiveResidual(serialize(node))),
                }
            }
            scan.note_occurrences(node);
        }
        "DisjointUnion" => return Err(Premise::UnsupportedAxiom(head.to_string())),
        "ObjectPropertyDomain" if args.len() == 2 => {
            let role = scan.role_iri(&args[0])?;
            scan.positive_el(&args[1])?;
            // `∃R.⊤ ⊑ C`: a body existential over R.
            scan.left_existential_roles.insert(role.clone());
            scan.note_constraint(&role, "a domain axiom");
            scan.note_head_existentials(&args[1])?;
            scan.note_occurrences(node);
        }
        "ObjectPropertyRange" if args.len() == 2 => {
            let role = scan.role_iri(&args[0])?;
            scan.positive_el(&args[1])?;
            // `⊤ ⊑ ∀R.C` types every R-successor, so `∃R.F` is really
            // `∃R.(F ⊓ C)` and the filler taxonomy no longer decides the proxy
            // hierarchy on its own.
            scan.note_constraint(&role, "a range axiom");
            scan.note_head_existentials(&args[1])?;
            scan.note_occurrences(node);
        }
        "SubObjectPropertyOf" if args.len() == 2 => {
            let super_role = scan.role_iri(&args[1])?;
            match &args[0] {
                Node::List("ObjectPropertyChain", chain) => {
                    for r in chain {
                        scan.role_iri(r)?;
                    }
                    if chain.len() >= 2 {
                        scan.chain_targets.insert(super_role);
                    }
                }
                other => {
                    let sub = scan.role_iri(other)?;
                    scan.super_roles.entry(sub).or_default().insert(super_role);
                }
            }
        }
        "EquivalentObjectProperties" => {
            let mut roles = Vec::new();
            for a in args {
                roles.push(scan.role_iri(a)?);
            }
            for a in &roles {
                for b in &roles {
                    if a != b {
                        scan.super_roles
                            .entry(a.clone())
                            .or_default()
                            .insert(b.clone());
                    }
                }
            }
        }
        "InverseObjectProperties" if args.len() == 2 => {
            let a = scan.role_iri(&args[0])?;
            let b = scan.role_iri(&args[1])?;
            scan.inverse_roles
                .entry(a.clone())
                .or_default()
                .insert(b.clone());
            scan.inverse_roles.entry(b).or_default().insert(a);
        }
        "TransitiveObjectProperty" if args.len() == 1 => {
            let r = scan.role_iri(&args[0])?;
            scan.transitive.insert(r);
        }
        "FunctionalObjectProperty" | "InverseFunctionalObjectProperty" if args.len() == 1 => {
            let r = scan.role_iri(&args[0])?;
            scan.functional.insert(r);
        }
        "SymmetricObjectProperty" | "AsymmetricObjectProperty" | "IrreflexiveObjectProperty"
            if args.len() == 1 =>
        {
            let role = scan.role_iri(&args[0])?;
            let kind = match head {
                "SymmetricObjectProperty" => "symmetry",
                "AsymmetricObjectProperty" => "asymmetry",
                _ => "irreflexivity",
            };
            scan.note_constraint(&role, kind);
        }
        "ReflexiveObjectProperty" if args.len() == 1 => {
            return Err(Premise::ReflexiveRole(scan.role_iri(&args[0])?));
        }
        "DisjointObjectProperties" => {
            for a in args {
                let role = scan.role_iri(a)?;
                scan.note_constraint(&role, "a property disjointness");
            }
        }
        "ClassAssertion"
        | "ObjectPropertyAssertion"
        | "NegativeObjectPropertyAssertion"
        | "DataPropertyAssertion"
        | "NegativeDataPropertyAssertion"
        | "SameIndividual"
        | "DifferentIndividuals" => {
            return Err(Premise::NotPureTbox(head.to_string()));
        }
        "DLSafeRule"
        | "SubDataPropertyOf"
        | "DataPropertyDomain"
        | "DataPropertyRange"
        | "FunctionalDataProperty"
        | "EquivalentDataProperties"
        | "DisjointDataProperties"
        | "DatatypeDefinition"
        | "HasKey" => {
            return Err(Premise::NotPureTbox(head.to_string()));
        }
        other => return Err(Premise::UnsupportedAxiom(other.to_string())),
    }
    Ok(())
}

/// Close the certificate over the collected facts and build the fragment.
fn finish(scan: Scan) -> Result<Option<Fragment>, Premise> {
    // Every complement sits inside exactly one mirror definition.
    if scan.complements != scan.mirrors.len() || scan.complement_axioms != scan.mirrors.len() {
        return Err(Premise::ComplementOutsideMirror(format!(
            "{} complements in {} axioms for {} mirrors",
            scan.complements,
            scan.complement_axioms,
            scan.mirrors.len()
        )));
    }

    // Each negative is declared and used nowhere but its own definition.
    for negative in scan.mirrors.keys() {
        if !scan.declared_classes.contains(negative) {
            return Err(Premise::UndeclaredNegative(negative.clone()));
        }
        if scan.occurrences.get(negative).copied().unwrap_or(0) != 1 {
            return Err(Premise::NegativeNotPrivate(negative.clone()));
        }
    }

    let mirror_roles: BTreeSet<String> = scan.mirrors.values().map(|(r, _)| r.clone()).collect();

    // Role-hierarchy closure over the mirror roles, so "super-role of a mirror
    // role" and "comparable mirror roles" are exact rather than syntactic.
    let mut role_supers: HashMap<String, BTreeSet<String>> = HashMap::new();
    for role in scan.super_roles.keys().chain(mirror_roles.iter()) {
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut stack = vec![role.clone()];
        while let Some(current) = stack.pop() {
            for next in scan.super_roles.get(&current).into_iter().flatten() {
                if seen.insert(next.clone()) {
                    stack.push(next.clone());
                }
            }
        }
        role_supers.insert(role.clone(), seen);
    }
    let supers_of = |r: &str| -> BTreeSet<String> {
        let mut set = role_supers.get(r).cloned().unwrap_or_default();
        set.insert(r.to_string());
        set
    };

    // Distinct mirror roles must be incomparable: otherwise `∃R_F.F ⊑ ∃R_G.G`
    // does not reduce to the same-role monotonicity case.
    for a in &mirror_roles {
        for b in &mirror_roles {
            if a != b && supers_of(a).contains(b) {
                return Err(Premise::ComparableMirrorRoles(a.clone(), b.clone()));
            }
        }
    }

    // No proxy may acquire a base supersumer, and no mirror successor may be
    // merged by cardinality or manufactured by a chain.
    let mut mirror_closure: BTreeSet<String> = BTreeSet::new();
    for r in &mirror_roles {
        mirror_closure.extend(supers_of(r));
    }
    for r in &mirror_closure {
        if scan.left_existential_roles.contains(r) {
            return Err(Premise::NoMirrorRoleLeftExistential(r.clone()));
        }
        if scan.chain_targets.contains(r) {
            return Err(Premise::MirrorRoleComposed(r.clone()));
        }
    }

    // Everything a mirror edge is also an edge of: the super-roles of a mirror
    // role, the named inverses of those, and their super-roles in turn. A
    // constraint anywhere in this closure is a constraint on the mirror edge —
    // a range on `R`, or equivalently a domain on `R⁻`, retypes the successor
    // and turns `P_F` into `∃R.(F ⊓ C)`; symmetry adds the back edge; asymmetry
    // and irreflexivity can make a proxy unsatisfiable; a property disjointness
    // can do the same. None of that survives filler-only reconstruction, so the
    // route refuses rather than approximating.
    let mut mirror_related: BTreeSet<String> = mirror_closure.clone();
    let mut frontier: Vec<String> = mirror_related.iter().cloned().collect();
    while let Some(role) = frontier.pop() {
        let mut next: BTreeSet<String> = supers_of(&role);
        next.extend(scan.inverse_roles.get(&role).into_iter().flatten().cloned());
        for candidate in next {
            if mirror_related.insert(candidate.clone()) {
                frontier.push(candidate);
            }
        }
    }
    for role in &mirror_related {
        if scan.functional.contains(role) {
            return Err(Premise::MirrorRoleCardinality(role.clone()));
        }
        if let Some(constraints) = scan.role_constraints.get(role) {
            if let Some(constraint) = constraints.iter().next() {
                return Err(Premise::MirrorRoleConstraint {
                    role: role.clone(),
                    constraint: (*constraint).to_string(),
                });
            }
        }
    }

    // Zero-cross: with no left-position existential over a mirror role a proxy
    // has no base supersumer, so it can only fall below a trigger if the
    // trigger is itself an existential the proxy structurally satisfies.
    for (role, filler) in &scan.existential_triggers {
        for mirror_role in &mirror_roles {
            if !supers_of(mirror_role).contains(role) {
                continue;
            }
            // `∃R.F ⊑ ∃S.C` with R ⊑ S needs `F ⊑ C`, which the projection
            // could well entail; refuse rather than reason about it here.
            let _ = filler;
            return Err(Premise::ZeroCrossTrigger(format!(
                "conjunction operand over mirror role {role}"
            )));
        }
    }

    let transitive_mirror_roles: BTreeSet<String> = mirror_roles
        .iter()
        .filter(|r| scan.transitive.contains(*r))
        .cloned()
        .collect();

    // The inverse-relevant family: a filler that is conjunction-defined through
    // a role inverse to its mirror role can gain a proxy consequence at the
    // successor, which no monotonicity argument over the filler taxonomy
    // reaches. Those proxies keep the source half and stay query roots.
    let mut selected_fillers: HashSet<String> = HashSet::new();
    for mirror_role in &mirror_roles {
        for inverse in scan.inverse_roles.get(mirror_role).into_iter().flatten() {
            if let Some(names) = scan.inverse_definable.get(inverse) {
                selected_fillers.extend(names.iter().cloned());
            }
        }
    }

    let mut mirrors: Vec<Mirror> = Vec::with_capacity(scan.mirrors.len());
    for (index, (negative, (role, filler))) in scan.mirrors.iter().enumerate() {
        let selected = match filler {
            ClassRef::Iri(iri) => selected_fillers.contains(iri),
            _ => false,
        };
        mirrors.push(Mirror {
            negative: negative.clone(),
            proxy: format!("{PROXY_IRI_PREFIX}{index}"),
            role: role.clone(),
            filler: filler.clone(),
            selected,
        });
    }

    let negatives: BTreeSet<String> = scan.mirrors.keys().cloned().collect();
    let base: BTreeSet<String> = scan
        .declared_classes
        .iter()
        .filter(|c| !negatives.contains(*c))
        .cloned()
        .collect();
    let mut negative_of_proxy = HashMap::with_capacity(mirrors.len());
    let mut proxies_of_filler: HashMap<ClassRef, Vec<usize>> = HashMap::new();
    let mut selected_proxies = BTreeSet::new();
    for (index, mirror) in mirrors.iter().enumerate() {
        negative_of_proxy.insert(mirror.proxy.clone(), mirror.negative.clone());
        proxies_of_filler
            .entry(mirror.filler.clone())
            .or_default()
            .push(index);
        if mirror.selected {
            selected_proxies.insert(mirror.proxy.clone());
        }
    }

    // Named triggers are certified by construction (a proxy has no base
    // supersumer), but the check is kept explicit so a future relaxation of the
    // left-existential premise cannot silently weaken it.
    debug_assert!(scan
        .named_triggers
        .iter()
        .all(|t| !t.starts_with(PROXY_IRI_PREFIX)));

    Ok(Some(Fragment {
        mirrors,
        declared: scan.declared_classes,
        base,
        negative_of_proxy,
        proxies_of_filler,
        mirror_roles,
        transitive_mirror_roles,
        selected_proxies,
    }))
}

// ---------------------------------------------------------------------------
// projection
// ---------------------------------------------------------------------------

/// Write the base projection (private definitions removed) and the neighbour
/// slice (base projection plus the proxy halves) in one streaming pass.
fn write_projections(
    text: &str,
    fragment: &Fragment,
    base_path: &Path,
    slice_path: &Path,
) -> Result<(), OrchestrateError> {
    let mut base = BufWriter::new(File::create(base_path)?);
    let mut slice = BufWriter::new(File::create(slice_path)?);
    let negatives: HashSet<&str> = fragment
        .mirrors
        .iter()
        .map(|m| m.negative.as_str())
        .collect();

    let mut header: Vec<String> = Vec::new();
    walk(text, |item| {
        if let Item::Header(head, args) = item {
            let node = Node::List(head, args.to_vec());
            header.push(serialize(&node));
        }
        Ok(())
    })
    .map_err(|p| OrchestrateError::OutOfFragment(p.to_string()))?;
    for line in &header {
        writeln!(base, "{line}")?;
        writeln!(slice, "{line}")?;
    }
    writeln!(base, "Ontology(<urn:km:mirror-projection:base>")?;
    writeln!(slice, "Ontology(<urn:km:mirror-projection:slice>")?;

    let mut error: Option<OrchestrateError> = None;
    walk(text, |item| {
        let Item::Axiom(node) = item else {
            return Ok(());
        };
        let keep = match node {
            Node::Atom(_) => false,
            Node::List(h, args) => match *h {
                "Declaration" => match declaration_entity(args) {
                    Some(("Class", token)) => {
                        let iri = token.trim_start_matches('<').trim_end_matches('>');
                        !negatives.contains(iri)
                    }
                    _ => true,
                },
                "EquivalentClasses" => count_complements(node) == 0,
                _ => true,
            },
        };
        if keep {
            let emit = |w: &mut BufWriter<File>| -> std::io::Result<()> {
                write_node(w, node)?;
                w.write_all(b"\n")
            };
            if let Err(e) = emit(&mut base).and_then(|_| emit(&mut slice)) {
                error = Some(OrchestrateError::Io(e));
            }
        }
        Ok(())
    })
    .map_err(|p| OrchestrateError::OutOfFragment(p.to_string()))?;
    if let Some(e) = error {
        return Err(e);
    }

    for mirror in &fragment.mirrors {
        let filler = match &mirror.filler {
            ClassRef::Top => format!("<{OWL_THING}>"),
            ClassRef::Bottom => format!("<{OWL_NOTHING}>"),
            ClassRef::Iri(iri) => format!("<{iri}>"),
        };
        let existential = format!("ObjectSomeValuesFrom(<{}> {filler})", mirror.role);
        writeln!(slice, "Declaration(Class(<{}>))", mirror.proxy)?;
        // The neighbour slice: proxy membership is derived on the successor
        // side, so no query root is created for it.
        writeln!(slice, "SubClassOf({existential} <{}>)", mirror.proxy)?;
        if mirror.selected {
            writeln!(slice, "SubClassOf(<{}> {existential})", mirror.proxy)?;
        }
    }
    writeln!(base, ")")?;
    writeln!(slice, ")")?;
    base.flush()?;
    slice.flush()?;
    Ok(())
}

// ---------------------------------------------------------------------------
// reconstruction
// ---------------------------------------------------------------------------

/// Row-indexed view of a projection classification.
struct Taxonomy {
    consistent: bool,
    /// base subject -> base supersumers
    base_base: HashMap<String, BTreeSet<String>>,
    /// base subject -> proxy supersumers
    base_proxy: HashMap<String, BTreeSet<String>>,
    /// proxy subject -> proxy supersumers
    proxy_proxy: HashMap<String, BTreeSet<String>>,
    /// proxy subject -> base supersumers (must stay empty under the premises)
    proxy_base: usize,
    unsat: BTreeSet<String>,
    base_pairs: usize,
}

fn index(classification: &Classification) -> Taxonomy {
    let mut taxonomy = Taxonomy {
        consistent: classification.consistent,
        base_base: HashMap::new(),
        base_proxy: HashMap::new(),
        proxy_proxy: HashMap::new(),
        proxy_base: 0,
        unsat: classification.unsatisfiable.iter().cloned().collect(),
        base_pairs: 0,
    };
    for pair in &classification.subsumptions {
        let (left, right) = (&pair[0], &pair[1]);
        let (lp, rp) = (
            left.starts_with(PROXY_IRI_PREFIX),
            right.starts_with(PROXY_IRI_PREFIX),
        );
        match (lp, rp) {
            (false, false) => {
                taxonomy.base_pairs += 1;
                taxonomy
                    .base_base
                    .entry(left.clone())
                    .or_default()
                    .insert(right.clone());
            }
            (false, true) => {
                taxonomy
                    .base_proxy
                    .entry(left.clone())
                    .or_default()
                    .insert(right.clone());
            }
            (true, true) => {
                taxonomy
                    .proxy_proxy
                    .entry(left.clone())
                    .or_default()
                    .insert(right.clone());
            }
            (true, false) => taxonomy.proxy_base += 1,
        }
    }
    taxonomy
}

impl Fragment {
    /// `P_F ⊑ P_G` for a mirror that is not classified exactly.
    ///
    /// The canonical model of `∃R.F` is the root plus the canonical model of
    /// `F` hanging off one `R` edge; premise
    /// [`Premise::NoMirrorRoleLeftExistential`] keeps the root free of any
    /// other structure. So the root satisfies `∃R.G` exactly when the edge
    /// itself lands in `G` (`F ⊑ G`, existential monotonicity) or, when `R` is
    /// transitive, when the edge composes with one inside `F`'s model
    /// (`F ⊑ ∃R.G`, i.e. `F ⊑ P_G`).
    fn derived_proxy_supers(
        &self,
        mirror: &Mirror,
        slice: &Taxonomy,
        unsat_proxy: &HashSet<usize>,
    ) -> BTreeSet<String> {
        let mut supers: BTreeSet<String> = BTreeSet::new();
        let add_filler = |filler: &ClassRef, supers: &mut BTreeSet<String>| {
            for &index in self.proxies_of_filler.get(filler).into_iter().flatten() {
                if unsat_proxy.contains(&index) {
                    continue;
                }
                let candidate = &self.mirrors[index];
                if candidate.role == mirror.role && candidate.proxy != mirror.proxy {
                    supers.insert(candidate.proxy.clone());
                }
            }
        };
        // Existential monotonicity over the exact filler taxonomy.
        add_filler(&mirror.filler, &mut supers);
        add_filler(&ClassRef::Top, &mut supers);
        if let ClassRef::Iri(filler) = &mirror.filler {
            for above in slice.base_base.get(filler).into_iter().flatten() {
                add_filler(&ClassRef::Iri(above.clone()), &mut supers);
            }
            // Role composition through the filler's own successors.
            if self.transitive_mirror_roles.contains(&mirror.role) {
                for proxy in slice.base_proxy.get(filler).into_iter().flatten() {
                    if proxy != &mirror.proxy {
                        supers.insert(proxy.clone());
                    }
                }
            }
        }
        supers
    }
}

/// Name the first exact disagreement between the base projection and the
/// neighbour slice over the base signature, or `None` when they agree. Both
/// the base pair relation and the unsatisfiable base classes must match
/// element for element; only proxy names may differ between the two.
fn base_disagreement(base: &Taxonomy, slice: &Taxonomy) -> Option<String> {
    for (subject, supers) in &base.base_base {
        match slice.base_base.get(subject) {
            None => return Some(format!("slice lost every super of {subject}")),
            Some(other) if other != supers => {
                let missing = supers.difference(other).next();
                let extra = other.difference(supers).next();
                return Some(match (missing, extra) {
                    (Some(m), _) => format!("slice lost {subject} ⊑ {m}"),
                    (None, Some(e)) => format!("slice invented {subject} ⊑ {e}"),
                    (None, None) => unreachable!("unequal sets differ somewhere"),
                });
            }
            Some(_) => {}
        }
    }
    for subject in slice.base_base.keys() {
        if !base.base_base.contains_key(subject) {
            return Some(format!("slice invented a base subject {subject}"));
        }
    }
    let base_unsat: BTreeSet<&String> = base
        .unsat
        .iter()
        .filter(|c| !c.starts_with(PROXY_IRI_PREFIX))
        .collect();
    let slice_unsat: BTreeSet<&String> = slice
        .unsat
        .iter()
        .filter(|c| !c.starts_with(PROXY_IRI_PREFIX))
        .collect();
    if base_unsat != slice_unsat {
        let missing = base_unsat.difference(&slice_unsat).next();
        let extra = slice_unsat.difference(&base_unsat).next();
        return Some(match (missing, extra) {
            (Some(m), _) => format!("slice lost unsatisfiable {m}"),
            (None, Some(e)) => format!("slice invented unsatisfiable {e}"),
            (None, None) => unreachable!("unequal sets differ somewhere"),
        });
    }
    None
}

/// Reconstruct the original public taxonomy from the two projection
/// classifications.
fn reconstruct(
    fragment: &Fragment,
    base: &Taxonomy,
    slice: &Taxonomy,
) -> Result<Classification, Premise> {
    if !base.consistent || !slice.consistent {
        return Err(Premise::ProjectionInconsistent);
    }
    // The base projection and the neighbour slice differ only by fresh
    // definitional names, so the slice is a conservative extension and the two
    // must agree on the base signature *exactly* — not merely in cardinality.
    // A disagreement means one of the two classifications lost or invented a
    // base consequence, and the reconstruction is built on both.
    if let Some(detail) = base_disagreement(base, slice) {
        return Err(Premise::BaseTaxonomyDisagreement(detail));
    }
    // A proxy can never fall below a base class under the certified premises;
    // seeing one means the premise did not hold of the classified projection.
    if slice.proxy_base != 0 {
        return Err(Premise::ZeroCrossTrigger(format!(
            "{} proxy-to-base edges in the projection",
            slice.proxy_base
        )));
    }
    for name in base.base_base.keys().chain(base.unsat.iter()) {
        if !fragment.declared.contains(name) {
            return Err(Premise::UnknownProjectedName(name.clone()));
        }
    }
    if !fragment.selected_proxies.is_empty()
        && !fragment
            .selected_proxies
            .iter()
            .any(|p| slice.proxy_proxy.contains_key(p))
    {
        return Err(Premise::SelectedProxiesNotClassified);
    }

    // `P_F ≡ ⊥` iff its filler is unsatisfiable (no other route to bottom
    // survives the premises), and then `N_F ≡ ⊤`. `P_F ≡ ⊤` is impossible: the
    // isolated element has no role edge, so it inhabits no proxy — hence no
    // negative is unsatisfiable.
    let mut unsat_proxy: HashSet<usize> = HashSet::new();
    let mut top_negatives: Vec<&str> = Vec::new();
    for (index, mirror) in fragment.mirrors.iter().enumerate() {
        let empty = match &mirror.filler {
            ClassRef::Bottom => true,
            ClassRef::Top => false,
            ClassRef::Iri(iri) => base.unsat.contains(iri),
        };
        if empty {
            unsat_proxy.insert(index);
            top_negatives.push(&mirror.negative);
        }
    }

    let satisfiable_base: Vec<&str> = fragment
        .base
        .iter()
        .filter(|c| !base.unsat.contains(*c))
        .map(String::as_str)
        .collect();

    let mut pairs: Vec<[String; 2]> = Vec::new();
    // base → base
    for (left, rights) in &base.base_base {
        if base.unsat.contains(left) {
            continue;
        }
        for right in rights {
            if !base.unsat.contains(right) {
                pairs.push([left.clone(), right.clone()]);
            }
        }
    }
    // negative → negative, by complement contravariance
    for (index, mirror) in fragment.mirrors.iter().enumerate() {
        if unsat_proxy.contains(&index) {
            continue;
        }
        let supers = if mirror.selected {
            slice
                .proxy_proxy
                .get(&mirror.proxy)
                .cloned()
                .unwrap_or_default()
        } else {
            fragment.derived_proxy_supers(mirror, slice, &unsat_proxy)
        };
        for proxy in &supers {
            let Some(negative) = fragment.negative_of_proxy.get(proxy) else {
                return Err(Premise::UnknownProjectedName(proxy.clone()));
            };
            if negative != &mirror.negative {
                pairs.push([negative.clone(), mirror.negative.clone()]);
            }
        }
    }
    // `N_F ≡ ⊤`: every satisfiable public class sits below it.
    for top in &top_negatives {
        for left in &satisfiable_base {
            pairs.push([(*left).to_string(), (*top).to_string()]);
        }
        for mirror in &fragment.mirrors {
            if mirror.negative != **top {
                pairs.push([mirror.negative.clone(), (*top).to_string()]);
            }
        }
    }

    pairs.sort();
    pairs.dedup();
    let mut unsatisfiable: Vec<String> = base
        .unsat
        .iter()
        .filter(|c| fragment.base.contains(*c))
        .cloned()
        .collect();
    unsatisfiable.sort();
    Ok(Classification {
        consistent: true,
        subsumptions: pairs,
        unsatisfiable,
        dropped: 0,
    })
}

// ---------------------------------------------------------------------------
// the route
// ---------------------------------------------------------------------------

thread_local! {
    /// The projections are classified through the ordinary pipeline, which
    /// re-enters this module; they carry no complement, but the guard makes the
    /// non-recursion structural rather than incidental.
    static ACTIVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Restores a `KM_*` key to its captured value on drop.
struct EnvVar(&'static str, Option<std::ffi::OsString>);

impl EnvVar {
    fn set(key: &'static str, value: &str) -> EnvVar {
        let previous = std::env::var_os(key);
        std::env::set_var(key, value);
        EnvVar(key, previous)
    }
}

impl Drop for EnvVar {
    fn drop(&mut self) {
        match self.1.take() {
            Some(value) => std::env::set_var(self.0, value),
            None => std::env::remove_var(self.0),
        }
    }
}

fn timing(message: std::fmt::Arguments<'_>) {
    if std::env::var_os("KM_TIMING").is_some() {
        eprintln!("KM_TIMING mirror-route: {message}");
    }
}

/// Try the certified mirror route. `Ok(None)` means the ontology is not in the
/// fragment (or the route is switched off) and the caller must classify it the
/// ordinary way.
///
/// Public so the route can be exercised on its own: the answer is the route's
/// verdict, not the reasoner's, and `None` distinguishes a refusal from an
/// answer in a way `classify` deliberately hides.
pub fn try_classify(cfg: &Config, ont: &Path) -> Result<Option<Classification>, OrchestrateError> {
    if std::env::var_os("KM_NO_MIRROR_ROUTE").is_some() {
        return Ok(None);
    }
    // Preserve the contract of explicitly selected atomic/diagnostic routes:
    // `KM_ROUTE=cb_plain16`, for example, must still mean that mechanism and
    // must not silently become this preprocessing route. The implicit route
    // and the default thread-count variants are the production classifier.
    if let Some(route) = std::env::var_os("KM_ROUTE") {
        if !matches!(
            route.to_str(),
            Some("auto" | "default" | "default8" | "default1")
        ) {
            return Ok(None);
        }
    }
    if ACTIVE.with(|a| a.get()) {
        return Ok(None);
    }
    let prepared = super::input::prepare(ont)?;
    let text = std::fs::read_to_string(prepared.path())?;
    let fragment = match detect(&text) {
        Ok(Some(fragment)) => fragment,
        Ok(None) => return Ok(None),
        Err(premise) => {
            timing(format_args!("declined: {premise}"));
            return Ok(None);
        }
    };
    timing(format_args!(
        "fragment: {} private mirrors over {} role(s), {} selected, {} base classes",
        fragment.mirrors.len(),
        fragment.mirror_roles.len(),
        fragment.selected_count(),
        fragment.base.len(),
    ));

    let base_path = TempPath::new(".mirror-base.ofn");
    let slice_path = TempPath::new(".mirror-slice.ofn");
    let retain_path = TempPath::new(".mirror-retain.txt");
    write_projections(&text, &fragment, base_path.path(), slice_path.path())?;
    {
        let mut retain = BufWriter::new(File::create(retain_path.path())?);
        for proxy in &fragment.selected_proxies {
            let internal = proxy.trim_start_matches(PROXY_IRI_PREFIX);
            writeln!(retain, "{PROXY_INTERNAL_PREFIX}{internal}")?;
        }
        retain.flush()?;
    }
    drop(text);

    let guard = ACTIVE.with(|a| {
        a.set(true);
        ActiveGuard
    });
    // The projections are ELI terminologies with a transitive mirror role, and
    // the reconstruction needs them classified EXACTLY: an existential
    // consequence reached through the mirror role's inverse (`X ⊑ ∃R.F` where
    // `F` is conjunction-defined through `R⁻`) is a real entailment that the
    // consequence-based arm does not derive. The Konclude bridge is the arm
    // that is complete on this fragment and answers-or-defers, so both
    // projections are routed to it and a defer is a refusal, not a fallback.
    let base = {
        let _route = EnvVar::set("KM_ROUTE", PROJECTION_ROUTE);
        super::classify(cfg, base_path.path())
    };
    let slice = {
        let _route = EnvVar::set("KM_ROUTE", PROJECTION_ROUTE);
        let _exclude = EnvVar::set("KM_QUERY_EXCLUDE_PREFIX", PROXY_INTERNAL_PREFIX);
        let _retain = EnvVar::set(
            "KM_QUERY_RETAIN_FILE",
            &retain_path.path().to_string_lossy(),
        );
        super::classify(cfg, slice_path.path())
    };
    drop(guard);
    let (base, slice) = match (base, slice) {
        (Ok(base), Ok(slice)) => (base, slice),
        (base, slice) => {
            let reason = base.err().or(slice.err());
            timing(format_args!(
                "declined: projection did not classify exactly: {}",
                reason
                    .map(|e| e.to_string())
                    .unwrap_or_else(|| "unknown".into())
            ));
            return Ok(None);
        }
    };
    timing(format_args!(
        "projections classified: base {} pairs, slice {} pairs",
        base.subsumptions.len(),
        slice.subsumptions.len()
    ));

    let base = index(&base);
    let slice = index(&slice);
    timing(format_args!(
        "base pairs {} / slice base pairs {}",
        base.base_pairs, slice.base_pairs
    ));
    match reconstruct(&fragment, &base, &slice) {
        Ok(classification) => {
            timing(format_args!(
                "reconstructed {} public pairs, {} unsatisfiable",
                classification.subsumptions.len(),
                classification.unsatisfiable.len()
            ));
            Ok(Some(classification))
        }
        Err(premise) => {
            timing(format_args!("declined after classification: {premise}"));
            Ok(None)
        }
    }
}

struct ActiveGuard;

impl Drop for ActiveGuard {
    fn drop(&mut self) {
        ACTIVE.with(|a| a.set(false));
    }
}

#[cfg(test)]
mod tests;
