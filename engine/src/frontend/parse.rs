//! Functional-syntax node -> SROIQ AST (`cls`, `role_cls`, `_dt_concept`,
//! `add_axiom`) plus the streaming document walk (`for_each_ontology_child`).
//!
//! Direct port of the corresponding `frontend.py` functions, reworked to
//! stream: each child of the top-level `Ontology(...)` node is parsed, handed
//! to the caller, and dropped, so the whole-document AST is never resident
//! (it used to be built in full AND deep-cloned for the rbox/declared scans,
//! which dominated peak memory on 500 MB ontologies).

use super::iri::{short_base, IriRegistry};
use super::sexpr::{Node, Parser};
use super::syntax::{mk_and, mk_or, Axiom, Concept, Ontology, Role, RuleAtom, RuleTerm};

/// Out-of-fragment marker (port of `OutOfFragment`).
#[derive(Debug)]
pub struct OutOfFragment(pub String);

/// Port of `role_str`: a *named* role -> short string.
fn role_str(reg: &mut IriRegistry, node: &Node) -> Result<String, OutOfFragment> {
    match node {
        Node::Atom(s) => Ok(reg.short(s)),
        _ => Err(OutOfFragment(format!("named role expected, got {:?}", node))),
    }
}

/// Port of `role_cls`: role expression for class constructs.
fn role_cls(reg: &mut IriRegistry, node: &Node) -> Result<Role, OutOfFragment> {
    match node {
        Node::Atom(s) => Ok(Role::Name(reg.short(s))),
        Node::List(head, args) if *head == "ObjectInverseOf" => {
            Ok(Role::Inverse(reg.short(args[0].as_atom().unwrap_or(""))))
        }
        Node::List(head, _) => Err(OutOfFragment(format!("role: {}", head))),
    }
}

/// The tokeniser ends a string token at its closing quote, so a typed or
/// language-tagged literal `"lex"^^dt` / `"lex"@lang` arrives as TWO sibling
/// atoms.  Re-glue them: returns the joined literal when `args[i]` is a
/// string atom whose successor is a `^^`/`@` suffix (and how many atoms were
/// consumed).
pub(super) fn glue_literal(args: &[&Node], i: usize) -> Option<(String, usize)> {
    let first = args.get(i)?.as_atom()?;
    if !first.starts_with('"') {
        return None;
    }
    if let Some(next) = args.get(i + 1).and_then(|n| n.as_atom()) {
        if next.starts_with("^^") || next.starts_with('@') {
            return Some((format!("{}{}", first, next), 2));
        }
    }
    Some((first.to_string(), 1))
}

/// Canonical text of a data-range node, used to key the abstraction concept
/// for complex ranges (facet restrictions, DataOneOf, …).  Adjacent
/// string-atom + `^^dt`/`@lang` pairs are re-glued into one literal token so
/// distinct typed literals stay distinct.
fn serialize_node(n: &Node) -> String {
    match n {
        Node::Atom(s) => (*s).to_string(),
        Node::List(h, args) => {
            let refs: Vec<&Node> = args.iter().collect();
            let mut out = String::from(*h);
            out.push('(');
            let mut i = 0;
            let mut first = true;
            while i < refs.len() {
                if !first {
                    out.push(' ');
                }
                first = false;
                if let Some((lit, used)) = glue_literal(&refs, i) {
                    out.push_str(&lit);
                    i += used;
                } else {
                    out.push_str(&serialize_node(refs[i]));
                    i += 1;
                }
            }
            out.push(')');
            out
        }
    }
}

/// Port of `_dt_concept`.  Complex ranges are keyed by their canonical text:
/// the old shared `__dt__opaque` name collapsed *different* facet
/// restrictions to one concept, which can invent subsumptions between their
/// consumers (the same hazard `dt_value_concept` fixed for literals).
/// Distinct ranges as distinct concepts can only lose an unsatisfiability,
/// never invent a subsumption.
fn dt_concept(node: &Node) -> Concept {
    match node {
        Node::Atom(s) => Concept::Name(format!("__dt__{}", short_base(s))),
        _ => Concept::Name(format!("__dt__c__{}", serialize_node(node))),
    }
}

/// `DataHasValue(p v)` ≡ ∃p.{v}: the filler MUST distinguish the literal value
/// `v`. Sharing one `__dt__val` concept across all values (the old behaviour)
/// collapses e.g. `Chinese ≡ ∃langCode."zh"` and `English ≡ ∃langCode."en"` to
/// the same concept, inventing the unsound subsumption Chinese ≡ English (seen
/// on ore_ont_13132 / 9881). Keying by the *glued* literal (lexical form plus
/// the `^^datatype`/`@lang` suffix the tokeniser splits off) keeps distinct
/// typed values distinct; the datatype-oracle pass then derives the genuine
/// equalities/memberships between them.
fn dt_value_concept(args: &[&Node], i: usize) -> Concept {
    match glue_literal(args, i) {
        Some((v, _)) => Concept::Name(format!("__dt__val__{}", v)),
        None => Concept::Name("__dt__val__opaque".to_string()),
    }
}

/// Port of `cls`.
fn cls(reg: &mut IriRegistry, node: &Node) -> Result<Concept, OutOfFragment> {
    match node {
        Node::Atom(s) => {
            let sh = reg.short(s);
            if sh == "owl:Thing" || sh == "Thing" {
                Ok(Concept::Top)
            } else if sh == "owl:Nothing" || sh == "Nothing" {
                Ok(Concept::Bottom)
            } else {
                Ok(Concept::Name(sh))
            }
        }
        Node::List(head, args) => match *head {
            "ObjectIntersectionOf" => {
                let mut cs = Vec::new();
                for a in args {
                    cs.push(cls(reg, a)?);
                }
                Ok(mk_and(cs))
            }
            "ObjectUnionOf" => {
                let mut cs = Vec::new();
                for a in args {
                    cs.push(cls(reg, a)?);
                }
                Ok(mk_or(cs))
            }
            "ObjectComplementOf" => Ok(Concept::Not(Box::new(cls(reg, &args[0])?))),
            "ObjectSomeValuesFrom" => Ok(Concept::Exists(
                role_cls(reg, &args[0])?,
                Box::new(cls(reg, &args[1])?),
            )),
            "ObjectAllValuesFrom" => Ok(Concept::Forall(
                role_cls(reg, &args[0])?,
                Box::new(cls(reg, &args[1])?),
            )),
            "ObjectMinCardinality" | "ObjectMaxCardinality" | "ObjectExactCardinality" => {
                let n: i64 = args[0]
                    .as_atom()
                    .and_then(|s| s.parse().ok())
                    .ok_or_else(|| OutOfFragment(format!("bad cardinality: {:?}", args[0])))?;
                let r = role_cls(reg, &args[1])?;
                let filler = if args.len() > 2 {
                    cls(reg, &args[2])?
                } else {
                    Concept::Top
                };
                match *head {
                    "ObjectMinCardinality" => Ok(Concept::AtLeast(n, r, Box::new(filler))),
                    "ObjectMaxCardinality" => Ok(Concept::AtMost(n, r, Box::new(filler))),
                    _ => Ok(mk_and([
                        Concept::AtLeast(n, r.clone(), Box::new(filler.clone())),
                        Concept::AtMost(n, r, Box::new(filler)),
                    ])),
                }
            }
            "ObjectOneOf" => {
                let noms: Vec<Concept> = args
                    .iter()
                    .map(|a| Concept::Nominal(reg.short(a.as_atom().unwrap_or(""))))
                    .collect();
                if noms.len() == 1 {
                    Ok(noms.into_iter().next().unwrap())
                } else {
                    Ok(mk_or(noms))
                }
            }
            "ObjectHasValue" => Ok(Concept::Exists(
                role_cls(reg, &args[0])?,
                Box::new(Concept::Nominal(reg.short(args[1].as_atom().unwrap_or("")))),
            )),
            "ObjectHasSelf" => Ok(Concept::HasSelf(role_cls(reg, &args[0])?)),
            "DataSomeValuesFrom" => Ok(Concept::Exists(
                Role::Name(reg.short(args[0].as_atom().unwrap_or(""))),
                Box::new(dt_concept(&args[1])),
            )),
            "DataAllValuesFrom" => Ok(Concept::Forall(
                Role::Name(reg.short(args[0].as_atom().unwrap_or(""))),
                Box::new(dt_concept(&args[1])),
            )),
            "DataHasValue" => {
                let refs: Vec<&Node> = args.iter().collect();
                Ok(Concept::Exists(
                    Role::Name(reg.short(args[0].as_atom().unwrap_or(""))),
                    Box::new(dt_value_concept(&refs, 1)),
                ))
            }
            "DataMinCardinality" | "DataMaxCardinality" | "DataExactCardinality" => {
                let n: i64 = args[0]
                    .as_atom()
                    .and_then(|s| s.parse().ok())
                    .ok_or_else(|| OutOfFragment(format!("bad cardinality: {:?}", args[0])))?;
                let r = Role::Name(reg.short(args[1].as_atom().unwrap_or("")));
                // Unqualified data cardinalities count ALL successors: the old
                // `__dt__val` filler only counted nodes carrying that one
                // concept, so e.g. `≤1 p` never clashed with two DataHasValue
                // successors (their classes are `__dt__val__<v>`, not
                // `__dt__val`).  `⊤` is the correct unqualified filler.
                let filler = if args.len() > 2 {
                    dt_concept(&args[2])
                } else {
                    Concept::Top
                };
                match *head {
                    "DataMinCardinality" => Ok(Concept::AtLeast(n, r, Box::new(filler))),
                    "DataMaxCardinality" => Ok(Concept::AtMost(n, r, Box::new(filler))),
                    _ => Ok(mk_and([
                        Concept::AtLeast(n, r.clone(), Box::new(filler.clone())),
                        Concept::AtMost(n, r, Box::new(filler)),
                    ])),
                }
            }
            other if other.starts_with("Data") => Err(OutOfFragment(format!(
                "datatype reasoning not supported: {}",
                other
            ))),
            other => Err(OutOfFragment(format!(
                "unsupported class construct: {}",
                other
            ))),
        },
    }
}

pub(super) fn strip_annotations<'a, 'n>(args: &'n [Node<'a>]) -> Vec<&'n Node<'a>> {
    args.iter()
        .filter(|a| a.head() != Some("Annotation"))
        .collect()
}

/// A SWRL rule term: `Variable(<iri>)` ⟶ a rule variable; a bare individual atom
/// ⟶ a named individual. Anything else (a nested expression) is unrepresentable.
fn parse_rule_term(reg: &mut IriRegistry, node: &Node) -> Option<RuleTerm> {
    match node {
        Node::List(h, a) if *h == "Variable" => Some(RuleTerm::Var(reg.short(a.first()?.as_atom()?))),
        Node::Atom(s) => Some(RuleTerm::Ind(reg.short(s))),
        _ => None,
    }
}

/// Parse a `Body(...)` / `Head(...)` node into rule atoms. Returns `None` if any
/// atom is of a kind we do not represent (datatype/builtin/data-range atom) or is
/// malformed — the caller then drops the whole rule (sound: a dropped constraint
/// can lose an inconsistency, never invent one).
fn parse_rule_atoms(reg: &mut IriRegistry, node: &Node) -> Option<Vec<RuleAtom>> {
    let args = match node {
        Node::List(_, a) => a,
        _ => return None,
    };
    let mut out = Vec::new();
    for atom in args.iter().filter(|a| a.head() != Some("Annotation")) {
        let (h, aa) = match atom {
            Node::List(h, aa) => (*h, aa),
            _ => return None,
        };
        match h {
            "ClassAtom" => out.push(RuleAtom::Class(
                cls(reg, aa.first()?).ok()?,
                parse_rule_term(reg, aa.get(1)?)?,
            )),
            "ObjectPropertyAtom" => out.push(RuleAtom::Role(
                role_str(reg, aa.first()?).ok()?,
                parse_rule_term(reg, aa.get(1)?)?,
                parse_rule_term(reg, aa.get(2)?)?,
            )),
            "DifferentIndividualsAtom" => out.push(RuleAtom::Diff(
                parse_rule_term(reg, aa.first()?)?,
                parse_rule_term(reg, aa.get(1)?)?,
            )),
            "SameIndividualAtom" => out.push(RuleAtom::Same(
                parse_rule_term(reg, aa.first()?)?,
                parse_rule_term(reg, aa.get(1)?)?,
            )),
            // DataPropertyAtom / BuiltInAtom / DataRangeAtom: drop the whole rule.
            _ => return None,
        }
    }
    Some(out)
}

/// Port of `add_axiom`.
fn add_axiom(reg: &mut IriRegistry, o: &mut Ontology, node: &Node) -> Result<(), OutOfFragment> {
    let (head, args) = match node {
        Node::List(h, a) => (*h, a),
        Node::Atom(_) => return Ok(()),
    };
    let args = strip_annotations(args);
    match head {
        "SubClassOf" => {
            o.add(Axiom::SubClassOf(cls(reg, args[0])?, cls(reg, args[1])?));
        }
        "EquivalentClasses" => {
            let mut cs = Vec::new();
            for a in &args {
                cs.push(cls(reg, a)?);
            }
            for k in 0..cs.len().saturating_sub(1) {
                o.add(Axiom::EquivalentClasses(cs[k].clone(), cs[k + 1].clone()));
            }
        }
        "DisjointClasses" => {
            let mut cs = Vec::new();
            for a in &args {
                cs.push(cls(reg, a)?);
            }
            for k in 0..cs.len() {
                for l in (k + 1)..cs.len() {
                    o.add(Axiom::DisjointClasses(cs[k].clone(), cs[l].clone()));
                }
            }
        }
        "SubObjectPropertyOf" => {
            let sub = args[0];
            if let Node::List(h, chain_args) = sub {
                if *h == "ObjectPropertyChain" {
                    let mut chain = Vec::new();
                    for r in chain_args {
                        chain.push(role_str(reg, r)?);
                    }
                    o.add(Axiom::RoleChain(chain, role_str(reg, args[1])?));
                    return Ok(());
                }
            }
            o.add(Axiom::RoleInclusion(
                role_str(reg, sub)?,
                role_str(reg, args[1])?,
            ));
        }
        "EquivalentObjectProperties" => {
            // R1 ≡ ... ≡ Rn  ⟹  pairwise Ri ⊑ Rj and Rj ⊑ Ri. Mirrors the
            // SubObjectPropertyOf convention (role_str handles inverses).
            let mut rs = Vec::new();
            for a in &args {
                rs.push(role_str(reg, a)?);
            }
            for k in 0..rs.len() {
                for l in (k + 1)..rs.len() {
                    o.add(Axiom::RoleInclusion(rs[k].clone(), rs[l].clone()));
                    o.add(Axiom::RoleInclusion(rs[l].clone(), rs[k].clone()));
                }
            }
        }
        "InverseObjectProperties" => {
            o.add(Axiom::InverseRoles(
                role_str(reg, args[0])?,
                role_str(reg, args[1])?,
            ));
        }
        "TransitiveObjectProperty" => o.add(Axiom::TransitiveRole(role_str(reg, args[0])?)),
        "SymmetricObjectProperty" => o.add(Axiom::SymmetricRole(role_str(reg, args[0])?)),
        "ReflexiveObjectProperty" => o.add(Axiom::ReflexiveRole(role_str(reg, args[0])?)),
        "FunctionalObjectProperty" => o.add(Axiom::FunctionalRole(role_str(reg, args[0])?)),
        "InverseFunctionalObjectProperty" => {
            o.add(Axiom::InverseFunctionalRole(role_str(reg, args[0])?))
        }
        "AsymmetricObjectProperty" => o.add(Axiom::AsymmetricRole(role_str(reg, args[0])?)),
        "IrreflexiveObjectProperty" => o.add(Axiom::IrreflexiveRole(role_str(reg, args[0])?)),
        "ClassAssertion" => {
            o.add(Axiom::ConceptAssertion(
                cls(reg, args[0])?,
                reg.short(args[1].as_atom().unwrap_or("")),
            ));
        }
        "ObjectPropertyAssertion" => {
            o.add(Axiom::RoleAssertion(
                role_str(reg, args[0])?,
                reg.short(args[1].as_atom().unwrap_or("")),
                reg.short(args[2].as_atom().unwrap_or("")),
            ));
        }
        "SameIndividual" => {
            let ids: Vec<String> = args
                .iter()
                .map(|a| reg.short(a.as_atom().unwrap_or("")))
                .collect();
            for k in 0..ids.len().saturating_sub(1) {
                o.add(Axiom::SameIndividual(ids[k].clone(), ids[k + 1].clone()));
            }
        }
        "DifferentIndividuals" => {
            let ids: Vec<String> = args
                .iter()
                .map(|a| reg.short(a.as_atom().unwrap_or("")))
                .collect();
            for k in 0..ids.len() {
                for l in (k + 1)..ids.len() {
                    o.add(Axiom::DifferentIndividuals(ids[k].clone(), ids[l].clone()));
                }
            }
        }
        "DLSafeRule" => {
            // DLSafeRule(Body(...) Head(...)). DL-safe: variables range only over
            // named individuals. A rule with any atom we cannot represent
            // (datatype/builtin) is dropped wholesale (sound — see parse_rule_atoms).
            let body = args.iter().find(|a| a.head() == Some("Body"));
            let head_n = args.iter().find(|a| a.head() == Some("Head"));
            if let (Some(b), Some(hd)) = (body, head_n) {
                if let (Some(bvec), Some(hvec)) =
                    (parse_rule_atoms(reg, b), parse_rule_atoms(reg, hd))
                {
                    if !hvec.is_empty() {
                        o.add(Axiom::Rule(bvec, hvec));
                    }
                }
            }
        }
        "DataPropertyDomain" => {
            // domain(p) = C ≡ ∃p.⊤ ⊑ C
            o.add(Axiom::SubClassOf(
                Concept::Exists(
                    Role::Name(reg.short(args[0].as_atom().unwrap_or(""))),
                    Box::new(Concept::Top),
                ),
                cls(reg, args[1])?,
            ));
        }
        "ObjectPropertyDomain"
            if matches!(args.first(), Some(Node::Atom(_)))
                && matches!(args.get(1), Some(Node::List(..))) =>
        {
            // domain(R) = C ≡ ∃R.⊤ ⊑ C. The simple (named-class) case stays on
            // the rbox path (byte-identical routing/clauses); only a COMPLEX
            // domain class on a NAMED role — previously dropped as
            // `complex-domain`, a real incompleteness (ore_ont_4827's
            // `domain(hasCase) = Adjective ⊔ ...`) — is clausified here through
            // the normal subclass encoding.
            o.add(Axiom::SubClassOf(
                Concept::Exists(role_cls(reg, args[0])?, Box::new(Concept::Top)),
                cls(reg, args[1])?,
            ));
        }
        "ObjectPropertyRange"
            if matches!(args.first(), Some(Node::Atom(_)))
                && matches!(args.get(1), Some(Node::List(..))) =>
        {
            // range(R) = C ≡ ⊤ ⊑ ∀R.C; complex-range case on a named role only.
            o.add(Axiom::SubClassOf(
                Concept::Top,
                Concept::Forall(role_cls(reg, args[0])?, Box::new(cls(reg, args[1])?)),
            ));
        }
        "Declaration" | "Prefix" | "Import" | "Annotation" | "AnnotationAssertion"
        | "DisjointObjectProperties" | "ObjectPropertyDomain" | "ObjectPropertyRange" => {
            // not part of the SROIQ core we validate here
        }
        // Data property axioms: data properties are abstracted as roles whose
        // fillers are data-node concepts (`__dt__…`), so the standard role
        // machinery captures their OWL semantics.  These were previously
        // dropped wholesale — a real incompleteness: ore_ont_6999's
        // `Distortion_Type_Affine ⊑ =2 affc2` with `Functional(affc2)` is
        // unsatisfiable, which the dropped functionality silently missed.
        "FunctionalDataProperty" => {
            o.add(Axiom::FunctionalRole(reg.short(args[0].as_atom().unwrap_or(""))));
        }
        "SubDataPropertyOf" => {
            o.add(Axiom::RoleInclusion(
                reg.short(args[0].as_atom().unwrap_or("")),
                reg.short(args[1].as_atom().unwrap_or("")),
            ));
        }
        "EquivalentDataProperties" => {
            let ps: Vec<String> = args
                .iter()
                .map(|a| reg.short(a.as_atom().unwrap_or("")))
                .collect();
            for i in 0..ps.len() {
                for j in (i + 1)..ps.len() {
                    o.add(Axiom::RoleInclusion(ps[i].clone(), ps[j].clone()));
                    o.add(Axiom::RoleInclusion(ps[j].clone(), ps[i].clone()));
                }
            }
        }
        "DisjointDataProperties" => {
            let ps: Vec<String> = args
                .iter()
                .map(|a| reg.short(a.as_atom().unwrap_or("")))
                .collect();
            for i in 0..ps.len() {
                for j in (i + 1)..ps.len() {
                    o.add(Axiom::DisjointRoles(ps[i].clone(), ps[j].clone()));
                }
            }
        }
        "DataPropertyRange" => {
            // range(p) = D ≡ ⊤ ⊑ ∀p.D over the range's abstraction concept.
            // (data_range.rs separately derives the empty-range constraints;
            // DataPropertyDomain already has its own arm above.)
            o.add(Axiom::SubClassOf(
                Concept::Top,
                Concept::Forall(
                    Role::Name(reg.short(args[0].as_atom().unwrap_or(""))),
                    Box::new(dt_concept(args[1])),
                ),
            ));
        }
        "DatatypeDefinition" => {
            o.add(Axiom::EquivalentClasses(dt_concept(args[0]), dt_concept(args[1])));
        }
        other if other.starts_with("Data") || other == "HasKey" => {
            // remaining datatype axioms (negative assertions, keys): sound to
            // drop — they only constrain named individuals, so dropping can
            // lose an inconsistency, never invent a consequence
        }
        _ => {
            // anything else: silently skipped
        }
    }
    Ok(())
}

/// Stream the children of every top-level `Ontology(...)` node: each child is
/// parsed, handed to `f`, and dropped, so peak memory is one axiom subtree
/// instead of the whole document AST. Non-`Ontology` top-level nodes
/// (`Prefix(...)` etc.) are parsed with the same strictness and discarded.
///
/// (A valid OFN document has exactly one `Ontology(...)` node; like the old
/// whole-tree parser this walks all of them.)
pub fn for_each_ontology_child<'a, F>(text: &'a str, mut f: F) -> Result<(), OutOfFragment>
where
    F: FnMut(&Node<'a>) -> Result<(), OutOfFragment>,
{
    let perr = |e: String| OutOfFragment(format!("parse error: {}", e));
    let mut p = Parser::new(text);
    while p.peek().is_some() {
        let t = p.next_tok().unwrap();
        if t == "(" {
            return Err(perr("unexpected (".to_string()));
        }
        if p.peek() == Some("(") {
            p.next_tok(); // consume '('
            let streamed = t == "Ontology";
            while p.peek() != Some(")") {
                if p.peek().is_none() {
                    return Err(perr("unexpected end of input".to_string()));
                }
                let node = p.parse().map_err(perr)?;
                if streamed {
                    f(&node)?;
                }
            }
            p.next_tok(); // consume ')'
        }
        // bare atom at top level: ignored (matches the old parser, which built
        // a Node::Atom and skipped it)
    }
    Ok(())
}

/// Port of `parse_ontology`'s axiom pass: build the SROIQ `Ontology` by
/// streaming over the document.
pub fn parse_axioms(reg: &mut IriRegistry, text: &str) -> Result<Ontology, OutOfFragment> {
    let mut o = Ontology::new();
    for_each_ontology_child(text, |node| add_axiom(reg, &mut o, node))?;
    Ok(o)
}

/// If `node` is `Declaration(Class(<name>))`, return the raw class token.
/// (Port of the match inside `declared_classes`; the `reg.short` call is
/// deferred to the caller so the registry call order — all rbox shorts, then
/// all declared shorts — matches the old two-sweep code exactly.)
pub fn declared_class_node<'a>(node: &Node<'a>) -> Option<&'a str> {
    if let Node::List(h, args) = node {
        if *h == "Declaration" && !args.is_empty() {
            if let Node::List(ch, cargs) = &args[0] {
                if *ch == "Class" && !cargs.is_empty() {
                    return cargs[0].as_atom();
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod rule_tests {
    use super::*;
    use crate::frontend::syntax::{Axiom, RuleAtom, RuleTerm};

    #[test]
    fn dlsafe_star_rule_parses() {
        // the ore_ont_2669 shape: br has two predecessors op1,op2 (not tree-shaped)
        let txt = "Ontology(\
DLSafeRule(Body(\
ClassAtom(<http://e#C> Variable(<http://e#op1>)) \
ClassAtom(<http://e#C> Variable(<http://e#op2>)) \
ClassAtom(<http://e#D> Variable(<http://e#br>)) \
ObjectPropertyAtom(<http://e#isPartOf> Variable(<http://e#op1>) Variable(<http://e#br>)) \
ObjectPropertyAtom(<http://e#isPartOf> Variable(<http://e#op2>) Variable(<http://e#br>)) \
DifferentIndividualsAtom(Variable(<http://e#op1>) Variable(<http://e#op2>)))\
Head(ObjectPropertyAtom(<http://e#inv> Variable(<http://e#op1>) Variable(<http://e#op2>)))))";
        let mut reg = IriRegistry::new();
        let o = parse_axioms(&mut reg, txt).expect("parse");
        let rules: Vec<&Axiom> = o.rules().collect();
        assert_eq!(rules.len(), 1, "exactly one rule parsed");
        match rules[0] {
            Axiom::Rule(body, head) => {
                assert_eq!(body.len(), 6, "5 atoms + 1 diff guard");
                assert_eq!(head.len(), 1);
                assert!(body.iter().any(|a| matches!(a, RuleAtom::Diff(..))), "diff guard kept");
                assert!(matches!(&head[0], RuleAtom::Role(_, RuleTerm::Var(_), RuleTerm::Var(_))));
            }
            _ => panic!("not a rule"),
        }
    }

    #[test]
    fn dlsafe_rule_with_builtin_atom_is_dropped() {
        // soundness: a rule with an unrepresentable atom is dropped wholesale
        let txt = "Ontology(\
DLSafeRule(Body(\
ClassAtom(<http://e#C> Variable(<http://e#x>)) \
BuiltInAtom(<http://e#gt> Variable(<http://e#x>) \"5\"))\
Head(ClassAtom(<http://e#D> Variable(<http://e#x>)))))";
        let mut reg = IriRegistry::new();
        let o = parse_axioms(&mut reg, txt).expect("parse");
        assert_eq!(o.rules().count(), 0, "rule with builtin atom dropped");
    }
}
