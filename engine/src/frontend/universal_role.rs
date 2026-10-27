//! Exact source rewrite of universal-role restrictions.
//!
//! `owl:topObjectProperty` (written `U` below) is interpreted as `ΔI × ΔI` in
//! every OWL 2 interpretation. KM has no universal-role object: the parser
//! maps the builtin to an ordinary named role, so `∃U.C` was clausified as an
//! ordinary existential and `∀U.C` as an ordinary universal. That is
//! incomplete (nothing makes every element a `U`-neighbour of every other,
//! so `A ⊑ F`, `F ⊑ ∀U.B` did not give `A ⊑ B`), and the ordinary
//! existential spawned role edges and successor contexts that made several
//! small inputs run for minutes.
//!
//! This pass rewrites the source, before profiling and routing, when every
//! logical occurrence of `U` (or `U⁻ = U`) is the role of an
//! `ObjectSomeValuesFrom`, `ObjectAllValuesFrom` or `ObjectHasValue`
//! restriction, the property of an `ObjectPropertyDomain` or
//! `ObjectPropertyRange` axiom, or the super-role of a (tautological)
//! `SubObjectPropertyOf(R U)`. Any other occurrence (a sub-role or chain
//! position, an assertion, a characteristic) leaves the source
//! byte-identical. Cardinalities and self restrictions on `U` are not OWL 2 DL.
//!
//! ## Rewrites
//!
//! Constant cases, exact in every interpretation because `ΔI` is non-empty:
//!
//! * `∃U.⊤ ≡ ⊤`, `∀U.⊤ ≡ ⊤`, `∃U.{a…} ≡ ⊤`, `U hasValue a ≡ ⊤`;
//! * `∃U.⊥ ≡ ⊥`, `∀U.⊥ ≡ ⊥`;
//! * `ObjectPropertyDomain(U C)` and `ObjectPropertyRange(U C)` are both
//!   `⊤ ⊑ C` (every element is its own U-successor and U-predecessor).
//!
//! General case, through a fresh hub individual `g` and a fresh role `S`
//! with the added axiom `⊤ ⊑ ∃S.{g}`:
//!
//! * `∃U.C  ↦  ∃S.({g} ⊓ ∃S⁻.C)`
//! * `∀U.C  ↦  ∀S.∀S⁻.C`
//!
//! Soundness and completeness: let `O'` be the rewritten ontology.
//!
//! 1. In every model `J` of `O'`, every element has an `S`-edge to `g`, so
//!    `(∃S.({g} ⊓ ∃S⁻.C))^J = ΔJ` iff some element is in `C^J`, and `∅`
//!    otherwise; that is exactly `(∃U.C)^J`. Likewise `(∀S.∀S⁻.C)^J` is `ΔJ`
//!    iff every element is in `C^J` (each one is an `S⁻`-successor of the
//!    `S`-successor `g`) and `∅` otherwise, i.e. `(∀U.C)^J`. By induction
//!    over the expression, every rewritten class expression has the same
//!    extension as its original, so `J` is a model of `O`.
//! 2. Every model `I` of `O` extends to a model of `O'` by choosing any
//!    `g^I ∈ ΔI` and `S^I = ΔI × {g^I}`: the hub axiom holds and, by 1, every
//!    rewritten expression keeps its extension.
//!
//! `S` and `g` are fresh, so `O'` is a conservative extension of `O`: the
//! two have the same consistency, the same entailed subsumptions and the
//! same unsatisfiable classes over the original signature. The rewrite is
//! polarity-independent, so it also holds inside equivalences, negations and
//! rule class atoms. No calculus changes: the rewritten source uses only a
//! nominal and an inverse role, which the routes for nominal ontologies
//! already handle, and the router sees them through the ordinary source
//! profile.

use std::borrow::Cow;

use super::sexpr::{tokens, Node, Parser};

/// Namespace of the generated hub symbols. A source that mentions it anywhere
/// is left unchanged, so the generated names can never alias a source entity.
const HUB_NAMESPACE: &str = "urn:km:internal:universal-role";
const HUB_ROLE: &str = "<urn:km:internal:universal-role#link>";
const HUB_INDIVIDUAL: &str = "<urn:km:internal:universal-role#hub>";
const THING: &str = "<http://www.w3.org/2002/07/owl#Thing>";
const NOTHING: &str = "<http://www.w3.org/2002/07/owl#Nothing>";

fn is_universal_role(token: &str) -> bool {
    matches!(
        token,
        "owl:topObjectProperty" | "<http://www.w3.org/2002/07/owl#topObjectProperty>"
    )
}

/// `U` or `ObjectInverseOf(U)`; the universal role is its own inverse.
fn is_universal_role_expression(node: &Node<'_>) -> bool {
    match node {
        Node::Atom(token) => is_universal_role(token),
        Node::List("ObjectInverseOf", args) => {
            matches!(args.as_slice(), [Node::Atom(token)] if is_universal_role(token))
        }
        Node::List(_, _) => false,
    }
}

fn is_thing(token: &str) -> bool {
    matches!(token, "owl:Thing" | "<http://www.w3.org/2002/07/owl#Thing>")
}

fn is_nothing(token: &str) -> bool {
    matches!(token, "owl:Nothing" | "<http://www.w3.org/2002/07/owl#Nothing>")
}

fn is_annotation_node(head: &str) -> bool {
    matches!(
        head,
        "Annotation"
            | "AnnotationAssertion"
            | "SubAnnotationPropertyOf"
            | "AnnotationPropertyDomain"
            | "AnnotationPropertyRange"
    )
}

struct Rewriter<'a> {
    text: &'a str,
    edits: Vec<(usize, usize, Cow<'static, str>)>,
    needs_hub: bool,
    blocked: bool,
}

impl<'a> Rewriter<'a> {
    fn offset(&self, token: &str) -> Result<usize, String> {
        let start = (token.as_ptr() as usize)
            .checked_sub(self.text.as_ptr() as usize)
            .ok_or("universal-role rewrite: foreign token")?;
        if self.text.get(start..start + token.len()) != Some(token) {
            return Err("universal-role rewrite: invalid token range".into());
        }
        Ok(start)
    }

    /// Byte offset of the first byte of `node`.
    fn start(&self, node: &Node<'a>) -> Result<usize, String> {
        match node {
            Node::Atom(token) | Node::List(token, _) if !token.is_empty() => self.offset(token),
            _ => Err("universal-role rewrite: anonymous list".into()),
        }
    }

    /// Byte offset just past `node`.
    fn end(&self, node: &Node<'a>) -> Result<usize, String> {
        match node {
            Node::Atom(token) => Ok(self.offset(token)? + token.len()),
            Node::List(_, _) => Ok(self.close(node)? + 1),
        }
    }

    /// Byte offset of the `)` closing a list node with at least one child.
    fn close(&self, node: &Node<'a>) -> Result<usize, String> {
        let Node::List(_, args) = node else {
            return Err("universal-role rewrite: atom has no closing parenthesis".into());
        };
        let last = args.last().ok_or("universal-role rewrite: empty list")?;
        let after = self.end(last)?;
        match tokens(&self.text[after..]).next() {
            // The token borrows from `text`, so its offset is exact.
            Some(token) if token == ")" => self.offset(token),
            _ => Err("universal-role rewrite: unbalanced list".into()),
        }
    }

    fn visit(&mut self, node: &Node<'a>) -> Result<(), String> {
        if self.blocked {
            return Ok(());
        }
        match node {
            Node::Atom(token) => {
                if is_universal_role(token) {
                    self.blocked = true;
                }
            }
            Node::List(head, _) if *head == "Declaration" || is_annotation_node(head) => {}
            Node::List("SubObjectPropertyOf", args) => {
                let logical: Vec<&Node<'a>> = args
                    .iter()
                    .filter(|arg| arg.head() != Some("Annotation"))
                    .collect();
                match logical.as_slice() {
                    // `R ⊑ U` is a tautology; the top-role elision removes it.
                    [sub, Node::Atom(sup)] if is_universal_role(sup) => self.visit(sub)?,
                    _ => {
                        for arg in logical {
                            self.visit(arg)?;
                        }
                    }
                }
            }
            Node::List(head @ ("ObjectSomeValuesFrom" | "ObjectAllValuesFrom"), args)
                if matches!(args.as_slice(), [role, _] if is_universal_role_expression(role)) =>
            {
                self.restriction(node, head == &"ObjectSomeValuesFrom", &args[0], &args[1])?;
            }
            Node::List("ObjectHasValue", args)
                if matches!(args.as_slice(), [role, _] if is_universal_role_expression(role)) =>
            {
                // `U hasValue a ≡ ⊤`: every element is U-related to `a`.
                self.replace(node, THING)?;
            }
            Node::List(head @ ("ObjectPropertyDomain" | "ObjectPropertyRange"), args) => {
                let logical: Vec<&Node<'a>> = args
                    .iter()
                    .filter(|arg| arg.head() != Some("Annotation"))
                    .collect();
                match logical.as_slice() {
                    // Every element has a U-successor and a U-predecessor
                    // (itself), so both axioms say `⊤ ⊑ C`.
                    [role, class] if is_universal_role_expression(role) => {
                        let head_start = self.offset(head)?;
                        self.edits.push((head_start, head_start + head.len(), Cow::Borrowed("SubClassOf")));
                        let role_start = self.start(role)?;
                        let role_end = self.end(role)?;
                        self.edits.push((role_start, role_end, Cow::Borrowed(THING)));
                        self.visit(class)?;
                    }
                    _ => {
                        for arg in logical {
                            self.visit(arg)?;
                        }
                    }
                }
            }
            Node::List(_, args) => {
                for arg in args {
                    self.visit(arg)?;
                }
            }
        }
        Ok(())
    }

    fn replace(&mut self, node: &Node<'a>, with: &'static str) -> Result<(), String> {
        let Node::List(head, _) = node else {
            return Err("universal-role rewrite: replace expects a list".into());
        };
        let start = self.offset(head)?;
        let end = self.close(node)? + 1;
        self.edits.push((start, end, Cow::Borrowed(with)));
        Ok(())
    }

    fn restriction(
        &mut self,
        node: &Node<'a>,
        existential: bool,
        role: &Node<'a>,
        filler: &Node<'a>,
    ) -> Result<(), String> {
        let constant = match filler {
            Node::Atom(name) if is_thing(name) => Some(THING),
            Node::Atom(name) if is_nothing(name) => Some(NOTHING),
            Node::List("ObjectOneOf", members) if existential && !members.is_empty() => Some(THING),
            _ => None,
        };
        if let Some(constant) = constant {
            return self.replace(node, constant);
        }
        let Node::List(head, _) = node else { unreachable!() };
        let start = self.offset(head)?;
        let role_end = self.end(role)?;
        let close = self.close(node)?;
        let (prefix, suffix) = if existential {
            (
                format!(
                    "ObjectSomeValuesFrom({HUB_ROLE} ObjectIntersectionOf(ObjectOneOf({HUB_INDIVIDUAL}) \
                     ObjectSomeValuesFrom(ObjectInverseOf({HUB_ROLE})"
                ),
                "))",
            )
        } else {
            (
                format!("ObjectAllValuesFrom({HUB_ROLE} ObjectAllValuesFrom(ObjectInverseOf({HUB_ROLE})"),
                ")",
            )
        };
        self.edits.push((start, role_end, Cow::Owned(prefix)));
        self.edits.push((close, close, Cow::Borrowed(suffix)));
        self.needs_hub = true;
        self.visit(filler)
    }
}

/// Rewrite universal-role restrictions (see the module documentation).
///
/// Returns the borrowed source when it has no rewritable restriction or when
/// any occurrence of the builtin lies outside the admitted positions. The
/// source must already be validated and have canonical builtin spellings
/// (`builtin_aliases::canonicalize`).
pub fn encode(text: &str) -> Result<Cow<'_, str>, String> {
    if !text.contains("topObjectProperty") || text.contains(HUB_NAMESPACE) {
        return Ok(Cow::Borrowed(text));
    }
    let mut parser = Parser::new(text);
    while parser.peek() == Some("Prefix") {
        parser.parse()?;
    }
    if parser.next_tok() != Some("Ontology") || parser.next_tok() != Some("(") {
        return Ok(Cow::Borrowed(text));
    }
    let mut rewriter = Rewriter { text, edits: Vec::new(), needs_hub: false, blocked: false };
    let close = loop {
        match parser.peek() {
            None => return Err("universal-role rewrite: unterminated Ontology".into()),
            Some(")") => {
                let token = parser.next_tok().unwrap_or(")");
                break rewriter.offset(token)?;
            }
            Some(_) => {
                // Bare ontology and version IRIs are not logical occurrences.
                if let node @ Node::List(_, _) = parser.parse()? {
                    rewriter.visit(&node)?;
                }
            }
        }
    };
    if rewriter.blocked || rewriter.edits.is_empty() {
        return Ok(Cow::Borrowed(text));
    }
    if rewriter.needs_hub {
        rewriter.edits.push((
            close,
            close,
            Cow::Owned(format!(
                " Declaration(ObjectProperty({HUB_ROLE})) Declaration(NamedIndividual({HUB_INDIVIDUAL})) \
                 SubClassOf({THING} ObjectHasValue({HUB_ROLE} {HUB_INDIVIDUAL}))\n"
            )),
        ));
    }
    let mut edits = rewriter.edits;
    edits.sort_by_key(|(start, end, _)| (*start, *end));
    let mut out = String::with_capacity(text.len() + 256 * edits.len());
    let mut copied = 0;
    for (start, end, replacement) in edits {
        if start < copied {
            return Err("universal-role rewrite: overlapping edits".into());
        }
        out.push_str(&text[copied..start]);
        out.push_str(&replacement);
        copied = end;
    }
    out.push_str(&text[copied..]);
    Ok(Cow::Owned(out))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rewritten(body: &str) -> String {
        let source = format!("Prefix(:=<urn:t#>) Ontology({body})");
        encode(&source).unwrap().into_owned()
    }

    #[test]
    fn constant_restrictions_fold_without_a_hub() {
        let out = rewritten("SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty owl:Thing)) \
            SubClassOf(:B ObjectAllValuesFrom(owl:topObjectProperty owl:Nothing)) \
            SubClassOf(:C ObjectHasValue(owl:topObjectProperty :a)) \
            SubClassOf(:D ObjectSomeValuesFrom(owl:topObjectProperty ObjectOneOf(:a)))");
        assert!(!out.contains("topObjectProperty"), "{out}");
        assert!(!out.contains(HUB_NAMESPACE), "{out}");
        assert!(out.contains(&format!("SubClassOf(:A {THING})")), "{out}");
        assert!(out.contains(&format!("SubClassOf(:B {NOTHING})")), "{out}");
        assert!(out.contains(&format!("SubClassOf(:C {THING})")), "{out}");
        assert!(out.contains(&format!("SubClassOf(:D {THING})")), "{out}");
    }

    #[test]
    fn general_restrictions_use_the_hub_and_nest() {
        let out = rewritten("EquivalentClasses(:T ObjectSomeValuesFrom(owl:topObjectProperty \
            ObjectIntersectionOf(:F ObjectAllValuesFrom(owl:topObjectProperty :G))))");
        assert!(!out.contains("topObjectProperty"), "{out}");
        let expected = format!(
            "EquivalentClasses(:T ObjectSomeValuesFrom({HUB_ROLE} ObjectIntersectionOf(ObjectOneOf({HUB_INDIVIDUAL}) \
             ObjectSomeValuesFrom(ObjectInverseOf({HUB_ROLE}) ObjectIntersectionOf(:F \
             ObjectAllValuesFrom({HUB_ROLE} ObjectAllValuesFrom(ObjectInverseOf({HUB_ROLE}) :G)))))))"
        );
        assert!(out.contains(&expected), "{out}\n{expected}");
        assert!(out.contains(&format!("SubClassOf({THING} ObjectHasValue({HUB_ROLE} {HUB_INDIVIDUAL}))")));
        // The output parses as one balanced ontology and is a fixpoint.
        let mut parser = Parser::new(&out);
        parser.parse().unwrap();
        let node = parser.parse().unwrap();
        assert_eq!(node.head(), Some("Ontology"));
        assert!(parser.peek().is_none());
        assert!(matches!(encode(&out).unwrap(), Cow::Borrowed(_)));
    }

    #[test]
    fn other_occurrences_leave_the_source_unchanged() {
        for body in [
            "SubObjectPropertyOf(owl:topObjectProperty :r) SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :B))",
            "SubObjectPropertyOf(ObjectPropertyChain(:r owl:topObjectProperty) :s) SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :B))",
            "SubClassOf(:A ObjectMinCardinality(2 owl:topObjectProperty :B))",
            "TransitiveObjectProperty(owl:topObjectProperty) SubClassOf(:A ObjectSomeValuesFrom(owl:topObjectProperty :B))",
            "ObjectPropertyAssertion(owl:topObjectProperty :a :b) SubClassOf(:A ObjectAllValuesFrom(owl:topObjectProperty :B))",
            "SubClassOf(:A ObjectSomeValuesFrom(:r :B))",
        ] {
            let source = format!("Prefix(:=<urn:t#>) Ontology({body})");
            assert!(matches!(encode(&source).unwrap(), Cow::Borrowed(_)), "{body}");
        }
    }

    #[test]
    fn inverse_universal_role_and_domain_range_axioms_are_encoded() {
        let out = rewritten("SubClassOf(:A ObjectSomeValuesFrom(ObjectInverseOf(owl:topObjectProperty) :B)) \
            ObjectPropertyDomain(Annotation(rdfs:comment \"d\") owl:topObjectProperty :C) \
            ObjectPropertyRange(ObjectInverseOf(owl:topObjectProperty) ObjectAllValuesFrom(owl:topObjectProperty :D))");
        assert!(!out.contains("topObjectProperty"), "{out}");
        assert!(out.contains(&format!("SubClassOf(:A ObjectSomeValuesFrom({HUB_ROLE} ObjectIntersectionOf(ObjectOneOf({HUB_INDIVIDUAL}) \
             ObjectSomeValuesFrom(ObjectInverseOf({HUB_ROLE}) :B))))")), "{out}");
        assert!(out.contains(&format!("SubClassOf(Annotation(rdfs:comment \"d\") {THING} :C)")), "{out}");
        assert!(out.contains(&format!("SubClassOf({THING} ObjectAllValuesFrom({HUB_ROLE} ObjectAllValuesFrom(ObjectInverseOf({HUB_ROLE}) :D)))")), "{out}");
    }

    #[test]
    fn admitted_side_occurrences_and_annotations_do_not_block() {
        let out = rewritten("Declaration(ObjectProperty(owl:topObjectProperty)) \
            SubObjectPropertyOf(:r owl:topObjectProperty) \
            AnnotationAssertion(rdfs:comment owl:topObjectProperty \"x\") \
            SubClassOf(Annotation(rdfs:comment \"y\") :A ObjectAllValuesFrom(owl:topObjectProperty :B))");
        assert!(out.contains("SubObjectPropertyOf(:r owl:topObjectProperty)"));
        assert!(out.contains(&format!("ObjectAllValuesFrom({HUB_ROLE} ObjectAllValuesFrom(ObjectInverseOf({HUB_ROLE}) :B))")), "{out}");
    }

    #[test]
    fn generated_namespace_in_source_disables_the_rewrite() {
        let source = "Ontology(SubClassOf(<urn:km:internal:universal-role#hub> \
            ObjectSomeValuesFrom(owl:topObjectProperty <urn:B>)))";
        assert!(matches!(encode(source).unwrap(), Cow::Borrowed(_)));
    }
}
