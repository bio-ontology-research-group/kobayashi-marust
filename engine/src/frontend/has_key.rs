//! Exact source rewrite of OWL 2 keys into DL-safe rules.
//!
//! `HasKey(CE (P1 … Pm) (D1 … Dn))` states, in the OWL 2 Direct Semantics,
//! that for all *named* individuals `x`, `y`, `z1 … zm` and all data values
//! `w1 … wn`: if `x` and `y` are instances of `CE`, `(x, zi)` and `(y, zi)`
//! are in `Pi` for every `i`, and `(x, wj)` and `(y, wj)` are in `Dj` for
//! every `j`, then `x = y`. That is exactly the DL-safe rule
//!
//! ```text
//! CE(?x) ∧ CE(?y) ∧ ⋀i (Pi(?x, ?zi) ∧ Pi(?y, ?zi)) ∧ ⋀j (Dj(?x, ?wj) ∧ Dj(?y, ?wj))
//!     → SameIndividual(?x, ?y)
//! ```
//!
//! because DL-safe rule variables range over named individuals (object
//! variables) and data values (data variables), and a shared data variable
//! joins on value equality, never on spelling. An inverse key property
//! `ObjectInverseOf(P)` becomes the atom `P(?zi, ?x)`.
//!
//! The rewrite runs on the source, before profiling and routing, so the source
//! profile, the rule certificates, the router and every rule consumer see an
//! ordinary `DLSafeRule`. A key is therefore handled, refused or counted as
//! `DROPPED` exactly as that rule would be. No calculus logic changes.
//!
//! Only the standard form with two parenthesised property lists is rewritten.
//! Any other spelling, and a source that already mentions the generated
//! variable namespace, leaves the source byte-identical (the key then stays a
//! counted drop). `KM_NO_HAS_KEY_RULES` disables the rewrite for differential
//! tests.

use std::borrow::Cow;

use super::sexpr::{tokens, Node, Parser};

/// Namespace of the generated rule variables. Variables are rule-local, but a
/// source that mentions the namespace is left unchanged all the same.
const VARIABLE_NAMESPACE: &str = "urn:km:internal:has-key";

fn variable(name: &str) -> String {
    format!("Variable(<{VARIABLE_NAMESPACE}#{name}>)")
}

struct Spans<'a> {
    text: &'a str,
}

impl<'a> Spans<'a> {
    fn offset(&self, token: &str) -> Result<usize, String> {
        let start = (token.as_ptr() as usize)
            .checked_sub(self.text.as_ptr() as usize)
            .ok_or("has-key rewrite: foreign token")?;
        if self.text.get(start..start + token.len()) != Some(token) {
            return Err("has-key rewrite: invalid token range".into());
        }
        Ok(start)
    }

    /// Byte range of a list node introduced by its head token `head`.
    fn list(&self, head: &str) -> Result<(usize, usize), String> {
        let start = self.offset(head)?;
        let mut depth = 0usize;
        for token in tokens(&self.text[start + head.len()..]) {
            match token {
                "(" => depth += 1,
                ")" => {
                    depth = depth.checked_sub(1).ok_or("has-key rewrite: unbalanced list")?;
                    if depth == 0 {
                        return Ok((start, self.offset(token)? + 1));
                    }
                }
                _ if depth == 0 => return Err("has-key rewrite: list without arguments".into()),
                _ => {}
            }
        }
        Err("has-key rewrite: unterminated list".into())
    }

    /// Source text of a named node: an atom or a list with a keyword head.
    fn source(&self, node: &Node<'a>) -> Result<&'a str, String> {
        match node {
            Node::Atom(token) => Ok(token),
            Node::List(head, _) if !head.is_empty() => {
                let (start, end) = self.list(head)?;
                Ok(&self.text[start..end])
            }
            Node::List(..) => Err("has-key rewrite: anonymous list".into()),
        }
    }
}

/// The rule for one key, or `None` when the key is not in the standard form.
fn key_rule<'a>(spans: &Spans<'a>, args: &[Node<'a>]) -> Result<Option<String>, String> {
    let logical: Vec<&Node<'a>> =
        args.iter().filter(|arg| arg.head() != Some("Annotation")).collect();
    let [class, Node::List("", objects), Node::List("", data)] = logical.as_slice() else {
        return Ok(None);
    };
    if objects.is_empty() && data.is_empty() {
        return Ok(None);
    }
    let class = spans.source(class)?;
    let (x, y) = (variable("x"), variable("y"));
    let mut body = vec![format!("ClassAtom({class} {x})"), format!("ClassAtom({class} {y})")];
    for (i, property) in objects.iter().enumerate() {
        let z = variable(&format!("z{i}"));
        match property {
            Node::Atom(name) => {
                body.push(format!("ObjectPropertyAtom({name} {x} {z})"));
                body.push(format!("ObjectPropertyAtom({name} {y} {z})"));
            }
            Node::List("ObjectInverseOf", inner) => match inner.as_slice() {
                [Node::Atom(name)] => {
                    body.push(format!("ObjectPropertyAtom({name} {z} {x})"));
                    body.push(format!("ObjectPropertyAtom({name} {z} {y})"));
                }
                _ => return Ok(None),
            },
            _ => return Ok(None),
        }
    }
    for (j, property) in data.iter().enumerate() {
        let Node::Atom(name) = property else { return Ok(None) };
        let w = variable(&format!("w{j}"));
        body.push(format!("DataPropertyAtom({name} {x} {w})"));
        body.push(format!("DataPropertyAtom({name} {y} {w})"));
    }
    Ok(Some(format!(
        "DLSafeRule(Body({}) Head(SameIndividualAtom({x} {y})))",
        body.join(" ")
    )))
}

/// Rewrite every standard-form key into its DL-safe rule. Sources without a
/// key are returned borrowed and byte-identical.
pub fn encode(text: &str) -> Result<Cow<'_, str>, String> {
    if !text.contains("HasKey") || text.contains(VARIABLE_NAMESPACE)
        || std::env::var_os("KM_NO_HAS_KEY_RULES").is_some()
    {
        return Ok(Cow::Borrowed(text));
    }
    let mut parser = Parser::new(text);
    while parser.peek() == Some("Prefix") {
        parser.parse()?;
    }
    if parser.next_tok() != Some("Ontology") || parser.next_tok() != Some("(") {
        return Ok(Cow::Borrowed(text));
    }
    let spans = Spans { text };
    let mut edits: Vec<(usize, usize, String)> = Vec::new();
    loop {
        match parser.peek() {
            None => return Err("has-key rewrite: unterminated Ontology".into()),
            Some(")") => break,
            Some(_) => {
                if let Node::List(head @ "HasKey", args) = parser.parse()? {
                    if let Some(rule) = key_rule(&spans, &args)? {
                        let (start, end) = spans.list(head)?;
                        edits.push((start, end, rule));
                    }
                }
            }
        }
    }
    if edits.is_empty() {
        return Ok(Cow::Borrowed(text));
    }
    // Top-level nodes are visited in source order and never overlap.
    let mut out = String::with_capacity(text.len() + 256 * edits.len());
    let mut copied = 0;
    for (start, end, rule) in edits {
        out.push_str(&text[copied..start]);
        out.push_str(&rule);
        copied = end;
    }
    out.push_str(&text[copied..]);
    Ok(Cow::Owned(out))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rewritten(body: &str) -> String {
        encode(&format!("Prefix(:=<urn:t#>) Ontology(<urn:t> {body})")).unwrap().into_owned()
    }

    #[test]
    fn object_inverse_and_data_keys_become_one_rule_each() {
        let out = rewritten("Declaration(Class(:A)) HasKey(Annotation(rdfs:comment \"k\") \
            ObjectIntersectionOf(:A :B) (:r ObjectInverseOf(:s)) (:d)) SubClassOf(:A :B)");
        let x = variable("x");
        let y = variable("y");
        let z0 = variable("z0");
        let z1 = variable("z1");
        let w0 = variable("w0");
        assert_eq!(out, format!("Prefix(:=<urn:t#>) Ontology(<urn:t> Declaration(Class(:A)) \
            DLSafeRule(Body(ClassAtom(ObjectIntersectionOf(:A :B) {x}) ClassAtom(ObjectIntersectionOf(:A :B) {y}) \
            ObjectPropertyAtom(:r {x} {z0}) ObjectPropertyAtom(:r {y} {z0}) \
            ObjectPropertyAtom(:s {z1} {x}) ObjectPropertyAtom(:s {z1} {y}) \
            DataPropertyAtom(:d {x} {w0}) DataPropertyAtom(:d {y} {w0})) \
            Head(SameIndividualAtom({x} {y}))) SubClassOf(:A :B))"));
    }

    #[test]
    fn sources_without_a_standard_key_stay_borrowed() {
        for source in [
            "Prefix(:=<urn:t#>) Ontology(SubClassOf(:A :B))",
            "Prefix(:=<urn:t#>) Ontology(HasKey(:A :r :d))",
            "Prefix(:=<urn:t#>) Ontology(HasKey(:A () ()))",
            "Prefix(:=<urn:t#>) Ontology(HasKey(:A (:r) ()) SubClassOf(:A ObjectHasValue(:r <urn:km:internal:has-key#x>)))",
        ] {
            assert!(matches!(encode(source).unwrap(), Cow::Borrowed(_)), "{source}");
        }
    }
}
