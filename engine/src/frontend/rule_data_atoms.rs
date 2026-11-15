//! Exact source rewrite of data variables in DL-safe rule bodies (W8).
//!
//! A DL-safe rule binds its object variables to named individuals and its
//! data variables to data values (any value, not only literals of the
//! source: HermiT answers `a : ∃p.xsd:integer`, `p(?x, ?v) → B(?x)` with
//! `a : B`). A data variable `?v` that occurs in the body in exactly one
//! `DataPropertyAtom(p t ?v)`, with `p` a named data property, and otherwise
//! only in `DataRangeAtom(Di ?v)` atoms of the body, is satisfied for a
//! binding of `t` exactly when the value of `t` has some `p`-value in every
//! `Di`, so those atoms are replaced by
//! `ClassAtom(DataSomeValuesFrom(p D) t)` with `D` the intersection of the
//! `Di` (`rdfs:Literal` when there is none). The rule is otherwise unchanged.
//! Any other occurrence of a data variable (in the head, a built-in, a second
//! data property atom, a join) leaves the rule as it is, so it is handled or
//! refused as before. Sources without such a variable are returned borrowed
//! and byte-identical. `KM_NO_RULE_DATA_ATOMS` disables the rewrite.

use std::borrow::Cow;
use std::collections::BTreeMap;

use super::sexpr::{tokens, Node, Parser};

struct Spans<'a> {
    text: &'a str,
}

impl<'a> Spans<'a> {
    fn offset(&self, token: &str) -> Result<usize, String> {
        let start = (token.as_ptr() as usize)
            .checked_sub(self.text.as_ptr() as usize)
            .ok_or("rule data rewrite: foreign token")?;
        if self.text.get(start..start + token.len()) != Some(token) {
            return Err("rule data rewrite: invalid token range".into());
        }
        Ok(start)
    }

    fn list(&self, head: &str) -> Result<(usize, usize), String> {
        let start = self.offset(head)?;
        let mut depth = 0usize;
        for token in tokens(&self.text[start + head.len()..]) {
            match token {
                "(" => depth += 1,
                ")" => {
                    depth = depth.checked_sub(1).ok_or("rule data rewrite: unbalanced list")?;
                    if depth == 0 {
                        return Ok((start, self.offset(token)? + 1));
                    }
                }
                _ if depth == 0 => return Err("rule data rewrite: list without arguments".into()),
                _ => {}
            }
        }
        Err("rule data rewrite: unterminated list".into())
    }

    fn source(&self, node: &Node<'a>) -> Result<&'a str, String> {
        match node {
            Node::Atom(token) => Ok(token),
            Node::List(head, _) if !head.is_empty() => {
                let (start, end) = self.list(head)?;
                Ok(&self.text[start..end])
            }
            Node::List(..) => Err("rule data rewrite: anonymous list".into()),
        }
    }
}

/// The variable IRI of a `Variable(<iri>)` node.
fn variable<'a>(node: &Node<'a>) -> Option<&'a str> {
    match node {
        Node::List("Variable", inner) => match inner.as_slice() {
            [Node::Atom(iri)] => Some(iri),
            _ => None,
        },
        _ => None,
    }
}

/// Every variable occurring in `node`.
fn variables_in<'a>(node: &Node<'a>, out: &mut Vec<&'a str>) {
    if let Some(v) = variable(node) {
        out.push(v);
        return;
    }
    if let Node::List(_, args) = node {
        for arg in args {
            variables_in(arg, out);
        }
    }
}

/// The rewritten rule, or `None` when no data variable qualifies.
fn rule<'a>(spans: &Spans<'a>, args: &[Node<'a>]) -> Result<Option<String>, String> {
    let annotations: Vec<&Node<'a>> = args.iter().filter(|a| a.head() == Some("Annotation")).collect();
    let logical: Vec<&Node<'a>> = args.iter().filter(|a| a.head() != Some("Annotation")).collect();
    let [Node::List("Body", body), Node::List("Head", head)] = logical.as_slice() else {
        return Ok(None);
    };
    // Occurrence counts of each variable outside the candidate shapes.
    let mut property_atoms: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    let mut range_atoms: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
    let mut other: BTreeMap<&str, usize> = BTreeMap::new();
    for (index, atom) in body.iter().enumerate() {
        match atom {
            Node::List("DataPropertyAtom", inner)
                if inner.len() == 3 && matches!(inner[0], Node::Atom(_)) && variable(&inner[2]).is_some() =>
            {
                property_atoms.entry(variable(&inner[2]).unwrap()).or_default().push(index);
                let mut vs = Vec::new();
                variables_in(&inner[1], &mut vs);
                for v in vs {
                    *other.entry(v).or_default() += 1;
                }
            }
            Node::List("DataRangeAtom", inner) if inner.len() == 2 && variable(&inner[1]).is_some() => {
                range_atoms.entry(variable(&inner[1]).unwrap()).or_default().push(index);
            }
            _ => {
                let mut vs = Vec::new();
                variables_in(atom, &mut vs);
                for v in vs {
                    *other.entry(v).or_default() += 1;
                }
            }
        }
    }
    for atom in head {
        let mut vs = Vec::new();
        variables_in(atom, &mut vs);
        for v in vs {
            *other.entry(v).or_default() += 1;
        }
    }
    let mut replaced: BTreeMap<usize, String> = BTreeMap::new();
    let mut dropped: Vec<usize> = Vec::new();
    for (v, atoms) in &property_atoms {
        if atoms.len() != 1 || other.get(v).copied().unwrap_or(0) != 0 {
            continue;
        }
        let Node::List(_, inner) = &body[atoms[0]] else { continue };
        let property = spans.source(&inner[0])?;
        let subject = spans.source(&inner[1])?;
        let ranges: Vec<&str> = match range_atoms.get(v) {
            Some(indices) => indices
                .iter()
                .map(|&i| match &body[i] {
                    Node::List(_, inner) => spans.source(&inner[0]),
                    _ => Err("rule data rewrite: data range atom".into()),
                })
                .collect::<Result<_, _>>()?,
            None => Vec::new(),
        };
        let range = match ranges.as_slice() {
            [] => "rdfs:Literal".to_string(),
            [one] => one.to_string(),
            many => format!("DataIntersectionOf({})", many.join(" ")),
        };
        replaced.insert(atoms[0], format!("ClassAtom(DataSomeValuesFrom({property} {range}) {subject})"));
        dropped.extend(range_atoms.get(v).into_iter().flatten().copied());
    }
    if replaced.is_empty() {
        return Ok(None);
    }
    let mut atoms = Vec::new();
    for (index, atom) in body.iter().enumerate() {
        if let Some(text) = replaced.get(&index) {
            atoms.push(text.clone());
        } else if !dropped.contains(&index) {
            atoms.push(spans.source(atom)?.to_string());
        }
    }
    let heads: Vec<String> = head.iter().map(|a| spans.source(a).map(str::to_string)).collect::<Result<_, _>>()?;
    let annotations: Vec<String> =
        annotations.iter().map(|a| spans.source(a).map(str::to_string)).collect::<Result<_, _>>()?;
    let prefix = if annotations.is_empty() { String::new() } else { format!("{} ", annotations.join(" ")) };
    Ok(Some(format!("DLSafeRule({prefix}Body({}) Head({}))", atoms.join(" "), heads.join(" "))))
}

/// Rewrite every qualifying rule (see the module docs).
pub fn encode(text: &str) -> Result<Cow<'_, str>, String> {
    if !text.contains("DLSafeRule") || !text.contains("DataPropertyAtom")
        || std::env::var_os("KM_NO_RULE_DATA_ATOMS").is_some()
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
            None => return Err("rule data rewrite: unterminated Ontology".into()),
            Some(")") => break,
            Some(_) => {
                if let Node::List(head @ "DLSafeRule", args) = parser.parse()? {
                    if let Some(rewritten) = rule(&spans, &args)? {
                        let (start, end) = spans.list(head)?;
                        edits.push((start, end, rewritten));
                    }
                }
            }
        }
    }
    if edits.is_empty() {
        return Ok(Cow::Borrowed(text));
    }
    let mut out = String::with_capacity(text.len() + 64 * edits.len());
    let mut copied = 0;
    for (start, end, rewritten) in edits {
        out.push_str(&text[copied..start]);
        out.push_str(&rewritten);
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
    fn lone_data_variables_become_data_restrictions() {
        let out = rewritten("DLSafeRule(Body(DataPropertyAtom(:p Variable(<urn:x>) Variable(<urn:v>)) \
            DataRangeAtom(xsd:integer Variable(<urn:v>))) Head(ClassAtom(:C Variable(<urn:x>))))");
        assert!(out.contains("DLSafeRule(Body(ClassAtom(DataSomeValuesFrom(:p xsd:integer) Variable(<urn:x>))) \
            Head(ClassAtom(:C Variable(<urn:x>))))"), "{out}");
        let plain = rewritten("DLSafeRule(Body(DataPropertyAtom(:p Variable(<urn:x>) Variable(<urn:v>))) \
            Head(ClassAtom(:C Variable(<urn:x>))))");
        assert!(plain.contains("DataSomeValuesFrom(:p rdfs:Literal)"), "{plain}");
    }

    #[test]
    fn joins_heads_and_builtins_are_left_alone() {
        for body in [
            "DLSafeRule(Body(DataPropertyAtom(:p Variable(<urn:x>) Variable(<urn:v>)) DataPropertyAtom(:p Variable(<urn:y>) Variable(<urn:v>))) Head(SameIndividualAtom(Variable(<urn:x>) Variable(<urn:y>))))",
            "DLSafeRule(Body(DataPropertyAtom(:p Variable(<urn:x>) Variable(<urn:v>))) Head(DataPropertyAtom(:q Variable(<urn:x>) Variable(<urn:v>))))",
            "DLSafeRule(Body(DataPropertyAtom(:p Variable(<urn:x>) Variable(<urn:v>)) BuiltInAtom(<urn:b> Variable(<urn:v>))) Head(ClassAtom(:C Variable(<urn:x>))))",
        ] {
            let source = format!("Prefix(:=<urn:t#>) Ontology(<urn:t> {body})");
            assert!(matches!(encode(&source).unwrap(), Cow::Borrowed(_)), "{body}");
        }
    }
}
