//! Fail-closed streaming quotient for large positive EL ABoxes.
//!
//! OWL has no unique-name assumption.  In the nominal-free positive EL
//! fragment, mapping every source individual to one representative produces a
//! homomorphic over-approximation of the ABox.  If that stronger ABox is
//! consistent, the original is consistent; positive ABox facts do not change
//! the named TBox taxonomy.  We publish only after the normal frontend has
//! independently recognized its positive-EL-ABox certificate.  A quotient
//! clash therefore means "defer", never "inconsistent".

use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::Path;

use super::tmpfile::TempPath;
use super::OrchestrateError;

const MIN_SOURCE_BYTES: u64 = 30_000_000;
const MERGED: &str = "<urn:km:positive-abox-quotient>";
const SAMPLE_BYTES: usize = 1 << 20;
const ABOX_TOKENS: &[&[u8]] = &[
    b"ClassAssertion(",
    b"ObjectPropertyAssertion(",
    b"SameIndividual(",
    b"DifferentIndividuals(",
];

/// Cheap source-feature gate.  Reading and rewriting every large ontology
/// would penalize unrelated routes, so require a dense ABox in a fixed middle
/// sample before the strict whole-source pass.  A false rejection merely keeps
/// the established complete path.
fn looks_like_dense_abox(path: &Path, bytes: u64) -> std::io::Result<bool> {
    let mut file = File::open(path)?;
    let sample_len = SAMPLE_BYTES.min(bytes as usize);
    let start = bytes.saturating_sub(sample_len as u64) / 2;
    file.seek(SeekFrom::Start(start))?;
    let mut sample = vec![0; sample_len];
    file.read_exact(&mut sample)?;
    let lines = sample.iter().filter(|&&byte| byte == b'\n').count();
    let abox = ABOX_TOKENS
        .iter()
        .map(|token| {
            sample
                .windows(token.len())
                .filter(|window| *window == *token)
                .count()
        })
        .sum::<usize>();
    Ok(abox >= 256 && abox * 2 >= lines.max(1))
}

#[derive(Default)]
struct Identities {
    ids: HashMap<String, usize>,
    parent: Vec<usize>,
    rank: Vec<u8>,
    different: Vec<Vec<usize>>,
}

impl Identities {
    fn id(&mut self, name: &str) -> usize {
        if let Some(&id) = self.ids.get(name) {
            return id;
        }
        let id = self.parent.len();
        self.ids.insert(name.to_owned(), id);
        self.parent.push(id);
        self.rank.push(0);
        id
    }

    fn root(&mut self, id: usize) -> usize {
        let parent = self.parent[id];
        if parent != id {
            let root = self.root(parent);
            self.parent[id] = root;
        }
        self.parent[id]
    }

    fn union(&mut self, left: usize, right: usize) {
        let mut left = self.root(left);
        let mut right = self.root(right);
        if left == right {
            return;
        }
        if self.rank[left] < self.rank[right] {
            std::mem::swap(&mut left, &mut right);
        }
        self.parent[right] = left;
        if self.rank[left] == self.rank[right] {
            self.rank[left] += 1;
        }
    }

    fn consistent(&mut self) -> bool {
        let groups = std::mem::take(&mut self.different);
        for group in groups {
            let mut roots = HashSet::with_capacity(group.len());
            for id in group {
                if !roots.insert(self.root(id)) {
                    return false;
                }
            }
        }
        true
    }
}

fn individual(token: &str) -> bool {
    (token.starts_with('<') && token.ends_with('>') && token.len() > 2)
        || (token.starts_with("_:") && token.len() > 2)
}

fn identity_args<'a>(line: &'a str, constructor: &str) -> Option<Vec<&'a str>> {
    let body = line
        .strip_prefix(constructor)?
        .strip_prefix('(')?
        .strip_suffix(')')?;
    let args: Vec<_> = body.split_ascii_whitespace().collect();
    (args.len() >= 2 && args.iter().all(|arg| individual(arg))).then_some(args)
}

fn rewrite_class_assertion(line: &str) -> Option<String> {
    let body = line.strip_prefix("ClassAssertion(")?.strip_suffix(')')?;
    let split = body.rfind(char::is_whitespace)?;
    let (class, source_individual) = body.split_at(split);
    let source_individual = source_individual.trim();
    if class.is_empty() || !individual(source_individual) {
        return None;
    }
    Some(format!("ClassAssertion({class} {MERGED})"))
}

fn rewrite_role_assertion(line: &str) -> Option<String> {
    let body = line
        .strip_prefix("ObjectPropertyAssertion(")?
        .strip_suffix(')')?;
    // The target family uses named roles.  Reject inverse expressions here;
    // the full fallback remains available for every rejected source.
    let args: Vec<_> = body.split_ascii_whitespace().collect();
    if args.len() != 3 || !individual(args[0]) || !individual(args[1]) || !individual(args[2]) {
        return None;
    }
    Some(format!(
        "ObjectPropertyAssertion({} {MERGED} {MERGED})",
        args[0]
    ))
}

/// Build a smaller ontology or return `None` without changing semantics of the
/// ordinary path.  Input must have exactly one complete top-level axiom per
/// line; this is deliberately stricter than the OWL functional-syntax parser.
pub(super) fn try_build(path: &Path) -> Result<Option<TempPath>, OrchestrateError> {
    let source_bytes = path.metadata()?.len();
    if !cfg!(test)
        && (source_bytes < MIN_SOURCE_BYTES || !looks_like_dense_abox(path, source_bytes)?)
    {
        return Ok(None);
    }
    let input = BufReader::with_capacity(1 << 20, File::open(path)?);
    let output_path = TempPath::new(".positive-abox-quotient.ofn");
    let mut output = BufWriter::with_capacity(1 << 20, File::create(output_path.path())?);
    let mut identities = Identities::default();
    let mut class_assertions = HashSet::new();
    let mut role_assertions = HashSet::new();
    let mut saw_class = false;
    let mut saw_ontology = false;
    let mut closed = false;

    for line in input.lines() {
        let line = line?;
        let trimmed = line.trim();
        if trimmed.is_empty() {
            writeln!(output)?;
            continue;
        }
        if closed {
            return Ok(None);
        }
        if trimmed.starts_with("Ontology(") {
            if saw_ontology {
                return Ok(None);
            }
            saw_ontology = true;
            writeln!(output, "{line}")?;
        } else if trimmed == ")" {
            closed = true;
            writeln!(output, "{line}")?;
        } else if trimmed.starts_with("ClassAssertion(") {
            let Some(rewritten) = rewrite_class_assertion(trimmed) else {
                return Ok(None);
            };
            saw_class = true;
            if class_assertions.insert(rewritten.clone()) {
                writeln!(output, "{rewritten}")?;
            }
        } else if trimmed.starts_with("ObjectPropertyAssertion(") {
            let Some(rewritten) = rewrite_role_assertion(trimmed) else {
                return Ok(None);
            };
            if role_assertions.insert(rewritten.clone()) {
                writeln!(output, "{rewritten}")?;
            }
        } else if trimmed.starts_with("SameIndividual(") {
            let Some(args) = identity_args(trimmed, "SameIndividual") else {
                return Ok(None);
            };
            let first = identities.id(args[0]);
            for arg in &args[1..] {
                let next = identities.id(arg);
                identities.union(first, next);
            }
        } else if trimmed.starts_with("DifferentIndividuals(") {
            let Some(args) = identity_args(trimmed, "DifferentIndividuals") else {
                return Ok(None);
            };
            let group = args.into_iter().map(|arg| identities.id(arg)).collect();
            identities.different.push(group);
        } else {
            // Preserve TBox/RBox/declarations/header material byte-for-byte.
            // Any other semantic ABox constructor remains present, causing the
            // normal frontend certificate checked by the caller to refuse.
            writeln!(output, "{line}")?;
        }
    }
    output.flush()?;
    if !saw_ontology || !closed || !saw_class || !identities.consistent() {
        return Ok(None);
    }
    Ok(Some(output_path))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn rewrites_nested_class_and_named_role_assertions() {
        assert_eq!(
            rewrite_class_assertion("ClassAssertion(ObjectSomeValuesFrom(<r> ObjectIntersectionOf(<A> <B>)) <i>)").as_deref(),
            Some("ClassAssertion(ObjectSomeValuesFrom(<r> ObjectIntersectionOf(<A> <B>)) <urn:km:positive-abox-quotient>)")
        );
        assert_eq!(
            rewrite_role_assertion("ObjectPropertyAssertion(<r> <a> <b>)").as_deref(),
            Some("ObjectPropertyAssertion(<r> <urn:km:positive-abox-quotient> <urn:km:positive-abox-quotient>)")
        );
    }

    #[test]
    fn identity_union_detects_nary_difference_clash() {
        let mut ids = Identities::default();
        let a = ids.id("<a>");
        let b = ids.id("<b>");
        let c = ids.id("<c>");
        ids.union(a, b);
        ids.different.push(vec![a, b, c]);
        assert!(!ids.consistent());
    }

    #[test]
    fn malformed_or_inverse_role_assertions_decline() {
        assert!(
            rewrite_role_assertion("ObjectPropertyAssertion(ObjectInverseOf(<r>) <a> <b>)")
                .is_none()
        );
        assert!(rewrite_class_assertion("ClassAssertion(<A>)").is_none());
    }

    #[test]
    fn dense_abox_sample_gate_separates_tbox_text() {
        let dense = TempPath::new(".dense.ofn");
        let tbox = TempPath::new(".tbox.ofn");
        fs::write(dense.path(), "ClassAssertion(<A> <a>)\n".repeat(300)).unwrap();
        fs::write(tbox.path(), "SubClassOf(<A> <B>)\n".repeat(300)).unwrap();
        assert!(
            looks_like_dense_abox(dense.path(), dense.path().metadata().unwrap().len()).unwrap()
        );
        assert!(
            !looks_like_dense_abox(tbox.path(), tbox.path().metadata().unwrap().len()).unwrap()
        );
    }

    #[test]
    fn complete_source_is_deduplicated_and_quotiented() {
        let source = TempPath::new(".source.ofn");
        fs::write(
            source.path(),
            "Prefix(:=<http://e/>)\nOntology(\n\
             Declaration(Class(<http://e/A>))\n\
             ClassAssertion(<http://e/A> <http://e/a>)\n\
             ClassAssertion(<http://e/A> <http://e/b>)\n\
             ObjectPropertyAssertion(<http://e/r> <http://e/a> <http://e/b>)\n\
             ObjectPropertyAssertion(<http://e/r> <http://e/b> <http://e/a>)\n\
             SameIndividual(<http://e/a> <http://e/c>)\n\
             DifferentIndividuals(<http://e/a> <http://e/b>)\n)\n",
        )
        .unwrap();
        let quotient = try_build(source.path()).unwrap().expect("safe quotient");
        let text = fs::read_to_string(quotient.path()).unwrap();
        assert_eq!(text.matches("ClassAssertion(").count(), 1);
        assert_eq!(text.matches("ObjectPropertyAssertion(").count(), 1);
        assert!(!text.contains("SameIndividual("));
        assert!(!text.contains("DifferentIndividuals("));
        assert_eq!(text.matches(MERGED).count(), 3);
    }

    #[test]
    fn contradictory_identity_source_declines() {
        let source = TempPath::new(".source.ofn");
        fs::write(
            source.path(),
            "Ontology(\nClassAssertion(<A> <a>)\n\
             SameIndividual(<a> <b>)\nDifferentIndividuals(<a> <b>)\n)\n",
        )
        .unwrap();
        assert!(try_build(source.path()).unwrap().is_none());
    }
}
