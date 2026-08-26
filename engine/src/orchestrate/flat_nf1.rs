//! Fail-closed direct classifier for very large flat named-class taxonomies.
//!
//! This path accepts only a strict, line-oriented subset of OWL functional
//! syntax: prefixes, one ontology header, class/object-property declarations,
//! named-class `SubClassOf` edges, existential leaves of
//! the form `A ⊑ ∃r.B`, and a positive simple RBox. Existential leaves and
//! role axioms cannot feed a named-class conclusion in this fragment, so the
//! public taxonomy is exactly the closure of the named edges. Universally valid
//! built-in edges (`A ⊑ owl:Thing` and `owl:Nothing ⊑ A`) are ignored.
//! Any annotation, import, existential antecedent, domain/range, semantically
//! active bottom/top occurrence, abbreviated name or malformed line declines
//! to the complete frontend before publishing an answer.

use super::GroupedJsonTaxonomy;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;
use std::sync::Arc;

const MIN_DIRECT_SOURCE_BYTES: u64 = 32 << 20;
const MIN_SPARSE_HORN_SOURCE_BYTES: u64 = 32 << 20;
const MIN_SPARSE_HORN_ABOX_SOURCE_BYTES: u64 = 24 << 20;
const MIN_MIXED_SPARSE_SOURCE_BYTES: u64 = 64 << 20;
const MIN_SPARSE_HORN_NAMES: usize = 25_000;
// Below this bound the established frontend is already cheap, while a second
// complete source read would affect far more misses than leaf-only hits.
const MIN_EMPTY_LEAF_SOURCE_BYTES: u64 = 4 << 20;
const MIN_POSITIVE_ABOX_SOURCE_BYTES: u64 = 16 << 20;
const OWL_THING: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING: &str = "http://www.w3.org/2002/07/owl#Nothing";

fn valid_full_iri(iri: &str) -> bool {
    !iri.is_empty()
        && !iri
            .chars()
            .any(|ch| ch.is_whitespace() || matches!(ch, '<' | '>' | '"' | '{' | '}' | '|'))
}

fn input_format_allows_direct(value: Option<&str>) -> bool {
    value.is_none_or(|value| {
        matches!(
            value.to_ascii_lowercase().as_str(),
            "auto" | "ofn" | "functional" | "functional-syntax"
        )
    })
}

fn source_has_class_assertion<R: BufRead>(mut reader: R) -> io::Result<bool> {
    let mut line = String::new();
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            return Ok(false);
        }
        if line.trim_start().starts_with("ClassAssertion(") {
            return Ok(true);
        }
    }
}

fn prefix_declaration(line: &str) -> bool {
    let Some(body) = line
        .strip_prefix("Prefix(")
        .and_then(|s| s.strip_suffix(')'))
    else {
        return false;
    };
    let Some((name, iri)) = body.split_once(":=<") else {
        return false;
    };
    let Some(iri) = iri.strip_suffix('>') else {
        return false;
    };
    (name.is_empty()
        || name
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '_' | '-' | '.')))
        && valid_full_iri(iri)
}

fn ontology_header(line: &str) -> bool {
    if line == "Ontology(" {
        return true;
    }
    let Some(body) = line.strip_prefix("Ontology(") else {
        return false;
    };
    let mut count = 0;
    for token in body.split_ascii_whitespace() {
        let Some(iri) = token.strip_prefix('<').and_then(|s| s.strip_suffix('>')) else {
            return false;
        };
        if !valid_full_iri(iri) {
            return false;
        }
        count += 1;
    }
    matches!(count, 1 | 2)
}

fn intern_class(
    iri: &str,
    ids: &mut HashMap<Arc<str>, u32>,
    names: &mut Vec<Arc<str>>,
) -> Option<(u32, bool)> {
    if !valid_full_iri(iri) || iri == OWL_THING || iri == OWL_NOTHING {
        return None;
    }
    if let Some(&id) = ids.get(iri) {
        return Some((id, false));
    }
    let id = u32::try_from(names.len()).ok()?;
    let iri: Arc<str> = Arc::from(iri);
    ids.insert(Arc::clone(&iri), id);
    names.push(iri);
    Some((id, true))
}

fn canonicalize_graph(
    ids: &mut HashMap<Arc<str>, u32>,
    names: &mut Vec<Arc<str>>,
    outgoing: &mut Vec<Vec<u32>>,
) -> Option<()> {
    canonicalize_graph_with_map(ids, names, outgoing).map(|_| ())
}

fn canonicalize_graph_with_map(
    ids: &mut HashMap<Arc<str>, u32>,
    names: &mut Vec<Arc<str>>,
    outgoing: &mut Vec<Vec<u32>>,
) -> Option<Vec<u32>> {
    let mut old_order: Vec<u32> = (0..names.len())
        .map(|index| u32::try_from(index).ok())
        .collect::<Option<_>>()?;
    old_order.sort_unstable_by(|left, right| names[*left as usize].cmp(&names[*right as usize]));
    let mut old_to_new = vec![0u32; names.len()];
    let mut sorted_names = Vec::with_capacity(names.len());
    for (new, old) in old_order.into_iter().enumerate() {
        old_to_new[old as usize] = u32::try_from(new).ok()?;
        sorted_names.push(Arc::clone(&names[old as usize]));
    }
    let mut sorted_outgoing = vec![Vec::new(); outgoing.len()];
    for (old_sub, supers) in outgoing.iter().enumerate() {
        let new_sub = old_to_new[old_sub] as usize;
        sorted_outgoing[new_sub] = supers.iter().map(|sup| old_to_new[*sup as usize]).collect();
    }
    *names = sorted_names;
    *outgoing = sorted_outgoing;
    ids.clear();
    ids.reserve(names.len());
    for (index, iri) in names.iter().enumerate() {
        ids.insert(Arc::clone(iri), u32::try_from(index).ok()?);
    }
    Some(old_to_new)
}

fn declaration_iri(line: &str) -> Option<&str> {
    line.strip_prefix("Declaration(Class(<")?
        .strip_suffix(">))")
}

fn object_property_declaration_iri(line: &str) -> Option<&str> {
    line.strip_prefix("Declaration(ObjectProperty(<")?
        .strip_suffix(">))")
}

fn subclass_iris(line: &str) -> Option<(&str, &str)> {
    let pair = line.strip_prefix("SubClassOf(<")?.strip_suffix(">)")?;
    pair.split_once("> <")
}

/// Recognize only built-in subclass axioms that hold in every OWL
/// interpretation.  They carry no named-to-named taxonomy information and can
/// therefore be discarded by the direct projection.  The converse forms
/// (`owl:Thing ⊑ A` and `A ⊑ owl:Nothing`) are intentionally absent.
fn tautological_builtin_subclass(line: &str) -> bool {
    if matches!(
        line,
        "SubClassOf(owl:Nothing owl:Nothing)"
            | "SubClassOf(owl:Nothing owl:Thing)"
            | "SubClassOf(owl:Thing owl:Thing)"
    ) {
        return true;
    }
    if let Some(iri) = line
        .strip_prefix("SubClassOf(<")
        .and_then(|body| body.strip_suffix("> owl:Thing)"))
    {
        return valid_full_iri(iri);
    }
    if let Some(iri) = line
        .strip_prefix("SubClassOf(owl:Nothing <")
        .and_then(|body| body.strip_suffix(">)"))
    {
        return valid_full_iri(iri);
    }
    false
}

fn disjoint_intersection_iris(line: &str) -> Option<(&str, &str)> {
    let pair = line
        .strip_prefix("SubClassOf(ObjectIntersectionOf(<")?
        .strip_suffix(">) owl:Nothing)")?;
    let (left, right) = pair.split_once("> <")?;
    (valid_full_iri(left) && valid_full_iri(right)).then_some((left, right))
}

/// The OWL spelling `A ⊑ ¬B` is equivalent to `A ⊓ B ⊑ ⊥`.
/// Normalize both source spellings to the same disjoint pair before applying
/// the existing common-descendant certificate below.
fn disjoint_complement_iris(line: &str) -> Option<(&str, &str)> {
    let body = line.strip_prefix("SubClassOf(<")?.strip_suffix(">))")?;
    let (left, right) = body.split_once("> ObjectComplementOf(<")?;
    (valid_full_iri(left) && valid_full_iri(right)).then_some((left, right))
}

fn disjoint_classes_iris(line: &str) -> Option<Vec<&str>> {
    let body = line.strip_prefix("DisjointClasses(<")?.strip_suffix(">)")?;
    let iris: Vec<_> = body.split("> <").collect();
    (iris.len() >= 2 && iris.iter().all(|iri| valid_full_iri(iri))).then_some(iris)
}

fn top_level_operands(body: &str) -> Option<Vec<&str>> {
    let mut operands = Vec::new();
    let mut depth = 0u32;
    let mut start = 0usize;
    for (at, byte) in body.bytes().enumerate() {
        match byte {
            b'(' => depth = depth.checked_add(1)?,
            b')' => depth = depth.checked_sub(1)?,
            b' ' if depth == 0 => {
                if at == start {
                    return None;
                }
                operands.push(&body[start..at]);
                start = at + 1;
            }
            _ => {}
        }
    }
    if depth != 0 || start == body.len() {
        return None;
    }
    operands.push(&body[start..]);
    Some(operands)
}

fn full_iri_token(token: &str) -> Option<&str> {
    let iri = token.strip_prefix('<')?.strip_suffix('>')?;
    valid_full_iri(iri).then_some(iri)
}

fn equivalent_named_union_iris(line: &str) -> Option<(&str, Vec<&str>)> {
    let body = line
        .strip_prefix("EquivalentClasses(<")?
        .strip_suffix("))")?;
    let (defined, alternatives) = body.split_once("> ObjectUnionOf(")?;
    if !valid_full_iri(defined) {
        return None;
    }
    let alternatives = top_level_operands(alternatives)?
        .into_iter()
        .map(full_iri_token)
        .collect::<Option<Vec<_>>>()?;
    (alternatives.len() >= 2).then_some((defined, alternatives))
}

fn equivalent_named_one_of(line: &str) -> Option<(&str, Vec<&str>)> {
    let body = line
        .strip_prefix("EquivalentClasses(<")?
        .strip_suffix("))")?;
    let (defined, individuals) = body.split_once("> ObjectOneOf(")?;
    if !valid_full_iri(defined) {
        return None;
    }
    let individuals = top_level_operands(individuals)?
        .into_iter()
        .map(|token| valid_individual_token(token).then_some(token))
        .collect::<Option<Vec<_>>>()?;
    (!individuals.is_empty()).then_some((defined, individuals))
}

fn named_existential_token(token: &str) -> Option<(&str, &str)> {
    let body = token
        .strip_prefix("ObjectSomeValuesFrom(<")?
        .strip_suffix(">)")?;
    let (role, filler) = body.split_once("> <")?;
    (valid_full_iri(role) && valid_full_iri(filler)).then_some((role, filler))
}

fn named_intersection_parts(line: &str, equivalent: bool) -> Option<(&str, Vec<&str>)> {
    let prefix = if equivalent {
        "EquivalentClasses(<"
    } else {
        "SubClassOf(<"
    };
    let body = line.strip_prefix(prefix)?.strip_suffix("))")?;
    let (defined, operands) = body.split_once("> ObjectIntersectionOf(")?;
    (valid_full_iri(defined)).then_some((defined, top_level_operands(operands)?))
}

fn existential_leaf_iris(line: &str) -> Option<(&str, &str, &str)> {
    let body = line.strip_prefix("SubClassOf(<")?.strip_suffix(">))")?;
    let (sub, restriction) = body.split_once("> ObjectSomeValuesFrom(<")?;
    let (role, filler) = restriction.split_once("> <")?;
    (valid_full_iri(sub) && valid_full_iri(role) && valid_full_iri(filler))
        .then_some((sub, role, filler))
}

fn positive_class_assertion_iris(line: &str) -> Option<(&str, &str)> {
    let (class, individual) = named_class_assertion_parts(line)?;
    let individual = individual.strip_prefix('<')?.strip_suffix('>')?;
    valid_full_iri(individual).then_some((class, individual))
}

fn valid_individual_token(token: &str) -> bool {
    token
        .strip_prefix('<')
        .and_then(|iri| iri.strip_suffix('>'))
        .is_some_and(valid_full_iri)
        || token.strip_prefix("_:").is_some_and(|label| {
            !label.is_empty()
                && !label
                    .chars()
                    .any(|ch| ch.is_whitespace() || matches!(ch, '(' | ')' | '<' | '>'))
        })
}

fn named_class_assertion_parts(line: &str) -> Option<(&str, &str)> {
    let body = line.strip_prefix("ClassAssertion(<")?.strip_suffix(')')?;
    let (class, individual) = body.split_once("> ")?;
    (valid_full_iri(class) && valid_individual_token(individual)).then_some((class, individual))
}

fn simple_existential_class_assertion_parts(line: &str) -> Option<(&str, &str, &str)> {
    let body = line
        .strip_prefix("ClassAssertion(ObjectSomeValuesFrom(<")?
        .strip_suffix(')')?;
    let (role, tail) = body.split_once("> <")?;
    let (filler, individual) = tail.split_once(">) ")?;
    (ordinary_role(role)
        && valid_full_iri(filler)
        && filler != OWL_THING
        && filler != OWL_NOTHING
        && valid_individual_token(individual))
    .then_some((role, filler, individual))
}

fn distinct_individuals_iris(line: &str) -> Option<Vec<&str>> {
    let body = line
        .strip_prefix("DifferentIndividuals(<")?
        .strip_suffix(">)")?;
    let iris: Vec<_> = body.split("> <").collect();
    (iris.len() >= 2 && iris.iter().all(|iri| valid_full_iri(iri))).then_some(iris)
}

fn conjunction_lhs_iris(line: &str) -> Option<(Vec<&str>, Option<&str>)> {
    let body = line
        .strip_prefix("SubClassOf(ObjectIntersectionOf(")?
        .strip_suffix(')')?;
    if let Some(bottom_body) = body.strip_suffix(" owl:Nothing") {
        let (operands, _) = bottom_body.rsplit_once(')')?;
        let operands = operands.strip_prefix('<')?.strip_suffix('>')?;
        let operands: Vec<_> = operands.split("> <").collect();
        return (operands.len() >= 2 && operands.iter().all(|iri| valid_full_iri(iri)))
            .then_some((operands, None));
    }
    let (operands, head) = body.rsplit_once(") <")?;
    let operands = operands.strip_prefix('<')?.strip_suffix('>')?;
    let head = head.strip_suffix('>')?;
    let operands: Vec<_> = operands.split("> <").collect();
    (operands.len() >= 2 && operands.iter().all(|iri| valid_full_iri(iri)) && valid_full_iri(head))
        .then_some((operands, Some(head)))
}

fn existential_lhs_iris(line: &str) -> Option<(&str, &str, &str)> {
    let body = line
        .strip_prefix("SubClassOf(ObjectSomeValuesFrom(<")?
        .strip_suffix(">)")?;
    let (role, tail) = body.split_once("> <")?;
    let (filler, head) = tail.split_once(">) <")?;
    (valid_full_iri(role) && valid_full_iri(filler) && valid_full_iri(head))
        .then_some((role, filler, head))
}

fn unary_role_axiom_iri(line: &str) -> Option<&str> {
    [
        "TransitiveObjectProperty(<",
        "SymmetricObjectProperty(<",
        "ReflexiveObjectProperty(<",
    ]
    .into_iter()
    .find_map(|prefix| line.strip_prefix(prefix)?.strip_suffix(">)"))
}

fn binary_role_axiom_iris(line: &str) -> Option<(&str, &str)> {
    [
        "SubObjectPropertyOf(<",
        "InverseObjectProperties(<",
        "EquivalentObjectProperties(<",
    ]
    .into_iter()
    .find_map(|prefix| {
        let pair = line.strip_prefix(prefix)?.strip_suffix(">)")?;
        pair.split_once("> <")
    })
}

fn top_role_super_axiom_iri(line: &str) -> Option<&str> {
    line.strip_prefix("SubObjectPropertyOf(<")?
        .strip_suffix("> owl:topObjectProperty)")
}

fn binary_role_chain_axiom_iris(line: &str) -> Option<(&str, &str, &str)> {
    let body = line
        .strip_prefix("SubObjectPropertyOf(ObjectPropertyChain(<")?
        .strip_suffix(">)")?;
    let (left, tail) = body.split_once("> <")?;
    let (right, sup) = tail.split_once(">) <")?;
    (valid_full_iri(left) && valid_full_iri(right) && valid_full_iri(sup))
        .then_some((left, right, sup))
}

/// Return an exact grouped taxonomy, or `None` before publication when the
/// source is outside the strict direct fragment.
pub(super) fn try_classify(path: &Path) -> io::Result<Option<GroupedJsonTaxonomy>> {
    let source_bytes = std::fs::metadata(path)?.len();
    if std::env::var_os("KM_NO_DIRECT_FLAT_NF1").is_some()
        || !input_format_allows_direct(std::env::var("KM_INPUT_FORMAT").ok().as_deref())
    {
        return Ok(None);
    }

    let sparse_horn_candidate = source_bytes >= MIN_SPARSE_HORN_SOURCE_BYTES
        || (source_bytes >= MIN_SPARSE_HORN_ABOX_SOURCE_BYTES
            && source_has_class_assertion(BufReader::with_capacity(1 << 20, File::open(path)?))?);
    if sparse_horn_candidate {
        let reader = BufReader::with_capacity(1 << 20, File::open(path)?);
        if let Some(result) = classify_sparse_horn_reader(
            reader,
            MIN_SPARSE_HORN_NAMES,
            source_bytes >= MIN_MIXED_SPARSE_SOURCE_BYTES,
        )? {
            if std::env::var_os("KM_TIMING").is_some() {
                eprintln!("KM_TIMING source certificate route=sparse_horn_taxonomy");
            }
            return Ok(Some(result));
        }
    }

    // Source-certified projection for generated positive annotation
    // ontologies. The strict source grammar and its composed empty-taxonomy
    // theorem authorize publication; every rejected byte falls through to the
    // complete frontend and automatic supervisor.
    if source_bytes >= MIN_POSITIVE_ABOX_SOURCE_BYTES
        && positive_abox_empty_taxonomy_screen(BufReader::with_capacity(
            1 << 20,
            File::open(path)?,
        ))?
    {
        if std::env::var_os("KM_TIMING").is_some() {
            eprintln!("KM_TIMING source certificate route=positive_empty_source");
        }
        return Ok(Some(GroupedJsonTaxonomy {
            iris: Vec::new(),
            rows: BTreeMap::new(),
            reachability_graph: None,
        }));
    }

    // A pure existential-leaf ontology has an empty public taxonomy: setting
    // every class and role extension to empty is a model, and no axiom has a
    // named-class conclusion.  Unlike the general flat closure below, this
    // decision needs no class dictionary or graph.  Admit medium-sized sources
    // with one allocation-free pass so generated leaf families do not pay for
    // parsing, normalization, and ELC merely to publish an empty relation.
    if source_bytes >= MIN_EMPTY_LEAF_SOURCE_BYTES
        && source_bytes < MIN_DIRECT_SOURCE_BYTES
        && pure_leaf_source_screen(BufReader::with_capacity(1 << 20, File::open(path)?))?
    {
        return Ok(Some(GroupedJsonTaxonomy {
            iris: Vec::new(),
            rows: BTreeMap::new(),
            reachability_graph: None,
        }));
    }
    if source_bytes < MIN_DIRECT_SOURCE_BYTES {
        return Ok(None);
    }

    let file = File::open(path)?;
    let reader = BufReader::with_capacity(1 << 20, file);
    if !flat_source_screen(reader)? {
        return Ok(None);
    }
    let file = File::open(path)?;
    let reader = BufReader::with_capacity(1 << 20, file);
    classify_reader(reader, 1_000)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PositiveClassShape {
    /// A named class at the current Boolean level. On the right of a subclass
    /// axiom this would be a public taxonomy conclusion.
    Named,
    /// A positive expression whose truth does not imply any named class at the
    /// current level (an existential, or an intersection of such expressions).
    Leaf,
}

struct PositiveCursor<'a> {
    text: &'a str,
    at: usize,
}

impl<'a> PositiveCursor<'a> {
    fn new(text: &'a str) -> Self {
        Self { text, at: 0 }
    }

    fn skip_space(&mut self) {
        while self
            .text
            .as_bytes()
            .get(self.at)
            .is_some_and(u8::is_ascii_whitespace)
        {
            self.at += 1;
        }
    }

    fn take(&mut self, token: &str) -> bool {
        self.skip_space();
        if self.text[self.at..].starts_with(token) {
            self.at += token.len();
            true
        } else {
            false
        }
    }

    fn iri(&mut self) -> bool {
        self.skip_space();
        let Some(rest) = self.text.get(self.at..).and_then(|s| s.strip_prefix('<')) else {
            return false;
        };
        let Some(end) = rest.find('>') else {
            return false;
        };
        let iri = &rest[..end];
        if !valid_full_iri(iri) {
            return false;
        }
        self.at += end + 2;
        true
    }

    fn class_iri(&mut self) -> bool {
        let start = self.at;
        if !self.iri() {
            return false;
        }
        let consumed = self.text[start..self.at].trim_ascii();
        consumed != "<http://www.w3.org/2002/07/owl#Thing>"
            && consumed != "<http://www.w3.org/2002/07/owl#Nothing>"
    }

    fn role_iri(&mut self) -> bool {
        let start = self.at;
        if !self.iri() {
            return false;
        }
        let consumed = self.text[start..self.at].trim_ascii();
        consumed != "<http://www.w3.org/2002/07/owl#topObjectProperty>"
            && consumed != "<http://www.w3.org/2002/07/owl#bottomObjectProperty>"
    }

    fn class_expression(&mut self) -> Option<PositiveClassShape> {
        self.class_expression_at(0)
    }

    fn class_expression_at(&mut self, depth: u16) -> Option<PositiveClassShape> {
        // A bounded recognizer must decline adversarial nesting instead of
        // risking a process-stack overflow before the complete parser runs.
        if depth >= 256 {
            return None;
        }
        self.skip_space();
        if self.text[self.at..].starts_with('<') {
            return self.class_iri().then_some(PositiveClassShape::Named);
        }
        if self.take("ObjectSomeValuesFrom(") {
            if !self.role_iri() {
                return None;
            }
            self.class_expression_at(depth + 1)?;
            return self.take(")").then_some(PositiveClassShape::Leaf);
        }
        if self.take("ObjectIntersectionOf(") {
            let mut operands = 0;
            let mut leaf_only = true;
            loop {
                self.skip_space();
                if self.take(")") {
                    return (operands >= 2).then_some(if leaf_only {
                        PositiveClassShape::Leaf
                    } else {
                        PositiveClassShape::Named
                    });
                }
                let shape = self.class_expression_at(depth + 1)?;
                leaf_only &= shape == PositiveClassShape::Leaf;
                operands += 1;
            }
        }
        None
    }

    fn done(&mut self) -> bool {
        self.skip_space();
        self.at == self.text.len()
    }
}

fn positive_leaf_subclass(line: &str) -> bool {
    let Some(body) = line
        .strip_prefix("SubClassOf(")
        .and_then(|text| text.strip_suffix(')'))
    else {
        return false;
    };
    let mut cursor = PositiveCursor::new(body);
    cursor.class_iri()
        && cursor.class_expression() == Some(PositiveClassShape::Leaf)
        && cursor.done()
}

fn positive_class_assertion(line: &str) -> bool {
    let Some(body) = line
        .strip_prefix("ClassAssertion(")
        .and_then(|text| text.strip_suffix(')'))
    else {
        return false;
    };
    let mut cursor = PositiveCursor::new(body);
    cursor.class_expression().is_some() && cursor.iri() && cursor.done()
}

fn positive_declaration(line: &str) -> bool {
    declaration_iri(line)
        .is_some_and(|iri| valid_full_iri(iri) && iri != OWL_THING && iri != OWL_NOTHING)
        || object_property_declaration_iri(line).is_some_and(ordinary_role)
}

/// Recognize a source family whose public taxonomy is empty without parsing or
/// normalizing its hundreds of thousands of positive ABox expressions. Every
/// TBox axiom is `A ⊑ E`, where E has no named top-level conjunct; every
/// ABox axiom is a positive class assertion. The grammar rejects all other
/// constructs before publication.
fn positive_abox_empty_taxonomy_screen<R: BufRead>(mut reader: R) -> io::Result<bool> {
    let mut line = String::new();
    let mut saw_ontology = false;
    let mut saw_subclass = false;
    let mut saw_abox = false;
    let mut closed = false;
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            break;
        }
        let text = line.trim();
        if text.is_empty() {
            continue;
        }
        if closed {
            return Ok(false);
        }
        if !saw_ontology {
            if prefix_declaration(text) {
                continue;
            }
            if ontology_header(text) {
                saw_ontology = true;
                continue;
            }
            return Ok(false);
        }
        if text == ")" {
            closed = true;
        } else if positive_declaration(text) {
            // Administrative only.
        } else if positive_leaf_subclass(text) {
            saw_subclass = true;
        } else if positive_class_assertion(text) {
            saw_abox = true;
        } else {
            return Ok(false);
        }
    }
    Ok(saw_ontology && closed && saw_subclass && saw_abox)
}

/// Recognize the empty-taxonomy subset of the proved existential-leaf source
/// fragment without retaining declarations or edges.  Every near miss returns
/// false before publication and therefore falls through to the complete path.
fn pure_leaf_source_screen<R: BufRead>(mut reader: R) -> io::Result<bool> {
    let mut line = String::new();
    let mut saw_ontology = false;
    let mut saw_leaf = false;
    let mut class_declarations = 0usize;
    let mut closed = false;
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            break;
        }
        let text = line.trim();
        if text.is_empty() {
            continue;
        }
        if closed {
            return Ok(false);
        }
        if !saw_ontology {
            if prefix_declaration(text) {
                continue;
            }
            if ontology_header(text) {
                saw_ontology = true;
                continue;
            }
            return Ok(false);
        }
        if text == ")" {
            closed = true;
            continue;
        }
        if let Some(iri) = declaration_iri(text) {
            if !valid_full_iri(iri) || iri == OWL_THING || iri == OWL_NOTHING {
                return Ok(false);
            }
            class_declarations = class_declarations.saturating_add(1);
            continue;
        }
        if let Some(iri) = object_property_declaration_iri(text) {
            if !ordinary_role(iri) {
                return Ok(false);
            }
            continue;
        }
        if let Some((sub, role, filler)) = existential_leaf_iris(text) {
            if [sub, filler]
                .into_iter()
                .any(|iri| iri == OWL_THING || iri == OWL_NOTHING)
                || !ordinary_role(role)
            {
                return Ok(false);
            }
            saw_leaf = true;
            continue;
        }
        if let Some(role) = unary_role_axiom_iri(text) {
            if !ordinary_role(role) {
                return Ok(false);
            }
            continue;
        }
        if let Some((sub, sup)) = binary_role_axiom_iris(text) {
            if !ordinary_role(sub) || !ordinary_role(sup) {
                return Ok(false);
            }
            continue;
        }
        if let Some(sub) = top_role_super_axiom_iri(text) {
            if !ordinary_role(sub) {
                return Ok(false);
            }
            continue;
        }
        if let Some((left, right, sup)) = binary_role_chain_axiom_iris(text) {
            if !ordinary_role(left) || !ordinary_role(right) || !ordinary_role(sup) {
                return Ok(false);
            }
            continue;
        }
        return Ok(false);
    }
    Ok(closed && saw_leaf && class_declarations >= 1_000)
}

fn ordinary_role(iri: &str) -> bool {
    valid_full_iri(iri)
        && iri != "http://www.w3.org/2002/07/owl#topObjectProperty"
        && iri != "http://www.w3.org/2002/07/owl#bottomObjectProperty"
}

/// Reject unsupported giant sources before allocating the declaration table
/// and adjacency graph. Generated ORE files can place their first complex
/// axiom after millions of otherwise flat lines; screening keeps such a miss
/// to one allocation-free sequential read before the complete frontend runs.
/// This is only a necessary lexical screen. `classify_reader` still validates
/// endpoints, graph semantics, and the complete grammar.
fn flat_source_screen<R: BufRead>(mut reader: R) -> io::Result<bool> {
    let mut line = String::new();
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            return Ok(true);
        }
        let text = line.trim();
        if text.is_empty()
            || text == ")"
            || prefix_declaration(text)
            || ontology_header(text)
            || declaration_iri(text).is_some()
            || object_property_declaration_iri(text).is_some()
            || subclass_iris(text).is_some()
            || tautological_builtin_subclass(text)
            || disjoint_intersection_iris(text).is_some()
            || disjoint_complement_iris(text).is_some()
            || disjoint_classes_iris(text).is_some()
            || existential_leaf_iris(text).is_some()
            || unary_role_axiom_iri(text).is_some()
            || binary_role_axiom_iris(text).is_some()
            || top_role_super_axiom_iri(text).is_some()
            || binary_role_chain_axiom_iris(text).is_some()
        {
            continue;
        }
        return Ok(false);
    }
}

#[derive(Clone)]
struct SparseHornRule {
    body: Vec<u32>,
    head: Option<u32>,
}

#[derive(Clone, Copy)]
struct SparseExistential {
    sub: u32,
    role: u32,
    filler: u32,
}

#[derive(Clone, Copy)]
struct SparseExistentialRule {
    role: u32,
    filler: u32,
    head: u32,
}

struct SparseMixedRule {
    named: Vec<u32>,
    existential: Vec<(u32, u32)>,
    head: u32,
}

struct SparseUnionRule {
    defined: u32,
    alternatives: Vec<u32>,
}

struct SparseRedundantNominal {
    defined: u32,
    individuals: Vec<Arc<str>>,
}

fn reverse_reach(target: u32, incoming: &[Vec<u32>]) -> Vec<bool> {
    let mut found = vec![false; incoming.len()];
    let mut stack = vec![target];
    while let Some(concept) = stack.pop() {
        if found[concept as usize] {
            continue;
        }
        found[concept as usize] = true;
        stack.extend(incoming[concept as usize].iter().copied());
    }
    found
}

fn close_downward(found: &mut [bool], incoming: &[Vec<u32>], seeds: impl IntoIterator<Item = u32>) {
    let mut stack: Vec<u32> = seeds.into_iter().collect();
    while let Some(concept) = stack.pop() {
        if found[concept as usize] {
            continue;
        }
        found[concept as usize] = true;
        stack.extend(incoming[concept as usize].iter().copied());
    }
}

fn forward_reach(source: u32, outgoing: &[Vec<u32>]) -> Vec<bool> {
    let mut found = vec![false; outgoing.len()];
    let mut stack = vec![source];
    while let Some(concept) = stack.pop() {
        if found[concept as usize] {
            continue;
        }
        found[concept as usize] = true;
        stack.extend(outgoing[concept as usize].iter().copied());
    }
    found
}

/// Saturate the named Horn layer of a very large, sparse EL source directly.
/// The accepted grammar is deliberately narrower than general EL: named NF1,
/// named conjunction NF2, named existential NF3/NF4, positive class
/// assertions, distinct individuals, and exact self-composition role chains.
/// Any other source line declines before an answer is published.
fn classify_sparse_horn_reader<R: BufRead>(
    mut reader: R,
    min_names: usize,
    allow_mixed_definitions: bool,
) -> io::Result<Option<GroupedJsonTaxonomy>> {
    let mut line = String::new();
    let mut saw_ontology = false;
    let mut closed = false;
    let mut saw_logical_axiom = false;
    let mut ids: HashMap<Arc<str>, u32> = HashMap::new();
    let mut names: Vec<Arc<str>> = Vec::new();
    let mut outgoing: Vec<Vec<u32>> = Vec::new();
    let mut role_ids: HashMap<Arc<str>, u32> = HashMap::new();
    let mut transitive_roles: HashSet<u32> = HashSet::new();
    let mut horn_rules: Vec<SparseHornRule> = Vec::new();
    let mut existentials: Vec<SparseExistential> = Vec::new();
    let mut existential_rules: Vec<SparseExistentialRule> = Vec::new();
    let mut mixed_rules: Vec<SparseMixedRule> = Vec::new();
    let mut union_rules: Vec<SparseUnionRule> = Vec::new();
    let mut redundant_nominals: Vec<SparseRedundantNominal> = Vec::new();
    let mut assertions: Vec<(Arc<str>, u32)> = Vec::new();
    let mut saw_existential_assertion = false;
    let mut saw_unimplemented_nf4_rbox = false;

    let intern = |iri: &str,
                  ids: &mut HashMap<Arc<str>, u32>,
                  names: &mut Vec<Arc<str>>,
                  outgoing: &mut Vec<Vec<u32>>|
     -> Option<u32> {
        let (id, inserted) = intern_class(iri, ids, names)?;
        if inserted {
            outgoing.push(Vec::new());
        }
        Some(id)
    };
    let intern_role = |iri: &str, role_ids: &mut HashMap<Arc<str>, u32>| -> Option<u32> {
        if !valid_full_iri(iri)
            || iri == "http://www.w3.org/2002/07/owl#topObjectProperty"
            || iri == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
        {
            return None;
        }
        if let Some(&id) = role_ids.get(iri) {
            return Some(id);
        }
        let id = u32::try_from(role_ids.len()).ok()?;
        role_ids.insert(Arc::from(iri), id);
        Some(id)
    };

    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            break;
        }
        let text = line.trim();
        if text.is_empty() {
            continue;
        }
        if closed {
            return Ok(None);
        }
        if !saw_ontology {
            if prefix_declaration(text) {
                continue;
            }
            if ontology_header(text) {
                saw_ontology = true;
                continue;
            }
            return Ok(None);
        }
        if text == ")" {
            closed = true;
            continue;
        }
        if let Some(iri) = declaration_iri(text) {
            if intern(iri, &mut ids, &mut names, &mut outgoing).is_none() {
                return Ok(None);
            }
            continue;
        }
        if let Some(role) = object_property_declaration_iri(text) {
            if intern_role(role, &mut role_ids).is_none() {
                return Ok(None);
            }
            continue;
        }
        if let Some((sub, sup)) = subclass_iris(text) {
            saw_logical_axiom = true;
            if sub == OWL_NOTHING || sup == OWL_THING {
                continue;
            }
            let Some(sub) = intern(sub, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            let Some(sup) = intern(sup, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            if sub != sup {
                outgoing[sub as usize].push(sup);
            }
            continue;
        }
        if let Some((sub, role, filler)) = existential_leaf_iris(text) {
            saw_logical_axiom = true;
            let Some(sub) = intern(sub, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            let Some(filler) = intern(filler, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            let Some(role) = intern_role(role, &mut role_ids) else {
                return Ok(None);
            };
            existentials.push(SparseExistential { sub, role, filler });
            continue;
        }
        if let Some((defined, operands)) = named_intersection_parts(text, false) {
            if !allow_mixed_definitions {
                return Ok(None);
            }
            saw_logical_axiom = true;
            let Some(defined) = intern(defined, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            for operand in operands {
                if let Some(named) = full_iri_token(operand) {
                    let Some(named) = intern(named, &mut ids, &mut names, &mut outgoing) else {
                        return Ok(None);
                    };
                    if defined != named {
                        outgoing[defined as usize].push(named);
                    }
                } else if let Some((role, filler)) = named_existential_token(operand) {
                    let Some(role) = intern_role(role, &mut role_ids) else {
                        return Ok(None);
                    };
                    let Some(filler) = intern(filler, &mut ids, &mut names, &mut outgoing) else {
                        return Ok(None);
                    };
                    existentials.push(SparseExistential {
                        sub: defined,
                        role,
                        filler,
                    });
                } else {
                    return Ok(None);
                }
            }
            continue;
        }
        if let Some((defined_iri, operands)) = named_intersection_parts(text, true) {
            if !allow_mixed_definitions {
                return Ok(None);
            }
            saw_logical_axiom = true;
            let Some(defined) = intern(defined_iri, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            let mut named_body = Vec::new();
            let mut existential_body = Vec::new();
            for operand in operands {
                if let Some(named) = full_iri_token(operand) {
                    let Some(named) = intern(named, &mut ids, &mut names, &mut outgoing) else {
                        return Ok(None);
                    };
                    named_body.push(named);
                    if defined != named {
                        outgoing[defined as usize].push(named);
                    }
                } else if let Some((role, filler)) = named_existential_token(operand) {
                    let Some(role) = intern_role(role, &mut role_ids) else {
                        return Ok(None);
                    };
                    let Some(filler) = intern(filler, &mut ids, &mut names, &mut outgoing) else {
                        return Ok(None);
                    };
                    existential_body.push((role, filler));
                    existentials.push(SparseExistential {
                        sub: defined,
                        role,
                        filler,
                    });
                } else {
                    return Ok(None);
                }
            }
            if named_body.is_empty() && existential_body.is_empty() {
                return Ok(None);
            }
            mixed_rules.push(SparseMixedRule {
                named: named_body,
                existential: existential_body,
                head: defined,
            });
            continue;
        }
        if let Some((defined_iri, alternatives)) = equivalent_named_union_iris(text) {
            if !allow_mixed_definitions {
                return Ok(None);
            }
            saw_logical_axiom = true;
            let Some(defined) = intern(defined_iri, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            let mut alternative_ids = Vec::with_capacity(alternatives.len());
            for alternative in alternatives {
                let Some(alternative) = intern(alternative, &mut ids, &mut names, &mut outgoing)
                else {
                    return Ok(None);
                };
                if alternative != defined {
                    outgoing[alternative as usize].push(defined);
                }
                alternative_ids.push(alternative);
            }
            union_rules.push(SparseUnionRule {
                defined,
                alternatives: alternative_ids,
            });
            continue;
        }
        if let Some((defined_iri, individuals)) = equivalent_named_one_of(text) {
            if !allow_mixed_definitions {
                return Ok(None);
            }
            saw_logical_axiom = true;
            let Some(defined) = intern(defined_iri, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            redundant_nominals.push(SparseRedundantNominal {
                defined,
                individuals: individuals.into_iter().map(Arc::from).collect(),
            });
            continue;
        }
        if let Some((operands, head)) = conjunction_lhs_iris(text) {
            saw_logical_axiom = true;
            let mut body = Vec::with_capacity(operands.len());
            for operand in operands {
                let Some(id) = intern(operand, &mut ids, &mut names, &mut outgoing) else {
                    return Ok(None);
                };
                body.push(id);
            }
            let head = match head {
                Some(iri) => {
                    let Some(id) = intern(iri, &mut ids, &mut names, &mut outgoing) else {
                        return Ok(None);
                    };
                    Some(id)
                }
                None => None,
            };
            horn_rules.push(SparseHornRule { body, head });
            continue;
        }
        if let Some(iris) = disjoint_classes_iris(text) {
            saw_logical_axiom = true;
            let mut operands = Vec::with_capacity(iris.len());
            for iri in iris {
                let Some(id) = intern(iri, &mut ids, &mut names, &mut outgoing) else {
                    return Ok(None);
                };
                operands.push(id);
            }
            for left in 0..operands.len() {
                for right in left + 1..operands.len() {
                    horn_rules.push(SparseHornRule {
                        body: vec![operands[left], operands[right]],
                        head: None,
                    });
                }
            }
            continue;
        }
        if let Some((role, filler, head)) = existential_lhs_iris(text) {
            saw_logical_axiom = true;
            let Some(role) = intern_role(role, &mut role_ids) else {
                return Ok(None);
            };
            let Some(filler) = intern(filler, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            let Some(head) = intern(head, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            existential_rules.push(SparseExistentialRule { role, filler, head });
            continue;
        }
        if let Some((class, individual)) = named_class_assertion_parts(text) {
            saw_logical_axiom = true;
            let Some(class) = intern(class, &mut ids, &mut names, &mut outgoing) else {
                return Ok(None);
            };
            assertions.push((Arc::from(individual), class));
            continue;
        }
        if simple_existential_class_assertion_parts(text).is_some() {
            saw_logical_axiom = true;
            saw_existential_assertion = true;
            continue;
        }
        if distinct_individuals_iris(text).is_some() {
            saw_logical_axiom = true;
            continue;
        }
        if let Some(role) = text
            .strip_prefix("TransitiveObjectProperty(<")
            .and_then(|body| body.strip_suffix(">)"))
        {
            saw_logical_axiom = true;
            let Some(role) = intern_role(role, &mut role_ids) else {
                return Ok(None);
            };
            transitive_roles.insert(role);
            continue;
        }
        if unary_role_axiom_iri(text).is_some() {
            return Ok(None);
        }
        if let Some(role) = top_role_super_axiom_iri(text) {
            saw_logical_axiom = true;
            if intern_role(role, &mut role_ids).is_none() {
                return Ok(None);
            }
            continue;
        }
        if let Some((sub, sup)) = binary_role_axiom_iris(text) {
            saw_logical_axiom = true;
            if intern_role(sub, &mut role_ids).is_none()
                || intern_role(sup, &mut role_ids).is_none()
            {
                return Ok(None);
            }
            // Role inclusions, inverses, and equivalent-role declarations can
            // change a named taxonomy only by supplying an existential-left
            // (NF4) premise.  The edge-elision certificate permits them when
            // no such rule exists; otherwise this specialized route declines.
            saw_unimplemented_nf4_rbox = true;
            continue;
        }
        if let Some((left, right, sup)) = binary_role_chain_axiom_iris(text) {
            saw_logical_axiom = true;
            let Some(left_id) = intern_role(left, &mut role_ids) else {
                return Ok(None);
            };
            if intern_role(right, &mut role_ids).is_none()
                || intern_role(sup, &mut role_ids).is_none()
            {
                return Ok(None);
            }
            if left == right && left == sup {
                transitive_roles.insert(left_id);
            } else {
                saw_unimplemented_nf4_rbox = true;
            }
            continue;
        }
        return Ok(None);
    }
    if !closed || !saw_logical_axiom || names.len() < min_names || outgoing.len() != names.len() {
        return Ok(None);
    }
    // A positive `i : exists r.C` cannot affect the named taxonomy or ABox
    // consistency in this fragment unless an NF4/existential-left rule can
    // turn that edge into a named type. Bottom roles/fillers and unsatisfiable
    // named fillers are rejected independently. Decline instead of attempting
    // to approximate whenever such a feedback rule exists.
    if saw_existential_assertion && !existential_rules.is_empty() {
        return Ok(None);
    }
    if saw_unimplemented_nf4_rbox && !existential_rules.is_empty() {
        return Ok(None);
    }
    // A finite nominal definition is taxonomy-inert in this positive Horn
    // fragment when every enumerated individual has exactly the defined class
    // as its only explicit named type. The assertions already provide the
    // reverse inclusion (each enumerand belongs to the class), while the
    // nominal restriction cannot distinguish their uniformly generated Horn
    // types. Object/existential assertions would invalidate that argument.
    if !redundant_nominals.is_empty() {
        if saw_existential_assertion {
            return Ok(None);
        }
        let mut explicit: HashMap<&str, Vec<u32>> = HashMap::new();
        for (individual, class) in &assertions {
            explicit
                .entry(individual.as_ref())
                .or_default()
                .push(*class);
        }
        for nominal in &redundant_nominals {
            for individual in &nominal.individuals {
                let Some(types) = explicit.get(individual.as_ref()) else {
                    return Ok(None);
                };
                if types.iter().any(|class| *class != nominal.defined)
                    || !types.contains(&nominal.defined)
                {
                    return Ok(None);
                }
            }
        }
    }

    let Some(old_to_new) = canonicalize_graph_with_map(&mut ids, &mut names, &mut outgoing) else {
        return Ok(None);
    };
    for rule in &mut horn_rules {
        for operand in &mut rule.body {
            *operand = old_to_new[*operand as usize];
        }
        if let Some(head) = &mut rule.head {
            *head = old_to_new[*head as usize];
        }
    }
    for edge in &mut existentials {
        edge.sub = old_to_new[edge.sub as usize];
        edge.filler = old_to_new[edge.filler as usize];
    }
    for rule in &mut existential_rules {
        rule.filler = old_to_new[rule.filler as usize];
        rule.head = old_to_new[rule.head as usize];
    }
    for rule in &mut mixed_rules {
        for concept in &mut rule.named {
            *concept = old_to_new[*concept as usize];
        }
        for (_, filler) in &mut rule.existential {
            *filler = old_to_new[*filler as usize];
        }
        rule.head = old_to_new[rule.head as usize];
    }
    for rule in &mut union_rules {
        rule.defined = old_to_new[rule.defined as usize];
        for alternative in &mut rule.alternatives {
            *alternative = old_to_new[*alternative as usize];
        }
    }
    for (_, class) in &mut assertions {
        *class = old_to_new[*class as usize];
    }
    for supers in &mut outgoing {
        supers.sort_unstable();
        supers.dedup();
    }
    let mut incoming = vec![Vec::<u32>::new(); names.len()];
    for (sub, supers) in outgoing.iter().enumerate() {
        for &sup in supers {
            incoming[sup as usize].push(sub as u32);
        }
    }

    loop {
        let mut additions: Vec<(u32, u32)> = Vec::new();
        for rule in &horn_rules {
            let mut common = reverse_reach(rule.body[0], &incoming);
            for &operand in &rule.body[1..] {
                let reaches = reverse_reach(operand, &incoming);
                for (candidate, reaches_operand) in common.iter_mut().zip(reaches) {
                    *candidate &= reaches_operand;
                }
            }
            let Some(head) = rule.head else {
                if common.into_iter().any(|candidate| candidate) {
                    return Ok(None);
                }
                continue;
            };
            let reaches_head = reverse_reach(head, &incoming);
            additions.extend(
                common
                    .into_iter()
                    .enumerate()
                    .filter_map(|(sub, candidate)| {
                        (candidate && !reaches_head[sub]).then_some((sub as u32, head))
                    }),
            );
        }

        for rule in &existential_rules {
            let filler_sources = reverse_reach(rule.filler, &incoming);
            let mut has_target = vec![false; names.len()];
            let seeds = existentials.iter().filter_map(|edge| {
                (edge.role == rule.role && filler_sources[edge.filler as usize]).then_some(edge.sub)
            });
            close_downward(&mut has_target, &incoming, seeds);
            if transitive_roles.contains(&rule.role) {
                loop {
                    let seeds: Vec<u32> = existentials
                        .iter()
                        .filter_map(|edge| {
                            (edge.role == rule.role
                                && has_target[edge.filler as usize]
                                && !has_target[edge.sub as usize])
                                .then_some(edge.sub)
                        })
                        .collect();
                    if seeds.is_empty() {
                        break;
                    }
                    close_downward(&mut has_target, &incoming, seeds);
                }
            }
            let reaches_head = reverse_reach(rule.head, &incoming);
            additions.extend(
                has_target
                    .into_iter()
                    .enumerate()
                    .filter_map(|(sub, holds)| {
                        (holds && !reaches_head[sub]).then_some((sub as u32, rule.head))
                    }),
            );
        }

        for rule in &mixed_rules {
            let mut common = vec![true; names.len()];
            for &operand in &rule.named {
                let reaches = reverse_reach(operand, &incoming);
                for (candidate, reaches_operand) in common.iter_mut().zip(reaches) {
                    *candidate &= reaches_operand;
                }
            }
            for &(role, filler) in &rule.existential {
                let filler_sources = reverse_reach(filler, &incoming);
                let mut has_target = vec![false; names.len()];
                let seeds = existentials.iter().filter_map(|edge| {
                    (edge.role == role && filler_sources[edge.filler as usize]).then_some(edge.sub)
                });
                close_downward(&mut has_target, &incoming, seeds);
                if transitive_roles.contains(&role) {
                    loop {
                        let seeds: Vec<u32> = existentials
                            .iter()
                            .filter_map(|edge| {
                                (edge.role == role
                                    && has_target[edge.filler as usize]
                                    && !has_target[edge.sub as usize])
                                    .then_some(edge.sub)
                            })
                            .collect();
                        if seeds.is_empty() {
                            break;
                        }
                        close_downward(&mut has_target, &incoming, seeds);
                    }
                }
                for (candidate, has_edge) in common.iter_mut().zip(has_target) {
                    *candidate &= has_edge;
                }
            }
            let reaches_head = reverse_reach(rule.head, &incoming);
            additions.extend(common.into_iter().enumerate().filter_map(|(sub, holds)| {
                (holds && !reaches_head[sub]).then_some((sub as u32, rule.head))
            }));
        }

        for rule in &union_rules {
            let mut common = forward_reach(rule.alternatives[0], &outgoing);
            for &alternative in &rule.alternatives[1..] {
                let reaches = forward_reach(alternative, &outgoing);
                for (candidate, reached) in common.iter_mut().zip(reaches) {
                    *candidate &= reached;
                }
            }
            let defined_reaches = forward_reach(rule.defined, &outgoing);
            additions.extend(common.into_iter().enumerate().filter_map(|(sup, holds)| {
                (holds && !defined_reaches[sup]).then_some((rule.defined, sup as u32))
            }));
        }

        additions.sort_unstable();
        additions.dedup();
        if additions.is_empty() {
            break;
        }
        for (sub, sup) in additions {
            outgoing[sub as usize].push(sup);
            incoming[sup as usize].push(sub);
        }
    }
    for supers in &mut outgoing {
        supers.sort_unstable();
        supers.dedup();
    }
    if !assertions.is_empty() {
        let mut by_individual: HashMap<Arc<str>, Vec<u32>> = HashMap::new();
        for (individual, class) in assertions {
            by_individual.entry(individual).or_default().push(class);
        }
        for classes in by_individual.into_values() {
            let mut types = vec![false; names.len()];
            let mut stack = classes;
            while let Some(class) = stack.pop() {
                if types[class as usize] {
                    continue;
                }
                types[class as usize] = true;
                stack.extend(outgoing[class as usize].iter().copied());
            }
            if horn_rules.iter().any(|rule| {
                rule.head.is_none() && rule.body.iter().all(|operand| types[*operand as usize])
            }) {
                return Ok(None);
            }
        }
    }
    Ok(Some(GroupedJsonTaxonomy {
        iris: names,
        rows: BTreeMap::new(),
        reachability_graph: Some(outgoing),
    }))
}

fn classify_reader<R: BufRead>(
    mut reader: R,
    min_names: usize,
) -> io::Result<Option<GroupedJsonTaxonomy>> {
    let mut line = String::new();
    let mut saw_ontology = false;
    let mut saw_logical_axiom = false;
    let mut closed = false;
    let mut ids: HashMap<Arc<str>, u32> = HashMap::new();
    let mut names: Vec<Arc<str>> = Vec::new();
    let mut outgoing: Vec<Vec<u32>> = Vec::new();
    let mut disjoint: Vec<(Arc<str>, Arc<str>)> = Vec::new();

    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            break;
        }
        let text = line.trim();
        if text.is_empty() {
            continue;
        }
        if closed {
            return Ok(None);
        }
        if !saw_ontology {
            if prefix_declaration(text) {
                continue;
            }
            if ontology_header(text) {
                saw_ontology = true;
                continue;
            }
            return Ok(None);
        }
        if text == ")" {
            closed = true;
            continue;
        }
        if let Some(iri) = declaration_iri(text) {
            let Some((_, inserted)) = intern_class(iri, &mut ids, &mut names) else {
                return Ok(None);
            };
            if inserted {
                outgoing.push(Vec::new());
            }
            continue;
        }
        if let Some(iri) = object_property_declaration_iri(text) {
            if !valid_full_iri(iri)
                || iri == "http://www.w3.org/2002/07/owl#topObjectProperty"
                || iri == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
            {
                return Ok(None);
            }
            continue;
        }
        if let Some((sub, sup)) = subclass_iris(text) {
            saw_logical_axiom = true;
            let Some((sub, sub_inserted)) = intern_class(sub, &mut ids, &mut names) else {
                return Ok(None);
            };
            if sub_inserted {
                outgoing.push(Vec::new());
            }
            let Some((sup, sup_inserted)) = intern_class(sup, &mut ids, &mut names) else {
                return Ok(None);
            };
            if sup_inserted {
                outgoing.push(Vec::new());
            }
            if sub != sup {
                outgoing[sub as usize].push(sup);
            }
            continue;
        }
        if tautological_builtin_subclass(text) {
            saw_logical_axiom = true;
            continue;
        }
        if let Some((left_iri, right_iri)) =
            disjoint_intersection_iris(text).or_else(|| disjoint_complement_iris(text))
        {
            saw_logical_axiom = true;
            let Some((_, left_inserted)) = intern_class(left_iri, &mut ids, &mut names) else {
                return Ok(None);
            };
            if left_inserted {
                outgoing.push(Vec::new());
            }
            let Some((_, right_inserted)) = intern_class(right_iri, &mut ids, &mut names) else {
                return Ok(None);
            };
            if right_inserted {
                outgoing.push(Vec::new());
            }
            disjoint.push((Arc::from(left_iri), Arc::from(right_iri)));
            continue;
        }
        if let Some(iris) = disjoint_classes_iris(text) {
            saw_logical_axiom = true;
            for iri in &iris {
                let Some((_, inserted)) = intern_class(iri, &mut ids, &mut names) else {
                    return Ok(None);
                };
                if inserted {
                    outgoing.push(Vec::new());
                }
            }
            for left in 0..iris.len() {
                for right in left + 1..iris.len() {
                    disjoint.push((Arc::from(iris[left]), Arc::from(iris[right])));
                }
            }
            continue;
        }
        if let Some((sub, role, filler)) = existential_leaf_iris(text) {
            saw_logical_axiom = true;
            let Some((_, sub_inserted)) = intern_class(sub, &mut ids, &mut names) else {
                return Ok(None);
            };
            if sub_inserted {
                outgoing.push(Vec::new());
            }
            let Some((_, filler_inserted)) = intern_class(filler, &mut ids, &mut names) else {
                return Ok(None);
            };
            if filler_inserted {
                outgoing.push(Vec::new());
            }
            if role == "http://www.w3.org/2002/07/owl#topObjectProperty"
                || role == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
            {
                return Ok(None);
            }
            continue;
        }
        if let Some(role) = unary_role_axiom_iri(text) {
            saw_logical_axiom = true;
            if !valid_full_iri(role)
                || role == "http://www.w3.org/2002/07/owl#topObjectProperty"
                || role == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
            {
                return Ok(None);
            }
            continue;
        }
        if let Some((sub, sup)) = binary_role_axiom_iris(text) {
            saw_logical_axiom = true;
            if !valid_full_iri(sub)
                || !valid_full_iri(sup)
                || [sub, sup].into_iter().any(|role| {
                    role == "http://www.w3.org/2002/07/owl#topObjectProperty"
                        || role == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
                })
            {
                return Ok(None);
            }
            continue;
        }
        if let Some(sub) = top_role_super_axiom_iri(text) {
            saw_logical_axiom = true;
            if !valid_full_iri(sub)
                || sub == "http://www.w3.org/2002/07/owl#topObjectProperty"
                || sub == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
            {
                return Ok(None);
            }
            continue;
        }
        if let Some((left, right, sup)) = binary_role_chain_axiom_iris(text) {
            saw_logical_axiom = true;
            if [left, right, sup].into_iter().any(|role| {
                role == "http://www.w3.org/2002/07/owl#topObjectProperty"
                    || role == "http://www.w3.org/2002/07/owl#bottomObjectProperty"
            }) {
                return Ok(None);
            }
            continue;
        }
        return Ok(None);
    }
    if !closed || !saw_logical_axiom || names.len() < min_names || outgoing.len() != names.len() {
        return Ok(None);
    }
    if canonicalize_graph(&mut ids, &mut names, &mut outgoing).is_none() {
        return Ok(None);
    }
    let disjoint: Vec<(u32, u32)> = disjoint
        .into_iter()
        .map(|(left, right)| Some((*ids.get(&left)?, *ids.get(&right)?)))
        .collect::<Option<_>>()
        .ok_or_else(|| io::Error::other("lost disjoint operand during canonicalization"))?;

    let n = names.len();
    for successors in &mut outgoing {
        successors.sort_unstable();
        successors.dedup();
    }

    // A disjointness axiom is taxonomy-inert exactly when no named source
    // reaches both operands. Compute each operand's reverse reachability over
    // the general graph and decline before publication on the first common
    // descendant. This is the executable premise of
    // `flatNF1Disjoint_sub_iff_flatReach`.
    let mut incoming = vec![Vec::<u32>::new(); n];
    for (sub, successors) in outgoing.iter().enumerate() {
        for &sup in successors {
            incoming[sup as usize].push(sub as u32);
        }
    }
    let reaches = |target: u32| {
        let mut found = vec![false; n];
        let mut stack = vec![target];
        while let Some(concept) = stack.pop() {
            if found[concept as usize] {
                continue;
            }
            found[concept as usize] = true;
            stack.extend(incoming[concept as usize].iter().copied());
        }
        found
    };
    for &(left, right) in &disjoint {
        let left_sources = reaches(left);
        let right_sources = reaches(right);
        if left_sources
            .iter()
            .zip(right_sources.iter())
            .any(|(left, right)| *left && *right)
        {
            return Ok(None);
        }
    }

    // Production-sized graphs are serialized from the directed graph one subject at a
    // time. Retaining their complete closure was both unnecessary and the
    // source of the prior direct route's memory regression on ORE868.
    if n >= 1_000 {
        return Ok(Some(GroupedJsonTaxonomy {
            iris: names,
            rows: BTreeMap::new(),
            reachability_graph: Some(outgoing),
        }));
    }

    let mut closure = vec![Vec::<u32>::new(); n];
    let mut seen = vec![0u32; n];
    let mut generation = 0u32;
    let mut stack = Vec::new();
    for concept in 0..n {
        generation = generation.wrapping_add(1);
        if generation == 0 {
            seen.fill(0);
            generation = 1;
        }
        seen[concept] = generation;
        stack.clear();
        stack.extend(outgoing[concept].iter().copied());
        while let Some(sup) = stack.pop() {
            let index = sup as usize;
            if seen[index] == generation {
                continue;
            }
            seen[index] = generation;
            closure[concept].push(sup);
            stack.extend(outgoing[index].iter().copied());
        }
        closure[concept].sort_unstable();
    }

    let mut rows = BTreeMap::new();
    for (concept, supers) in closure.into_iter().enumerate() {
        if !supers.is_empty() {
            rows.insert(concept as u32, supers);
        }
    }
    Ok(Some(GroupedJsonTaxonomy {
        iris: names,
        rows,
        reachability_graph: None,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(declarations: usize, tail: &str) -> String {
        let mut file = String::from("Ontology(<http://example.org/o>\n");
        for index in 0..declarations {
            file.push_str(&format!("Declaration(Class(<http://e/C{index:04}>))\n"));
        }
        file.push_str(tail);
        file
    }

    #[test]
    fn parses_sparse_horn_left_sides() {
        assert_eq!(
            conjunction_lhs_iris(
                "SubClassOf(ObjectIntersectionOf(<http://e/A> <http://e/B>) <http://e/C>)"
            ),
            Some((vec!["http://e/A", "http://e/B"], Some("http://e/C")))
        );
        assert_eq!(
            conjunction_lhs_iris(
                "SubClassOf(ObjectIntersectionOf(<http://e/A> <http://e/B>) owl:Nothing)"
            ),
            Some((vec!["http://e/A", "http://e/B"], None))
        );
        assert_eq!(
            existential_lhs_iris(
                "SubClassOf(ObjectSomeValuesFrom(<http://e/r> <http://e/A>) <http://e/B>)"
            ),
            Some(("http://e/r", "http://e/A", "http://e/B"))
        );
    }

    #[test]
    fn sparse_horn_saturates_conjunction_and_existential_left_rules() {
        let text = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
Declaration(Class(<http://e/C>))\n\
Declaration(Class(<http://e/D>))\n\
Declaration(Class(<http://e/E>))\n\
Declaration(Class(<http://e/F>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
SubClassOf(<http://e/A> <http://e/C>)\n\
SubClassOf(ObjectIntersectionOf(<http://e/B> <http://e/C>) <http://e/D>)\n\
SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/E>))\n\
SubClassOf(ObjectSomeValuesFrom(<http://e/r> <http://e/E>) <http://e/F>)\n\
ClassAssertion(<http://e/A> <http://e/i>)\n\
DifferentIndividuals(<http://e/i> <http://e/j>)\n\
)\n";
        let result = classify_sparse_horn_reader(std::io::Cursor::new(text), 6, true)
            .unwrap()
            .expect("strict sparse Horn source");
        let graph = result.reachability_graph.expect("streamed closure graph");
        let a = result
            .iris
            .iter()
            .position(|iri| &**iri == "http://e/A")
            .unwrap();
        let d = result
            .iris
            .iter()
            .position(|iri| &**iri == "http://e/D")
            .unwrap() as u32;
        let f = result
            .iris
            .iter()
            .position(|iri| &**iri == "http://e/F")
            .unwrap() as u32;
        assert!(graph[a].contains(&d));
        assert!(graph[a].contains(&f));
    }

    #[test]
    fn sparse_horn_saturates_named_union_and_mixed_equivalence() {
        let text = r#"Ontology(
Declaration(Class(<http://e/A>))
Declaration(Class(<http://e/B>))
Declaration(Class(<http://e/C>))
Declaration(Class(<http://e/D>))
Declaration(Class(<http://e/E>))
Declaration(Class(<http://e/F>))
Declaration(ObjectProperty(<http://e/r>))
SubClassOf(<http://e/A> <http://e/C>)
SubClassOf(<http://e/B> <http://e/C>)
EquivalentClasses(<http://e/D> ObjectUnionOf(<http://e/A> <http://e/B>))
SubClassOf(<http://e/E> <http://e/C>)
SubClassOf(<http://e/E> ObjectSomeValuesFrom(<http://e/r> <http://e/F>))
EquivalentClasses(<http://e/A> ObjectIntersectionOf(<http://e/C> ObjectSomeValuesFrom(<http://e/r> <http://e/F>)))
)
"#;
        let result = classify_sparse_horn_reader(std::io::Cursor::new(text), 6, true)
            .expect("reader")
            .expect("accepted mixed fragment");
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(text), 6, false)
                .expect("reader")
                .is_none()
        );
        let graph = result.reachability_graph.expect("graph taxonomy");
        let id = |iri: &str| {
            result
                .iris
                .iter()
                .position(|candidate| candidate.as_ref() == iri)
                .expect("declared class")
        };
        let reaches = |sub: &str, sup: &str| forward_reach(id(sub) as u32, &graph)[id(sup)];
        assert!(reaches("http://e/D", "http://e/C"));
        assert!(reaches("http://e/E", "http://e/A"));
    }

    #[test]
    fn sparse_horn_accepts_only_redundantly_witnessed_nominals() {
        let witnessed = r#"Ontology(
Declaration(Class(<http://e/A>))
Declaration(Class(<http://e/B>))
EquivalentClasses(<http://e/A> ObjectOneOf(<http://e/i> <http://e/j>))
ClassAssertion(<http://e/A> <http://e/i>)
ClassAssertion(<http://e/A> <http://e/j>)
SubClassOf(<http://e/A> <http://e/B>)
)
"#;
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(witnessed), 2, true)
                .expect("reader")
                .is_some()
        );
        let extra_type = witnessed.replace(
            "ClassAssertion(<http://e/A> <http://e/j>)",
            "ClassAssertion(<http://e/A> <http://e/j>)\nClassAssertion(<http://e/B> <http://e/j>)",
        );
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(extra_type), 2, true)
                .expect("reader")
                .is_none()
        );
    }

    #[test]
    fn sparse_horn_declines_a_joint_abox_disjointness_clash() {
        let text = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
SubClassOf(ObjectIntersectionOf(<http://e/A> <http://e/B>) owl:Nothing)\n\
ClassAssertion(<http://e/A> <http://e/i>)\n\
ClassAssertion(<http://e/B> <http://e/i>)\n\
)\n";
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(text), 2, true)
                .unwrap()
                .is_none()
        );

        let native = text.replace(
            "SubClassOf(ObjectIntersectionOf(<http://e/A> <http://e/B>) owl:Nothing)",
            "DisjointClasses(<http://e/A> <http://e/B>)",
        );
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(&native), 2, true)
                .unwrap()
                .is_none()
        );
        let native_consistent = native.replace("ClassAssertion(<http://e/B> <http://e/i>)\n", "");
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(native_consistent), 2, true)
                .unwrap()
                .is_some()
        );

        let blank_nodes = text
            .replace("<http://e/i>", "_:genid1")
            .replace("DifferentIndividuals(<http://e/i> <http://e/j>)\n", "");
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(blank_nodes), 2, true)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn sparse_horn_accepts_inert_simple_existential_abox_only_without_nf4_feedback() {
        let inert = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
ClassAssertion(ObjectSomeValuesFrom(<http://e/r> <http://e/B>) _:genid1)\n\
)\n";
        let result = classify_sparse_horn_reader(std::io::Cursor::new(inert), 2, true)
            .unwrap()
            .expect("positive existential ABox has no named feedback");
        let graph = result.reachability_graph.expect("streamed graph");
        assert_eq!(graph[0], vec![1]);
        assert_eq!(
            simple_existential_class_assertion_parts(
                "ClassAssertion(ObjectSomeValuesFrom(<http://e/r> <http://e/B>) _:genid1)"
            ),
            Some(("http://e/r", "http://e/B", "_:genid1"))
        );

        let feedback = inert.replace(
            "ClassAssertion(",
            "SubClassOf(ObjectSomeValuesFrom(<http://e/r> <http://e/B>) <http://e/A>)\n\
ClassAssertion(",
        );
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(feedback), 2, true)
                .unwrap()
                .is_none()
        );

        let nested = inert.replace(
            "ObjectSomeValuesFrom(<http://e/r> <http://e/B>)",
            "ObjectSomeValuesFrom(<http://e/r> ObjectIntersectionOf(<http://e/A> <http://e/B>))",
        );
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(nested), 2, true)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn sparse_horn_profitability_screen_detects_only_class_assertions() {
        let no_abox = "Ontology(\nSubClassOf(<http://e/A> <http://e/B>)\n)\n";
        assert!(!source_has_class_assertion(std::io::Cursor::new(no_abox)).unwrap());
        let abox = "Ontology(\n  ClassAssertion(<http://e/A> _:i)\n)\n";
        assert!(source_has_class_assertion(std::io::Cursor::new(abox)).unwrap());
    }

    #[test]
    fn sparse_horn_elides_complex_rbox_only_without_nf4_feedback() {
        let inert = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
Declaration(ObjectProperty(<http://e/s>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
SubObjectPropertyOf(<http://e/r> <http://e/s>)\n\
SubObjectPropertyOf(ObjectPropertyChain(<http://e/r> <http://e/s>) <http://e/s>)\n\
)\n";
        let result = classify_sparse_horn_reader(std::io::Cursor::new(inert), 2, true)
            .unwrap()
            .expect("RBox cannot feed the named taxonomy without NF4");
        assert_eq!(
            result.reachability_graph.expect("streamed graph")[0],
            vec![1]
        );

        let feedback = inert.replace(
            "SubObjectPropertyOf(<http://e/r> <http://e/s>)",
            "SubClassOf(ObjectSomeValuesFrom(<http://e/s> <http://e/B>) <http://e/A>)\n\
SubObjectPropertyOf(<http://e/r> <http://e/s>)",
        );
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(feedback), 2, true)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn sparse_horn_does_not_confuse_symmetry_with_transitivity() {
        let text = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
SymmetricObjectProperty(<http://e/r>)\n\
)\n";
        assert!(
            classify_sparse_horn_reader(std::io::Cursor::new(text), 2, true)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn exact_line_parser_and_closure() {
        let text = source(
            3,
            "SubClassOf(<http://e/C0000> <http://e/C0001>)\n\
             SubClassOf(<http://e/C0001> <http://e/C0002>)\n)\n",
        );
        let result = classify_reader(std::io::Cursor::new(text), 3)
            .unwrap()
            .expect("strict flat taxonomy");
        assert_eq!(result.iris.len(), 3);
        assert_eq!(result.rows.get(&0), Some(&vec![1, 2]));
        assert_eq!(result.rows.get(&1), Some(&vec![2]));
        assert_eq!(
            declaration_iri("Declaration(Class(<http://e/A>))"),
            Some("http://e/A")
        );
        assert_eq!(
            subclass_iris("SubClassOf(<http://e/A> <http://e/B>)"),
            Some(("http://e/A", "http://e/B"))
        );
        assert_eq!(
            existential_leaf_iris(
                "SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))"
            ),
            Some(("http://e/A", "http://e/r", "http://e/B"))
        );
    }

    #[test]
    fn cyclic_named_edges_emit_equivalent_peers_without_reflexive_pairs() {
        let text = source(
            3,
            "SubClassOf(<http://e/C0000> <http://e/C0001>)\n\
             SubClassOf(<http://e/C0001> <http://e/C0000>)\n\
             SubClassOf(<http://e/C0001> <http://e/C0002>)\n)\n",
        );
        let result = classify_reader(std::io::Cursor::new(text), 3)
            .unwrap()
            .expect("cyclic flat taxonomy");
        assert_eq!(result.rows.get(&0), Some(&vec![1, 2]));
        assert_eq!(result.rows.get(&1), Some(&vec![0, 2]));
        assert_eq!(result.rows.get(&2), None);
    }

    #[test]
    fn universal_builtin_edges_are_ignored_without_changing_named_closure() {
        let text = source(
            3,
            "SubClassOf(<http://e/C0000> <http://e/C0001>)\n\
             SubClassOf(<http://e/C0001> <http://e/C0000>)\n\
             SubClassOf(<http://e/C0000> owl:Thing)\n\
             SubClassOf(owl:Nothing <http://e/C0000>)\n\
             SubClassOf(owl:Nothing owl:Nothing)\n\
             SubClassOf(owl:Nothing owl:Thing)\n\
             SubClassOf(owl:Thing owl:Thing)\n)\n",
        );
        assert!(flat_source_screen(std::io::Cursor::new(&text)).unwrap());
        let result = classify_reader(std::io::Cursor::new(text), 3)
            .unwrap()
            .expect("flat taxonomy with universal built-in edges");
        assert_eq!(result.rows.get(&0), Some(&vec![1]));
        assert_eq!(result.rows.get(&1), Some(&vec![0]));
        assert_eq!(result.rows.get(&2), None);
    }

    #[test]
    fn semantically_active_builtin_edges_still_decline() {
        for axiom in [
            "SubClassOf(owl:Thing <http://e/C0000>)",
            "SubClassOf(<http://e/C0000> owl:Nothing)",
        ] {
            let text = source(1, &format!("{axiom}\n)\n"));
            assert!(!flat_source_screen(std::io::Cursor::new(&text)).unwrap());
            assert!(classify_reader(std::io::Cursor::new(text), 1)
                .unwrap()
                .is_none());
        }
    }

    #[test]
    fn allocation_free_screen_is_necessary_but_not_sufficient() {
        let flat = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n)\n";
        assert!(flat_source_screen(std::io::Cursor::new(flat)).unwrap());

        let complex_tail = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
SubClassOf(ObjectIntersectionOf(<http://e/A> <http://e/B>) owl:Nothing)\n)\n";
        // The lexical screen admits the proved disjointness syntax; the
        // authoritative graph check rejects this active pair because A reaches
        // both A and B.
        assert!(flat_source_screen(std::io::Cursor::new(complex_tail)).unwrap());
        assert!(classify_reader(std::io::Cursor::new(complex_tail), 2)
            .unwrap()
            .is_none());

        // Duplicate declarations are semantically inert and remain accepted
        // by the authoritative parser.
        let duplicate = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/A>))\n\
SubClassOf(<http://e/A> <http://e/A>)\n)\n";
        assert!(flat_source_screen(std::io::Cursor::new(duplicate)).unwrap());
        assert!(classify_reader(std::io::Cursor::new(duplicate), 1)
            .unwrap()
            .is_some());
    }

    #[test]
    fn pure_leaf_screen_proves_empty_taxonomy_without_a_graph() {
        let leaf = "Prefix(:=<http://e/>)\n\
Ontology(<http://e/o>\n\
Declaration(Class(<http://e/A>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))\n\
)\n";
        // Production requires 1,000 declarations. Repeat the declaration to
        // exercise the threshold without allocating a production-size fixture.
        let leaf = leaf.replacen(
            "Declaration(Class(<http://e/A>))\n",
            &"Declaration(Class(<http://e/A>))\n".repeat(1_000),
            1,
        );
        assert!(pure_leaf_source_screen(std::io::Cursor::new(leaf)).unwrap());

        let named_conclusion = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
)\n";
        assert!(!pure_leaf_source_screen(std::io::Cursor::new(named_conclusion)).unwrap());

        let bottom_filler = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://www.w3.org/2002/07/owl#Nothing>))\n\
)\n";
        assert!(!pure_leaf_source_screen(std::io::Cursor::new(bottom_filler)).unwrap());
    }

    #[test]
    fn canonicalizes_declarations_and_rejects_compound_axioms() {
        let mut ids = HashMap::new();
        let mut names = Vec::new();
        let mut outgoing = Vec::new();
        for iri in ["http://e/B", "http://e/A"] {
            let (_, inserted) = intern_class(iri, &mut ids, &mut names).unwrap();
            if inserted {
                outgoing.push(Vec::new());
            }
        }
        canonicalize_graph(&mut ids, &mut names, &mut outgoing).unwrap();
        assert_eq!(
            names.iter().map(AsRef::as_ref).collect::<Vec<_>>(),
            vec!["http://e/A", "http://e/B"]
        );
        assert_eq!(ids.get("http://e/A"), Some(&0));
        assert!(subclass_iris("SubClassOf(ObjectSomeValuesFrom(<r> <A>) <B>)").is_none());
        assert!(input_format_allows_direct(None));
        assert!(input_format_allows_direct(Some("FUNCTIONAL")));
        assert!(!input_format_allows_direct(Some("rdfxml")));
        assert!(!input_format_allows_direct(Some("unknown")));
        assert!(prefix_declaration("Prefix(:=<http://e/>)"));
        assert!(prefix_declaration(
            "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)"
        ));
        assert!(!prefix_declaration("Prefix(not functional syntax)"));
        assert!(ontology_header("Ontology(<http://e/o>"));
        assert!(ontology_header("Ontology(<http://e/o> <http://e/v1>"));
        assert!(!ontology_header("Ontology(<http://e/o> trailing"));
    }

    #[test]
    fn unsorted_source_is_canonicalized_before_closure() {
        let text = "Ontology(\n\
Declaration(Class(<http://e/C>))\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
SubClassOf(<http://e/B> <http://e/C>)\n)\n";
        let result = classify_reader(std::io::Cursor::new(text), 3)
            .unwrap()
            .expect("strict flat taxonomy");
        assert_eq!(
            result.iris.iter().map(AsRef::as_ref).collect::<Vec<_>>(),
            vec!["http://e/A", "http://e/B", "http://e/C"]
        );
        assert_eq!(result.rows.get(&0), Some(&vec![1, 2]));
    }

    #[test]
    fn existential_leaves_and_positive_rbox_do_not_change_named_closure() {
        let text = "Ontology(\n\
Declaration(Class(<http://e/C>))\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
Declaration(ObjectProperty(<http://e/s>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/C>))\n\
SubObjectPropertyOf(<http://e/r> <http://e/s>)\n\
SubObjectPropertyOf(<http://e/r> owl:topObjectProperty)\n\
SubObjectPropertyOf(ObjectPropertyChain(<http://e/r> <http://e/s>) <http://e/r>)\n\
InverseObjectProperties(<http://e/r> <http://e/s>)\n\
SymmetricObjectProperty(<http://e/s>)\n\
TransitiveObjectProperty(<http://e/r>)\n\
)\n";
        assert!(flat_source_screen(std::io::Cursor::new(text)).unwrap());
        let result = classify_reader(std::io::Cursor::new(text), 3)
            .unwrap()
            .expect("edge-safe existential-leaf source");
        assert_eq!(
            result.iris.iter().map(AsRef::as_ref).collect::<Vec<_>>(),
            vec!["http://e/A", "http://e/B", "http://e/C"]
        );
        assert_eq!(result.rows.get(&0), Some(&vec![1]));
        assert_eq!(result.rows.len(), 1);
        assert_eq!(
            top_role_super_axiom_iri("SubObjectPropertyOf(<http://e/r> owl:topObjectProperty)"),
            Some("http://e/r")
        );
        assert_eq!(
            binary_role_chain_axiom_iris(
                "SubObjectPropertyOf(ObjectPropertyChain(<http://e/r> <http://e/s>) <http://e/r>)"
            ),
            Some(("http://e/r", "http://e/s", "http://e/r"))
        );
    }

    #[test]
    fn inert_disjointness_preserves_closure_and_common_descendant_declines() {
        let inert = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
Declaration(Class(<http://e/C>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
SubClassOf(ObjectIntersectionOf(<http://e/B> <http://e/C>) owl:Nothing)\n\
)\n";
        let result = classify_reader(std::io::Cursor::new(inert), 3)
            .unwrap()
            .expect("inert disjointness");
        assert_eq!(result.rows.get(&0), Some(&vec![1]));
        assert!(result.reachability_graph.is_none());

        let active = inert.replace(
            "ObjectIntersectionOf(<http://e/B> <http://e/C>)",
            "ObjectIntersectionOf(<http://e/A> <http://e/B>)",
        );
        assert!(classify_reader(std::io::Cursor::new(active), 3)
            .unwrap()
            .is_none());
        assert_eq!(
            disjoint_intersection_iris(
                "SubClassOf(ObjectIntersectionOf(<http://e/A> <http://e/B>) owl:Nothing)"
            ),
            Some(("http://e/A", "http://e/B"))
        );

        let complement = inert.replace(
            "SubClassOf(ObjectIntersectionOf(<http://e/B> <http://e/C>) owl:Nothing)",
            "SubClassOf(<http://e/B> ObjectComplementOf(<http://e/C>))",
        );
        let complement_result = classify_reader(std::io::Cursor::new(complement), 3)
            .unwrap()
            .expect("equivalent inert complement spelling");
        assert_eq!(complement_result.rows, result.rows);
        assert_eq!(
            disjoint_complement_iris("SubClassOf(<http://e/A> ObjectComplementOf(<http://e/B>))"),
            Some(("http://e/A", "http://e/B"))
        );

        let source_spelling = inert.replace(
            "SubClassOf(ObjectIntersectionOf(<http://e/B> <http://e/C>) owl:Nothing)",
            "DisjointClasses(<http://e/B> <http://e/C>)",
        );
        let source_result = classify_reader(std::io::Cursor::new(source_spelling), 3)
            .unwrap()
            .expect("inert DisjointClasses spelling");
        assert_eq!(source_result.rows, result.rows);
        assert_eq!(
            disjoint_classes_iris("DisjointClasses(<http://e/A> <http://e/B> <http://e/C>)"),
            Some(vec!["http://e/A", "http://e/B", "http://e/C"])
        );
    }

    #[test]
    fn reflexive_roles_are_inert_in_the_existential_leaf_fragment() {
        let text = "Ontology(\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/B>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
SubClassOf(<http://e/A> <http://e/B>)\n\
SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))\n\
ReflexiveObjectProperty(<http://e/r>)\n\
)\n";
        assert!(flat_source_screen(std::io::Cursor::new(text)).unwrap());
        let result = classify_reader(std::io::Cursor::new(text), 2)
            .unwrap()
            .expect("reflexivity cannot feed a named head in the leaf fragment");
        assert_eq!(result.rows.get(&0), Some(&vec![1]));
        assert_eq!(
            unary_role_axiom_iri("ReflexiveObjectProperty(<http://e/r>)"),
            Some("http://e/r")
        );
    }

    #[test]
    fn existential_leaf_fragment_declines_reverse_restrictions_and_domains() {
        let cases = [
            "Ontology(\nDeclaration(Class(<http://e/A>))\nDeclaration(Class(<http://e/B>))\nDeclaration(ObjectProperty(<http://e/r>))\nSubClassOf(ObjectSomeValuesFrom(<http://e/r> <http://e/A>) <http://e/B>)\n)\n",
            "Ontology(\nDeclaration(Class(<http://e/A>))\nDeclaration(ObjectProperty(<http://e/r>))\nObjectPropertyDomain(<http://e/r> <http://e/A>)\n)\n",
        ];
        for case in cases {
            assert!(classify_reader(std::io::Cursor::new(case), 1)
                .unwrap()
                .is_none());
        }
    }

    #[test]
    fn declarations_are_order_independent_and_optional() {
        let text = "Ontology(\n\
SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))\n\
Declaration(Class(<http://e/A>))\n\
Declaration(Class(<http://e/A>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
)\n";
        let result = classify_reader(std::io::Cursor::new(text), 2)
            .unwrap()
            .expect("declarations do not constrain the logical fragment");
        assert_eq!(
            result.iris.iter().map(AsRef::as_ref).collect::<Vec<_>>(),
            vec!["http://e/A", "http://e/B"]
        );
        assert!(result.rows.is_empty());
    }

    #[test]
    fn positive_nested_leaf_abox_source_has_an_empty_taxonomy_shape() {
        let text = "Prefix(:=<http://e/>)\n\
Ontology(<http://e/o>\n\
Declaration(Class(<http://e/A>))\n\
Declaration(ObjectProperty(<http://e/r>))\n\
SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> \
ObjectIntersectionOf(ObjectSomeValuesFrom(<http://e/s> <http://e/B>) <http://e/C>)))\n\
ClassAssertion(ObjectSomeValuesFrom(<http://e/p> \
ObjectIntersectionOf(ObjectSomeValuesFrom(<http://e/q> <http://e/D>) <http://e/E>)) \
<http://e/a>)\n\
)\n";
        assert!(positive_abox_empty_taxonomy_screen(std::io::Cursor::new(text)).unwrap());
        assert!(positive_leaf_subclass(
            "SubClassOf(<http://e/A> ObjectIntersectionOf(\
ObjectSomeValuesFrom(<http://e/r> <http://e/B>) \
ObjectSomeValuesFrom(<http://e/s> <http://e/C>)))"
        ));
    }

    #[test]
    fn positive_empty_taxonomy_screen_rejects_named_heads_and_negative_shapes() {
        let cases = [
            "Ontology(\nSubClassOf(<http://e/A> <http://e/B>)\n\
ClassAssertion(<http://e/A> <http://e/a>)\n)\n",
            "Ontology(\nSubClassOf(<http://e/A> ObjectIntersectionOf(\
ObjectSomeValuesFrom(<http://e/r> <http://e/B>) <http://e/C>))\n\
ClassAssertion(<http://e/A> <http://e/a>)\n)\n",
            "Ontology(\nSubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))\n\
ClassAssertion(ObjectComplementOf(<http://e/A>) <http://e/a>)\n)\n",
            "Ontology(\nSubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))\n\
ObjectPropertyAssertion(<http://e/r> <http://e/a> <http://e/b>)\n)\n",
            "Ontology(\nSubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> \
<http://www.w3.org/2002/07/owl#Nothing>))\n\
ClassAssertion(<http://e/A> <http://e/a>)\n)\n",
            "Ontology(\nSubClassOf(<http://e/A> ObjectSomeValuesFrom(\
<http://www.w3.org/2002/07/owl#bottomObjectProperty> <http://e/B>))\n\
ClassAssertion(<http://e/A> <http://e/a>)\n)\n",
            "Ontology(\nSubClassOf(<http://www.w3.org/2002/07/owl#Thing> \
ObjectSomeValuesFrom(<http://e/r> <http://e/B>))\n\
ClassAssertion(<http://e/A> <http://e/a>)\n)\n",
            "Ontology(\nDeclaration(Class(<http://www.w3.org/2002/07/owl#Nothing>))\n\
SubClassOf(<http://e/A> ObjectSomeValuesFrom(<http://e/r> <http://e/B>))\n\
ClassAssertion(<http://e/A> <http://e/a>)\n)\n",
        ];
        for case in cases {
            assert!(!positive_abox_empty_taxonomy_screen(std::io::Cursor::new(case)).unwrap());
        }
    }

    #[test]
    fn declines_every_semantically_unsafe_shape() {
        let cases = [
            // Bottom has semantic force beyond graph reachability.
            "Ontology(\nDeclaration(Class(<http://e/A>))\nSubClassOf(<http://e/A> <http://www.w3.org/2002/07/owl#Nothing>)\n)\n",
            // Content after the ontology closes.
            "Ontology(\nDeclaration(Class(<http://e/A>))\nSubClassOf(<http://e/A> <http://e/A>)\n)\nAnnotation(<http://e/p> <http://e/v>)\n",
        ];
        for case in cases {
            assert!(classify_reader(std::io::Cursor::new(case), 1)
                .unwrap()
                .is_none());
        }
    }
}
