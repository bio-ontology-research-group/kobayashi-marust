//! Provably empty and provably universal data ranges.
//!
//! The `__dt__` abstraction gives every data range its own concept label and
//! relates labels only pairwise (`datatype_relation_clauses`). A range whose
//! value space is empty, such as `DataComplementOf(rdfs:Literal)`,
//! `DataIntersectionOf(xsd:integer xsd:string)` or a facet interval with
//! crossed bounds, carries a label that no clause forbids, so `∃p.R`,
//! `≥n p.R` and `∀p.R ⊓ ∃p.⊤` stayed satisfiable. Dually, a range equal to
//! the whole data domain, such as `rdfs:Literal` or
//! `DataUnionOf(D DataComplementOf(D))`, carries a label that no clause
//! forces, so `∀p.R` was not `⊤` and `≤n p.R` was not `≤n p`.
//!
//! [`data_range_extent`] decides these two cases from the source structure
//! of the range. The decision is sound: `Some(Empty)` only when no data value
//! lies in the range under the OWL 2 datatype map, `Some(Universal)` only when
//! every data value does. Anything the datatype oracle cannot decide yields
//! `None`, which keeps the ordinary label encoding.
use super::{enumerate_range, range_disjoint, range_from_node, range_subsumed,
    val_in_range, DRange, Node, Parser};

/// The value space of a data range, when it is one of the two trivial ones.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DataExtent {
    /// No data value lies in the range (the range is `⊥` on data values).
    Empty,
    /// Every data value lies in the range (the range is `rdfs:Literal`).
    Universal,
}

/// Recursion guard. Each step descends into a strict subterm, so the bound
/// only limits work on deeply nested ranges; hitting it answers "unknown".
const MAX_DEPTH: usize = 32;
/// Finite enumeration width for subset tests such as `xsd:boolean ⊆ {true, false}`.
const ENUMERATION_CAP: usize = 64;

/// Extent of a data-range source node (named datatype or complex range).
pub(crate) fn data_range_extent(node: &Node) -> Option<DataExtent> {
    if empty(node, 0) {
        Some(DataExtent::Empty)
    } else if universal(node, 0) {
        Some(DataExtent::Universal)
    } else {
        None
    }
}

/// Extent of an internal `__dt__` range concept (`__dt__<named>` or
/// `__dt__c__<canonical text>`). Value concepts (`__dt__val__…`) are
/// singletons and never trivial.
pub(crate) fn data_concept_extent(name: &str) -> Option<DataExtent> {
    let rest = name.strip_prefix("__dt__")?;
    if rest.starts_with("val__") {
        return None;
    }
    if let Some(text) = rest.strip_prefix("c__") {
        let node = Parser::new(text).parse().ok()?;
        return data_range_extent(&node);
    }
    matches!(rest, "Literal" | "rdfs:Literal").then_some(DataExtent::Universal)
}

fn args<'n, 'a>(node: &'n Node<'a>, head: &str) -> Option<&'n [Node<'a>]> {
    match node {
        Node::List(h, args) if *h == head => Some(args),
        _ => None,
    }
}

fn complement_of<'n, 'a>(node: &'n Node<'a>) -> Option<&'n Node<'a>> {
    match args(node, "DataComplementOf") {
        Some([inner]) => Some(inner),
        _ => None,
    }
}

/// Emptiness of a single (non-boolean) range as decided by the datatype map.
fn leaf_empty(range: &DRange) -> bool {
    match range {
        DRange::Float(r) => r.empty(),
        DRange::OneOf(values) => values.is_empty(),
        DRange::Num(_) => num_bounds_cross(range),
        _ => false,
    }
}

/// A rational facet interval whose bounds exclude every number.
fn num_bounds_cross(range: &DRange) -> bool {
    let DRange::Num(r) = range else { return false };
    if r.integral {
        return matches!(super::integral_interval(range), Some((Some(lo), Some(hi))) if lo > hi);
    }
    match (&r.min, &r.max) {
        (Some((lo, lo_inclusive)), Some((hi, hi_inclusive))) => match super::rat_cmp(lo, hi) {
            Some(std::cmp::Ordering::Greater) => true,
            Some(std::cmp::Ordering::Equal) => !(*lo_inclusive && *hi_inclusive),
            _ => false,
        },
        _ => false,
    }
}

/// `true` only when the range provably contains no data value.
fn empty(node: &Node, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return false;
    }
    if let Some(inner) = complement_of(node) {
        return universal(inner, depth + 1);
    }
    if let Some(members) = args(node, "DataUnionOf") {
        return !members.is_empty() && members.iter().all(|m| empty(m, depth + 1));
    }
    if let Some(members) = args(node, "DataIntersectionOf") {
        return members.iter().any(|m| empty(m, depth + 1))
            || members.iter().enumerate().any(|(i, left)| {
                members.iter().skip(i + 1).any(|right| disjoint(left, right, depth + 1))
            })
            || finite_intersection_empty(members);
    }
    if let Some(literals) = args(node, "DataOneOf") {
        // `DataOneOf()` lists no value. Non-empty lists denote their values.
        if literals.is_empty() {
            return true;
        }
    }
    leaf_empty(&range_from_node(node))
}

/// The values of a finite range (an enumeration, or a small named or
/// facet-restricted range), when the datatype oracle can list them.
fn finite_values(range: &DRange) -> Option<Vec<super::Val>> {
    match range {
        DRange::OneOf(values) => Some(values.clone()),
        _ => enumerate_range(range, ENUMERATION_CAP)?
            .iter()
            .map(|literal| super::parse_literal(literal).map(|(value, _)| value))
            .collect(),
    }
}

/// An intersection with a finite member is empty when each of that member's
/// values is provably outside some other member (e.g. `[1,2] ∩ ¬{1} ∩ ¬{2}`,
/// which no pair of members decides).
fn finite_intersection_empty(members: &[Node]) -> bool {
    let ranges: Vec<DRange> = members.iter().map(range_from_node).collect();
    ranges.iter().enumerate().any(|(i, range)| {
        finite_values(range).is_some_and(|values| {
            values.iter().all(|value| {
                ranges.iter().enumerate()
                    .any(|(j, other)| i != j && val_in_range(value, other) == Some(false))
            })
        })
    })
}

/// `true` only when every data value lies in the range.
fn universal(node: &Node, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return false;
    }
    if let Some(inner) = complement_of(node) {
        return empty(inner, depth + 1);
    }
    if let Some(members) = args(node, "DataUnionOf") {
        return union_universal(members, depth + 1);
    }
    if let Some(members) = args(node, "DataIntersectionOf") {
        return !members.is_empty() && members.iter().all(|m| universal(m, depth + 1));
    }
    matches!(range_from_node(node), DRange::Top)
}

/// `⋃ members` is the whole data domain: some member is, or the union holds
/// a complement `¬x` together with a member `m ⊇ x` (then `¬x ∪ m ⊇ ¬x ∪ x`).
fn union_universal(members: &[Node], depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return false;
    }
    members.iter().any(|m| universal(m, depth + 1))
        || members.iter().enumerate().any(|(i, member)| {
            complement_of(member).is_some_and(|excluded| {
                members.iter().enumerate()
                    .any(|(j, other)| i != j && subset(excluded, other, depth + 1))
            })
        })
}

/// `true` only when `left ∩ right` is provably empty.
fn disjoint(left: &Node, right: &Node, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return false;
    }
    if empty(left, depth + 1) || empty(right, depth + 1) {
        return true;
    }
    match (complement_of(left), complement_of(right)) {
        // `¬x ∩ ¬y = ¬(x ∪ y)` is empty when `x ∪ y` is universal.
        (Some(x), Some(y)) => union_universal(&[x.clone(), y.clone()], depth + 1),
        (Some(x), None) => subset(right, x, depth + 1),
        (None, Some(y)) => subset(left, y, depth + 1),
        (None, None) => {
            if let Some(members) = args(left, "DataUnionOf") {
                return members.iter().all(|m| disjoint(m, right, depth + 1));
            }
            if let Some(members) = args(right, "DataUnionOf") {
                return members.iter().all(|m| disjoint(left, m, depth + 1));
            }
            if let Some(members) = args(left, "DataIntersectionOf") {
                return members.iter().any(|m| disjoint(m, right, depth + 1));
            }
            if let Some(members) = args(right, "DataIntersectionOf") {
                return members.iter().any(|m| disjoint(left, m, depth + 1));
            }
            range_disjoint(&range_from_node(left), &range_from_node(right)) == Some(true)
        }
    }
}

/// `true` only when `left ⊆ right` provably holds.
fn subset(left: &Node, right: &Node, depth: usize) -> bool {
    if depth > MAX_DEPTH {
        return false;
    }
    if empty(left, depth + 1) || universal(right, depth + 1) {
        return true;
    }
    if let Some(excluded) = complement_of(right) {
        return disjoint(left, excluded, depth + 1);
    }
    if let Some(excluded) = complement_of(left) {
        // `¬x ⊆ r` iff `x ∪ r` is universal.
        return union_universal(&[excluded.clone(), right.clone()], depth + 1);
    }
    if let Some(members) = args(left, "DataUnionOf") {
        return members.iter().all(|m| subset(m, right, depth + 1));
    }
    if let Some(members) = args(right, "DataIntersectionOf") {
        return members.iter().all(|m| subset(left, m, depth + 1));
    }
    if let Some(members) = args(left, "DataIntersectionOf") {
        if members.iter().any(|m| subset(m, right, depth + 1)) {
            return true;
        }
    }
    if let Some(members) = args(right, "DataUnionOf") {
        if members.iter().any(|m| subset(left, m, depth + 1)) {
            return true;
        }
    }
    let (inner, outer) = (range_from_node(left), range_from_node(right));
    if range_subsumed(&inner, &outer) == Some(true) {
        return true;
    }
    // A finite range lies inside `outer` when each of its values does.
    finite_values(&inner)
        .is_some_and(|values| values.iter().all(|value| val_in_range(value, &outer) == Some(true)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn extent(text: &str) -> Option<DataExtent> {
        data_range_extent(&Parser::new(text).parse().unwrap())
    }

    #[test]
    fn empty_ranges_are_decided() {
        for text in [
            "DataComplementOf(rdfs:Literal)",
            "DataIntersectionOf(xsd:integer xsd:string)",
            "DataIntersectionOf(xsd:integer DataComplementOf(xsd:integer))",
            "DatatypeRestriction(xsd:integer xsd:minInclusive \"5\"^^xsd:integer xsd:maxInclusive \"3\"^^xsd:integer)",
            "DatatypeRestriction(xsd:decimal xsd:minExclusive \"1\"^^xsd:decimal xsd:maxExclusive \"1\"^^xsd:decimal)",
            "DataIntersectionOf(DataOneOf(\"1\"^^xsd:integer) DataOneOf(\"2\"^^xsd:integer))",
            "DataComplementOf(DataUnionOf(xsd:string DataComplementOf(xsd:string)))",
            "DataUnionOf(DataComplementOf(rdfs:Literal) DataIntersectionOf(xsd:boolean xsd:integer))",
            "DataIntersectionOf(xsd:boolean DataComplementOf(DataOneOf(\"true\"^^xsd:boolean \"false\"^^xsd:boolean)))",
            "DataOneOf()",
            "DataIntersectionOf(DataComplementOf(xsd:integer) DataComplementOf(DataComplementOf(xsd:integer)))",
            "DataIntersectionOf(DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer \
             xsd:maxInclusive \"2\"^^xsd:integer) DataComplementOf(DataOneOf(\"1\"^^xsd:integer)) \
             DataComplementOf(DataOneOf(\"2\"^^xsd:integer)))",
        ] {
            assert_eq!(extent(text), Some(DataExtent::Empty), "{text}");
        }
    }

    #[test]
    fn universal_ranges_are_decided() {
        for text in [
            "rdfs:Literal",
            "<http://www.w3.org/2000/01/rdf-schema#Literal>",
            "DataComplementOf(DataComplementOf(rdfs:Literal))",
            "DataUnionOf(xsd:integer DataComplementOf(xsd:integer))",
            "DataComplementOf(DataIntersectionOf(xsd:integer xsd:string))",
            "DataUnionOf(xsd:string rdfs:Literal)",
            "DataUnionOf(DataComplementOf(xsd:int) xsd:integer)",
        ] {
            assert_eq!(extent(text), Some(DataExtent::Universal), "{text}");
        }
    }

    #[test]
    fn ordinary_and_undecided_ranges_are_left_alone() {
        for text in [
            "xsd:integer",
            "xsd:string",
            "DataComplementOf(xsd:integer)",
            "DataOneOf(\"1\"^^xsd:integer)",
            "DataIntersectionOf(xsd:integer xsd:int)",
            "DataUnionOf(xsd:integer xsd:string)",
            // `xsd:integer ⊄ xsd:int`, so the union is not the whole domain.
            "DataUnionOf(DataComplementOf(xsd:integer) xsd:int)",
            "DataIntersectionOf(DatatypeRestriction(xsd:integer xsd:minInclusive \"1\"^^xsd:integer \
             xsd:maxInclusive \"3\"^^xsd:integer) DataComplementOf(DataOneOf(\"1\"^^xsd:integer)) \
             DataComplementOf(DataOneOf(\"2\"^^xsd:integer)))",
            "DatatypeRestriction(xsd:integer xsd:minInclusive \"3\"^^xsd:integer xsd:maxInclusive \"3\"^^xsd:integer)",
            "DatatypeRestriction(xsd:string xsd:pattern \"[a-z]+\")",
            "DataIntersectionOf(xsd:string DatatypeRestriction(xsd:string xsd:pattern \"x\"))",
            "<http://example.org/UnknownDatatype>",
            "DataComplementOf(<http://example.org/UnknownDatatype>)",
            "rdf:PlainLiteral",
            "DataComplementOf(rdf:PlainLiteral)",
        ] {
            assert_eq!(extent(text), None, "{text}");
        }
    }

    #[test]
    fn internal_concept_names_are_decided() {
        assert_eq!(data_concept_extent("__dt__Literal"), Some(DataExtent::Universal));
        assert_eq!(data_concept_extent("__dt__c__DataComplementOf(rdfs:Literal)"), Some(DataExtent::Empty));
        assert_eq!(data_concept_extent("__dt__integer"), None);
        assert_eq!(data_concept_extent("__dt__val__\"1\"^^xsd:integer"), None);
        assert_eq!(data_concept_extent("A"), None);
    }
}
