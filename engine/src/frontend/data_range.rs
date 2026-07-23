//! Sound detection of data properties with a provably-empty range.
//!
//! Multiple `DataPropertyRange` axioms for one property are conjunctive, so the
//! property's range is their intersection. When two `DataOneOf` ranges have
//! disjoint literal sets the intersection is empty: no value can satisfy the
//! range, so no element may carry a value of the property. We emit the
//! constraint `P(x,y) -> ⊥`, which makes any class forced to have at least one
//! `P`-value (`DataSomeValuesFrom`, `DataHasValue`, `DataMin`/`DataExact`
//! cardinality with n >= 1) unsatisfiable, while leaving `DataAllValuesFrom`
//! and `DataMax` untouched (they impose no value).
//!
//! Sound by construction. Full typed/language literal tokens are retained.
//! Two finite ranges are declared disjoint only when the exact datatype-value
//! oracle proves every cross-pair unequal. Any unsupported canonicalisation
//! (including XML whitespace collapse and IEEE float rounding) blocks the
//! certificate. `DataPropertyRange` axioms are otherwise dropped (the datatype
//! over-approximation in `parse`), so collecting them here changes no other
//! clause. To keep the internal-name assignment order identical to a run
//! without any empty range, the property IRI is resolved (`reg.short`) only
//! when a constraint is actually emitted.

use std::collections::{HashMap, HashSet};

use super::clauses::{constraint, var_x, var_y, Atom, DLClause};
use super::iri::IriRegistry;
use super::parse::strip_annotations;
use super::sexpr::Node;

#[derive(Default)]
pub struct DataRanges {
    /// raw property IRI -> one literal set per `DataPropertyRange(P DataOneOf)`.
    one_of: HashMap<String, Vec<HashSet<String>>>,
}

impl DataRanges {
    /// Record the literal set if `node` is `DataPropertyRange(P DataOneOf(...))`.
    /// Stores the raw IRI (no `reg` interaction) so the name-assignment order is
    /// untouched for ontologies that turn out to have no empty range.
    pub fn observe(&mut self, node: &Node) {
        let args = match node {
            Node::List("DataPropertyRange", args) => strip_annotations(args),
            _ => return,
        };
        if args.len() < 2 {
            return;
        }
        let prop = match args[0].as_atom() {
            Some(s) => s,
            None => return,
        };
        if let Node::List("DataOneOf", lits) = args[1] {
            let refs: Vec<&Node> = lits.iter().collect();
            let mut set = HashSet::new();
            let mut complete = true;
            let mut index = 0;
            while index < refs.len() {
                let Some((literal, used)) = super::parse::glue_literal(&refs, index) else {
                    complete = false;
                    break;
                };
                set.insert(literal);
                index += used;
            }
            if complete && !set.is_empty() {
                self.one_of.entry(prop.to_string()).or_default().push(set);
            }
        }
    }

    /// `P(x,y) -> ⊥` for every property whose `DataOneOf` ranges have an empty
    /// mutual intersection (>= 2 such ranges required: a single `DataOneOf` is a
    /// non-empty range). The property name is resolved through `reg`, returning
    /// the name already assigned in pass 1 when the property is used in a
    /// restriction (the only case in which the constraint has a consumer).
    pub fn empty_range_constraints(&self, reg: &mut IriRegistry) -> Vec<DLClause> {
        let mut out = Vec::new();
        for (prop, sets) in &self.one_of {
            if sets.len() < 2 {
                continue;
            }
            let disjoint_pair = sets.iter().enumerate().any(|(index, left)| {
                sets.iter().skip(index + 1).any(|right| {
                    left.iter().all(|left_value| {
                        right.iter().all(|right_value| {
                            super::datatypes::exact_literal_value_equal(left_value, right_value)
                                == Some(false)
                        })
                    })
                })
            });
            if disjoint_pair {
                let name = reg.short(prop);
                out.push(constraint([Atom::Role(name, var_x(), var_y())]));
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::super::sexpr::Parser;
    use super::*;

    fn parse_one(text: &str) -> Node<'_> {
        Parser::new(text).parse().unwrap()
    }

    fn observe_all(dr: &mut DataRanges, texts: &[&str]) {
        for t in texts {
            dr.observe(&parse_one(t));
        }
    }

    #[test]
    fn disjoint_dataoneof_ranges_are_empty() {
        let mut dr = DataRanges::default();
        observe_all(
            &mut dr,
            &[
                "DataPropertyRange(P DataOneOf(\"a\"^^xsd:string \"b\"^^xsd:string))",
                "DataPropertyRange(P DataOneOf(\"c\"^^xsd:string \"d\"^^xsd:string))",
            ],
        );
        let mut reg = IriRegistry::new();
        let cs = dr.empty_range_constraints(&mut reg);
        assert_eq!(cs.len(), 1);
        assert!(cs[0].head.is_empty());
        assert!(matches!(cs[0].body[0], Atom::Role(..)));
    }

    #[test]
    fn overlapping_dataoneof_ranges_are_nonempty() {
        let mut dr = DataRanges::default();
        observe_all(
            &mut dr,
            &[
                "DataPropertyRange(P DataOneOf(\"a\"^^xsd:string \"b\"^^xsd:string))",
                "DataPropertyRange(P DataOneOf(\"b\"^^xsd:string \"c\"^^xsd:string))",
            ],
        );
        let mut reg = IriRegistry::new();
        assert!(dr.empty_range_constraints(&mut reg).is_empty());
    }

    #[test]
    fn equal_values_with_alternative_lexical_forms_block_emptiness() {
        for ranges in [
            [
                "DataPropertyRange(P DataOneOf(\"1\"^^xsd:boolean))",
                "DataPropertyRange(P DataOneOf(\"true\"^^xsd:boolean))",
            ],
            [
                "DataPropertyRange(P DataOneOf(\"5\"^^xsd:integer))",
                "DataPropertyRange(P DataOneOf(\"05\"^^xsd:integer))",
            ],
            [
                "DataPropertyRange(P DataOneOf(\"a  b\"^^xsd:token))",
                "DataPropertyRange(P DataOneOf(\"a b\"^^xsd:string))",
            ],
            [
                "DataPropertyRange(P DataOneOf(\"1\"^^ex:boolean))",
                "DataPropertyRange(P DataOneOf(\"true\"^^ex:boolean))",
            ],
        ] {
            let mut dr = DataRanges::default();
            observe_all(&mut dr, &ranges);
            let mut reg = IriRegistry::new();
            assert!(
                dr.empty_range_constraints(&mut reg).is_empty(),
                "equal or unknown value intersection was declared empty: {ranges:?}"
            );
        }
    }

    #[test]
    fn single_dataoneof_range_is_nonempty() {
        let mut dr = DataRanges::default();
        observe_all(
            &mut dr,
            &["DataPropertyRange(P DataOneOf(\"a\"^^xsd:string))"],
        );
        let mut reg = IriRegistry::new();
        assert!(dr.empty_range_constraints(&mut reg).is_empty());
    }
}
