//! Entity names in `km classify` output (`--iris source|full`,
//! docs/INPUT-FORMATS.md, "Entity names in output").
//!
//! By default (`source`) every row names an entity as the source wrote it: a
//! prefixed name keeps its prefix (`ex:A`), a full IRI is printed without
//! angle brackets, and an entity written in more than one spelling is printed
//! as its full IRI (docs/REALIZATION.md). Inputs in another syntax are
//! converted to Functional Syntax without prefixes, so their names are full
//! IRIs already.
//!
//! With `full` the CLI passes the finished result through [`FullIris`] right
//! before it writes it: every entity name becomes its full IRI, expanded with
//! the input's own `Prefix` declarations and the four standard prefixes
//! (`owl`, `rdf`, `rdfs`, `xsd`). Each list is then sorted again (and the
//! unordered `SAME` and `DIFFERENT` pairs put in order) by the same string
//! order the writers use, so the output does not depend on how the input
//! spelled its names. Names that are already full IRIs, anonymous
//! individuals and anything with an undeclared prefix stay as they are.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

use super::OrchestrateError;

/// The `--iris` option.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IriMode {
    /// Names as the source spells them (the default).
    Source,
    /// Every name as its full IRI.
    Full,
}

impl IriMode {
    pub fn parse(value: &str) -> Result<Self, String> {
        match value {
            "source" => Ok(IriMode::Source),
            "full" => Ok(IriMode::Full),
            other => Err(format!("--iris takes source or full, got {other:?}")),
        }
    }

    /// `KM_IRIS`, for clients that cannot pass flags; `source` when unset.
    pub fn from_env() -> Result<Self, String> {
        match std::env::var("KM_IRIS") {
            Ok(value) if !value.is_empty() => IriMode::parse(&value),
            _ => Ok(IriMode::Source),
        }
    }
}

/// The prefix map of one input, applied to output names.
pub struct FullIris {
    prefixes: BTreeMap<String, String>,
}

impl FullIris {
    /// The prefixes of `path`: its `Prefix` declarations if it is a
    /// Functional-Syntax document, and the four standard prefixes. Only the
    /// head of the file before the `Ontology` keyword is read.
    pub fn for_input(path: &Path) -> Result<Self, OrchestrateError> {
        let head = super::input::functional_prefix_head(path)?;
        let prefixes = crate::frontend::conformance::prefixes(&head)
            .map_err(OrchestrateError::InvalidOntology)?;
        Ok(FullIris { prefixes })
    }

    #[cfg(test)]
    fn with(prefixes: &[(&str, &str)]) -> Self {
        let mut map = crate::frontend::conformance::prefixes("").unwrap();
        for (name, iri) in prefixes {
            map.insert((*name).to_string(), (*iri).to_string());
        }
        FullIris { prefixes: map }
    }

    /// The full IRI of one printed name. `ObjectInverseOf(r)` (a property
    /// expression of `--properties`) keeps its form with `r` expanded.
    pub fn name(&self, name: &str) -> String {
        if let Some(inner) = name.strip_prefix("ObjectInverseOf(").and_then(|rest| rest.strip_suffix(')')) {
            return format!("ObjectInverseOf({})", self.name(inner));
        }
        if let Some(iri) = name.strip_prefix('<').and_then(|rest| rest.strip_suffix('>')) {
            return iri.to_string();
        }
        let Some((prefix, local)) = name.split_once(':') else {
            return name.to_string();
        };
        // `scheme://...` is a full IRI even if a prefix of that name exists.
        if local.starts_with("//") {
            return name.to_string();
        }
        match self.prefixes.get(prefix) {
            Some(base) => format!("{base}{local}"),
            None => name.to_string(),
        }
    }

    fn list(&self, names: &mut Vec<String>) {
        for name in names.iter_mut() {
            *name = self.name(name);
        }
        names.sort();
        names.dedup();
    }

    fn pairs(&self, pairs: &mut Vec<[String; 2]>, unordered: bool) {
        for pair in pairs.iter_mut() {
            for name in pair.iter_mut() {
                *name = self.name(name);
            }
            if unordered && pair[0] > pair[1] {
                pair.swap(0, 1);
            }
        }
        pairs.sort();
        pairs.dedup();
    }

    fn triples(&self, rows: &mut Vec<[String; 3]>) {
        for row in rows.iter_mut() {
            for name in row.iter_mut() {
                *name = self.name(name);
            }
        }
        rows.sort();
        rows.dedup();
    }

    /// The plain classification (`--lines`, and the JSON of the extended
    /// outputs).
    pub fn classification(&self, c: &mut super::Classification) {
        self.pairs(&mut c.subsumptions, false);
        self.list(&mut c.unsatisfiable);
    }

    /// The JSON classification, including its grouped taxonomy (default
    /// JSON and `--json-edges`). The grouped form is renumbered so that ids
    /// follow the sorted full IRIs, as they follow the sorted names of a
    /// full-IRI input.
    pub fn json(&self, j: &mut super::JsonClassification) {
        self.classification(&mut j.classification);
        let Some(grouped) = j.grouped_subsumptions.as_mut() else { return };
        let names: Vec<String> = grouped.iris.iter().map(|iri| self.name(iri)).collect();
        let mut order: Vec<usize> = (0..names.len()).collect();
        order.sort_by(|&a, &b| names[a].cmp(&names[b]));
        let mut new_id = vec![0u32; names.len()];
        for (position, &old) in order.iter().enumerate() {
            new_id[old] = position as u32;
        }
        let remap = |ids: &[u32]| -> Vec<u32> {
            let mut out: Vec<u32> = ids.iter().map(|&id| new_id[id as usize]).collect();
            out.sort_unstable();
            out.dedup();
            out
        };
        grouped.rows = std::mem::take(&mut grouped.rows)
            .into_iter()
            .map(|(subject, supers)| (new_id[subject as usize], remap(&supers)))
            .collect();
        if let Some(graph) = grouped.reachability_graph.as_mut() {
            let mut renumbered = vec![Vec::new(); graph.len()];
            for (old, successors) in graph.iter().enumerate() {
                renumbered[new_id[old] as usize] = remap(successors);
            }
            *graph = renumbered;
        }
        grouped.iris = order.iter().map(|&old| Arc::from(names[old].as_str())).collect();
    }

    /// Every row of `--realize`, `--values`, `--different`, `--properties`,
    /// `--data-properties` and `--top`.
    pub fn extended(&self, e: &mut super::realize::Extended) {
        self.classification(&mut e.realization.classification);
        self.pairs(&mut e.realization.types, false);
        self.pairs(&mut e.realization.same, true);
        if let Some(p) = e.properties.as_mut() {
            self.pairs(&mut p.sub, false);
            self.list(&mut p.top);
            self.list(&mut p.bottom);
            self.pairs(&mut p.domains, false);
            self.pairs(&mut p.ranges, false);
        }
        if let Some(d) = e.data_properties.as_mut() {
            self.pairs(&mut d.sub, false);
            self.list(&mut d.top);
            self.list(&mut d.bottom);
            self.pairs(&mut d.domains, false);
            self.pairs(&mut d.disjoint, false);
        }
        if let Some(values) = e.abox.values.as_mut() {
            self.triples(values);
        }
        if let Some(different) = e.abox.different.as_mut() {
            self.pairs(different, true);
        }
        if let Some(top) = e.top.as_mut() {
            self.list(top);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_expand_with_declared_and_standard_prefixes_only() {
        let iris = FullIris::with(&[("ex", "http://example.org/"), ("", "urn:t#")]);
        assert_eq!(iris.name("ex:A"), "http://example.org/A");
        assert_eq!(iris.name(":A"), "urn:t#A");
        assert_eq!(iris.name("owl:Thing"), "http://www.w3.org/2002/07/owl#Thing");
        assert_eq!(iris.name("http://example.org/B"), "http://example.org/B");
        assert_eq!(iris.name("urn:t#r"), "urn:t#r");
        assert_eq!(iris.name("<urn:x>"), "urn:x");
        assert_eq!(iris.name("_:b0"), "_:b0");
        assert_eq!(iris.name("ObjectInverseOf(ex:r)"), "ObjectInverseOf(http://example.org/r)");
    }

    #[test]
    fn unordered_pairs_are_reordered_after_expansion() {
        let iris = FullIris::with(&[("z", "http://a.org/"), ("a", "http://z.org/")]);
        let mut same = vec![["a:x".to_string(), "z:y".to_string()]];
        iris.pairs(&mut same, true);
        assert_eq!(same, vec![["http://a.org/y".to_string(), "http://z.org/x".to_string()]]);
    }
}
