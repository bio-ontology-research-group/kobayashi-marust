//! Collision-safe IRI -> internal-name registry.
//!
//! Direct port of `frontend._short_base`, `short`, `full_iri`, `is_named_iri`,
//! `local_name` and the `_short_iri` / `_short_owner` maps. The registry is
//! reset per ontology (`reset_short` in Python; a fresh `IriRegistry` here).

use std::collections::HashMap;

const OWL_THING_IRI: &str = "http://www.w3.org/2002/07/owl#Thing";
const OWL_NOTHING_IRI: &str = "http://www.w3.org/2002/07/owl#Nothing";

/// Return KM's canonical spelling for an actual OWL top/bottom IRI.
///
/// This tests the complete source token rather than its local name. A non-OWL
/// class IRI may legally end in `#Thing` or `#Nothing` and must remain named.
fn owl_builtin_class(name: &str) -> Option<&'static str> {
    let raw = name.trim();
    let raw = raw
        .strip_prefix('<')
        .and_then(|s| s.strip_suffix('>'))
        .unwrap_or(raw);
    match raw {
        "owl:Thing" | OWL_THING_IRI => Some("owl:Thing"),
        "owl:Nothing" | OWL_NOTHING_IRI => Some("owl:Nothing"),
        _ => None,
    }
}

/// Fragment / local-name of an IRI. Port of `_short_base`. NOT collision-safe
/// on its own; `IriRegistry::short` disambiguates collisions.
pub fn short_base(name: &str) -> String {
    let name = name.trim();
    let name = if name.starts_with('<') && name.ends_with('>') {
        &name[1..name.len() - 1]
    } else {
        name
    };
    if let Some(idx) = name.rfind('#') {
        return name[idx + 1..].to_string();
    }
    if let Some(stripped) = name.strip_prefix(':') {
        return stripped.to_string();
    }
    if name.starts_with("owl:") {
        return name.to_string(); // keep owl:Thing / owl:Nothing for special-casing
    }
    if name.contains('/') && name.contains("://") {
        if let Some(idx) = name.rfind('/') {
            return name[idx + 1..].to_string();
        }
    }
    if let Some(idx) = name.find(':') {
        // other prefixed name pfx:Local
        return name[idx + 1..].to_string();
    }
    name.to_string()
}

/// Per-ontology IRI -> internal-name registry. Port of the module-level
/// `_short_iri` / `_short_owner` dicts plus `reset_short`/`short`/`full_iri`/
/// `is_named_iri`/`local_name`.
#[derive(Default)]
pub struct IriRegistry {
    /// full IRI -> assigned unique short name
    short_iri: HashMap<String, String>,
    /// short name -> full IRI that owns it
    short_owner: HashMap<String, String>,
}

impl IriRegistry {
    pub fn new() -> Self {
        IriRegistry::default()
    }

    /// Port of `short`. Distinct full IRIs always get distinct internal names;
    /// unique local names are returned unchanged.
    pub fn short(&mut self, name: &str) -> String {
        let raw = name.trim();
        let full = if raw.starts_with('<') && raw.ends_with('>') {
            raw[1..raw.len() - 1].to_string()
        } else {
            raw.to_string()
        };
        if let Some(cached) = self.short_iri.get(&full) {
            return cached.clone();
        }
        if let Some(builtin) = owl_builtin_class(name) {
            // Builtins are semantic constants rather than source-owned named
            // classes. Canonicalise both abbreviated and full spellings.
            self.short_iri.insert(full, builtin.to_string());
            return builtin.to_string();
        }
        let raw_base = short_base(name);
        // Source IRIs and generated concepts are different symbol kinds in
        // Sequoia. KM historically encoded that distinction through prefixes,
        // so a legal source class such as `#__A` was mistaken for an auxiliary:
        // no query context was created and definer preprocessing could rewrite
        // it. Escape only registry-owned source names; generated symbols never
        // pass through this registry. The inverse `full_iri` mapping preserves
        // the exact public IRI.
        let base = if reserved_internal_prefix(&raw_base) {
            format!("km_src_{raw_base}")
        } else {
            raw_base.clone()
        };
        let mut cand = base.clone();
        if let Some(owner) = self.short_owner.get(&cand) {
            if owner != &full {
                // collision with a different IRI
                // `base` may be the escaped spelling, which is not a suffix of
                // the source IRI. Namespace extraction must use `raw_base`.
                let ns: &str = full[..full.len().saturating_sub(raw_base.len())]
                    .trim_end_matches(['#', '/', ':']);
                let tag = {
                    let t = short_base(ns);
                    if t.is_empty() {
                        "ns".to_string()
                    } else {
                        t
                    }
                };
                cand = format!("{}__{}", base, tag);
                let mut i = 2;
                // while _short_owner.get(cand, full) != full
                while self
                    .short_owner
                    .get(&cand)
                    .map(|s| s.as_str())
                    .unwrap_or(full.as_str())
                    != full.as_str()
                {
                    cand = format!("{}__{}{}", base, tag, i);
                    i += 1;
                }
            }
        }
        self.short_owner.insert(cand.clone(), full.clone());
        self.short_iri.insert(full, cand.clone());
        cand
    }

    /// Port of `full_iri`: internal name -> full IRI, identity if unregistered.
    pub fn full_iri(&self, internal: &str) -> String {
        self.short_owner
            .get(internal)
            .cloned()
            .unwrap_or_else(|| internal.to_string())
    }

    /// Port of `is_named_iri`: true iff `internal` names a real OWL IRI.
    pub fn is_named_iri(&self, internal: &str) -> bool {
        self.short_owner.contains_key(internal)
    }

    /// All internal short names registered to a real IRI (keys of `_short_owner`).
    pub fn owned_names(&self) -> Vec<String> {
        self.short_owner.keys().cloned().collect()
    }
}

fn reserved_internal_prefix(name: &str) -> bool {
    matches!(name, "Thing" | "Nothing" | "owl:Thing" | "owl:Nothing")
        || name.starts_with("Q_")
        || name.starts_with("__")
        || name.starts_with("_aux")
        || name.starts_with("aux_")
        || name.starts_with("def_")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_names_that_look_generated_are_typed_as_named() {
        let mut reg = IriRegistry::new();
        for local in ["__A", "Q_7", "_auxA", "aux_A", "def_A"] {
            let full = format!("http://example.org#{local}");
            let internal = reg.short(&format!("<{full}>"));
            assert!(internal.starts_with("km_src_"), "{local} -> {internal}");
            assert!(!reserved_internal_prefix(&internal));
            assert_eq!(reg.full_iri(&internal), full);
            assert!(reg.is_named_iri(&internal));
        }
    }

    #[test]
    fn escaped_source_name_remains_collision_safe() {
        let mut reg = IriRegistry::new();
        let ordinary = reg.short("<http://first.example#km_src___A>");
        let escaped = reg.short("<http://second.example#__A>");
        assert_ne!(ordinary, escaped);
        assert!(!reserved_internal_prefix(&escaped));
        assert_eq!(reg.full_iri(&ordinary), "http://first.example#km_src___A");
        assert_eq!(reg.full_iri(&escaped), "http://second.example#__A");
    }

    #[test]
    fn only_actual_owl_thing_and_nothing_are_builtins() {
        let mut reg = IriRegistry::new();
        for (source, canonical) in [
            ("owl:Thing", "owl:Thing"),
            ("<http://www.w3.org/2002/07/owl#Thing>", "owl:Thing"),
            ("owl:Nothing", "owl:Nothing"),
            ("<http://www.w3.org/2002/07/owl#Nothing>", "owl:Nothing"),
        ] {
            let internal = reg.short(source);
            assert_eq!(internal, canonical, "{source}");
            assert!(!reg.is_named_iri(&internal), "{source} is a builtin");
        }
    }

    #[test]
    fn non_owl_thing_and_nothing_local_names_remain_named() {
        let mut reg = IriRegistry::new();
        for source in [
            "<http://example.org#Thing>",
            "<http://example.org#Nothing>",
            "example:Thing",
            "example:Nothing",
            "<http://example.org#owl:Thing>",
            "<http://example.org#owl:Nothing>",
        ] {
            let full = source.trim_matches(['<', '>']);
            let internal = reg.short(source);
            assert!(internal.starts_with("km_src_"), "{source} -> {internal}");
            assert_ne!(internal, "owl:Thing");
            assert_ne!(internal, "owl:Nothing");
            assert_eq!(reg.full_iri(&internal), full);
            assert!(reg.is_named_iri(&internal));
        }
    }
}
