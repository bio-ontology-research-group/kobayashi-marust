//! Collision-safe IRI -> internal-name registry.
//!
//! Direct port of `frontend._short_base`, `short`, `full_iri`, `is_named_iri`,
//! `local_name` and the `_short_iri` / `_short_owner` maps. The registry is
//! reset per ontology (`reset_short` in Python; a fresh `IriRegistry` here).

use std::collections::HashMap;

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
        let base = short_base(name);
        if base == "owl:Thing" || base == "owl:Nothing" {
            // specials: never disambiguate
            self.short_iri.insert(full, base.clone());
            return base;
        }
        let mut cand = base.clone();
        if let Some(owner) = self.short_owner.get(&cand) {
            if owner != &full {
                // collision with a different IRI
                let ns: &str = full[..full.len() - base.len()].trim_end_matches(['#', '/', ':']);
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
