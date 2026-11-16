//! Entailed object property values and different individuals between named
//! individuals (W5b, `km classify --values`, `--different`).
//!
//! # Semantics
//!
//! For a consistent ontology `O`, named individuals `a`, `b` and a named
//! object property `r` of the source (not `owl:topObjectProperty` or
//! `owl:bottomObjectProperty`):
//!
//! * `VALUE r a b` iff `O ⊨ r(a, b)`;
//! * `DIFFERENT a b` iff `O ⊨ a ≠ b`, once per pair with `a < b`.
//!
//! # Mechanism
//!
//! The realization run's probes `P_a ≡ {a}` plus, for every property `r` and
//! individual `b`, a fresh class `V_rb ≡ ∃r.{b}` (`--values`) and, for every
//! individual `b`, `N_b ≡ ¬{b}` (`--different`). The extension only defines
//! fresh names, so it is conservative, and `O ⊨ r(a, b)` iff `{a} ⊑ ∃r.{b}`
//! iff `P_a ⊑ V_rb`, and `O ⊨ a ≠ b` iff `{a} ⊑ ¬{b}` iff `P_a ⊑ N_b`. All
//! pairs come from the one classification of the extended ontology that the
//! realization already needs, instead of one consistency test per pair.

use std::collections::{BTreeMap, BTreeSet};

use super::realize::{fresh_namespace_for, public_name};
use super::{Classification, OrchestrateError};

/// The rows of `--values` and `--different`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AboxRows {
    /// `[r, a, b]` rows, sorted; present iff `--values`.
    pub values: Option<Vec<[String; 3]>>,
    /// `[a, b]` rows with `a < b`, sorted; present iff `--different`.
    pub different: Option<Vec<[String; 2]>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Probe {
    Value(usize, usize),
    Not(usize),
}

/// The probe classes of one extension.
#[derive(Clone, Debug)]
pub struct AboxProbes {
    probes: BTreeMap<String, Probe>,
    roles: Vec<String>,
    individuals: Vec<String>,
    values: bool,
    different: bool,
}

impl AboxProbes {
    pub(super) fn is_probe(&self, name: &str) -> bool {
        self.probes.contains_key(name)
    }
}

/// The probe axioms for `roles` and `individuals` (source spellings).
pub(super) fn extension(
    text: &str,
    roles: &[String],
    individuals: &[String],
    values: bool,
    different: bool,
) -> (String, AboxProbes) {
    let ns = fresh_namespace_for(text, "aboxrows");
    let mut out = String::new();
    let mut probes = BTreeMap::new();
    if values {
        for (r, role) in roles.iter().enumerate() {
            for (b, individual) in individuals.iter().enumerate() {
                let probe = format!("{ns}value{r}_{b}");
                out.push_str(&format!(
                    "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectSomeValuesFrom({role} ObjectOneOf({individual})))\n"
                ));
                probes.insert(probe, Probe::Value(r, b));
            }
        }
    }
    if different {
        for (b, individual) in individuals.iter().enumerate() {
            let probe = format!("{ns}not{b}");
            out.push_str(&format!(
                "Declaration(Class(<{probe}>))\nEquivalentClasses(<{probe}> ObjectComplementOf(ObjectOneOf({individual})))\n"
            ));
            probes.insert(probe, Probe::Not(b));
        }
    }
    let probes = AboxProbes {
        probes,
        roles: roles.iter().map(|r| public_name(r)).collect(),
        individuals: individuals.iter().map(|a| public_name(a)).collect(),
        values,
        different,
    };
    (out, probes)
}

/// Remove the probes from the classification and read the rows off the
/// subsumptions `P_a ⊑ probe`. `individual_of` maps the realization probe
/// class of each individual to its public name.
pub(super) fn split(
    extended: &mut Classification,
    probes: &AboxProbes,
    individual_of: &BTreeMap<String, String>,
) -> Result<AboxRows, OrchestrateError> {
    let probe = |name: &str| probes.probes.get(name).copied();
    let unsatisfiable: Vec<Probe> = extended.unsatisfiable.iter().filter_map(|n| probe(n)).collect();
    extended.unsatisfiable.retain(|name| probe(name).is_none());
    let mut values = BTreeSet::new();
    let mut different = BTreeSet::new();
    extended.subsumptions.retain(|[low, high]| {
        let (low_probe, high_probe) = (probe(low), probe(high));
        if low_probe.is_none() && high_probe.is_none() {
            return true;
        }
        if let (Some(a), Some(p)) = (individual_of.get(low), high_probe) {
            match p {
                Probe::Value(r, b) => {
                    values.insert([probes.roles[r].clone(), a.clone(), probes.individuals[b].clone()]);
                }
                Probe::Not(b) => {
                    let b = &probes.individuals[b];
                    if a != b {
                        let (x, y) = if a < b { (a, b) } else { (b, a) };
                        different.insert([x.clone(), y.clone()]);
                    }
                }
            }
        }
        false
    });
    if extended.consistent && unsatisfiable.iter().any(|p| matches!(p, Probe::Not(_))) {
        // `¬{b}` is unsatisfiable only when the domain is `{b}`; then no
        // other individual is different from `b`, and the rows above are
        // already right. Nothing to report.
    }
    Ok(AboxRows {
        values: probes.values.then(|| values.into_iter().collect()),
        different: probes.different.then(|| different.into_iter().collect()),
    })
}
