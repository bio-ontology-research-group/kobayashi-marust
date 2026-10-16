//! Small exact-source support proposals for inconsistent initial revisions.
//!
//! These heuristics do not certify inconsistency. The retained-session caller
//! must independently classify the proposed source subset before reusing it.

mod data;
mod rules;
mod object;

/// Object-only optional proposal for the admitted-source early verifier.
/// Returned supports never authorize publication without independent checking.
pub(crate) fn propose_object(text: &str, scan: &crate::source_locality::Scan) -> Option<Vec<u128>> {
    if text.len() > 4 << 20 { return None; }
    object::propose(text, scan)
}

pub(crate) fn propose(text: &str, scan: &crate::source_locality::Scan) -> Option<Vec<u128>> {
    // Keep optional preparation bounded on large sources. A miss leaves the
    // existing verified-core path available.
    if text.len() > 4 << 20 {
        return None;
    }
    data::propose(text, scan).or_else(|| rules::propose(text, scan))
        .or_else(|| object::propose(text, scan))
}
