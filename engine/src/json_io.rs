//! JSON schema (de)serialisation for the DL-clause set.
//!
//! Reuses the term/atom/clause schema of the sibling `sroiq-saturation` crate.
//!
//! ## Input
//! ```json
//! { "clauses": [ <clause>, ... ] }
//! ```
//!
//! ## Output
//! ```json
//! {
//!   "subsumptions": { "<concept>": ["<super>", ...], ... },
//!   "derived_clauses": [ <clause>, ... ],
//!   "inconsistent": <bool>
//! }
//! ```
//!
//! A `<clause>` is `{ "body": [<atom>...], "head": [<atom>...] }`.
//!
//! An `<atom>` is one of:
//!   - `{ "kind": "concept", "concept": <str>, "term": <term> }`
//!   - `{ "kind": "role", "role": <str>, "source": <term>, "target": <term> }`
//!   - `{ "kind": "eq", "left": <term>, "right": <term> }`
//!
//! A `<term>` is one of:
//!   - `{ "kind": "var", "name": <str> }`
//!   - `{ "kind": "ind", "name": <str> }`
//!   - `{ "kind": "aux", "root": <str>, "label": [[<str>, <int>], ...] }`
//!   - `{ "kind": "fun", "function": <str>, "arg": <term> }`

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Clone, PartialEq, Eq)]
#[serde(tag = "kind")]
pub enum JTerm {
    #[serde(rename = "var")]
    Var { name: String },
    #[serde(rename = "ind")]
    Ind { name: String },
    #[serde(rename = "aux")]
    Aux {
        root: String,
        label: Vec<(String, i64)>,
    },
    #[serde(rename = "fun")]
    Fun { function: String, arg: Box<JTerm> },
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(tag = "kind")]
pub enum JAtom {
    #[serde(rename = "concept")]
    Concept { concept: String, term: JTerm },
    #[serde(rename = "role")]
    Role {
        role: String,
        source: JTerm,
        target: JTerm,
    },
    #[serde(rename = "eq")]
    Eq { left: JTerm, right: JTerm },
}

#[derive(Serialize, Deserialize, Clone)]
pub struct JClause {
    pub body: Vec<JAtom>,
    pub head: Vec<JAtom>,
}

/// KM_HT_CARD side-channel: a first-class qualified number restriction recorded
/// by the frontend (`define`) so cb_to_ht can install it as a Konclude
/// `≥n`/`≤n` rule (and drop the clausal `⋁ Eq` pigeonhole) instead of letting
/// the legacy Eq-merge over-count. `marker` is the reified concept name carrying
/// the restriction; `min` distinguishes `≥n` (true) from `≤n` (false). Emitted
/// only under the frontend `KM_HT_CARD` flag, so the default clause/meta output
/// is byte-identical (empty list, skipped on serialize).
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct CardMeta {
    pub marker: String,
    pub min: bool,
    pub n: u32,
    pub role: String,
    pub filler: String,
}

/// Structural provenance for a fresh clausifier concept. The trigger absorber
/// uses this side channel instead of reverse-engineering `Q_*` definitions from
/// clause shapes. It is emitted only with `KM_TRIGGER_ABSORB` and is ignored by
/// the certified CB engine.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct DefinerMeta {
    pub marker: String,
    pub kind: DefinerKind,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub operands: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub role: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub n: Option<i64>,
}

/// A normalized source-level TBox axiom. Konclude runs binary implication
/// absorption over this compact concept DAG, before clausification introduces
/// recognition and definer clauses. Emitted only under `KM_TRIGGER_ABSORB`.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct SourceAxiomMeta {
    pub kind: SourceAxiomKind,
    pub left: crate::frontend::syntax::Concept,
    pub right: crate::frontend::syntax::Concept,
}

#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum SourceAxiomKind {
    SubClass,
    Equivalent,
    Disjoint,
}

#[derive(Serialize, Deserialize, Clone, Copy, Debug, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum DefinerKind {
    Top,
    Bottom,
    Not,
    NotSelf,
    And,
    Or,
    Exists,
    Forall,
    SelfRestriction,
    AtLeast,
    AtMost,
}

/// KM_HT_RULES side-channel (Stage 2 of SWRL DL-safe rule support). A parsed
/// `DLSafeRule` carried verbatim from the frontend to `cb_to_ht`, where it is
/// turned into an HT DL-clause (with an O-guard restricting every variable to a
/// named individual). Emitted by the frontend ONLY under `KM_HT_RULES`, and
/// skipped on serialize when empty, so the default clause/meta output is
/// byte-identical.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(tag = "kind")]
pub enum JRuleTerm {
    #[serde(rename = "var")]
    Var { name: String },
    #[serde(rename = "ind")]
    Ind { name: String },
}

#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(tag = "kind")]
pub enum JRuleAtom {
    #[serde(rename = "class")]
    Class { concept: String, term: JRuleTerm },
    #[serde(rename = "role")]
    Role {
        role: String,
        source: JRuleTerm,
        target: JRuleTerm,
    },
    #[serde(rename = "same")]
    Same { left: JRuleTerm, right: JRuleTerm },
    #[serde(rename = "diff")]
    Diff { left: JRuleTerm, right: JRuleTerm },
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct JRule {
    pub body: Vec<JRuleAtom>,
    pub head: Vec<JRuleAtom>,
}

#[derive(Deserialize)]
pub struct JInput {
    pub clauses: Vec<JClause>,
    #[serde(default)]
    pub cardinalities: Vec<CardMeta>,
    #[serde(default)]
    pub rules: Vec<JRule>,
    #[serde(default)]
    pub definers: Vec<DefinerMeta>,
    #[serde(default)]
    pub source_axioms: Vec<SourceAxiomMeta>,
}

#[derive(Serialize)]
pub struct JOutput {
    pub subsumptions: std::collections::BTreeMap<String, Vec<String>>,
    pub derived_clauses: Vec<JClause>,
    pub inconsistent: bool,
    /// Number of input clauses dropped as unsupported (i.e. needing the general
    /// role-automaton transformation). Soundness-preserving; nonzero only costs
    /// completeness. Zero on all benchmarks after the `augment` preprocessing.
    pub dropped: usize,
}
