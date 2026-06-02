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

#[derive(Serialize, Deserialize, Clone)]
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

#[derive(Deserialize)]
pub struct JInput {
    pub clauses: Vec<JClause>,
}

#[derive(Serialize)]
pub struct JOutput {
    pub subsumptions: std::collections::BTreeMap<String, Vec<String>>,
    pub derived_clauses: Vec<JClause>,
    pub inconsistent: bool,
}
