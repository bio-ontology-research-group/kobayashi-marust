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
use std::collections::{BTreeMap, HashMap};
use std::io::{self, Write};

const ELC_BINARY_MAGIC: &[u8; 8] = b"KMELC\0\x01\0";
const ELC_OUTPUT_BINARY_MAGIC: &[u8; 8] = b"KMELCO\x01\0";
const MAX_BINARY_ITEMS: usize = 100_000_000;

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

#[derive(Serialize, Deserialize, Clone, PartialEq, Eq)]
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

#[derive(Serialize, Deserialize, Clone, PartialEq, Eq)]
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

/// Exact source-level nominal/ABox payload for the native Konclude completion
/// bridge. The ordinary DL-clause path deliberately drops ground ABox facts;
/// this typed channel lets the bridge reconstruct the corresponding ontology
/// individuals without inferring semantics from generated `__nom__` names.
///
/// `complete` is a certificate produced by the frontend, not a best-effort
/// flag. It is true only when every source ABox axiom is represented here and
/// every individual is backed by at least one clausifier nominal proxy. The
/// bridge independently validates ids/names and otherwise defers.
#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
#[serde(default)]
pub struct NominalAboxMeta {
    pub complete: bool,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub individuals: Vec<NominalIndividualMeta>,
    /// Explicit source equalities. The native HT bridge currently declines
    /// these, while the EL ABox-consistency certificate consumes them exactly.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub same: Vec<(String, String)>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub different: Vec<(String, String)>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub role_assertions: Vec<NominalRoleAssertionMeta>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub negative_role_assertions: Vec<NominalRoleAssertionMeta>,
    /// Fail-closed diagnostics explaining why `complete` is false.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unsupported: Vec<String>,
}

impl NominalAboxMeta {
    pub fn is_empty(&self) -> bool {
        !self.complete
            && self.individuals.is_empty()
            && self.same.is_empty()
            && self.different.is_empty()
            && self.role_assertions.is_empty()
            && self.negative_role_assertions.is_empty()
            && self.unsupported.is_empty()
    }
}

#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq)]
#[serde(default)]
pub struct NominalIndividualMeta {
    pub individual: String,
    /// One individual normally has one proxy; a vector preserves exactness if
    /// two source spellings normalize to aliases of the same singleton.
    pub proxies: Vec<String>,
    /// Source class assertions, retained structurally so assertions of complex
    /// expressions do not depend on clausifier-definer reconstruction.
    pub assertions: Vec<crate::frontend::syntax::Concept>,
    /// One normalized concept marker for every entry in `assertions`, in the
    /// same order.  A count/name mismatch invalidates the certificate.
    pub assertion_markers: Vec<String>,
}

#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
#[serde(default)]
pub struct NominalRoleAssertionMeta {
    pub role: String,
    pub source: String,
    pub target: String,
}

#[derive(Serialize, Deserialize)]
pub struct JInput {
    pub clauses: Vec<JClause>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub rbox: Vec<Vec<String>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub cardinalities: Vec<CardMeta>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub definers: Vec<DefinerMeta>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub source_axioms: Vec<SourceAxiomMeta>,
    #[serde(default, skip_serializing_if = "NominalAboxMeta::is_empty")]
    pub nominal_abox: NominalAboxMeta,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub rules: Vec<JRule>,
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

/// Dictionary-coded complete EL taxonomy used only for the worker-to-
/// orchestrator handoff. Each concept name is owned once and relation rows
/// carry integer endpoints, avoiding one allocated `String` per taxonomy pair.
#[derive(Debug, PartialEq, Eq)]
pub struct CompactElcOutput {
    pub names: Vec<String>,
    pub rows: Vec<(u32, Vec<u32>)>,
    pub inconsistent: bool,
    pub dropped: usize,
}

/// Write a complete EL result in a compact, versioned representation. The
/// caller must retain JSON for partial results because their residue is merged
/// with a CB taxonomy through the established map-based path.
pub fn write_elc_output_binary<W: Write>(
    mut writer: W,
    subsumptions: &BTreeMap<String, Vec<String>>,
    inconsistent: bool,
    dropped: usize,
) -> io::Result<()> {
    let mut ids: HashMap<&str, u32> = HashMap::with_capacity(subsumptions.len());
    let mut names: Vec<&str> = Vec::with_capacity(subsumptions.len());
    for name in subsumptions.keys() {
        let id = u32::try_from(names.len()).map_err(|_| invalid_binary("too many names"))?;
        ids.insert(name.as_str(), id);
        names.push(name);
    }
    for supers in subsumptions.values() {
        for superclass in supers {
            if !ids.contains_key(superclass.as_str()) {
                let id =
                    u32::try_from(names.len()).map_err(|_| invalid_binary("too many names"))?;
                ids.insert(superclass.as_str(), id);
                names.push(superclass);
            }
        }
    }

    writer.write_all(ELC_OUTPUT_BINARY_MAGIC)?;
    writer.write_all(&[u8::from(inconsistent)])?;
    write_len(&mut writer, dropped)?;
    write_len(&mut writer, names.len())?;
    for name in names {
        write_string(&mut writer, name)?;
    }
    write_len(&mut writer, subsumptions.len())?;
    for (subject, supers) in subsumptions {
        writer.write_all(&ids[subject.as_str()].to_le_bytes())?;
        write_len(&mut writer, supers.len())?;
        for superclass in supers {
            writer.write_all(&ids[superclass.as_str()].to_le_bytes())?;
        }
    }
    Ok(())
}

/// Decode a compact complete EL result. `Ok(None)` preserves compatibility
/// with the established JSON worker contract.
pub fn decode_elc_output_binary(bytes: &[u8]) -> io::Result<Option<CompactElcOutput>> {
    if !bytes.starts_with(ELC_OUTPUT_BINARY_MAGIC) {
        return Ok(None);
    }
    let mut cursor = BinaryCursor {
        bytes,
        offset: ELC_OUTPUT_BINARY_MAGIC.len(),
    };
    let inconsistent = match cursor.byte()? {
        0 => false,
        1 => true,
        _ => return Err(invalid_binary("invalid consistency flag")),
    };
    let dropped = cursor.len()?;
    let name_count = cursor.len()?;
    let mut names = Vec::with_capacity(name_count);
    for _ in 0..name_count {
        names.push(cursor.string()?);
    }
    let row_count = cursor.len()?;
    let mut rows = Vec::with_capacity(row_count);
    let mut pair_count = 0usize;
    for _ in 0..row_count {
        let subject = cursor.u32()?;
        if subject as usize >= name_count {
            return Err(invalid_binary("subject id out of range"));
        }
        let super_count = cursor.len()?;
        pair_count = pair_count
            .checked_add(super_count)
            .ok_or_else(|| invalid_binary("pair count overflow"))?;
        if pair_count > MAX_BINARY_ITEMS {
            return Err(invalid_binary("pair count exceeds limit"));
        }
        let mut supers = Vec::with_capacity(super_count);
        for _ in 0..super_count {
            let superclass = cursor.u32()?;
            if superclass as usize >= name_count {
                return Err(invalid_binary("superclass id out of range"));
            }
            supers.push(superclass);
        }
        rows.push((subject, supers));
    }
    if cursor.offset != bytes.len() {
        return Err(invalid_binary("trailing bytes"));
    }
    Ok(Some(CompactElcOutput {
        names,
        rows,
        inconsistent,
        dropped,
    }))
}

#[inline]
pub fn is_elc_output_binary(bytes: &[u8]) -> bool {
    bytes.starts_with(ELC_OUTPUT_BINARY_MAGIC)
}

/// Write the clause-only input consumed by exact EL completion in a compact,
/// versioned representation. The ordinary JSON file remains authoritative for
/// every non-EL route and fallback.
pub fn write_elc_binary<W: Write>(mut writer: W, clauses: &[JClause]) -> io::Result<()> {
    writer.write_all(ELC_BINARY_MAGIC)?;
    write_len(&mut writer, clauses.len())?;
    for clause in clauses {
        write_len(&mut writer, clause.body.len())?;
        for atom in &clause.body {
            write_atom(&mut writer, atom)?;
        }
        write_len(&mut writer, clause.head.len())?;
        for atom in &clause.head {
            write_atom(&mut writer, atom)?;
        }
    }
    Ok(())
}

/// Decode a compact EL handoff. `Ok(None)` means the input uses the established
/// JSON contract, allowing one worker entry point to accept both formats.
pub fn decode_elc_binary(bytes: &[u8]) -> io::Result<Option<Vec<JClause>>> {
    if !bytes.starts_with(ELC_BINARY_MAGIC) {
        return Ok(None);
    }
    let mut cursor = BinaryCursor {
        bytes,
        offset: ELC_BINARY_MAGIC.len(),
    };
    let clause_count = cursor.len()?;
    let mut clauses = Vec::with_capacity(clause_count);
    for _ in 0..clause_count {
        let body_count = cursor.len()?;
        let mut body = Vec::with_capacity(body_count);
        for _ in 0..body_count {
            body.push(cursor.atom()?);
        }
        let head_count = cursor.len()?;
        let mut head = Vec::with_capacity(head_count);
        for _ in 0..head_count {
            head.push(cursor.atom()?);
        }
        clauses.push(JClause { body, head });
    }
    if cursor.offset != bytes.len() {
        return Err(invalid_binary("trailing bytes"));
    }
    Ok(Some(clauses))
}

fn write_len<W: Write>(writer: &mut W, len: usize) -> io::Result<()> {
    let len = u32::try_from(len).map_err(|_| invalid_binary("length exceeds u32"))?;
    writer.write_all(&len.to_le_bytes())
}

fn write_string<W: Write>(writer: &mut W, value: &str) -> io::Result<()> {
    write_len(writer, value.len())?;
    writer.write_all(value.as_bytes())
}

fn write_term<W: Write>(writer: &mut W, term: &JTerm) -> io::Result<()> {
    match term {
        JTerm::Var { name } => {
            writer.write_all(&[0])?;
            write_string(writer, name)
        }
        JTerm::Ind { name } => {
            writer.write_all(&[1])?;
            write_string(writer, name)
        }
        JTerm::Aux { root, label } => {
            writer.write_all(&[2])?;
            write_string(writer, root)?;
            write_len(writer, label.len())?;
            for (name, value) in label {
                write_string(writer, name)?;
                writer.write_all(&value.to_le_bytes())?;
            }
            Ok(())
        }
        JTerm::Fun { function, arg } => {
            writer.write_all(&[3])?;
            write_string(writer, function)?;
            write_term(writer, arg)
        }
    }
}

fn write_atom<W: Write>(writer: &mut W, atom: &JAtom) -> io::Result<()> {
    match atom {
        JAtom::Concept { concept, term } => {
            writer.write_all(&[0])?;
            write_string(writer, concept)?;
            write_term(writer, term)
        }
        JAtom::Role {
            role,
            source,
            target,
        } => {
            writer.write_all(&[1])?;
            write_string(writer, role)?;
            write_term(writer, source)?;
            write_term(writer, target)
        }
        JAtom::Eq { left, right } => {
            writer.write_all(&[2])?;
            write_term(writer, left)?;
            write_term(writer, right)
        }
    }
}

fn invalid_binary(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

struct BinaryCursor<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> BinaryCursor<'a> {
    fn take(&mut self, len: usize) -> io::Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .ok_or_else(|| invalid_binary("offset overflow"))?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or_else(|| invalid_binary("truncated input"))?;
        self.offset = end;
        Ok(value)
    }

    fn byte(&mut self) -> io::Result<u8> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> io::Result<u32> {
        let bytes: [u8; 4] = self.take(4)?.try_into().unwrap();
        Ok(u32::from_le_bytes(bytes))
    }

    fn i64(&mut self) -> io::Result<i64> {
        let bytes: [u8; 8] = self.take(8)?.try_into().unwrap();
        Ok(i64::from_le_bytes(bytes))
    }

    fn len(&mut self) -> io::Result<usize> {
        let len = self.u32()? as usize;
        if len > MAX_BINARY_ITEMS {
            return Err(invalid_binary("item count exceeds limit"));
        }
        Ok(len)
    }

    fn string(&mut self) -> io::Result<String> {
        let len = self.len()?;
        let bytes = self.take(len)?;
        String::from_utf8(bytes.to_vec()).map_err(|_| invalid_binary("invalid UTF-8"))
    }

    fn term(&mut self) -> io::Result<JTerm> {
        match self.byte()? {
            0 => Ok(JTerm::Var {
                name: self.string()?,
            }),
            1 => Ok(JTerm::Ind {
                name: self.string()?,
            }),
            2 => {
                let root = self.string()?;
                let count = self.len()?;
                let mut label = Vec::with_capacity(count);
                for _ in 0..count {
                    label.push((self.string()?, self.i64()?));
                }
                Ok(JTerm::Aux { root, label })
            }
            3 => Ok(JTerm::Fun {
                function: self.string()?,
                arg: Box::new(self.term()?),
            }),
            _ => Err(invalid_binary("unknown term tag")),
        }
    }

    fn atom(&mut self) -> io::Result<JAtom> {
        match self.byte()? {
            0 => Ok(JAtom::Concept {
                concept: self.string()?,
                term: self.term()?,
            }),
            1 => Ok(JAtom::Role {
                role: self.string()?,
                source: self.term()?,
                target: self.term()?,
            }),
            2 => Ok(JAtom::Eq {
                left: self.term()?,
                right: self.term()?,
            }),
            _ => Err(invalid_binary("unknown atom tag")),
        }
    }
}

#[cfg(test)]
mod elc_binary_tests {
    use super::*;

    #[test]
    fn compact_elc_handoff_round_trips_every_atom_and_term_shape() {
        let clauses = vec![JClause {
            body: vec![
                JAtom::Concept {
                    concept: "A".into(),
                    term: JTerm::Var { name: "x".into() },
                },
                JAtom::Role {
                    role: "r".into(),
                    source: JTerm::Ind { name: "i".into() },
                    target: JTerm::Fun {
                        function: "f".into(),
                        arg: Box::new(JTerm::Aux {
                            root: "root".into(),
                            label: vec![("L".into(), -7)],
                        }),
                    },
                },
            ],
            head: vec![JAtom::Eq {
                left: JTerm::Var { name: "x".into() },
                right: JTerm::Ind { name: "i".into() },
            }],
        }];
        let mut bytes = Vec::new();
        write_elc_binary(&mut bytes, &clauses).unwrap();
        let decoded = decode_elc_binary(&bytes).unwrap().unwrap();
        assert_eq!(
            serde_json::to_vec(&clauses).unwrap(),
            serde_json::to_vec(&decoded).unwrap()
        );
        assert!(decode_elc_binary(br#"{"clauses":[]}"#).unwrap().is_none());
    }

    #[test]
    fn compact_elc_handoff_rejects_truncation_and_trailing_bytes() {
        let mut bytes = Vec::new();
        write_elc_binary(&mut bytes, &[]).unwrap();
        assert!(decode_elc_binary(&bytes[..bytes.len() - 1]).is_err());
        bytes.push(0);
        assert!(decode_elc_binary(&bytes).is_err());
    }

    #[test]
    fn compact_elc_output_shares_names_and_round_trips_rows() {
        let subsumptions = BTreeMap::from([
            ("A".to_string(), vec!["A".to_string(), "Top".to_string()]),
            ("B".to_string(), vec!["Top".to_string()]),
        ]);
        let mut bytes = Vec::new();
        write_elc_output_binary(&mut bytes, &subsumptions, true, 7).unwrap();
        let decoded = decode_elc_output_binary(&bytes).unwrap().unwrap();
        assert_eq!(decoded.names, vec!["A", "B", "Top"]);
        assert_eq!(decoded.rows, vec![(0, vec![0, 2]), (1, vec![2])]);
        assert!(decoded.inconsistent);
        assert_eq!(decoded.dropped, 7);
        assert!(decode_elc_output_binary(br#"{"subsumptions":{}}"#)
            .unwrap()
            .is_none());
    }

    #[test]
    fn compact_elc_output_rejects_bad_ids_and_truncation() {
        let subsumptions = BTreeMap::from([("A".to_string(), vec!["A".to_string()])]);
        let mut bytes = Vec::new();
        write_elc_output_binary(&mut bytes, &subsumptions, false, 0).unwrap();
        assert!(decode_elc_output_binary(&bytes[..bytes.len() - 1]).is_err());

        // Header + flag + dropped + name-count + one length-prefixed name +
        // row-count, followed by the first subject id.
        let subject_offset = ELC_OUTPUT_BINARY_MAGIC.len() + 1 + 4 + 4 + 4 + 1 + 4;
        bytes[subject_offset..subject_offset + 4].copy_from_slice(&9u32.to_le_bytes());
        assert!(decode_elc_output_binary(&bytes).is_err());
    }
}
