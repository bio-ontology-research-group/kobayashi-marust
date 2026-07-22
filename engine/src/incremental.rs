//! Stateful, addition-only incremental reasoning.
//!
//! The library API is [`IncrementalElClassifier`]. [`run_jsonl_session`] is a
//! small transport adapter used by `km incremental`: it keeps one classifier
//! alive while a client submits additions and queries over newline-delimited
//! JSON. The protocol intentionally consumes the same normalised `JClause`
//! representation as `km elc`; OWL frontends must normalise one stable union so
//! generated symbols remain stable across edits.

use std::io::{BufRead, Write};

use serde::Deserialize;
use serde_json::{json, Value};

use crate::json_io::JClause;

pub use crate::elcomplete::{IncrementalElClassifier, IncrementalError, IncrementalUpdate};

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
enum Command {
    /// Start or replace the current session at revision 0.
    Init { clauses: Vec<JClause> },
    /// Atomically add normalised clauses to the current session.
    Add { clauses: Vec<JClause> },
    /// Return the current complete EL++ classification.
    Classify,
    /// Ask one named-class subsumption query.
    IsSubsumedBy { sub: String, sup: String },
    /// Return cheap session metadata without materialising all answers.
    Stats,
}

/// Serve one incremental classifier over newline-delimited JSON.
///
/// Command errors are returned as JSON records and do not terminate the
/// stream. In particular, a rejected `add` leaves the preceding session live.
/// Only transport I/O errors are returned from this function.
pub fn run_jsonl_session<R: BufRead, W: Write>(reader: R, mut writer: W) -> std::io::Result<()> {
    let mut session: Option<IncrementalElClassifier> = None;
    for line in reader.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let response = match serde_json::from_str::<Command>(&line) {
            Ok(command) => handle(command, &mut session),
            Err(error) => error_response("parse", error.to_string()),
        };
        serde_json::to_writer(&mut writer, &response)
            .map_err(|error| std::io::Error::new(std::io::ErrorKind::InvalidData, error))?;
        writer.write_all(b"\n")?;
        writer.flush()?;
    }
    Ok(())
}

fn handle(command: Command, session: &mut Option<IncrementalElClassifier>) -> Value {
    match command {
        Command::Init { clauses } => match IncrementalElClassifier::new(clauses) {
            Ok(classifier) => {
                let response = json!({
                    "status": "ok",
                    "op": "init",
                    "revision": classifier.revision(),
                    "total_clauses": classifier.clause_count(),
                    "inconsistent": classifier.is_inconsistent(),
                });
                *session = Some(classifier);
                response
            }
            Err(error) => error_response("init", error.to_string()),
        },
        Command::Add { clauses } => match session.as_mut() {
            Some(classifier) => match classifier.add_clauses(clauses) {
                Ok(update) => json!({
                    "status": "ok",
                    "op": "add",
                    "update": update,
                    "inconsistent": classifier.is_inconsistent(),
                }),
                Err(error) => error_response("add", error.to_string()),
            },
            None => no_session("add"),
        },
        Command::Classify => match session.as_ref() {
            Some(classifier) => json!({
                "status": "ok",
                "op": "classify",
                "revision": classifier.revision(),
                "result": classifier.result(),
            }),
            None => no_session("classify"),
        },
        Command::IsSubsumedBy { sub, sup } => match session.as_ref() {
            Some(classifier) => {
                let entailed = classifier.is_subsumed_by(&sub, &sup);
                json!({
                    "status": "ok",
                    "op": "is_subsumed_by",
                    "revision": classifier.revision(),
                    "sub": sub,
                    "sup": sup,
                    "entailed": entailed,
                })
            }
            None => no_session("is_subsumed_by"),
        },
        Command::Stats => match session.as_ref() {
            Some(classifier) => json!({
                "status": "ok",
                "op": "stats",
                "revision": classifier.revision(),
                "total_clauses": classifier.clause_count(),
                "inconsistent": classifier.is_inconsistent(),
            }),
            None => no_session("stats"),
        },
    }
}

fn no_session(op: &str) -> Value {
    error_response(op, "session is not initialised; send an init command first")
}

fn error_response(op: &str, message: impl Into<String>) -> Value {
    json!({
        "status": "error",
        "op": op,
        "error": message.into(),
    })
}
