#!/usr/bin/env python3
"""Atomically attach a validated sparse fingerprint to one KM result record."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def atomic_json(path: Path, value: dict) -> None:
    temporary = Path(str(path) + f".part.{os.getpid()}")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def atomic_copy(source: Path, target: Path) -> None:
    temporary = Path(str(target) + f".part.{os.getpid()}")
    with source.open("rb") as reader, temporary.open("wb") as writer:
        shutil.copyfileobj(reader, writer, 8 * 1024 * 1024)
    temporary.replace(target)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--result", required=True, type=Path)
    parser.add_argument("--taxonomy", required=True, type=Path)
    parser.add_argument("--source-ontology", required=True, type=Path)
    parser.add_argument("--recovery-prefix", required=True, type=Path)
    parser.add_argument("--fingerprinter", required=True, type=Path)
    parser.add_argument("--expected-array-job-id", required=True)
    parser.add_argument("--fingerprint-job-id", required=True)
    parser.add_argument("--differential-job-id", required=True)
    args = parser.parse_args()

    for path in (args.result, args.taxonomy, args.source_ontology, args.fingerprinter):
        require(path.is_file(), f"missing recovery input: {path}")
    source_receipt = Path(str(args.recovery_prefix) + ".json")
    source_nodes = Path(str(args.recovery_prefix) + ".nodes.tsv.gz")
    source_unsat = Path(str(args.recovery_prefix) + ".unsat.txt.gz")
    for path in (source_receipt, source_nodes, source_unsat):
        require(path.is_file(), f"missing sparse fingerprint evidence: {path}")

    record = json.loads(args.result.read_text(encoding="utf-8"))
    receipt = json.loads(source_receipt.read_text(encoding="utf-8"))
    require(record.get("baseline") == "km", "recovery is KM-only")
    require(record.get("status") == "fingerprint_error", "result is not a fingerprint failure")
    require(record.get("checkpointed") is True and record.get("rc") == 0,
            "reasoner did not complete successfully")
    require(record.get("slurm_array_job_id") == args.expected_array_job_id,
            "result belongs to a different array")
    require(record.get("ontology_sha256") == sha256(args.source_ontology),
            "source ontology digest mismatch")
    taxonomy_digest = sha256(args.taxonomy)
    require(receipt.get("status") == "ok", "sparse fingerprint is not terminal")
    require(receipt.get("algorithm") == "km-json-sparse-scc-closure-fingerprint-v1",
            "wrong sparse fingerprint algorithm")
    require(receipt.get("input_sha256") == taxonomy_digest,
            "sparse fingerprint input digest mismatch")
    require(receipt.get("source_ontology_sha256") == record.get("ontology_sha256"),
            "sparse fingerprint source mismatch")
    require(receipt.get("node_fingerprints_sha256") == sha256(source_nodes),
            "node receipt digest mismatch")
    require(receipt.get("unsatisfiable_names_sha256") == sha256(source_unsat),
            "unsatisfiable receipt digest mismatch")
    for field in ("taxonomy_sha256", "relation_sha256"):
        require(isinstance(receipt.get(field), str) and len(receipt[field]) == 64,
                f"invalid {field}")

    stem = args.result.name.removesuffix(".result.json")
    target_prefix = args.result.parent / f"{stem}.fingerprint"
    target_nodes = Path(str(target_prefix) + ".nodes.tsv.gz")
    target_unsat = Path(str(target_prefix) + ".unsat.txt.gz")
    target_receipt = Path(str(target_prefix) + ".json")
    atomic_copy(source_nodes, target_nodes)
    atomic_copy(source_unsat, target_unsat)
    receipt["node_fingerprints"] = str(target_nodes)
    receipt["unsatisfiable_names"] = str(target_unsat)
    atomic_json(target_receipt, receipt)

    record.pop("fingerprint_error", None)
    record.update(
        status="ok",
        output_sha256=taxonomy_digest,
        consistency=str(receipt["consistent"]).lower(),
        subsumptions=receipt["subsumptions"],
        unsatisfiable=receipt["unsatisfiable"],
        taxonomy_sha256=receipt["taxonomy_sha256"],
        relation_sha256=receipt["relation_sha256"],
        fingerprint_wall_s=receipt["wall_s"],
        fingerprint_peak_mb=receipt["peak_mb"],
        fingerprint_recovery={
            "schema": 1,
            "original_status": "fingerprint_error",
            "reasoner_output_unchanged": True,
            "fingerprinter_sha256": sha256(args.fingerprinter),
            "fingerprint_job_id": args.fingerprint_job_id,
            "differential_job_id": args.differential_job_id,
            "recovery_script_sha256": sha256(Path(__file__)),
        },
    )
    atomic_json(args.result, record)
    print(json.dumps({"status": "recovered", "ontology_id": record.get("ontology_id"),
                      "taxonomy_sha256": record["taxonomy_sha256"]}, sort_keys=True))


if __name__ == "__main__":
    main()
