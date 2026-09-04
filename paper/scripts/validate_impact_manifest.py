#!/usr/bin/env python3
"""Fail closed on the paper impact-use-case plan and its checked-in controls."""

from __future__ import annotations

import csv
import hashlib
from pathlib import Path


PAPER = Path(__file__).resolve().parents[1]
ROOT = PAPER.parent
MANIFEST = PAPER / "IMPACT-USE-CASE-MANIFEST.tsv"
LEDGER = PAPER / "IMPACT-USE-CASE-LEDGER.md"

EXPECTED_IDS = {
    "BIO-UBERON-CONSISTENCY-GUARDED",
    "BIO-UBERON-FULL-EL",
    "BIO-UBERON-FMA-BRIDGE",
    "BIO-GALEN-ORE-FULL",
    "BIO-GALEN-FULL-EL",
    "BIO-GALEN-BIOPORTAL",
    "BIO-FMA-FULL-EL",
    "BIO-NCIT-FULL-EL",
    "BIO-NCIT-NEGATION-QC",
    "BIO-CHEBI-FULL-EL",
    "BIO-SNOMED-SYNTH",
    "BIO-SNOMED-LICENSED",
    "BIO-UNMIREOT-2018",
    "BIO-UNMIREOT-2026",
    "BIO-MERGE-CONTROL",
    "NONBIO-ACCESS-CONTROL",
    "NONBIO-PRODUCT-CONFIG",
    "NONBIO-FIBO-IDENTITY",
}

REQUIRED_FIELDS = {
    "id",
    "priority",
    "domain",
    "evidence_status",
    "ontology_version_source",
    "source_sha256",
    "input_path",
    "input_sha256",
    "dl_features",
    "scientific_user_question",
    "controlled_transformation_or_query",
    "expected_observation",
    "comparators",
    "km_command",
    "oracle_validation",
    "risks_confounders",
    "dependencies",
    "resource_class",
    "outputs",
    "acceptance_gate",
}


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def logical_axioms(path: Path) -> set[str]:
    return {
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
        and not line.startswith("Prefix(")
        and not line.startswith("Ontology(")
        and line.strip() != ")"
        and not line.strip().startswith("Declaration(")
    }


def require_one_axiom_pair(stem: str, expected_fragment: str) -> None:
    directory = PAPER / "impact" / "proposed"
    conflict = logical_axioms(directory / f"{stem}-conflict.ofn")
    control = logical_axioms(directory / f"{stem}-control.ofn")
    added = conflict - control
    removed = control - conflict
    if removed or len(added) != 1 or expected_fragment not in next(iter(added), ""):
        raise ValueError(
            f"{stem} is not the expected one-axiom pair: added={sorted(added)}, "
            f"removed={sorted(removed)}"
        )


def main() -> None:
    with MANIFEST.open(encoding="utf-8", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if set(reader.fieldnames or ()) != REQUIRED_FIELDS:
            raise ValueError(f"manifest fields changed: {reader.fieldnames}")
        rows = list(reader)
    if any(None in row or any(value is None for value in row.values()) for row in rows):
        raise ValueError("malformed manifest TSV")
    if any(not value.strip() for row in rows for value in row.values()):
        raise ValueError("blank manifest field")
    ids = [row["id"] for row in rows]
    if len(ids) != len(set(ids)) or set(ids) != EXPECTED_IDS:
        raise ValueError(
            f"impact IDs changed: missing={sorted(EXPECTED_IDS - set(ids))}, "
            f"extra={sorted(set(ids) - EXPECTED_IDS)}"
        )

    ledger = LEDGER.read_text(encoding="utf-8")
    for identifier in EXPECTED_IDS:
        if identifier not in ledger:
            raise ValueError(f"ledger omits manifest row {identifier}")
    for row in rows:
        status = row["evidence_status"].lower()
        if not any(word in status for word in ("verified", "proposed", "blocked", "running")):
            raise ValueError(f"unscoped evidence state for {row['id']}: {status}")
        if "$KM" not in row["km_command"]:
            raise ValueError(f"KM command is not scheduler-bindable for {row['id']}")
        if row["id"] == "BIO-UBERON-CONSISTENCY-GUARDED":
            if "tableau" not in row["km_command"] or "classify" in row["km_command"]:
                raise ValueError("guarded Uberon row must remain a direct consistency operation")
        elif "classify" not in row["km_command"]:
            raise ValueError(f"KM classification command changed for {row['id']}")
        input_path = row["input_path"]
        input_hash = row["input_sha256"]
        if input_path.startswith("paper/") and len(input_hash) == 64:
            path = ROOT / input_path
            if not path.is_file() or sha256(path) != input_hash:
                raise ValueError(f"checked-in input hash mismatch for {row['id']}")

    nonbio = {row["domain"] for row in rows if row["id"].startswith("NONBIO-")}
    if len(nonbio) < 2:
        raise ValueError("impact plan no longer covers two non-biomedical domains")
    require_one_axiom_pair("product-configuration", "ObjectMaxCardinality")
    require_one_axiom_pair("fibo-identity-document", "DifferentIndividuals")

    guarded = next(row for row in rows if row["id"] == "BIO-UBERON-CONSISTENCY-GUARDED")
    if guarded["input_sha256"] != "01dca21c579745be5e8e5eca9d8b752d7811070a69475f73441b9150ae0853c6":
        raise ValueError("guarded Uberon TInput binding changed")
    if "4.46 s" not in guarded["expected_observation"] or "157544 KiB" not in guarded["expected_observation"]:
        raise ValueError("guarded Uberon time or memory claim changed")
    if "no coherence or taxonomy" not in guarded["risks_confounders"]:
        raise ValueError("guarded Uberon empty-array boundary is missing")
    if "a taxonomy" not in guarded["acceptance_gate"]:
        raise ValueError("guarded Uberon consistency/taxonomy boundary is missing")

    java = PAPER / "benchmark" / "runners" / "owlapi"
    pom = (java / "pom.xml").read_text(encoding="utf-8")
    for name in ("MakeELProjection", "MergeOntologies"):
        if not (java / f"{name}.java").is_file() or f"<include>{name}.java</include>" not in pom:
            raise ValueError(f"missing OWLAPI transform helper {name}")
    print(f"IMPACT_MANIFEST_OK\t{len(rows)} rows\t{len(nonbio)} non-biomedical domains")


if __name__ == "__main__":
    main()
