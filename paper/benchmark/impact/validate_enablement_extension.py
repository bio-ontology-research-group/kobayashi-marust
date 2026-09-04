#!/usr/bin/env python3
"""Validate the bounded product-configuration and GALEN impact extension."""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
import os
from pathlib import Path


EXPECTED = {
    "km": "c8688f6b286db2b422f1ec1df0874eadbbce0cc9e2899f35dbe143ccad70639d",
    "elk": "7ffc442f2966667a488479a748502276136445c8e44ffd9e8498873a401cb3d4",
    "hermit": "59a7dc34d874c0dd9fb752594eb8d55b611e70d3cf7e839d581d7c366a5dd99c",
    "product_control": "baad9238c8bcbf1519d3b006299334a52cf489a5f4b57292de32ffec69e0d2f3",
    "product_conflict": "a92e020a6957504fc4ee1d206389288e65a8c8637d874d42aaacc31899e0fde6",
    "galen": "00c80e07aa57578c168d15a1755b62fde41c53dd69a2f04cc5d88c888c8baf19",
}
TARGET = "http://example.org/km-impact/configuration#DualSensorSurveyDrone"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def receipt(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if len(row) >= 2 and row[0] and row[0] not in values:
                values[row[0]] = row[1]
    return values


def projection_receipt(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    complete = in_profile = False
    with path.open(encoding="utf-8", newline="") as stream:
        for row in csv.reader(stream, delimiter="\t"):
            if row[:2] == ["Z", "complete"]:
                complete = True
            elif row[:4] == ["P", "OWL2EL", "true", "0"]:
                in_profile = True
            elif len(row) >= 3 and row[0] == "M":
                values[row[1]] = row[2]
    if not complete or not in_profile:
        raise ValueError(f"projection is not terminal OWL 2 EL: {path}")
    return values


def km_semantics(
    path: Path, default_prefix: str | None = None
) -> tuple[bool, set[str], set[tuple[str, str]]]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value.get("consistent"), bool):
        raise ValueError(f"missing consistency: {path}")
    def expand(name: str) -> str:
        if default_prefix is not None and name.startswith(":"):
            return default_prefix + name[1:]
        return name

    unsat = {expand(name) for name in value.get("unsatisfiable", [])}
    relations = {
        (expand(pair[0]), expand(pair[1]))
        for pair in value.get("subsumptions", [])
    }
    return value["consistent"], unsat, relations


def java_semantics(path: Path) -> tuple[bool, set[str], set[tuple[str, str]]]:
    consistent: bool | None = None
    unsat: set[str] = set()
    relations: set[tuple[str, str]] = set()
    with path.open(encoding="utf-8") as stream:
        for raw in stream:
            row = raw.rstrip("\n").split("\t")
            if row[:1] == ["C"]:
                consistent = row[1].lower() == "true"
            elif row[:1] == ["U"]:
                unsat.add(row[1])
            elif row[:1] == ["S"]:
                relations.add((row[1], row[2]))
    if consistent is None:
        raise ValueError(f"missing consistency: {path}")
    return consistent, unsat, relations


def semantic_digest(value: tuple[bool, set[str], set[tuple[str, str]]]) -> str:
    consistent, unsat, relations = value
    digest = hashlib.sha256()
    digest.update(f"C\t{str(consistent).lower()}\n".encode())
    for name in sorted(unsat):
        digest.update(f"U\t{name}\n".encode())
    for sub, sup in sorted(relations):
        digest.update(f"S\t{sub}\t{sup}\n".encode())
    return digest.hexdigest()


def require_km(
    root: Path, name: str, ontology_sha: str, default_prefix: str | None = None
):
    prefix = root / "results" / "km" / name
    row = receipt(prefix.with_suffix(".receipt.tsv"))
    if row.get("status") != "ok" or row.get("exit_code") != "0":
        raise ValueError(f"KM did not complete: {name}")
    if row.get("terminal_marker") != "TASK_COMPLETE":
        raise ValueError(f"KM missing terminal marker: {name}")
    if row.get("binary_sha256") != EXPECTED["km"] or row.get("ontology_sha256") != ontology_sha:
        raise ValueError(f"KM binding changed: {name}")
    output = prefix.with_suffix(".json")
    if not output.is_file() or output.stat().st_size == 0 or sha256(output) != row.get("output_sha256"):
        raise ValueError(f"KM output binding changed: {name}")
    return km_semantics(output, default_prefix), row


def require_java(root: Path, reasoner: str, name: str, ontology_sha: str):
    prefix = root / "results" / reasoner / name
    result_path = prefix.with_suffix(".result.json")
    value = json.loads(result_path.read_text(encoding="utf-8"))
    if value.get("status") != "ok" or value.get("rc") != 0 or not value.get("checkpointed"):
        raise ValueError(f"{reasoner} did not complete: {name}")
    if value.get("runtime_sha256") != EXPECTED[reasoner] or value.get("ontology_sha256") != ontology_sha:
        raise ValueError(f"{reasoner} binding changed: {name}")
    taxonomy = prefix.with_suffix(".taxonomy.tsv")
    if sha256(taxonomy) != value.get("output_sha256"):
        raise ValueError(f"{reasoner} output binding changed: {name}")
    return java_semantics(taxonomy), value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--old-impact-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    root = args.root.resolve()

    prep = receipt(root / "receipts" / "preparation.receipt.tsv")
    if prep.get("status") != "complete" or prep.get("terminal_marker") != "PREPARATION_COMPLETE":
        raise ValueError("preparation receipt is incomplete")

    projections: dict[str, dict[str, str]] = {}
    for name, source_hash in (
        ("product-control-el", EXPECTED["product_control"]),
        ("product-conflict-el", EXPECTED["product_conflict"]),
        ("galen-ore9724-el", EXPECTED["galen"]),
    ):
        row = projection_receipt(root / "receipts" / f"{name}.projection.tsv")
        if row.get("source_sha256") != source_hash:
            raise ValueError(f"projection source changed: {name}")
        output = root / "inputs" / f"{name}.ofn"
        if row.get("output_sha256") != sha256(output):
            raise ValueError(f"projection output changed: {name}")
        projections[name] = row

    product_prefix = "http://example.org/km-impact/configuration#"
    km_control, km_control_row = require_km(
        root, "product-control-full", EXPECTED["product_control"], product_prefix
    )
    km_conflict, km_conflict_row = require_km(
        root, "product-conflict-full", EXPECTED["product_conflict"], product_prefix
    )
    h_control, h_control_row = require_java(root, "hermit", "product-control-full", EXPECTED["product_control"])
    h_conflict, h_conflict_row = require_java(root, "hermit", "product-conflict-full", EXPECTED["product_conflict"])

    if not km_control[0] or km_control[1] or not km_conflict[0] or TARGET not in km_conflict[1]:
        raise ValueError("KM product conflict/control outcome is not the predeclared one")
    if (h_control[0], h_control[1]) != (km_control[0], km_control[1]):
        raise ValueError("HermiT disagrees with KM on product control")
    if (h_conflict[0], h_conflict[1]) != (km_conflict[0], km_conflict[1]):
        raise ValueError("HermiT disagrees with KM on product conflict")

    product_el: dict[str, tuple[bool, set[str], set[tuple[str, str]]]] = {}
    product_el_rows: dict[str, dict[str, object]] = {}
    for stem in ("product-control-el", "product-conflict-el"):
        digest = projections[stem]["output_sha256"]
        km_value, _ = require_km(root, stem, digest, product_prefix)
        elk_value, elk_row = require_java(root, "elk", stem, digest)
        if km_value != elk_value:
            raise ValueError(f"KM and ELK disagree on EL projection: {stem}")
        if not km_value[0] or km_value[1]:
            raise ValueError(f"EL product projection unexpectedly incoherent/inconsistent: {stem}")
        product_el[stem] = km_value
        product_el_rows[stem] = elk_row
    if product_el["product-control-el"] != product_el["product-conflict-el"]:
        raise ValueError("product projections should be semantically identical")

    galen_projection_sha = projections["galen-ore9724-el"]["output_sha256"]
    galen_km, galen_km_row = require_km(root, "galen-ore9724-el", galen_projection_sha)
    galen_elk, galen_elk_row = require_java(root, "elk", "galen-ore9724-el", galen_projection_sha)
    if galen_km != galen_elk:
        raise ValueError("KM and ELK disagree on the GALEN EL projection")
    if not galen_km[0] or galen_km[1] or len(galen_km[2]) < 1000:
        raise ValueError("GALEN EL projection result is not a nontrivial consistent taxonomy")

    old_receipt = receipt(args.old_impact_root / "results" / "galen-ore9724.receipt.tsv")
    if old_receipt.get("ontology_sha256") != EXPECTED["galen"] or old_receipt.get("status") != "ok":
        raise ValueError("established full GALEN receipt is not valid")
    full_path = args.old_impact_root / "results" / "galen-ore9724.json"
    if old_receipt.get("output_sha256") != sha256(full_path):
        raise ValueError("established full GALEN output binding changed")
    galen_full = km_semantics(full_path)
    projection_only = galen_km[2] - galen_full[2]
    projection_unsat_only = galen_km[1] - galen_full[1]
    if projection_only or projection_unsat_only:
        raise ValueError("GALEN EL projection is not a semantic subset of full GALEN")
    full_only = galen_full[2] - galen_km[2]

    explanation = root / "results" / "km" / "product-conflict-explain.json"
    explanation_row = receipt(root / "results" / "km" / "product-conflict-explain.receipt.tsv")
    if explanation_row.get("status") != "ok" or sha256(explanation) != explanation_row.get("output_sha256"):
        raise ValueError("product explanation is missing or unbound")
    explanation_text = explanation.read_text(encoding="utf-8")
    required_support = (
        "ObjectMaxCardinality",
        "OpticalCamera",
        "ThermalCamera",
        "DisjointClasses",
    )
    if not all(token in explanation_text for token in required_support):
        raise ValueError("product explanation omits a required conflict feature")

    summary = {
        "schema": 1,
        "status": "validated",
        "product_configuration": {
            "km_hybrid_development_binary_sha256": EXPECTED["km"],
            "full_control": {"consistent": km_control[0], "unsatisfiable": sorted(km_control[1]), "semantic_sha256": semantic_digest(km_control)},
            "full_conflict": {"consistent": km_conflict[0], "unsatisfiable": sorted(km_conflict[1]), "semantic_sha256": semantic_digest(km_conflict)},
            "hermit_agreement": True,
            "el_projection_km_elk_exact": True,
            "control_and_conflict_el_semantics_equal": True,
            "conflict_removed_axioms": int(projections["product-conflict-el"]["removed_axioms"]),
            "control_removed_axioms": int(projections["product-control-el"]["removed_axioms"]),
            "explanation_feature_gate": True,
            "jobs": sorted({km_control_row["slurm_job_id"], km_conflict_row["slurm_job_id"], str(h_control_row["slurm_job_id"]), str(h_conflict_row["slurm_job_id"]), explanation_row["slurm_job_id"]}),
        },
        "galen": {
            "source_sha256": EXPECTED["galen"],
            "source_axioms": int(projections["galen-ore9724-el"]["source_axioms"]),
            "removed_axioms": int(projections["galen-ore9724-el"]["removed_axioms"]),
            "projection_sha256": galen_projection_sha,
            "projection_subsumptions": len(galen_km[2]),
            "full_subsumptions": len(galen_full[2]),
            "full_only_subsumptions": len(full_only),
            "projection_only_subsumptions": 0,
            "projection_km_elk_exact": True,
            "projection_subset_of_full": True,
            "projection_semantic_sha256": semantic_digest(galen_km),
            "full_semantic_sha256": semantic_digest(galen_full),
            "full_only_sample": [list(pair) for pair in sorted(full_only)[:20]],
            "jobs": sorted({galen_km_row["slurm_job_id"], str(galen_elk_row["slurm_job_id"])}),
        },
        "validation": {
            "slurm_job_id": os.environ.get("SLURM_JOB_ID"),
            "host": os.uname().nodename,
            "validator_sha256": sha256(Path(__file__)),
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
