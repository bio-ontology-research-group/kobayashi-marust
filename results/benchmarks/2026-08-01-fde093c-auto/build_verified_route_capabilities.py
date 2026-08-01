#!/usr/bin/env python3
"""Build the long-form, source-bound KM route capability ledger.

The input panel directory must contain one 55-row JSONL file per ontology from
the corrected v0.2.0 uniform route panel.  The automatic TSV supplies the
current independently verified 4669 route, whose generic panel postprocessor
could not finish within its memory cgroup.
"""

import argparse
import csv
import json
from pathlib import Path


FIELDS = [
    "ontology",
    "arm",
    "route",
    "source_revision",
    "binary_sha256",
    "status",
    "verdict",
    "correctness_basis",
    "wall_s",
    "peak_mb",
    "signature_sha256",
    "slurm_job_id",
]

COLLISION_SAFE_DIGEST = "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a"


def panel_rows(panel_dir: Path):
    for path in sorted(panel_dir.glob("ore_ont_*.owl.jsonl")):
        rows = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
        if len(rows) != 55 or len({row["arm"] for row in rows}) != 55:
            raise ValueError(f"{path}: expected 55 distinct arms")
        for row in rows:
            contract = row["procedure_contract"]
            adjudicated_nogold = row.get("ont") == "ore_ont_10860.owl" and row.get("status") == "ok"
            collision_safe = (
                row.get("ont") in {"ore_ont_3524.owl", "ore_ont_15703.owl"}
                and row.get("status") == "ok"
                and row.get("verdict") == "match"
                and row.get("fulliri_taxonomy_sha256") == COLLISION_SAFE_DIGEST
            )
            if contract.get("kind") != "km" or not (row.get("solved") or adjudicated_nogold or collision_safe):
                continue
            route = contract.get("route", contract.get("documented_route"))
            if not route:
                raise ValueError(f"{path}: KM arm {row['arm']} has no route name")
            yield {
                "ontology": row["ont"],
                "arm": row["arm"],
                "route": route,
                "source_revision": contract["source_revision"],
                "binary_sha256": row["binary_sha256"],
                "status": row["status"],
                "verdict": row["verdict"],
                "correctness_basis": (
                    "independently_adjudicated_consistency"
                    if adjudicated_nogold
                    else "same_job_fulliri_identity_to_konclude"
                    if collision_safe
                    else row.get("correctness_basis", "")
                ),
                "wall_s": row.get("wall_s", ""),
                "peak_mb": row.get("peak_mb", ""),
                "signature_sha256": row.get("signature_sha256", ""),
                "slurm_job_id": row.get("slurm_job_id", ""),
            }


def current_4669(auto_tsv: Path):
    with auto_tsv.open(newline="") as handle:
        matches = [row for row in csv.DictReader(handle, delimiter="\t") if row["ontology"] == "ore_ont_4669.owl"]
    if len(matches) != 1 or matches[0]["status"] != "ok" or matches[0]["solved"] != "true":
        raise ValueError("current automatic TSV lacks one verified successful 4669 row")
    row = matches[0]
    return {
        "ontology": row["ontology"],
        "arm": "km_current_automatic",
        "route": row["selected_route"],
        "source_revision": "fde093c",
        "binary_sha256": row["binary_sha256"],
        "status": row["status"],
        "verdict": row["verdict"],
        "correctness_basis": row["correctness_basis"],
        "wall_s": row["wall_s"],
        "peak_mb": row["peak_mb"],
        "signature_sha256": row["signature_sha256"],
        "slurm_job_id": row["slurm_job_id"],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("panel_dir", type=Path)
    parser.add_argument("automatic_tsv", type=Path)
    parser.add_argument("output_tsv", type=Path)
    args = parser.parse_args()

    rows = list(panel_rows(args.panel_dir))
    rows.append(current_4669(args.automatic_tsv))
    rows.sort(key=lambda row: (int(row["ontology"].split("_")[-1].split(".")[0]), row["arm"]))
    if len({(row["ontology"], row["arm"], row["source_revision"]) for row in rows}) != len(rows):
        raise ValueError("duplicate ontology/arm/source rows in capability ledger")
    if len({row["ontology"] for row in rows}) != 591:
        raise ValueError("verified route union must cover exactly 591 ontologies")
    if any(row["ontology"] == "ore_ont_1194.owl" for row in rows):
        raise ValueError("1194 must remain absent until a route completes correctly")

    with args.output_tsv.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


if __name__ == "__main__":
    main()
