#!/usr/bin/env python3
"""Render audited IBEX JSON rows as the stable benchmark TSV schema."""

import argparse
import csv
import glob
import json


FIELDS = [
    "ontology",
    "index",
    "status",
    "verdict",
    "solved",
    "selected_route",
    "wall_s",
    "peak_mb",
    "binary_sha256",
    "signature_sha256",
    "correctness_basis",
    "slurm_job_id",
]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("results_glob")
    parser.add_argument("baseline_tsv")
    parser.add_argument("output_tsv")
    args = parser.parse_args()

    with open(args.baseline_tsv, newline="") as source:
        baseline = {
            row["ontology"]: row for row in csv.DictReader(source, delimiter="\t")
        }

    rows = []
    for path in glob.glob(args.results_glob):
        with open(path) as source:
            raw = json.load(source)
        ontology = raw["ont"]
        rows.append(
            {
                "ontology": ontology,
                "index": raw["slurm_array_task_id"],
                "status": raw["status"],
                "verdict": raw["verdict"],
                "solved": raw["solved"],
                "selected_route": raw.get("selected_route_trace") or "",
                "wall_s": raw["wall_s"],
                "peak_mb": raw["peak_mb"],
                "binary_sha256": raw["binary_sha256"],
                "signature_sha256": raw.get("signature_sha256") or "",
                "correctness_basis": baseline[ontology]["correctness_basis"],
                "slurm_job_id": raw["slurm_job_id"],
            }
        )

    assert len(rows) == 592
    assert {int(row["index"]) for row in rows} == set(range(592))
    rows.sort(key=lambda row: int(row["index"]))
    with open(args.output_tsv, "w", newline="") as target:
        writer = csv.DictWriter(
            target, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


if __name__ == "__main__":
    main()
