#!/usr/bin/env python3
"""Build the verified ontology-route registry from the current IBEX proof run."""

import argparse
import csv
import glob
import json
import os
from collections import Counter


FIELDS = [
    "ontology",
    "route",
    "result_class",
    "status",
    "verdict",
    "wall_s",
    "peak_mb",
    "binary_sha256",
    "gold_kind",
    "gold_sha256",
    "signature_sha256",
    "subsumptions",
    "unsatisfiable",
    "invocation",
    "evidence_file",
]


def classify(row):
    if row.get("status") != "ok":
        return None
    if row.get("verdict") == "match":
        return "exact_gold"
    if row.get("verdict") == "nogold":
        return "completed_unadjudicated"
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("result_root")
    parser.add_argument("output")
    parser.add_argument("--summary")
    parser.add_argument(
        "--ontology-list",
        help="expected 592-entry ontology list; enables missing-ontology audit",
    )
    args = parser.parse_args()

    records = []
    seen = set()
    for path in sorted(glob.glob(os.path.join(args.result_root, "*", "*.jsonl"))):
        with open(path, encoding="utf-8") as handle:
            lines = [line for line in handle if line.strip()]
        if len(lines) != 1:
            raise SystemExit(f"{path}: expected one JSON row, found {len(lines)}")
        row = json.loads(lines[0])
        result_class = classify(row)
        if result_class is None:
            continue
        key = (row["ont"], row["arm"])
        if key in seen:
            raise SystemExit(f"duplicate successful pair: {key}")
        seen.add(key)
        records.append(
            {
                "ontology": row["ont"],
                "route": row["arm"],
                "result_class": result_class,
                "status": row["status"],
                "verdict": row["verdict"],
                "wall_s": row.get("wall_s", ""),
                "peak_mb": row.get("peak_mb", ""),
                "binary_sha256": row.get("binary_sha256", ""),
                "gold_kind": row.get("gold_kind", ""),
                "gold_sha256": row.get("gold_sha256", ""),
                "signature_sha256": row.get("signature_sha256", ""),
                "subsumptions": row.get("subsumptions", ""),
                "unsatisfiable": row.get("unsatisfiable", ""),
                "invocation": f"km classify --route {row['arm']} {row['ont']}",
                "evidence_file": os.path.relpath(path, args.result_root),
            }
        )

    records.sort(key=lambda row: (row["ontology"], row["route"]))
    with open(args.output, "w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS, delimiter="\t")
        writer.writeheader()
        writer.writerows(records)

    if args.summary:
        route_counts = Counter(row["route"] for row in records)
        ontology_counts = Counter(row["ontology"] for row in records)
        expected = set()
        if args.ontology_list:
            with open(args.ontology_list, encoding="utf-8") as handle:
                expected = {line.strip() for line in handle if line.strip()}
        summary = {
            "rows": len(records),
            "ontologies_with_a_completing_route": len(ontology_counts),
            "routes_with_a_completion": len(route_counts),
            "result_classes": dict(Counter(row["result_class"] for row in records)),
            "route_counts": dict(sorted(route_counts.items())),
            "ontologies_without_a_completing_route": sorted(
                expected - set(ontology_counts)
            ),
        }
        with open(args.summary, "w", encoding="utf-8") as handle:
            json.dump(summary, handle, indent=2, sort_keys=True)
            handle.write("\n")


if __name__ == "__main__":
    main()
