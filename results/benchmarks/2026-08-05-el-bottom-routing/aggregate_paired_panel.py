#!/usr/bin/env python3
"""Strictly validate and summarize the 2a32741 same-node panel."""

from __future__ import annotations

import argparse
import csv
import json
import statistics
from pathlib import Path


BASELINE_SHA = "6dc20602cb531f5a19bc688da5ce4b2e74da18bec95d858574c43128488a42a1"
CANDIDATE_SHA = "d8fd398d79e044e1daada75dff9812960de72bf2dca94399bf4836a1c0bab7b6"
SEMANTIC_FIELDS = (
    "status", "verdict", "solved", "consistent", "consistency_mismatch",
    "subsumptions", "unsatisfiable", "extra", "missing", "extra_unsat",
    "missing_unsat", "reported_incomplete", "signature_sha256",
    "fulliri_taxonomy_sha256",
)


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    expected = {
        row["ontology"]
        for row in csv.DictReader((root / "route-delta.tsv").open(), delimiter="\t")
    }
    if len(expected) != 60:
        raise SystemExit(f"expected 60 route changes, found {len(expected)}")
    results = root / "panel" / "results"
    checkpoints = root / "panel" / "checkpoints"
    if list(results.glob("*.tmp")):
        raise SystemExit("temporary panel results remain")
    if len(list(results.glob("*.json"))) != 120:
        raise SystemExit("expected exactly 120 result files")
    if len(list(checkpoints.glob("*.json"))) != 120:
        raise SystemExit("expected exactly 120 checkpoints")

    rows = []
    for ontology in sorted(expected):
        baseline = load(results / f"baseline__{ontology}.json")
        candidate = load(results / f"candidate__{ontology}.json")
        if baseline.get("binary_sha256") != BASELINE_SHA:
            raise SystemExit(f"baseline binary mismatch for {ontology}")
        if candidate.get("binary_sha256") != CANDIDATE_SHA:
            raise SystemExit(f"candidate binary mismatch for {ontology}")
        if baseline.get("selected_route_trace") != "production_all":
            raise SystemExit(f"baseline route mismatch for {ontology}")
        if candidate.get("selected_route_trace") != "elc":
            raise SystemExit(f"candidate route mismatch for {ontology}")
        differences = {
            field: (baseline.get(field), candidate.get(field))
            for field in SEMANTIC_FIELDS
            if baseline.get(field) != candidate.get(field)
        }
        if differences:
            raise SystemExit(f"semantic regression for {ontology}: {differences}")
        rows.append({
            "ont": ontology,
            "baseline_wall_s": float(baseline["wall_s"]),
            "candidate_wall_s": float(candidate["wall_s"]),
            "wall_delta_s": float(candidate["wall_s"]) - float(baseline["wall_s"]),
            "baseline_peak_mb": float(baseline["peak_mb"]),
            "candidate_peak_mb": float(candidate["peak_mb"]),
            "peak_delta_mb": float(candidate["peak_mb"]) - float(baseline["peak_mb"]),
            "signature_sha256": candidate["signature_sha256"],
        })

    output = root / "paired-results.tsv"
    with output.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)
    summary = {
        "candidate_revision": "2a32741",
        "candidate_binary_sha256": CANDIDATE_SHA,
        "baseline_revision": "e9cb3d1",
        "baseline_binary_sha256": BASELINE_SHA,
        "pairs": len(rows),
        "semantically_identical_pairs": len(rows),
        "baseline_mean_wall_s": sum(row["baseline_wall_s"] for row in rows) / len(rows),
        "candidate_mean_wall_s": sum(row["candidate_wall_s"] for row in rows) / len(rows),
        "baseline_median_wall_s": statistics.median(row["baseline_wall_s"] for row in rows),
        "candidate_median_wall_s": statistics.median(row["candidate_wall_s"] for row in rows),
        "baseline_mean_peak_mb": sum(row["baseline_peak_mb"] for row in rows) / len(rows),
        "candidate_mean_peak_mb": sum(row["candidate_peak_mb"] for row in rows) / len(rows),
        "baseline_median_peak_mb": statistics.median(row["baseline_peak_mb"] for row in rows),
        "candidate_median_peak_mb": statistics.median(row["candidate_peak_mb"] for row in rows),
    }
    (root / "panel-summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
