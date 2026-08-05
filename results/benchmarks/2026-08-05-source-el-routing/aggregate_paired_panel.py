#!/usr/bin/env python3
"""Validate and summarize the source-EL same-node panel."""

from __future__ import annotations

import argparse
import csv
import json
import statistics
from pathlib import Path


BASELINE_SHA = "4812d656144b4b822523acf97d6500238391aff5912078868535604f1aef22b1"
CANDIDATE_SHA = "7ac98a33a26579d9a2e3abaf95dfd8fba44e2dc842db1d12ce65144dd1a5c0f1"
EXPECTED = {
    "ore_ont_15059.owl", "ore_ont_11395.owl", "ore_ont_14042.owl",
    "ore_ont_3836.owl", "ore_ont_9498.owl", "ore_ont_9794.owl",
    "ore_ont_10445.owl", "ore_ont_4802.owl", "ore_ont_11389.owl",
    "ore_ont_2243.owl", "ore_ont_10248.owl", "ore_ont_14607.owl",
    "ore_ont_15929.owl", "ore_ont_11293.owl", "ore_ont_5927.owl",
    "ore_ont_6198.owl", "ore_ont_8864.owl", "ore_ont_15178.owl",
}
SEMANTIC_FIELDS = (
    "status", "verdict", "solved", "consistent", "consistency_mismatch",
    "subsumptions", "unsatisfiable", "extra", "missing", "extra_unsat",
    "missing_unsat", "reported_incomplete", "signature_sha256",
)


def load(path: Path) -> dict:
    return json.loads(path.read_text())


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    results = root / "results"
    if list(results.glob("*.tmp")):
        raise SystemExit("temporary panel results remain")

    rows = []
    for ontology in sorted(EXPECTED):
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

    with (root / "paired-results.tsv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)

    summary = {
        "candidate_revision": "3938b30",
        "candidate_binary_sha256": CANDIDATE_SHA,
        "baseline_release": "v0.2.5",
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
