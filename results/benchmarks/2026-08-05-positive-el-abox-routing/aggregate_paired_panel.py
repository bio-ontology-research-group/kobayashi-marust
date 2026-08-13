#!/usr/bin/env python3
"""Validate and summarize the positive-EL ABox same-node panel."""

from __future__ import annotations

import argparse
import csv
import json
import statistics
from pathlib import Path


BASELINE_SHA = "7ac98a33a26579d9a2e3abaf95dfd8fba44e2dc842db1d12ce65144dd1a5c0f1"
CANDIDATE_SHA = "6dc20602cb531f5a19bc688da5ce4b2e74da18bec95d858574c43128488a42a1"
EXPECTED = {
    "ore_ont_1012.owl", "ore_ont_1212.owl", "ore_ont_1306.owl",
    "ore_ont_1370.owl", "ore_ont_2046.owl", "ore_ont_2253.owl",
    "ore_ont_2266.owl", "ore_ont_3313.owl", "ore_ont_3954.owl",
    "ore_ont_4033.owl", "ore_ont_4054.owl", "ore_ont_4527.owl",
    "ore_ont_4557.owl", "ore_ont_4662.owl", "ore_ont_5519.owl",
    "ore_ont_5602.owl", "ore_ont_5755.owl", "ore_ont_5760.owl",
    "ore_ont_6102.owl", "ore_ont_6233.owl", "ore_ont_6817.owl",
    "ore_ont_7251.owl", "ore_ont_7993.owl", "ore_ont_8175.owl",
    "ore_ont_8744.owl", "ore_ont_9567.owl", "ore_ont_9761.owl",
    "ore_ont_9768.owl", "ore_ont_9772.owl", "ore_ont_10750.owl",
    "ore_ont_12528.owl", "ore_ont_13482.owl", "ore_ont_13755.owl",
    "ore_ont_13969.owl", "ore_ont_14216.owl", "ore_ont_14543.owl",
    "ore_ont_15280.owl", "ore_ont_15860.owl",
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
        "candidate_revision": "e9cb3d1",
        "candidate_binary_sha256": CANDIDATE_SHA,
        "baseline_release": "v0.2.6",
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
