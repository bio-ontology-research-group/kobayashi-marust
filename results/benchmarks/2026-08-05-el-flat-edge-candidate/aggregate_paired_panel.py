#!/usr/bin/env python3
"""Validate and summarize the same-node v0.2.5/candidate panel."""

from __future__ import annotations

import argparse
import csv
import json
import statistics
from pathlib import Path


BASELINE_SHA = "4812d656144b4b822523acf97d6500238391aff5912078868535604f1aef22b1"
CANDIDATE_SHA = "8f4a8ca4617be1039614b85de9a2ebb2c11e49cc14e7f9d9a444c250f88a315a"
EXPECTED = {
    "ore_ont_1194.owl", "ore_ont_3215.owl", "ore_ont_6934.owl",
    "ore_ont_8737.owl", "ore_ont_16744.owl", "ore_ont_15059.owl",
    "ore_ont_8486.owl",
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
    results = root / "raw"
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
        if baseline.get("ont") != ontology or candidate.get("ont") != ontology:
            raise SystemExit(f"ontology mismatch for {ontology}")
        differences = {
            field: (baseline.get(field), candidate.get(field))
            for field in SEMANTIC_FIELDS
            if baseline.get(field) != candidate.get(field)
        }
        if differences:
            raise SystemExit(f"semantic regression for {ontology}: {differences}")
        rows.append({
            "ont": ontology,
            "status": candidate.get("status"),
            "verdict": candidate.get("verdict"),
            "route": candidate.get("selected_route_trace"),
            "baseline_wall_s": float(baseline["wall_s"]),
            "candidate_wall_s": float(candidate["wall_s"]),
            "wall_delta_s": float(candidate["wall_s"]) - float(baseline["wall_s"]),
            "baseline_peak_mb": float(baseline["peak_mb"]),
            "candidate_peak_mb": float(candidate["peak_mb"]),
            "peak_delta_mb": float(candidate["peak_mb"]) - float(baseline["peak_mb"]),
        })

    with (root / "paired-results.tsv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)

    ok = [row for row in rows if row["status"] == "ok"]
    summary = {
        "candidate_revision": "2624799",
        "candidate_binary_sha256": CANDIDATE_SHA,
        "baseline_release": "v0.2.5",
        "baseline_binary_sha256": BASELINE_SHA,
        "pairs": len(rows),
        "semantically_identical_pairs": len(rows),
        "ok_pairs": len(ok),
        "baseline_mean_wall_s": sum(row["baseline_wall_s"] for row in ok) / len(ok),
        "candidate_mean_wall_s": sum(row["candidate_wall_s"] for row in ok) / len(ok),
        "baseline_median_wall_s": statistics.median(row["baseline_wall_s"] for row in ok),
        "candidate_median_wall_s": statistics.median(row["candidate_wall_s"] for row in ok),
        "baseline_mean_peak_mb": sum(row["baseline_peak_mb"] for row in ok) / len(ok),
        "candidate_mean_peak_mb": sum(row["candidate_peak_mb"] for row in ok) / len(ok),
        "baseline_median_peak_mb": statistics.median(row["baseline_peak_mb"] for row in ok),
        "candidate_median_peak_mb": statistics.median(row["candidate_peak_mb"] for row in ok),
    }
    (root / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
