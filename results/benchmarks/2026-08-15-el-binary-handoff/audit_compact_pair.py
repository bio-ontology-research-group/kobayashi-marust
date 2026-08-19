#!/usr/bin/env python3
"""Audit the order-balanced v0.2.27 versus compact-handoff ORE pair."""

from __future__ import annotations

import argparse
import collections
import json
import statistics
from pathlib import Path


ONTOLOGIES = 592
SUCCESSFUL = 591
BASELINE_SHA = "628b11d8e95dcedf2394afac53a35399ba1e9106b0e844aae3dbbad41852875a"
CANDIDATE_SHA = "1cd7dcbeea96e39b4b4b50eec48e42a9005e223a26515661b6329e746578033c"
SEMANTIC_KEYS = (
    "status",
    "verdict",
    "signature_sha256",
    "consistent",
    "missing",
    "extra",
    "missing_unsat",
    "extra_unsat",
    "subsumptions",
    "unsatisfiable",
)


def metrics(rows: list[dict]) -> dict[str, float | int]:
    ok = [row for row in rows if row["status"] == "ok"]
    assert len(ok) == SUCCESSFUL, len(ok)
    wall = [float(row["wall_s"]) for row in ok]
    rss = [float(row["peak_mb"]) for row in ok]
    return {
        "successful": len(ok),
        "wall_mean_s": sum(wall) / len(wall),
        "wall_median_s": statistics.median(wall),
        "peak_mean_mib": sum(rss) / len(rss),
        "peak_median_mib": statistics.median(rss),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    results = root / "results"

    assert not list(root.glob("**/*.tmp")), "temporary outputs remain"
    result_paths = sorted(
        path for path in results.glob("*.json") if not path.name.endswith(".checkpoint.json")
    )
    checkpoint_paths = sorted(results.glob("*.checkpoint.json"))
    assert len(result_paths) == 2 * ONTOLOGIES, len(result_paths)
    assert len(checkpoint_paths) == 2 * ONTOLOGIES, len(checkpoint_paths)

    paired: dict[str, dict[str, dict]] = collections.defaultdict(dict)
    for path in result_paths:
        row = json.loads(path.read_text())
        arm = row["arm"].split("-", 1)[1]
        assert arm in {"baseline", "candidate"}, row["arm"]
        expected_sha = BASELINE_SHA if arm == "baseline" else CANDIDATE_SHA
        assert row["binary_sha256"] == expected_sha, (path, row["binary_sha256"])
        assert arm not in paired[row["ont"]], (row["ont"], arm)
        paired[row["ont"]][arm] = row

    assert len(paired) == ONTOLOGIES, len(paired)
    semantic_differences = []
    route_differences = []
    arms = {"baseline": [], "candidate": []}
    for ontology, pair in sorted(paired.items()):
        assert set(pair) == {"baseline", "candidate"}, (ontology, set(pair))
        baseline = pair["baseline"]
        candidate = pair["candidate"]
        arms["baseline"].append(baseline)
        arms["candidate"].append(candidate)
        changed = [key for key in SEMANTIC_KEYS if baseline.get(key) != candidate.get(key)]
        if changed:
            semantic_differences.append({"ontology": ontology, "keys": changed})
        if baseline.get("selected_route_trace") != candidate.get("selected_route_trace"):
            route_differences.append(ontology)

    assert not semantic_differences, semantic_differences
    assert not route_differences, route_differences
    for arm, rows in arms.items():
        counts = collections.Counter(row["status"] for row in rows)
        assert counts == {"ok": SUCCESSFUL, "error": 1}, (arm, counts)
        errors = [row["ont"] for row in rows if row["status"] != "ok"]
        assert errors == ["ore_ont_1194.owl"], (arm, errors)

    baseline_metrics = metrics(arms["baseline"])
    candidate_metrics = metrics(arms["candidate"])
    report = {
        "baseline_sha256": BASELINE_SHA,
        "candidate_sha256": CANDIDATE_SHA,
        "ontologies": ONTOLOGIES,
        "semantic_differences": semantic_differences,
        "route_differences": route_differences,
        "baseline": baseline_metrics,
        "candidate": candidate_metrics,
        "delta_candidate_minus_baseline": {
            key: candidate_metrics[key] - baseline_metrics[key]
            for key in (
                "wall_mean_s",
                "wall_median_s",
                "peak_mean_mib",
                "peak_median_mib",
            )
        },
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
