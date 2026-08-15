#!/usr/bin/env python3
"""Audit the same-node, order-balanced v0.2.26/candidate ORE sweep."""

from __future__ import annotations

import collections
import json
import statistics
from pathlib import Path


EXPECTED_BASELINE = "4d8d81378d565d6b5d0b33b8fe352d2e6aa076b7c82a0c196bb58bc167401071"
EXPECTED_CANDIDATE = "628b11d8e95dcedf2394afac53a35399ba1e9106b0e844aae3dbbad41852875a"
EXPECTED_CPU = "Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"
EXPECTED_ONTOLOGIES = 592
EXPECTED_ROUTE_CHANGES = {
    "ore_ont_868.owl",
    "ore_ont_9590.owl",
    "ore_ont_10806.owl",
    "ore_ont_13664.owl",
}
BEHAVIOR_FIELDS = (
    "status", "verdict", "solved", "consistent", "signature_sha256",
    "missing", "extra", "missing_unsat", "extra_unsat",
)
METRIC_FIELDS = ("mean_wall_s", "median_wall_s", "mean_peak_mb", "median_peak_mb")


def load_arm(root: Path, arm: str, expected_hash: str) -> list[dict]:
    result_root = root / f"results-{arm}"
    results = sorted(result_root.glob("ore_ont_*.owl.json"))
    checkpoints = sorted(result_root.glob("ore_ont_*.owl.checkpoint.json"))
    if (len(results), len(checkpoints)) != (EXPECTED_ONTOLOGIES, EXPECTED_ONTOLOGIES):
        raise SystemExit(
            f"{arm}: expected 592 results/checkpoints, got {len(results)}/{len(checkpoints)}"
        )
    rows = [json.loads(path.read_text()) for path in results]
    names = [row.get("ont") for row in rows]
    indices = [int(row["slurm_array_task_id"]) for row in rows]
    if len(set(names)) != EXPECTED_ONTOLOGIES:
        raise SystemExit(f"{arm}: ontology names are not unique")
    if set(indices) != set(range(EXPECTED_ONTOLOGIES)):
        raise SystemExit(f"{arm}: task IDs are not exactly 0..591")
    if {row.get("binary_sha256") for row in rows} != {expected_hash}:
        raise SystemExit(f"{arm}: mixed or unexpected binary hash")
    if {row.get("cpu_model") for row in rows} != {EXPECTED_CPU}:
        raise SystemExit(f"{arm}: mixed or unexpected CPU model")
    if any(not row.get("checkpointed") for row in rows):
        raise SystemExit(f"{arm}: a result lacks its terminal checkpoint")
    if any(not row.get("selected_route_trace") for row in rows):
        raise SystemExit(f"{arm}: a result lacks a selected-route trace")
    return rows


def metrics(rows: list[dict]) -> dict:
    ok = [row for row in rows if row.get("status") == "ok"]
    walls = [float(row["wall_s"]) for row in ok]
    peaks = [float(row["peak_mb"]) for row in ok]
    return {
        "rows": len(rows),
        "successful": len(ok),
        "status": dict(sorted(collections.Counter(row.get("status") for row in rows).items())),
        "verdict": dict(sorted(collections.Counter(row.get("verdict") for row in rows).items())),
        "mean_wall_s": statistics.mean(walls),
        "median_wall_s": statistics.median(walls),
        "mean_peak_mb": statistics.mean(peaks),
        "median_peak_mb": statistics.median(peaks),
    }


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    temporary = sorted(root.glob("**/*.tmp"))
    if temporary:
        raise SystemExit(f"temporary files remain: {temporary[:10]}")

    baseline = load_arm(root, "baseline", EXPECTED_BASELINE)
    candidate = load_arm(root, "candidate", EXPECTED_CANDIDATE)
    baseline_by_ont = {row["ont"]: row for row in baseline}
    candidate_by_ont = {row["ont"]: row for row in candidate}
    if baseline_by_ont.keys() != candidate_by_ont.keys():
        raise SystemExit("baseline and candidate ontology sets differ")

    behavior_differences = {
        ont: {
            field: [baseline_by_ont[ont].get(field), candidate_by_ont[ont].get(field)]
            for field in BEHAVIOR_FIELDS
            if baseline_by_ont[ont].get(field) != candidate_by_ont[ont].get(field)
        }
        for ont in sorted(baseline_by_ont)
    }
    behavior_differences = {ont: fields for ont, fields in behavior_differences.items() if fields}
    if behavior_differences:
        raise SystemExit(f"behavioral differences: {json.dumps(behavior_differences, sort_keys=True)}")

    route_differences = {
        ont: [
            baseline_by_ont[ont].get("selected_route_trace"),
            candidate_by_ont[ont].get("selected_route_trace"),
        ]
        for ont in sorted(baseline_by_ont)
        if baseline_by_ont[ont].get("selected_route_trace")
        != candidate_by_ont[ont].get("selected_route_trace")
    }
    if set(route_differences) != EXPECTED_ROUTE_CHANGES:
        raise SystemExit(f"unexpected route changes: {json.dumps(route_differences, sort_keys=True)}")

    baseline_metrics = metrics(baseline)
    candidate_metrics = metrics(candidate)
    changes = {name: candidate_metrics[name] - baseline_metrics[name] for name in METRIC_FIELDS}
    improvements = {name: changes[name] < 0 for name in METRIC_FIELDS}
    paired_wall_deltas = [
        float(candidate_by_ont[ont]["wall_s"]) - float(baseline_by_ont[ont]["wall_s"])
        for ont in sorted(baseline_by_ont)
        if baseline_by_ont[ont].get("status") == candidate_by_ont[ont].get("status") == "ok"
    ]
    report = {
        "baseline_binary_sha256": EXPECTED_BASELINE,
        "candidate_binary_sha256": EXPECTED_CANDIDATE,
        "behavioral_differences": behavior_differences,
        "route_differences": route_differences,
        "baseline": baseline_metrics,
        "candidate": candidate_metrics,
        "candidate_minus_baseline": changes,
        "improvements": improvements,
        "all_four_improve": all(improvements.values()),
        "paired_wall_delta": {
            "faster": sum(delta < 0 for delta in paired_wall_deltas),
            "equal": sum(delta == 0 for delta in paired_wall_deltas),
            "slower": sum(delta > 0 for delta in paired_wall_deltas),
            "median_s": statistics.median(paired_wall_deltas),
        },
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
