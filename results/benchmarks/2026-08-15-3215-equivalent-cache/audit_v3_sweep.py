#!/usr/bin/env python3
"""Validate V3's strict sweep and compare it with the v0.2.26 sweep."""

from __future__ import annotations

import argparse
import collections
import json
import statistics
from pathlib import Path


EXPECTED_BINARY = "eb2f4335500dd4c6621676f4c87636a30867fe0d5484a3b879841f423adc4c84"
EXPECTED_BASELINE = "4d8d81378d565d6b5d0b33b8fe352d2e6aa076b7c82a0c196bb58bc167401071"
EXPECTED_CPU = "Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"
EXPECTED_ONTOLOGIES = 592


def load_and_validate(root: Path, expected_binary: str) -> list[dict]:
    result_paths = sorted((root / "results").glob("ore_ont_*.owl.json"))
    profile_paths = sorted((root / "profiles").glob("ore_ont_*.owl.json"))
    checkpoint_paths = sorted((root / "results").glob("ore_ont_*.owl.checkpoint.json"))
    temporary_paths = sorted(root.glob("**/*.tmp"))
    counts = (len(result_paths), len(profile_paths), len(checkpoint_paths))
    if counts != (EXPECTED_ONTOLOGIES,) * 3:
        raise SystemExit(f"invalid result/profile/checkpoint counts: {counts}")
    if temporary_paths:
        raise SystemExit(f"temporary files remain: {temporary_paths[:10]}")

    rows = [json.loads(path.read_text()) for path in result_paths]
    profiles = [json.loads(path.read_text()) for path in profile_paths]
    names = [row.get("ont") for row in rows]
    indices = [int(row["slurm_array_task_id"]) for row in rows]
    if len(set(names)) != EXPECTED_ONTOLOGIES:
        raise SystemExit("ontology names are not unique")
    if set(indices) != set(range(EXPECTED_ONTOLOGIES)):
        raise SystemExit("array indices are not exactly 0..591")
    if {row.get("binary_sha256") for row in rows} != {expected_binary}:
        raise SystemExit("mixed or unexpected binary hash")
    if {row.get("cpu_model") for row in rows} != {EXPECTED_CPU}:
        raise SystemExit("mixed or unexpected CPU model")
    if any(not row.get("checkpointed") for row in rows):
        raise SystemExit("a result lacks a terminal checkpoint")
    if any(not row.get("selected_route_trace") for row in rows):
        raise SystemExit("a result lacks a selected-route trace")
    if {profile.get("ont") for profile in profiles} != set(names):
        raise SystemExit("profile ontology set differs from results")
    if any(profile.get("status") != "ok" or not profile.get("selected_route") for profile in profiles):
        raise SystemExit("a profile is invalid or lacks a selected route")
    return rows


def metrics(rows: list[dict]) -> dict[str, float | int | dict]:
    ok = [row for row in rows if row.get("status") == "ok"]
    walls = [float(row["wall_s"]) for row in ok]
    rss = [float(row["peak_mb"]) for row in ok]
    return {
        "rows": len(rows),
        "successful": len(ok),
        "status": dict(sorted(collections.Counter(row.get("status") for row in rows).items())),
        "verdict": dict(sorted(collections.Counter(row.get("verdict") for row in rows).items())),
        "mean_wall_s": sum(walls) / len(walls),
        "median_wall_s": statistics.median(walls),
        "mean_peak_mb": sum(rss) / len(rss),
        "median_peak_mb": statistics.median(rss),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate", type=Path)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--candidate-hash", default=EXPECTED_BINARY)
    parser.add_argument("--baseline-hash", default=EXPECTED_BASELINE)
    parser.add_argument("--allow-route-change", action="store_true")
    args = parser.parse_args()

    candidate = load_and_validate(args.candidate.resolve(), args.candidate_hash)
    baseline = load_and_validate(args.baseline.resolve(), args.baseline_hash)
    candidate_by_ont = {row["ont"]: row for row in candidate}
    baseline_by_ont = {row["ont"]: row for row in baseline}
    if candidate_by_ont.keys() != baseline_by_ont.keys():
        raise SystemExit("candidate and baseline ontology sets differ")

    behavior_fields = (
        "status", "verdict", "solved", "consistent", "signature_sha256",
        "missing", "extra", "missing_unsat", "extra_unsat",
    )
    differences = {
        ont: {
            field: [baseline_by_ont[ont].get(field), candidate_by_ont[ont].get(field)]
            for field in behavior_fields
            if baseline_by_ont[ont].get(field) != candidate_by_ont[ont].get(field)
        }
        for ont in sorted(candidate_by_ont)
    }
    differences = {ont: fields for ont, fields in differences.items() if fields}
    if differences:
        raise SystemExit(f"behavioral differences: {json.dumps(differences, sort_keys=True)}")
    route_differences = {
        ont: [baseline_by_ont[ont].get("selected_route_trace"), candidate_by_ont[ont].get("selected_route_trace")]
        for ont in sorted(candidate_by_ont)
        if baseline_by_ont[ont].get("selected_route_trace")
        != candidate_by_ont[ont].get("selected_route_trace")
    }
    if route_differences and not args.allow_route_change:
        raise SystemExit(f"route differences: {json.dumps(route_differences, sort_keys=True)}")

    baseline_metrics = metrics(baseline)
    candidate_metrics = metrics(candidate)
    metric_names = ("mean_wall_s", "median_wall_s", "mean_peak_mb", "median_peak_mb")
    changes = {
        name: candidate_metrics[name] - baseline_metrics[name]
        for name in metric_names
    }
    improvements = {name: changes[name] < 0 for name in metric_names}
    report = {
        "candidate_binary_sha256": args.candidate_hash,
        "baseline_binary_sha256": args.baseline_hash,
        "behavioral_differences": differences,
        "route_differences": route_differences,
        "baseline": baseline_metrics,
        "candidate": candidate_metrics,
        "candidate_minus_baseline": changes,
        "all_four_improve": all(improvements.values()),
        "improvements": improvements,
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
