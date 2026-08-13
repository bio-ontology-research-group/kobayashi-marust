#!/usr/bin/env python3
"""Strictly validate and summarize the positive-EL ABox candidate e9cb3d1 ORE sweep."""

from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import json
import statistics
from pathlib import Path


EXPECTED_BINARY = "6dc20602cb531f5a19bc688da5ce4b2e74da18bec95d858574c43128488a42a1"
EXPECTED_CPU = "Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"
EXPECTED_ONTOLOGIES = 592


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()

    result_paths = sorted((root / "results").glob("ore_ont_*.owl.json"))
    profile_paths = sorted((root / "profiles").glob("ore_ont_*.owl.json"))
    checkpoint_paths = sorted((root / "results").glob("ore_ont_*.owl.checkpoint.json"))
    temporary_paths = sorted(root.glob("**/*.tmp"))
    if len(result_paths) != EXPECTED_ONTOLOGIES:
        raise SystemExit(f"expected 592 results, found {len(result_paths)}")
    if len(profile_paths) != EXPECTED_ONTOLOGIES:
        raise SystemExit(f"expected 592 profiles, found {len(profile_paths)}")
    if len(checkpoint_paths) != EXPECTED_ONTOLOGIES:
        raise SystemExit(f"expected 592 checkpoints, found {len(checkpoint_paths)}")
    if temporary_paths:
        raise SystemExit(f"temporary files remain: {temporary_paths[:10]}")

    rows = [json.loads(path.read_text()) for path in result_paths]
    profiles = [json.loads(path.read_text()) for path in profile_paths]
    names = [row.get("ont") for row in rows]
    indices = [row.get("slurm_array_task_id") for row in rows]
    if len(set(names)) != EXPECTED_ONTOLOGIES:
        raise SystemExit("result ontology names are not unique")
    if {int(index) for index in indices} != set(range(EXPECTED_ONTOLOGIES)):
        raise SystemExit("result array indices are not exactly 0..591")
    if {row.get("binary_sha256") for row in rows} != {EXPECTED_BINARY}:
        raise SystemExit("mixed or unexpected result binary")
    if {row.get("cpu_model") for row in rows} != {EXPECTED_CPU}:
        raise SystemExit("mixed or unexpected CPU model")
    if any(not row.get("checkpointed") for row in rows):
        raise SystemExit("a result lacks its terminal checkpoint")
    if any(
        not row.get("selected_route_trace")
        and not (row.get("ont") == "ore_ont_10860.owl" and row.get("status") == "unsupported")
        for row in rows
    ):
        raise SystemExit("a result lacks its production route trace")
    if {profile.get("ont") for profile in profiles} != set(names):
        raise SystemExit("profile ontology set differs from result ontology set")
    if any(profile.get("status") != "ok" or not profile.get("selected_route") for profile in profiles):
        raise SystemExit("a profile is invalid or lacks a selected route")

    ok = [row for row in rows if row.get("status") == "ok"]
    walls = [float(row["wall_s"]) for row in ok]
    rss = [float(row["peak_mb"]) for row in ok]
    summary = {
        "revision": "e9cb3d1",
        "baseline_release": "v0.2.6",
        "binary_sha256": EXPECTED_BINARY,
        "cpu_model": EXPECTED_CPU,
        "rows": len(rows),
        "status": dict(sorted(collections.Counter(row.get("status") for row in rows).items())),
        "verdict": dict(sorted(collections.Counter(row.get("verdict") for row in rows).items())),
        "routes": dict(sorted(collections.Counter(row.get("selected_route_trace") for row in rows).items(), key=lambda item: str(item[0]))),
        "mean_wall_s": sum(walls) / len(walls),
        "median_wall_s": statistics.median(walls),
        "mean_peak_mb": sum(rss) / len(rss),
        "median_peak_mb": statistics.median(rss),
    }

    tsv_path = root / "automatic-results.tsv"
    fields = [
        "ont", "status", "verdict", "solved", "consistent", "wall_s", "peak_mb",
        "selected_route_trace", "signature_sha256", "binary_sha256", "host", "cpu_model",
        "slurm_array_job_id", "slurm_array_task_id",
    ]
    with tsv_path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, delimiter="\t", extrasaction="ignore")
        writer.writeheader()
        writer.writerows(sorted(rows, key=lambda row: int(row["slurm_array_task_id"])))
    summary["automatic_results_sha256"] = sha256(tsv_path)
    (root / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
