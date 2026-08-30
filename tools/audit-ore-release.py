#!/usr/bin/env python3
"""Fail-closed audit for an automatic-route ORE release sweep."""

from __future__ import annotations

import argparse
import collections
import json
import statistics
from pathlib import Path


GOLD_6248 = "Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"
SEMANTIC_FIELDS = (
    "status",
    "verdict",
    "rc",
    "solved",
    "consistent",
    "consistency_mismatch",
    "reported_incomplete",
    "signature_sha256",
    "subsumptions",
    "unsatisfiable",
    "missing",
    "extra",
    "missing_unsat",
    "extra_unsat",
    "selected_route_trace",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path, help="sweep directory containing ore592.txt")
    parser.add_argument("--binary-sha256", required=True)
    parser.add_argument("--release", required=True)
    parser.add_argument("--owner-job", required=True)
    parser.add_argument("--baseline", type=Path, help="prior sweep directory")
    return parser.parse_args()


def load(path: Path) -> dict:
    with path.open(encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise AssertionError(f"expected JSON object: {path}")
    return value


def result_path(root: Path, ontology: str) -> Path:
    return root / "results" / f"{ontology}.json"


def audit() -> dict:
    args = parse_args()
    root = args.root.resolve()
    ontologies = [line.strip() for line in (root / "ore592.txt").read_text().splitlines() if line.strip()]
    assert len(ontologies) == 592, f"expected 592 ontology rows, got {len(ontologies)}"
    assert len(set(ontologies)) == 592, "duplicate ontology in ore592.txt"

    rows: list[dict] = []
    profiles: list[dict] = []
    semantic_differences: list[dict] = []
    for index, ontology in enumerate(ontologies):
        result_file = result_path(root, ontology)
        checkpoint_file = root / "results" / f"{ontology}.checkpoint.json"
        profile_file = root / "profiles" / f"{ontology}.json"
        for required in (result_file, checkpoint_file, profile_file):
            assert required.is_file(), f"missing record: {required}"
        assert result_file.read_bytes() == checkpoint_file.read_bytes(), (
            f"checkpoint differs from result: {ontology}"
        )

        row = load(result_file)
        profile = load(profile_file)
        assert row.get("ontology_index") == str(index), f"wrong index: {ontology}"
        assert row.get("slurm_array_task_id") == str(index), f"wrong task: {ontology}"
        assert row.get("ont") == ontology, f"wrong ontology in result: {ontology}"
        assert profile.get("ont") == ontology, f"wrong ontology in profile: {ontology}"
        assert profile.get("status") == "ok", f"profile failed: {ontology}"
        assert row.get("binary_sha256") == args.binary_sha256, f"wrong binary: {ontology}"
        assert row.get("cpu_model") == GOLD_6248, f"wrong CPU: {ontology}"
        assert row.get("cpus") == 16, f"wrong CPU allocation: {ontology}"
        assert row.get("requested_route") == "auto", f"forced route: {ontology}"
        assert row.get("explicit_environment") == ["KM_ROUTE=auto"], (
            f"unexpected environment: {ontology}"
        )
        assert row.get("checkpointed") is True, f"not checkpointed: {ontology}"

        if args.baseline:
            baseline = load(result_path(args.baseline.resolve(), ontology))
            difference = {
                field: {"baseline": baseline.get(field), "candidate": row.get(field)}
                for field in SEMANTIC_FIELDS
                if baseline.get(field) != row.get(field)
            }
            if difference:
                semantic_differences.append({"ontology": ontology, "fields": difference})
        rows.append(row)
        profiles.append(profile)

    assert not semantic_differences, json.dumps(semantic_differences, sort_keys=True)
    ok = [row for row in rows if row.get("status") == "ok"]
    assert all(isinstance(row.get("wall_s"), (int, float)) for row in ok)
    assert all(isinstance(row.get("peak_mb"), (int, float)) for row in ok)

    return {
        "schema": 1,
        "release": args.release,
        "owner_job": args.owner_job,
        "binary_sha256": args.binary_sha256,
        "records": {"profiles": len(profiles), "results": len(rows), "checkpoints": len(rows)},
        "status": dict(sorted(collections.Counter(row["status"] for row in rows).items())),
        "verdict": dict(sorted(collections.Counter(row["verdict"] for row in rows).items())),
        "routes": dict(
            sorted(collections.Counter(profile["selected_route"] for profile in profiles).items())
        ),
        "execution_routes": dict(
            sorted(collections.Counter(row["selected_route_trace"] for row in rows).items())
        ),
        "metrics": {
            "correct_completions": len(ok),
            "mean_wall_s": sum(row["wall_s"] for row in ok) / len(ok),
            "median_wall_s": statistics.median(row["wall_s"] for row in ok),
            "mean_peak_mb": sum(row["peak_mb"] for row in ok) / len(ok),
            "median_peak_mb": statistics.median(row["peak_mb"] for row in ok),
        },
        "semantic_differences_from_baseline": semantic_differences,
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))
