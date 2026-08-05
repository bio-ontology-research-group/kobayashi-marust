#!/usr/bin/env python3
"""Audit an in-progress candidate sweep without relying on cluster utilities."""

from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path


BASELINE_SHA = "4812d656144b4b822523acf97d6500238391aff5912078868535604f1aef22b1"
CANDIDATE_SHA = "7ac98a33a26579d9a2e3abaf95dfd8fba44e2dc842db1d12ce65144dd1a5c0f1"
SEMANTIC_FIELDS = (
    "status", "verdict", "solved", "consistent", "consistency_mismatch",
    "subsumptions", "unsatisfiable", "extra", "missing", "extra_unsat",
    "missing_unsat", "reported_incomplete", "signature_sha256",
    "fulliri_taxonomy_sha256",
)
FAILURE_MARKERS = (
    "PROFILE_FAILED", "Traceback", "UNEXPECTED_CPU", "runner did not",
    "missing production route",
)


def load_rows(root: Path) -> dict[str, dict]:
    rows = {}
    for path in (root / "results").glob("ore_ont_*.owl.json"):
        row = json.loads(path.read_text())
        ontology = row.get("ont")
        if not ontology or ontology in rows:
            raise SystemExit(f"invalid or duplicate result: {path}")
        rows[ontology] = row
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--jobs", nargs="*", default=[])
    args = parser.parse_args()
    baseline_root = args.baseline.resolve()
    candidate_root = args.candidate.resolve()
    baseline = load_rows(baseline_root)
    candidate = load_rows(candidate_root)

    semantic_differences = {}
    route_changes = {}
    for ontology, new in candidate.items():
        old = baseline.get(ontology)
        if old is None:
            raise SystemExit(f"candidate ontology absent from baseline: {ontology}")
        if old.get("binary_sha256") != BASELINE_SHA:
            raise SystemExit(f"baseline binary mismatch: {ontology}")
        if new.get("binary_sha256") != CANDIDATE_SHA:
            raise SystemExit(f"candidate binary mismatch: {ontology}")
        if not new.get("checkpointed"):
            raise SystemExit(f"candidate lacks terminal checkpoint: {ontology}")
        differences = {
            field: (old.get(field), new.get(field))
            for field in SEMANTIC_FIELDS
            if old.get(field) != new.get(field)
        }
        if differences:
            semantic_differences[ontology] = differences
        old_route = old.get("selected_route_trace")
        new_route = new.get("selected_route_trace")
        if old_route != new_route:
            route_changes[ontology] = (old_route, new_route)

    unexpected_routes = {
        ontology: routes
        for ontology, routes in route_changes.items()
        if routes != ("production_all", "elc")
    }
    log_paths = []
    for job in args.jobs:
        log_paths.extend(candidate_root.glob(f"slurm-{job}_*.out"))
    bad_logs = {}
    completed_logs = 0
    for path in log_paths:
        text = path.read_text(errors="replace")
        markers = [marker for marker in FAILURE_MARKERS if marker in text]
        if markers:
            bad_logs[path.name] = markers
        if "TASK_COMPLETE" in text or "ALREADY_COMPLETE" in text:
            completed_logs += 1

    summary = {
        "results": len(candidate),
        "profiles": len(list((candidate_root / "profiles").glob("ore_ont_*.owl.json"))),
        "checkpoints": len(list((candidate_root / "results").glob("ore_ont_*.owl.checkpoint.json"))),
        "temporary_files": len(list(candidate_root.glob("**/*.tmp"))),
        "status": dict(collections.Counter(row.get("status") for row in candidate.values())),
        "verdict": dict(collections.Counter(row.get("verdict") for row in candidate.values())),
        "semantic_differences": semantic_differences,
        "route_changes": len(route_changes),
        "route_transitions": dict(collections.Counter(str(routes) for routes in route_changes.values())),
        "unexpected_route_changes": unexpected_routes,
        "logs": len(log_paths),
        "completed_logs": completed_logs,
        "bad_logs": bad_logs,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    if semantic_differences or unexpected_routes or bad_logs:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
