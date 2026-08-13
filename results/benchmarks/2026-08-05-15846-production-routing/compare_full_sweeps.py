#!/usr/bin/env python3
"""Reject any semantic, coverage, or unintended routing change versus v0.2.6."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path


BASELINE_SHA = "7ac98a33a26579d9a2e3abaf95dfd8fba44e2dc842db1d12ce65144dd1a5c0f1"
CANDIDATE_SHA = "7e0e28e77a0c86d937f814198a0c85ad35ea086c91d5fefa70b5fd0c3dc775b7"
EXPECTED_ONTOLOGIES = 592
SEMANTIC_FIELDS = (
    "status", "verdict", "solved", "consistent", "consistency_mismatch",
    "subsumptions", "unsatisfiable", "extra", "missing", "extra_unsat",
    "missing_unsat", "reported_incomplete", "signature_sha256",
    "fulliri_taxonomy_sha256",
)


def load_results(root: Path) -> dict[str, dict]:
    rows = {}
    for path in sorted((root / "results").glob("ore_ont_*.owl.json")):
        row = json.loads(path.read_text())
        ontology = row.get("ont")
        if ontology in rows:
            raise SystemExit(f"duplicate result for {ontology}")
        rows[ontology] = row
    if len(rows) != EXPECTED_ONTOLOGIES:
        raise SystemExit(f"expected 592 results under {root}, found {len(rows)}")
    return rows


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    args = parser.parse_args()
    baseline_root = args.baseline.resolve()
    candidate_root = args.candidate.resolve()
    baseline = load_results(baseline_root)
    candidate = load_results(candidate_root)
    expected_rows = list(csv.DictReader(
        (candidate_root / "route-delta-v026.tsv").open(), delimiter="\t"
    ))
    expected_changed = {row["ontology"] for row in expected_rows}
    if len(expected_rows) != 99 or len(expected_changed) != 99:
        raise SystemExit("expected exactly 99 unique source-bound route changes")
    expected_transitions = {
        ("production_all", "elc"),
        ("certified_nominals", "production_all"),
    }
    if any(
        (row["old_route"], row["new_route"]) not in expected_transitions
        for row in expected_rows
    ):
        raise SystemExit("route-delta-v026.tsv contains an unexpected transition")
    if set(baseline) != set(candidate):
        raise SystemExit("baseline and candidate ontology sets differ")

    regressions = {}
    route_changes = {}
    for ontology in sorted(baseline):
        old = baseline[ontology]
        new = candidate[ontology]
        if old.get("binary_sha256") != BASELINE_SHA:
            raise SystemExit(f"baseline binary mismatch for {ontology}")
        if new.get("binary_sha256") != CANDIDATE_SHA:
            raise SystemExit(f"candidate binary mismatch for {ontology}")
        differences = {
            field: (old.get(field), new.get(field))
            for field in SEMANTIC_FIELDS
            if old.get(field) != new.get(field)
        }
        if differences:
            regressions[ontology] = differences
        old_route = old.get("selected_route_trace")
        new_route = new.get("selected_route_trace")
        if old_route != new_route:
            route_changes[ontology] = (old_route, new_route)

    if regressions:
        sample = dict(list(regressions.items())[:10])
        raise SystemExit(f"semantic or coverage regressions ({len(regressions)}): {sample}")
    expected_by_ontology = {
        row["ontology"]: (row["old_route"], row["new_route"])
        for row in expected_rows
    }
    unexpected_routes = {
        ontology: routes
        for ontology, routes in route_changes.items()
        if routes != expected_by_ontology.get(ontology)
    }
    if unexpected_routes:
        raise SystemExit(f"unexpected route changes: {unexpected_routes}")
    if set(route_changes) != expected_changed:
        missing = sorted(expected_changed - set(route_changes))
        extra = sorted(set(route_changes) - expected_changed)
        raise SystemExit(
            f"wrong route-change set: missing={missing}, extra={extra}"
        )

    summary = {
        "ontologies": len(candidate),
        "semantic_regressions": 0,
        "coverage_regressions": 0,
        "route_changes": len(route_changes),
        "route_transitions": {
            "production_all -> elc": 98,
            "certified_nominals -> production_all": 1,
        },
        "changed_ontologies": sorted(route_changes),
    }
    output = candidate_root / "comparison-v026.json"
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
