#!/usr/bin/env python3
"""Reject any semantic, coverage, or unintended routing change versus v0.2.6."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


BASELINE_SHA = "7ac98a33a26579d9a2e3abaf95dfd8fba44e2dc842db1d12ce65144dd1a5c0f1"
CANDIDATE_SHA = "6dc20602cb531f5a19bc688da5ce4b2e74da18bec95d858574c43128488a42a1"
EXPECTED_ONTOLOGIES = 592
EXPECTED_CHANGED = {
    f"ore_ont_{number}.owl"
    for number in (
        1012, 1212, 1306, 1370, 2046, 2253, 2266, 3313, 3954, 4033,
        4054, 4527, 4557, 4662, 5519, 5602, 5755, 5760, 6102, 6233,
        6817, 7251, 7993, 8175, 8744, 9567, 9761, 9768, 9772, 10750,
        12528, 13482, 13755, 13969, 14216, 14543, 15280, 15860,
    )
}
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
    baseline = load_results(args.baseline.resolve())
    candidate = load_results(args.candidate.resolve())
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
    unexpected_routes = {
        ontology: routes
        for ontology, routes in route_changes.items()
        if routes != ("production_all", "elc")
    }
    if unexpected_routes:
        raise SystemExit(f"unexpected route changes: {unexpected_routes}")
    if set(route_changes) != EXPECTED_CHANGED:
        missing = sorted(EXPECTED_CHANGED - set(route_changes))
        extra = sorted(set(route_changes) - EXPECTED_CHANGED)
        raise SystemExit(
            f"wrong production_all -> elc set: missing={missing}, extra={extra}"
        )

    summary = {
        "ontologies": len(candidate),
        "semantic_regressions": 0,
        "coverage_regressions": 0,
        "route_changes": len(route_changes),
        "route_transition": "production_all -> elc",
        "changed_ontologies": sorted(route_changes),
    }
    output = args.candidate.resolve() / "comparison-v026.json"
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
