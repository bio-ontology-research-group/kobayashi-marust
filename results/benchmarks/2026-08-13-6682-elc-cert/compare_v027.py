#!/usr/bin/env python3
"""Reject semantic, coverage, or unintended routing changes versus v0.2.7."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


BASELINE_SHA = "7e0e28e77a0c86d937f814198a0c85ad35ea086c91d5fefa70b5fd0c3dc775b7"
CANDIDATE_SHA = "1abb488945d16df5ba16ee6aa261b1a2aac356b2bfe183b256856c7e28fe9734"
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
        if old.get("selected_route_trace") != new.get("selected_route_trace"):
            route_changes[ontology] = (
                old.get("selected_route_trace"), new.get("selected_route_trace")
            )

    if regressions:
        raise SystemExit(f"semantic or coverage regressions: {regressions}")
    expected = {
        "ore_ont_6682.owl": ("production_all", "certified_el_production")
    }
    if route_changes != expected:
        raise SystemExit(f"unexpected route changes: {route_changes}")

    summary = {
        "ontologies": len(candidate),
        "semantic_regressions": 0,
        "coverage_regressions": 0,
        "route_changes": route_changes,
    }
    output = args.candidate.resolve() / "comparison-v027.json"
    output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
