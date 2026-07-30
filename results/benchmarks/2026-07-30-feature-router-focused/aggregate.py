#!/usr/bin/env python3
"""Fail-closed aggregation for the feature-router 592-ontology sweep."""

import argparse
import collections
import json
import pathlib


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ontology-list", required=True, type=pathlib.Path)
    parser.add_argument("--results", required=True, type=pathlib.Path)
    parser.add_argument("--profiles", required=True, type=pathlib.Path)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    args = parser.parse_args()

    ontologies = [line.strip() for line in args.ontology_list.read_text().splitlines()]
    if len(ontologies) != 592 or len(set(ontologies)) != 592:
        raise SystemExit("ontology list must contain exactly 592 unique entries")

    rows = []
    profiles = []
    missing = []
    for ontology in ontologies:
        result_path = args.results / f"{ontology}.json"
        profile_path = args.profiles / f"{ontology}.json"
        if not result_path.is_file() or not profile_path.is_file():
            missing.append(ontology)
            continue
        row = json.loads(result_path.read_text())
        profile = json.loads(profile_path.read_text())
        if row.get("ont") != ontology or not row.get("checkpointed"):
            raise SystemExit(f"invalid terminal result for {ontology}")
        if profile.get("ont") != ontology or profile.get("status") != "ok":
            raise SystemExit(f"invalid profile for {ontology}")
        rows.append(row)
        profiles.append(profile)

    if missing:
        raise SystemExit(f"missing {len(missing)} ontologies: {','.join(missing)}")

    status = collections.Counter(row["status"] for row in rows)
    verdict = collections.Counter(row["verdict"] for row in rows)
    routes = collections.Counter(profile["selected_route"] for profile in profiles)
    exact = [
        row
        for row in rows
        if row["status"] == "ok"
        and row["verdict"] == "match"
        and row.get("missing", 0) == 0
        and row.get("extra", 0) == 0
        and not row.get("consistency_mismatch", False)
    ]
    summary = {
        "schema_version": 1,
        "ontologies": len(rows),
        "exact": len(exact),
        "not_exact": len(rows) - len(exact),
        "status": dict(sorted(status.items())),
        "verdict": dict(sorted(verdict.items())),
        "selected_routes": dict(sorted(routes.items())),
        "binary_sha256": sorted({row["binary_sha256"] for row in rows}),
        "not_exact_ontologies": [
            row["ont"] for row in rows if row not in exact
        ],
    }
    if len(summary["binary_sha256"]) != 1:
        raise SystemExit(f"mixed binaries: {summary['binary_sha256']}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
