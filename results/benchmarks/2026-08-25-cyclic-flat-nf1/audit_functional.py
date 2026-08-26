#!/usr/bin/env python3
"""Fail-closed audit of the eight large flat-NF1 functional rows."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path


EXPECTED_IDS = {3524, 8486, 9674, 10689, 11739, 13355, 14459, 16008}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=Path)
    parser.add_argument("v1_ledger", type=Path)
    parser.add_argument("binary_sha256")
    args = parser.parse_args()

    with args.v1_ledger.open(newline="") as stream:
        v1 = {row["ontology"]: row for row in csv.DictReader(stream, delimiter="\t")}
    errors: list[str] = []
    seen: set[int] = set()
    for ontology_id in sorted(EXPECTED_IDS):
        name = f"ore_ont_{ontology_id}.owl"
        terminal = args.results / f"{name}.json"
        checkpoint = args.results / f"{name}.checkpoint.json"
        if not terminal.is_file() or not checkpoint.is_file():
            errors.append(f"missing terminal/checkpoint pair: {name}")
            continue
        if terminal.read_bytes() != checkpoint.read_bytes():
            errors.append(f"checkpoint differs: {name}")
            continue
        row = json.loads(terminal.read_text())
        seen.add(ontology_id)
        if row.get("ont") != name:
            errors.append(f"ontology identity mismatch: {name}")
        if row.get("binary_sha256") != args.binary_sha256:
            errors.append(f"binary mismatch: {name}")
        if row.get("status") != "ok" or row.get("verdict") != "match":
            errors.append(f"nonmatching result: {name}")
        if row.get("selected_route_trace") != "flat_nf1":
            errors.append(f"wrong route: {name} -> {row.get('selected_route_trace')}")
        if row.get("signature_sha256") != v1[name]["signature_sha256"]:
            errors.append(f"v1 signature changed: {name}")
        if row.get("wall_s") is None or row.get("peak_mb") is None:
            errors.append(f"missing performance profile: {name}")

    extra = sorted(
        path.name
        for path in args.results.glob("*.json")
        if not path.name.endswith(".checkpoint.json")
        and path.name not in {f"ore_ont_{value}.owl.json" for value in EXPECTED_IDS}
    )
    if extra:
        errors.append("unexpected terminal rows: " + ", ".join(extra))
    if seen != EXPECTED_IDS:
        errors.append(f"incomplete ID set: {sorted(seen)}")
    print(f"audited={len(seen)}/{len(EXPECTED_IDS)} errors={len(errors)}")
    for error in errors:
        print(f"ERROR {error}")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
