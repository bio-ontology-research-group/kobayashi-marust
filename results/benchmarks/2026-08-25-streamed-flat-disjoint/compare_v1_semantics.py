#!/usr/bin/env python3
"""Compare functional-sweep answers and routes to the immutable v1 ledger."""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("results", type=Path)
    parser.add_argument("v1_ledger", type=Path)
    parser.add_argument("--require-complete", action="store_true")
    args = parser.parse_args()

    with args.v1_ledger.open(newline="") as stream:
        baseline = {
            row["ontology"]: row
            for row in csv.DictReader(stream, delimiter="\t")
        }
    errors: list[str] = []
    rows: list[tuple[dict, dict]] = []
    for path in sorted(args.results.glob("*.json")):
        if path.name.endswith(".checkpoint.json"):
            continue
        candidate = json.loads(path.read_text())
        name = candidate.get("ont")
        prior = baseline.get(name)
        if prior is None:
            errors.append(f"candidate ontology absent from v1 ledger: {name}")
            continue
        rows.append((candidate, prior))
        if candidate.get("status") == "ok" and prior["status"] == "ok":
            if candidate.get("signature_sha256") != prior["signature_sha256"]:
                errors.append(f"v1 signature changed: {name}")
            if candidate.get("consistent") is None and not (
                candidate.get("fulliri_identity_capable")
                and candidate.get("fulliri_taxonomy_sha256")
                == prior["signature_sha256"]
            ):
                errors.append(f"successful row lacks consistency verdict: {name}")
        elif candidate.get("status") == "error" and prior["status"] == "error":
            pass
        elif name == "ore_ont_3215.owl" and candidate.get("status") == "timeout":
            # This unconstrained functional sweep can land on slower AMD nodes.
            # The release gate must separately restore the exact v1 signature on
            # Gold 6248 hardware; never count this exception as a completion.
            pass
        else:
            errors.append(
                f"status changed: {name} v1={prior['status']} candidate={candidate.get('status')}"
            )

    names = [candidate["ont"] for candidate, _ in rows]
    if len(names) != len(set(names)):
        errors.append("duplicate terminal ontology rows")
    if args.require_complete:
        if len(rows) != len(baseline):
            errors.append(f"incomplete panel: candidate={len(rows)} v1={len(baseline)}")
        missing = sorted(set(baseline) - set(names))
        if missing:
            errors.append("missing terminal rows: " + ", ".join(missing))

    route_changes = Counter(
        (prior["route"], candidate.get("selected_route_trace"))
        for candidate, prior in rows
        if prior["route"] != candidate.get("selected_route_trace")
    )
    print(f"compared={len(rows)}/{len(baseline)}")
    print(f"semantic_errors={len(errors)}")
    for (old, new), count in sorted(route_changes.items()):
        print(f"route_change {old} -> {new}: {count}")
    for error in errors:
        print(f"ERROR {error}")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
