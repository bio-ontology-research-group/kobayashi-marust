#!/usr/bin/env python3
"""Extract the immutable v0.2.36 candidate arm and external-target gaps."""

from __future__ import annotations

import argparse
import csv
import json
from collections import defaultdict
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("raw", type=Path)
    parser.add_argument("targets", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("summary", type=Path)
    args = parser.parse_args()

    targets = {
        row["ontology"]: row
        for row in csv.DictReader(args.targets.open(), delimiter="\t")
    }
    rows = []
    for path in sorted(args.raw.glob("*.json")):
        if path.name.endswith(".checkpoint.json"):
            continue
        row = json.loads(path.read_text())
        if not str(row.get("arm", "")).endswith("candidate"):
            continue
        target = targets.get(row["ont"])
        wall_target = float(target["wall_target_s_exclusive"]) if target else None
        peak_target = float(target["peak_target_mib_exclusive"]) if target else None
        wall = float(row["wall_s"])
        peak = float(row["peak_mb"])
        rows.append({
            "ontology": row["ont"],
            "status": row["status"],
            "verdict": row.get("verdict"),
            "route": row.get("selected_route_trace"),
            "wall_s": wall,
            "peak_mib": peak,
            "subsumptions": row.get("subsumptions"),
            "unsatisfiable": row.get("unsatisfiable"),
            "signature_sha256": row.get("signature_sha256"),
            "wall_target_s": wall_target,
            "peak_target_mib": peak_target,
            "wall_excess_s": max(0.0, wall - wall_target) if wall_target is not None else None,
            "peak_excess_mib": max(0.0, peak - peak_target) if peak_target is not None else None,
        })
    if len(rows) != 592 or len({row["ontology"] for row in rows}) != 592:
        raise SystemExit(f"expected 592 unique candidate rows, found {len(rows)}")

    fields = list(rows[0])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fields, delimiter="\t", lineterminator="\n")
        writer.writeheader()
        writer.writerows(sorted(rows, key=lambda row: (-row["wall_s"], row["ontology"])))

    route = defaultdict(lambda: {"count": 0, "wall_s": 0.0, "peak_mib": 0.0})
    ok = [row for row in rows if row["status"] == "ok"]
    for row in ok:
        aggregate = route[row["route"]]
        aggregate["count"] += 1
        aggregate["wall_s"] += row["wall_s"]
        aggregate["peak_mib"] += row["peak_mib"]
    comparable = [row for row in ok if row["wall_target_s"] is not None]
    summary = {
        "rows": len(rows),
        "successful": len(ok),
        "wall_sum_s": sum(row["wall_s"] for row in ok),
        "peak_sum_mib": sum(row["peak_mib"] for row in ok),
        "external_comparable": len(comparable),
        "wall_target_wins": sum(row["wall_excess_s"] == 0 for row in comparable),
        "peak_target_wins": sum(row["peak_excess_mib"] == 0 for row in comparable),
        "both_target_wins": sum(
            row["wall_excess_s"] == 0 and row["peak_excess_mib"] == 0
            for row in comparable
        ),
        "wall_excess_sum_s": sum(row["wall_excess_s"] for row in comparable),
        "peak_excess_sum_mib": sum(row["peak_excess_mib"] for row in comparable),
        "routes": dict(sorted(route.items())),
    }
    args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
