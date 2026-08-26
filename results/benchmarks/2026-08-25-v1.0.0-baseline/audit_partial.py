#!/usr/bin/env python3
"""Validate a partial strict sweep and report current performance gates."""

from __future__ import annotations

import argparse
import csv
import json
import statistics
from pathlib import Path


TERMINAL = {"ok", "timeout", "memout", "error", "unsupported"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--binary-sha256", required=True)
    parser.add_argument("--targets", type=Path, required=True)
    args = parser.parse_args()

    targets = {
        row["ontology"]: row
        for row in csv.DictReader(args.targets.open(), delimiter="\t")
    }
    temporary = sorted(args.root.rglob("*.tmp"))
    if temporary:
        raise SystemExit(f"temporary outputs remain: {temporary[:10]}")

    rows = []
    seen = set()
    for path in sorted((args.root / "results").glob("ore_ont_*.owl.json")):
        row = json.loads(path.read_text())
        ontology = row.get("ont")
        if ontology in seen:
            raise SystemExit(f"duplicate terminal ontology: {ontology}")
        seen.add(ontology)
        if path.name != f"{ontology}.json":
            raise SystemExit(f"result/path mismatch: {path} vs {ontology}")
        if row.get("status") not in TERMINAL:
            raise SystemExit(f"invalid terminal status: {row}")
        if row.get("binary_sha256") != args.binary_sha256:
            raise SystemExit(f"binary mismatch: {ontology}")
        if not row.get("checkpointed"):
            raise SystemExit(f"result is not checkpointed: {ontology}")
        profile_path = args.root / "profiles" / f"{ontology}.json"
        if not profile_path.exists():
            raise SystemExit(f"missing profile: {ontology}")
        profile = json.loads(profile_path.read_text())
        if profile.get("ont") != ontology or profile.get("status") != "ok":
            raise SystemExit(f"invalid profile: {ontology}")
        if not profile.get("selected_route"):
            raise SystemExit(f"profile lacks selected route: {ontology}")
        if not row.get("selected_route_trace") and ontology != "ore_ont_10860.owl":
            raise SystemExit(f"result lacks route trace: {ontology}")
        rows.append(row)

    successful = [row for row in rows if row["status"] == "ok"]
    exact = [row for row in successful if row.get("verdict") == "match"]
    walls = [float(row["wall_s"]) for row in successful]
    peaks = [float(row["peak_mb"]) for row in successful]
    wall_wins = peak_wins = both_wins = comparable = 0
    for row in successful:
        target = targets.get(row["ont"])
        if target is None:
            continue
        comparable += 1
        wall = float(row["wall_s"]) < float(target["wall_target_s_exclusive"])
        peak = float(row["peak_mb"]) < float(target["peak_target_mib_exclusive"])
        wall_wins += wall
        peak_wins += peak
        both_wins += wall and peak

    summary = {
        "terminal": len(rows),
        "successful": len(successful),
        "exact_matches": len(exact),
        "mean_wall_s": sum(walls) / len(walls) if walls else None,
        "median_wall_s": statistics.median(walls) if walls else None,
        "mean_peak_mib": sum(peaks) / len(peaks) if peaks else None,
        "median_peak_mib": statistics.median(peaks) if peaks else None,
        "externally_comparable": comparable,
        "wall_wins": wall_wins,
        "peak_wins": peak_wins,
        "both_wins": both_wins,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
