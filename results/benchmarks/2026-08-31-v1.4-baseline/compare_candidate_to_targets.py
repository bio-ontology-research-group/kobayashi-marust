#!/usr/bin/env python3
"""Compare one complete KM sweep with the adjudicated baseline target ledger."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--targets", type=Path, required=True)
    parser.add_argument("--km-results", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    with args.targets.open(encoding="utf-8", newline="") as stream:
        targets = list(csv.DictReader(stream, delimiter="\t"))
    if len(targets) != 592:
        raise SystemExit(f"expected 592 target rows, found {len(targets)}")

    km: dict[str, dict] = {}
    for path in args.km_results.glob("ore_ont_*.owl.json"):
        row = json.loads(path.read_text(encoding="utf-8"))
        km[row["ont"]] = row
    if len(km) != 592:
        raise SystemExit(f"expected 592 KM records, found {len(km)}")

    fields = (
        "ontology",
        "km_status",
        "km_wall_s",
        "best_baseline_wall_s",
        "wall_ratio",
        "wall_win",
        "km_peak_mb",
        "best_baseline_peak_mb",
        "memory_ratio",
        "memory_win",
        "both_win",
        "baseline_arms",
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        for target in targets:
            ontology = target["ontology"]
            current = km[ontology]
            wall = float(current["wall_s"])
            peak = float(current["peak_mb"])
            best_wall = (
                float(target["best_baseline_wall_s"])
                if target["best_baseline_wall_s"]
                else None
            )
            best_peak = (
                float(target["best_baseline_peak_mb"])
                if target["best_baseline_peak_mb"]
                else None
            )
            solved = current.get("solved") is True and current.get("status") == "ok"
            wall_win = solved and best_wall is not None and wall < best_wall
            memory_win = solved and best_peak is not None and peak < best_peak
            writer.writerow(
                {
                    "ontology": ontology,
                    "km_status": current["status"],
                    "km_wall_s": wall,
                    "best_baseline_wall_s": "" if best_wall is None else best_wall,
                    "wall_ratio": "" if best_wall is None else wall / best_wall,
                    "wall_win": wall_win,
                    "km_peak_mb": peak,
                    "best_baseline_peak_mb": "" if best_peak is None else best_peak,
                    "memory_ratio": "" if best_peak is None else peak / best_peak,
                    "memory_win": memory_win,
                    "both_win": wall_win and memory_win,
                    "baseline_arms": target["baseline_arms"],
                }
            )


if __name__ == "__main__":
    main()
