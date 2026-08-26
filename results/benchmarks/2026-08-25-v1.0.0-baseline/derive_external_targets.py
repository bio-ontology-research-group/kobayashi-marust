#!/usr/bin/env python3
"""Derive aggregate and per-ontology external performance gates.

Only empirically sound-and-complete, terminally successful answers can set a
target. For v1.2, KM must be strictly below the minimum wall and peak RSS among
the four named external reasoners for each ontology having such a reference.
"""

from __future__ import annotations

import argparse
import csv
import gzip
import json
import statistics
from collections import defaultdict
from pathlib import Path


ARMS = ("konclude", "elk", "hermit", "sequoia_strict")


def rows(path: Path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", newline="") as handle:
        yield from csv.DictReader(handle, delimiter="\t")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("panel", type=Path)
    parser.add_argument("--targets", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    args = parser.parse_args()

    accepted = defaultdict(list)
    by_arm = defaultdict(list)
    for row in rows(args.panel):
        arm = row["arm"]
        if arm not in ARMS:
            continue
        if not (
            row["status"] == "ok"
            and row["sound"] == "yes"
            and row["complete"] == "yes"
        ):
            continue
        record = {
            "ontology": row["ontology"],
            "arm": arm,
            "wall_s": float(row["wall_s"]),
            "peak_mib": float(row["peak_mb"]),
        }
        accepted[row["ontology"]].append(record)
        by_arm[arm].append(record)

    target_rows = []
    for ontology in sorted(accepted):
        candidates = accepted[ontology]
        wall = min(candidates, key=lambda item: item["wall_s"])
        peak = min(candidates, key=lambda item: item["peak_mib"])
        target_rows.append(
            {
                "ontology": ontology,
                "wall_target_s_exclusive": wall["wall_s"],
                "wall_target_arm": wall["arm"],
                "peak_target_mib_exclusive": peak["peak_mib"],
                "peak_target_arm": peak["arm"],
                "correct_external_arms": ",".join(
                    sorted(item["arm"] for item in candidates)
                ),
            }
        )

    args.targets.parent.mkdir(parents=True, exist_ok=True)
    with args.targets.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=target_rows[0], delimiter="\t")
        writer.writeheader()
        writer.writerows(target_rows)

    summary = {"eligible_ontologies": len(target_rows), "arms": {}}
    for arm in ARMS:
        records = by_arm[arm]
        walls = sorted(item["wall_s"] for item in records)
        peaks = sorted(item["peak_mib"] for item in records)
        summary["arms"][arm] = {
            "correct_completions": len(records),
            "mean_wall_s": sum(walls) / len(walls),
            "median_wall_s": statistics.median(walls),
            "mean_peak_mib": sum(peaks) / len(peaks),
            "median_peak_mib": statistics.median(peaks),
        }
    args.summary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
