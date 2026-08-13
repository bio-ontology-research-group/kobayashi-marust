#!/usr/bin/env python3
"""Require corpus behavior identity and summarize resource changes."""

from __future__ import annotations

import argparse
import json
import statistics
from pathlib import Path


def load(root: Path) -> dict[str, dict]:
    rows = {}
    for path in (root / "results").glob("ore_ont_*.owl.json"):
        row = json.loads(path.read_text())
        rows[row["ont"]] = row
    return rows


def metrics(rows: dict[str, dict]) -> dict[str, float]:
    ok = [row for row in rows.values() if row.get("status") == "ok"]
    wall = [float(row["wall_s"]) for row in ok]
    peak = [float(row["peak_mb"]) for row in ok]
    return {
        "mean_wall_s": statistics.mean(wall),
        "median_wall_s": statistics.median(wall),
        "mean_peak_mb": statistics.mean(peak),
        "median_peak_mb": statistics.median(peak),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    args = parser.parse_args()
    baseline = load(args.baseline)
    candidate = load(args.candidate)
    if len(baseline) != 592 or len(candidate) != 592:
        raise SystemExit(f"expected 592+592 rows, got {len(baseline)}+{len(candidate)}")
    if baseline.keys() != candidate.keys():
        raise SystemExit("ontology sets differ")

    regressions = []
    for ont in sorted(baseline):
        old, new = baseline[ont], candidate[ont]
        for field in ("status", "consistent", "signature_sha256"):
            if old.get(field) != new.get(field):
                regressions.append((ont, field, old.get(field), new.get(field)))
        if old.get("status") == "ok" and new.get("status") != "ok":
            regressions.append((ont, "coverage", "ok", new.get("status")))
    if regressions:
        raise SystemExit(f"behavior regressions: {regressions[:20]}")

    old_metrics = metrics(baseline)
    new_metrics = metrics(candidate)
    summary = {
        "behavior_regressions": 0,
        "baseline": old_metrics,
        "candidate": new_metrics,
        "change": {
            key: new_metrics[key] - old_metrics[key] for key in old_metrics
        },
        "change_pct": {
            key: 100.0 * (new_metrics[key] / old_metrics[key] - 1.0)
            for key in old_metrics
        },
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
