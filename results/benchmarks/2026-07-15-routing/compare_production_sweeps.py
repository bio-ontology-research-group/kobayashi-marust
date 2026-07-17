#!/usr/bin/env python3
"""Strictly validate and compare two 592-row production sweep datasets."""

import argparse
import collections
import glob
import json
import os
import statistics
import sys


TERMINAL = {"ok", "timeout", "memout", "unsupported"}


def load(root, tag, expected_sha):
    result_dir = os.path.join(root, "production-sweeps", tag, "results")
    rows = {}
    problems = []
    for path in sorted(glob.glob(os.path.join(result_dir, "*.jsonl"))):
        try:
            with open(path, encoding="utf-8") as handle:
                values = [json.loads(line) for line in handle if line.strip()]
        except (OSError, ValueError) as exc:
            problems.append(f"{path}: {exc}")
            continue
        if len(values) != 1:
            problems.append(f"{path}: expected one JSON row, found {len(values)}")
            continue
        row = values[0]
        ont = row.get("ont")
        if not ont or ont in rows:
            problems.append(f"{path}: missing or duplicate ontology {ont!r}")
            continue
        if row.get("status") not in TERMINAL:
            problems.append(f"{path}: non-terminal status {row.get('status')!r}")
        if row.get("binary_sha256") != expected_sha:
            problems.append(
                f"{path}: binary SHA {row.get('binary_sha256')!r} != {expected_sha}"
            )
        rows[ont] = row
    if len(rows) != 592:
        problems.append(f"{tag}: expected 592 unique rows, found {len(rows)}")
    if problems:
        raise ValueError("\n".join(problems))
    return rows


def summary(rows):
    exact = [row for row in rows.values() if row.get("verdict") == "match"]
    wall = [row["wall_s"] for row in exact if isinstance(row.get("wall_s"), (int, float))]
    peak = [row["peak_mb"] for row in exact if isinstance(row.get("peak_mb"), (int, float))]
    return {
        "rows": len(rows),
        "status": dict(sorted(collections.Counter(r["status"] for r in rows.values()).items())),
        "verdict": dict(
            sorted(collections.Counter(r.get("verdict") for r in rows.values()).items())
        ),
        # IBEX still provides Python 3.7, before statistics.fmean.  The values
        # are ordinary finite benchmark measurements, so sum/len has the same
        # semantics and keeps the strict comparator runnable where sweeps live.
        "exact_wall_avg_s": sum(wall) / len(wall),
        "exact_wall_median_s": statistics.median(wall),
        "exact_peak_avg_mb": sum(peak) / len(peak),
        "exact_peak_median_mb": statistics.median(peak),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--baseline-tag", required=True)
    parser.add_argument("--baseline-sha", required=True)
    parser.add_argument("--candidate-tag", required=True)
    parser.add_argument("--candidate-sha", required=True)
    args = parser.parse_args()
    try:
        baseline = load(args.root, args.baseline_tag, args.baseline_sha)
        candidate = load(args.root, args.candidate_tag, args.candidate_sha)
    except ValueError as exc:
        print(exc, file=sys.stderr)
        return 2

    changes = []
    for ont in sorted(baseline):
        before, after = baseline[ont], candidate[ont]
        old = (before.get("status"), before.get("verdict"))
        new = (after.get("status"), after.get("verdict"))
        if old != new:
            changes.append({"ont": ont, "before": old, "after": new})
    print(
        json.dumps(
            {
                "baseline": summary(baseline),
                "candidate": summary(candidate),
                "outcome_changes": changes,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
