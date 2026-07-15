#!/usr/bin/env python3
"""Aggregate the 592-ontology ORE 14817 closure sweep on IBEX."""

from collections import Counter
import glob
import json
import os


ROOT = "/ibex/scratch/hohndor/km"
BASELINE = os.environ.get(
    "KM_SWEEP_BASELINE_DIR", os.path.join(ROOT, "9724_closure_20260714", "sweep-res")
)
CANDIDATE = os.environ.get(
    "KM_SWEEP_RESULT_DIR",
    os.path.join(ROOT, "14817_closure_20260714", "sweep-res-atleast"),
)


def load(directory):
    rows = {}
    for path in glob.glob(os.path.join(directory, "*.jsonl")):
        with open(path, encoding="utf-8") as stream:
            row = json.load(stream)
        rows[row["ont"]] = row
    return rows


def result_key(row):
    return row["status"], row["verdict"], row.get("extra", 0), row.get("miss", 0)


def main():
    baseline = load(BASELINE)
    candidate = load(CANDIDATE)
    common = sorted(set(baseline) & set(candidate))
    changes = {
        ontology: {
            "before": result_key(baseline[ontology]),
            "after": result_key(candidate[ontology]),
        }
        for ontology in common
        if result_key(baseline[ontology]) != result_key(candidate[ontology])
    }
    exact_regressions = sorted(
        ontology
        for ontology in common
        if baseline[ontology]["verdict"] == "match"
        and candidate[ontology]["verdict"] != "match"
    )
    exact_recoveries = sorted(
        ontology
        for ontology in common
        if baseline[ontology]["verdict"] != "match"
        and candidate[ontology]["verdict"] == "match"
    )
    report = {
        "attempted": len(candidate),
        "status": dict(sorted(Counter(row["status"] for row in candidate.values()).items())),
        "verdict": dict(
            sorted(Counter(row["verdict"] for row in candidate.values()).items())
        ),
        "binary_sha256": sorted(
            {row.get("binary_sha256", "") for row in candidate.values()}
        ),
        "baseline_attempted": len(baseline),
        "common": len(common),
        "changes": changes,
        "exact_regressions": exact_regressions,
        "exact_recoveries": exact_recoveries,
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
