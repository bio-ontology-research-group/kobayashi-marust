#!/usr/bin/env python3
"""Compare two IBEX ORE sweep JSONL directories by ontology."""

import collections
import glob
import json
import os
import sys


def load(directory):
    rows = {}
    for path in glob.glob(os.path.join(directory, "*.jsonl")):
        with open(path, encoding="utf-8") as stream:
            row = json.load(stream)
        rows[row["ont"]] = row
    return rows


def result_key(row):
    return row["status"], row["verdict"], row["extra"], row["miss"]


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: compare_sweeps.py BASELINE_DIR CANDIDATE_DIR")
    baseline = load(sys.argv[1])
    candidate = load(sys.argv[2])
    common = sorted(set(baseline) & set(candidate))
    changed = [
        (ontology, result_key(baseline[ontology]), result_key(candidate[ontology]))
        for ontology in common
        if result_key(baseline[ontology]) != result_key(candidate[ontology])
    ]

    print("baseline", len(baseline), collections.Counter(r["verdict"] for r in baseline.values()))
    print("candidate", len(candidate), collections.Counter(r["verdict"] for r in candidate.values()))
    print("common", len(common), "changed", len(changed))
    for ontology, before, after in changed:
        print(ontology, "before=", before, "after=", after)


if __name__ == "__main__":
    main()
