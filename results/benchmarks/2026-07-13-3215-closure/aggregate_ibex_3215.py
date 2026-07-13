#!/usr/bin/env python3
"""Aggregate the 3215 closure sweep and compare it with plan 15."""

from collections import Counter
import glob
import hashlib
import json
import os


KM_ROOT = "/ibex/scratch/hohndor/km"
CANDIDATE = os.environ.get(
    "KM_SWEEP_RESULT_DIR", os.path.join(KM_ROOT, "3215_closure_20260713", "res")
)
BASELINE = os.environ.get(
    "KM_SWEEP_BASELINE_DIR", os.path.join(KM_ROOT, "plan15_7914_closure", "final_res")
)


def read_records(directory):
    records = {}
    for path in glob.glob(os.path.join(directory, "*.jsonl")):
        try:
            with open(path, encoding="utf-8") as stream:
                record = json.loads(stream.readline())
        except (OSError, json.JSONDecodeError):
            continue
        records[record["ont"]] = record
    return records


def signature(record):
    return (
        record.get("status"),
        record.get("verdict"),
        record.get("extra", 0),
        record.get("miss", 0),
    )


def main():
    candidate = read_records(CANDIDATE)
    baseline = read_records(BASELINE)
    statuses = Counter(record.get("status") for record in candidate.values())
    verdicts = Counter(record.get("verdict") for record in candidate.values())

    changes = {
        ontology: {"baseline": signature(baseline[ontology]), "candidate": signature(record)}
        for ontology, record in sorted(candidate.items())
        if ontology in baseline and signature(record) != signature(baseline[ontology])
    }
    missing_candidate = sorted(set(baseline) - set(candidate))
    match_regressions = sorted(
        ontology
        for ontology, old in baseline.items()
        if old.get("verdict") == "match"
        and candidate.get(ontology, {}).get("verdict") != "match"
    )
    match_recoveries = sorted(
        ontology
        for ontology, new in candidate.items()
        if new.get("verdict") == "match"
        and baseline.get(ontology, {}).get("verdict") != "match"
    )

    binary_hashes = sorted(
        {record.get("binary_sha256") for record in candidate.values() if record.get("binary_sha256")}
    )
    report = {
        "candidate_directory": CANDIDATE,
        "baseline_directory": BASELINE,
        "attempted": len(candidate),
        "baseline_count": len(baseline),
        "status": dict(sorted(statuses.items())),
        "verdict": dict(sorted(verdicts.items())),
        "binary_sha256": binary_hashes,
        "missing_candidate_count": len(missing_candidate),
        "missing_candidate": missing_candidate,
        "result_change_count": len(changes),
        "result_changes_vs_plan15": changes,
        "gold_match_regressions": match_regressions,
        "gold_match_recoveries": match_recoveries,
    }
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    print(encoded, end="")
    print(
        "aggregate_sha256=" + hashlib.sha256(encoded.encode("utf-8")).hexdigest(),
        file=os.sys.stderr,
    )


if __name__ == "__main__":
    main()
