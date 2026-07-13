#!/usr/bin/env python3
"""Aggregate the 592-ontology IBEX plan-15 regression sweep."""

from collections import Counter
import glob
import json
import os


ROOT = "/ibex/scratch/hohndor/km"
CANDIDATE = os.environ.get(
    "KM_SWEEP_RESULT_DIR", os.path.join(ROOT, "plan15_7914_closure", "res")
)
BASELINE = os.path.join(ROOT, "fullsweep", "res")
AB_RESULTS = os.environ.get(
    "KM_AB_RESULT_DIR", os.path.join(ROOT, "plan15_7914_closure", "ab_res")
)


def read_one(path):
    try:
        with open(path, encoding="utf-8") as stream:
            return json.loads(stream.readline())
    except (OSError, json.JSONDecodeError):
        return None


def load_candidate():
    records = {}
    for path in glob.glob(os.path.join(CANDIDATE, "*.jsonl")):
        record = read_one(path)
        if record:
            records[record["ont"]] = record
    return records


def load_baseline_default():
    records = {}
    for path in glob.glob(os.path.join(BASELINE, "*.jsonl")):
        try:
            with open(path, encoding="utf-8") as stream:
                for line in stream:
                    record = json.loads(line)
                    if record.get("config") == "default":
                        records[record["ont"]] = record
        except (OSError, json.JSONDecodeError):
            continue
    return records


def load_controlled_ab():
    records = {}
    for path in glob.glob(os.path.join(AB_RESULTS, "*.jsonl")):
        record = read_one(path)
        if record:
            records.setdefault(record["ont"], {})[record["variant"]] = record
    return records


def main():
    candidate = load_candidate()
    baseline = load_baseline_default()
    controlled_ab = load_controlled_ab()
    statuses = Counter(record["status"] for record in candidate.values())
    verdicts = Counter(record["verdict"] for record in candidate.values())
    gold_matches = sorted(
        ontology for ontology, record in candidate.items() if record["verdict"] == "match"
    )
    no_gold = {
        ontology: {
            "status": record["status"],
            "verdict": record["verdict"],
        }
        for ontology, record in sorted(candidate.items())
        if not os.path.exists(os.path.join(ROOT, "gold", f"konclude__{ontology}.sig.gz"))
    }
    disagreements = {
        ontology: {
            "verdict": record["verdict"],
            "extra": record.get("extra", 0),
            "missing": record.get("miss", 0),
        }
        for ontology, record in sorted(candidate.items())
        if record["status"] == "ok" and record["verdict"] not in ("match", "nogold", "incons")
    }
    failures = {
        ontology: record["status"]
        for ontology, record in sorted(candidate.items())
        if record["status"] != "ok"
    }
    regressions = sorted(
        ontology
        for ontology, old in baseline.items()
        if old.get("solved") == 1
        and candidate.get(ontology, {}).get("solved") != 1
    )
    correctness_regressions = sorted(
        ontology
        for ontology, old in baseline.items()
        if old.get("verdict") == "match"
        and candidate.get(ontology, {}).get("verdict") != "match"
    )
    recoveries = sorted(
        ontology
        for ontology, new in candidate.items()
        if new.get("verdict") == "match"
        and baseline.get(ontology, {}).get("verdict") != "match"
    )
    ab_changes = {}
    ab_regressions = []
    ab_improvements = []
    for ontology, variants in sorted(controlled_ab.items()):
        previous = variants.get("previous")
        plan15 = variants.get("plan15")
        if not previous or not plan15:
            continue
        previous_key = (
            previous["status"], previous["verdict"], previous.get("extra", 0), previous.get("miss", 0)
        )
        plan15_key = (
            plan15["status"], plan15["verdict"], plan15.get("extra", 0), plan15.get("miss", 0)
        )
        if previous_key != plan15_key:
            ab_changes[ontology] = {"previous": previous_key, "plan15": plan15_key}
        if previous["verdict"] == "match" and plan15["verdict"] != "match":
            ab_regressions.append(ontology)
        if previous["verdict"] != "match" and plan15["verdict"] == "match":
            ab_improvements.append(ontology)

    report = {
        "attempted": len(candidate),
        "status": dict(sorted(statuses.items())),
        "verdict": dict(sorted(verdicts.items())),
        "gold_match_count": len(gold_matches),
        "no_gold": no_gold,
        "failures": failures,
        "disagreements": disagreements,
        "solved_regressions_vs_previous_default": regressions,
        "correctness_regressions_vs_previous_default": correctness_regressions,
        "recoveries_vs_previous_default": recoveries,
        "controlled_ab_completed_pairs": sum(
            1 for variants in controlled_ab.values() if {"previous", "plan15"} <= set(variants)
        ),
        "controlled_ab_changes": ab_changes,
        "controlled_ab_regressions": ab_regressions,
        "controlled_ab_improvements": ab_improvements,
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
