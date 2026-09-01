#!/usr/bin/env python3
"""Validate and render the eight-reasoner FMA hard-case sweep."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path


ORDER = ("km", "konclude", "hermit", "jfact", "openllet", "more", "elk", "whelk")
LABEL = {"km": "KM", "konclude": "Konclude", "hermit": "HermiT", "jfact": "JFact",
         "openllet": "Openllet", "more": "MORe", "elk": "ELK", "whelk": "Whelk"}
TASK = {baseline: index for index, baseline in enumerate(ORDER)}
FMA_SHA256 = "aff1dfb7cdcd153ce6fb2f0e4899e29f60a7eec04940a48acbef7e9bd3fb4bb6"
RUNNER = {"km": "17f965be04025a88fbf60bb2eb7ab705bc4349ae0ac342e35f9ee69c05b94977",
          "konclude": "17f965be04025a88fbf60bb2eb7ab705bc4349ae0ac342e35f9ee69c05b94977"}
JAVA_RUNNER = "89c6005a8eba19c84305c9d53627e7565686d94f82a3f3f731f16af58d68f88b"


def baseline_hashes(path: Path) -> dict[str, str]:
    with path.open(encoding="utf-8", newline="") as stream:
        return {row["id"]: row["artifact_sha256"]
                for row in csv.DictReader(stream, delimiter="\t")}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", required=True, type=Path)
    parser.add_argument("--logs", required=True, type=Path)
    parser.add_argument("--baselines", required=True, type=Path)
    parser.add_argument("--output-json", required=True, type=Path)
    parser.add_argument("--output-tex", required=True, type=Path)
    args = parser.parse_args()
    artifacts = baseline_hashes(args.baselines)
    if set(ORDER) - artifacts.keys():
        raise ValueError("baseline manifest incomplete")

    records = {}
    evidence_sha256 = {}
    for baseline in ORDER:
        path = args.results / baseline / "fma.result.json"
        record = json.loads(path.read_text(encoding="utf-8"))
        problems = []
        expected_runner = RUNNER.get(baseline, JAVA_RUNNER)
        runtime_key = "binary_sha256" if baseline in {"km", "konclude"} else "runtime_sha256"
        checks = {
            "schema": record.get("schema") == 1,
            "baseline": record.get("baseline") == baseline,
            "ontology_id": record.get("ontology_id") == "fma",
            "ontology_sha256": record.get("ontology_sha256") == FMA_SHA256,
            runtime_key: record.get(runtime_key) == artifacts[baseline],
            "runner_sha256": record.get("runner_sha256") == expected_runner,
            "terminal": record.get("status") not in {None, "running"},
            "checkpointed": record.get("checkpointed") is True,
            "peak_mb": isinstance(record.get("peak_mb"), (int, float)) and record.get("peak_mb", 0) > 0,
            "wall_s": isinstance(record.get("wall_s"), (int, float)) and record.get("wall_s", 0) > 0,
        }
        problems.extend(name for name, okay in checks.items() if not okay)
        if record.get("status") == "ok":
            for key in ("taxonomy_sha256", "relation_sha256"):
                if not isinstance(record.get(key), str) or len(record[key]) != 64: problems.append(key)
        log = args.logs / f"fma-benchmark-51021833_{TASK[baseline]}.out"
        log_text = log.read_text(encoding="utf-8")
        if f'"terminal_status": "{record.get("status")}"' not in log_text: problems.append("validator_log")
        if f"FMA_BENCHMARK_TERMINAL\t{baseline}" not in log_text: problems.append("terminal_marker")
        if problems: raise ValueError(f"invalid FMA record {baseline}: {problems}")
        records[baseline] = record
        evidence_sha256[baseline] = {"result_json": sha256(path), "validator_log": sha256(log)}

    output = {
        "schema": 1,
        "case": "FMA 5.1.0",
        "ontology_sha256": FMA_SHA256,
        "owl2dl": True,
        "owl2el": False,
        "owl2ql": False,
        "owl2rl": False,
        "job": "51021833",
        "evidence_sha256": evidence_sha256,
        "records": records,
        "interpretation": {
            "expressive_completions": [baseline for baseline in ("km", "konclude", "hermit", "jfact", "openllet", "more")
                                       if records[baseline]["status"] == "ok"],
            "profile_limited_out_of_scope_completions": [baseline for baseline in ("elk", "whelk")
                                                           if records[baseline]["status"] == "ok"],
        },
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    encoded = (json.dumps(output, indent=2, sort_keys=True) + "\n").encode()
    temporary = Path(str(args.output_json) + ".part")
    temporary.write_bytes(encoded); temporary.replace(args.output_json)

    lines = [f"% Generated from FMA aggregate SHA-256 {hashlib.sha256(encoded).hexdigest()}",
             "\\begin{table*}[t]", "\\centering", "\\small",
             "\\caption{FMA hard-case classification under 600 seconds and 32~GiB. ELK and Whelk executions are outside their complete profiles.}",
             "\\label{tab:fma-results}", "\\begin{tabular}{llrrrl}", "\\toprule",
             "Reasoner & Status & Wall s & Peak MiB & Subsumptions & Interpretation \\\\", "\\midrule"]
    for baseline in ORDER:
        record = records[baseline]
        interpretation = "complete-profile result" if baseline == "konclude" and record["status"] == "ok" else (
            "outside complete profile" if baseline in {"elk", "whelk"} and record["status"] == "ok" else "no result")
        subsumptions = str(record.get("subsumptions", "--"))
        lines.append(f"{LABEL[baseline]} & {record['status']} & {record['wall_s']:.3f} & "
                     f"{record['peak_mb']:.1f} & {subsumptions} & {interpretation} \\\\")
    lines.extend(["\\bottomrule", "\\end{tabular}", "\\end{table*}", ""])
    temporary = Path(str(args.output_tex) + ".part")
    temporary.write_text("\n".join(lines), encoding="utf-8"); temporary.replace(args.output_tex)
    print("FMA_AGGREGATE_OK\t8")


if __name__ == "__main__":
    main()
