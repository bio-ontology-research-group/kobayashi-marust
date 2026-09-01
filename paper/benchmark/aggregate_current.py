#!/usr/bin/env python3
"""Aggregate the frozen current-corpus sweep without inventing a gold reasoner."""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import json
from pathlib import Path
import statistics


BASELINES = ("km", "konclude", "hermit", "jfact", "openllet", "more", "elk", "whelk")
EXPRESSIVE = ("km", "konclude", "hermit", "jfact", "openllet", "more")
EXTERNAL_EXPRESSIVE = tuple(baseline for baseline in EXPRESSIVE if baseline != "km")
CONSISTENCY_CAPABLE = ("km", "konclude", "hermit", "jfact", "openllet")
NAMED_OBO_CASES = ("ncit", "uberon", "chebi")
SIZE_BINS = (
    ("<1k", 0, 1_000),
    ("1k--10k", 1_000, 10_000),
    ("10k--100k", 10_000, 100_000),
    (">=100k", 100_000, None),
)


def tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def receipt_value(path: Path, key: str) -> str:
    found = []
    terminal = None
    with path.open(encoding="utf-8") as stream:
        for raw in stream:
            fields = raw.rstrip("\n").split("\t")
            if len(fields) == 3 and fields[:2] == ["M", key]: found.append(fields[2])
            if fields[0] == "Z": terminal = fields[1:]
    if terminal != ["complete"] or len(found) != 1:
        raise ValueError(f"invalid receipt {path} for {key}")
    return found[0]


def profile(path: Path) -> dict[str, bool]:
    answer = {}
    terminal = None
    with path.open(encoding="utf-8") as stream:
        for raw in stream:
            fields = raw.rstrip("\n").split("\t")
            if len(fields) == 4 and fields[0] == "P":
                if fields[1] in answer or fields[2] not in {"true", "false"}:
                    raise ValueError(f"invalid profile row in {path}")
                answer[fields[1]] = fields[2] == "true"
            if fields[0] == "Z": terminal = fields[1:]
    if terminal != ["complete"] or set(answer) != {"OWL2", "OWL2DL", "OWL2EL", "OWL2QL", "OWL2RL"}:
        raise ValueError(f"incomplete profile {path}")
    return answer


def size_bin(logical_axioms: int) -> str:
    for label, lower, upper in SIZE_BINS:
        if logical_axioms >= lower and (upper is None or logical_axioms < upper):
            return label
    raise AssertionError("unreachable size bin")


def expressivity_bin(values: dict[str, bool]) -> str:
    if values["OWL2EL"]: return "OWL 2 EL"
    if values["OWL2DL"]: return "OWL 2 DL, non-EL"
    return "outside OWL 2 DL"


def summary(values: list[float]) -> dict[str, float | int | None]:
    if not values: return {"n": 0, "mean": None, "median": None}
    return {"n": len(values), "mean": round(statistics.fmean(values), 4),
            "median": round(statistics.median(values), 4)}


def paired_performance(pairs: list[tuple[dict, dict]]) -> dict[str, dict[str, dict[str, float | int | None]]]:
    return {
        "left": {
            "wall_s": summary([float(left["wall_s"]) for left, _ in pairs]),
            "peak_mb": summary([float(left["peak_mb"]) for left, _ in pairs]),
        },
        "right": {
            "wall_s": summary([float(right["wall_s"]) for _, right in pairs]),
            "peak_mb": summary([float(right["peak_mb"]) for _, right in pairs]),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--baselines", required=True, type=Path)
    parser.add_argument("--execution-jobs", required=True, type=Path)
    parser.add_argument("--preparation-artifacts", required=True, type=Path)
    parser.add_argument("--receipts", required=True, type=Path)
    parser.add_argument("--serialization-receipts", required=True, type=Path)
    parser.add_argument("--profiles", required=True, type=Path)
    parser.add_argument("--results", required=True, type=Path)
    parser.add_argument("--output-json", required=True, type=Path)
    parser.add_argument("--disagreements-tsv", required=True, type=Path)
    parser.add_argument("--allow-incomplete", action="store_true",
                        help="write a diagnostic partial aggregate instead of failing on missing/invalid rows")
    args = parser.parse_args()

    ontologies = [row["id"] for row in tsv(args.manifest) if row["eligible"] == "true"]
    if len(ontologies) != 189 or len(set(ontologies)) != len(ontologies):
        raise ValueError("expected exactly 189 unique eligible OBO ontologies")
    baseline_manifest = {row["id"]: row for row in tsv(args.baselines)}
    execution_manifest = {row["id"]: row for row in tsv(args.execution_jobs)}
    preparation_manifest = {row["id"]: row for row in tsv(args.preparation_artifacts)}
    converter_digest = preparation_manifest.get("verified-xml-converter", {}).get("runtime_sha256", "")
    if len(converter_digest) != 64:
        raise ValueError("verified XML converter artifact is absent")
    artifact_hash = {key: row["artifact_sha256"] for key, row in baseline_manifest.items()}
    if set(BASELINES) - artifact_hash.keys(): raise ValueError("baseline artifact manifest incomplete")
    if set(execution_manifest) != set(BASELINES):
        raise ValueError("execution-job manifest must contain exactly the eight baselines")
    expected_runner = {}
    allowed_jobs = {}
    for baseline in BASELINES:
        runner_digest = execution_manifest[baseline].get("runner_sha256", "")
        if len(runner_digest) != 64:
            raise ValueError(f"runner digest missing for {baseline}")
        jobs = {value.strip() for value in
                execution_manifest[baseline].get("allowed_array_job_ids", "").split(",")
                if value.strip()}
        if not jobs:
            raise ValueError(f"allowed array jobs missing for {baseline}")
        expected_runner[baseline] = runner_digest
        allowed_jobs[baseline] = jobs
    for baseline in BASELINES:
        if not baseline_manifest[baseline].get("version_or_commit"):
            raise ValueError(f"baseline version missing for {baseline}")

    profiles = {ontology: profile(args.profiles / f"{ontology}.tsv") for ontology in ontologies}
    logical_axioms = {
        ontology: int(receipt_value(args.profiles / f"{ontology}.tsv", "logical_axioms"))
        for ontology in ontologies
    }
    expected_input = {ontology: receipt_value(args.receipts / f"{ontology}.tsv", "merged_sha256")
                      for ontology in ontologies}
    expected_serialized = {}
    for ontology in ontologies:
        receipt = args.serialization_receipts / f"{ontology}.tsv"
        source_digest = receipt_value(receipt, "source_sha256")
        if source_digest != expected_input[ontology]:
            raise ValueError(f"serialization source mismatch for {ontology}")
        if receipt_value(receipt, "conversion") != "konclude-compatible-serialization-v2":
            raise ValueError(f"wrong serialization conversion for {ontology}")
        if receipt_value(receipt, "converter_sha256") != converter_digest:
            raise ValueError(f"wrong serialization converter for {ontology}")
        if receipt_value(receipt, "roundtrip_logical_axioms_equal") != "true":
            raise ValueError(f"logical round trip failed for {ontology}")
        if receipt_value(receipt, "roundtrip_signature_equal") != "true":
            raise ValueError(f"signature round trip failed for {ontology}")
        expected_serialized[ontology] = receipt_value(receipt, "output_sha256")
    records: dict[str, dict[str, dict]] = defaultdict(dict)
    status_counts: dict[str, Counter] = {baseline: Counter() for baseline in BASELINES}
    status_counts_dl: dict[str, Counter] = {baseline: Counter() for baseline in BASELINES}
    violations = []
    for baseline in BASELINES:
        for ontology in ontologies:
            path = args.results / baseline / f"{ontology}.result.json"
            if not path.is_file():
                status_counts[baseline]["missing"] += 1
                if profiles[ontology]["OWL2DL"]: status_counts_dl[baseline]["missing"] += 1
                continue
            record = json.loads(path.read_text(encoding="utf-8"))
            problems = []
            if record.get("schema") != 1: problems.append("schema")
            if record.get("baseline") != baseline: problems.append("baseline")
            if record.get("ontology_id") != ontology: problems.append("ontology_id")
            if record.get("ontology_sha256") != expected_input[ontology]: problems.append("ontology_sha256")
            if baseline == "km" and record.get("input_ontology_sha256") != expected_input[ontology]:
                problems.append("input_ontology_sha256")
            if baseline == "konclude" and record.get("input_ontology_sha256") != expected_serialized[ontology]:
                problems.append("input_ontology_sha256")
            runtime_key = "binary_sha256" if baseline in {"km", "konclude"} else "runtime_sha256"
            if record.get(runtime_key) != artifact_hash[baseline]: problems.append(runtime_key)
            if record.get("runner_sha256") != expected_runner[baseline]: problems.append("runner_sha256")
            if str(record.get("slurm_array_job_id", "")) not in allowed_jobs[baseline]:
                problems.append("slurm_array_job_id")
            if record.get("status") == "running" or not record.get("checkpointed"): problems.append("terminal")
            if not isinstance(record.get("peak_mb"), (int, float)) or record.get("peak_mb", 0) <= 0:
                problems.append("peak_mb")
            if problems:
                violations.append({"baseline": baseline, "ontology": ontology, "problems": problems})
                status_counts[baseline]["invalid"] += 1
                if profiles[ontology]["OWL2DL"]: status_counts_dl[baseline]["invalid"] += 1
                continue
            status = record["status"]
            if status == "ok":
                for field in ("taxonomy_sha256", "relation_sha256"):
                    if not isinstance(record.get(field), str) or len(record[field]) != 64:
                        problems.append(field)
                if problems:
                    violations.append({"baseline": baseline, "ontology": ontology, "problems": problems})
                    status_counts[baseline]["invalid"] += 1
                    if profiles[ontology]["OWL2DL"]: status_counts_dl[baseline]["invalid"] += 1
                    continue
            status_counts[baseline][status] += 1
            if profiles[ontology]["OWL2DL"]: status_counts_dl[baseline][status] += 1
            records[ontology][baseline] = record

    profile_counts = Counter()
    for values in profiles.values():
        for name, present in values.items():
            if present: profile_counts[name] += 1

    agreement_counts_all = Counter()
    agreement_counts_dl = Counter()
    consistency_counts_all = Counter()
    consistency_counts_dl = Counter()
    km_external_consensus_all = Counter()
    km_external_consensus_dl = Counter()
    disagreement_rows = []
    relation_keys: dict[str, dict[str, str]] = {}
    unanimously_inconsistent = []
    for ontology in ontologies:
        consistency = {baseline: records[ontology][baseline].get("consistency")
                       for baseline in CONSISTENCY_CAPABLE
                       if records[ontology].get(baseline, {}).get("status") == "ok"
                       and records[ontology][baseline].get("consistency") in {"true", "false"}}
        # An inconsistent ontology entails every named subsumption.  Reasoners
        # differ in whether they serialize that universal relation, an empty
        # taxonomy, or only an inconsistency flag.  When at least two capable
        # systems complete and every observed consistency answer is false,
        # compare all completing outputs through one semantic key.
        normalize_inconsistent = (len(consistency) >= 2
                                  and set(consistency.values()) == {"false"})
        if normalize_inconsistent:
            unanimously_inconsistent.append(ontology)
        relation_keys[ontology] = {
            baseline: ("semantic:inconsistent" if normalize_inconsistent
                       else record["relation_sha256"])
            for baseline, record in records[ontology].items()
            if record.get("status") == "ok"
        }
        completed = {baseline: records[ontology][baseline] for baseline in EXPRESSIVE
                     if records[ontology].get(baseline, {}).get("status") == "ok"}
        groups: dict[str, list[str]] = defaultdict(list)
        for baseline in completed: groups[relation_keys[ontology][baseline]].append(baseline)
        if len(completed) == len(EXPRESSIVE) and len(groups) == 1:
            category = "all_expressive_complete_agree"
        elif len(completed) == len(EXPRESSIVE):
            category = "all_expressive_complete_disagree"
        elif completed and len(groups) == 1:
            category = "partial_expressive_complete_agree"
        elif completed:
            category = "partial_expressive_complete_disagree"
        else:
            category = "no_expressive_completion"
        agreement_counts_all[category] += 1
        if profiles[ontology]["OWL2DL"]:
            agreement_counts_dl[category] += 1

        external_completed = {
            baseline: records[ontology][baseline]
            for baseline in EXTERNAL_EXPRESSIVE
            if records[ontology].get(baseline, {}).get("status") == "ok"
        }
        external_digests = {relation_keys[ontology][baseline]
                            for baseline in external_completed}
        km_record = records[ontology].get("km")
        if len(external_completed) < 2:
            km_consensus_category = "insufficient_external_completion"
        elif len(external_digests) != 1:
            km_consensus_category = "external_disagreement"
        elif not km_record or km_record.get("status") != "ok":
            km_consensus_category = "km_not_complete"
        elif relation_keys[ontology]["km"] in external_digests:
            km_consensus_category = "km_agrees_unanimous_external"
        else:
            km_consensus_category = "km_disagrees_unanimous_external"
        km_external_consensus_all[km_consensus_category] += 1
        if profiles[ontology]["OWL2DL"]:
            km_external_consensus_dl[km_consensus_category] += 1

        if len(consistency) == len(CONSISTENCY_CAPABLE) and len(set(consistency.values())) == 1:
            consistency_category = "all_capable_complete_agree"
        elif len(consistency) == len(CONSISTENCY_CAPABLE):
            consistency_category = "all_capable_complete_disagree"
        elif consistency and len(set(consistency.values())) == 1:
            consistency_category = "partial_capable_complete_agree"
        elif consistency:
            consistency_category = "partial_capable_complete_disagree"
        else:
            consistency_category = "no_capable_completion"
        consistency_counts_all[consistency_category] += 1
        if profiles[ontology]["OWL2DL"]:
            consistency_counts_dl[consistency_category] += 1
        if "disagree" in category or "disagree" in consistency_category:
            disagreement_rows.append({
                "ontology": ontology, "owl2dl": str(profiles[ontology]["OWL2DL"]).lower(),
                "relation_category": category,
                "relation_groups": ";".join(",".join(sorted(names)) + "=" + digest
                                           for digest, names in sorted(groups.items())),
                "consistency_category": consistency_category,
                "consistency_values": ";".join(f"{name}={value}"
                                                 for name, value in sorted(consistency.items())),
            })

    pairwise = {}
    for left_index, left in enumerate(BASELINES):
        for right in BASELINES[left_index + 1:]:
            shared = agree = shared_dl = agree_dl = 0
            agreeing_pairs = []
            agreeing_pairs_dl = []
            for ontology in ontologies:
                a, b = records[ontology].get(left), records[ontology].get(right)
                if not a or not b or a.get("status") != "ok" or b.get("status") != "ok": continue
                shared += 1
                relation_agrees = relation_keys[ontology][left] == relation_keys[ontology][right]
                agree += relation_agrees
                if relation_agrees: agreeing_pairs.append((a, b))
                if profiles[ontology]["OWL2DL"]:
                    shared_dl += 1
                    agree_dl += relation_agrees
                    if relation_agrees: agreeing_pairs_dl.append((a, b))
            pairwise[f"{left}:{right}"] = {
                "left": left,
                "right": right,
                "shared_completions_all": shared,
                "relation_agreements_all": agree,
                "relation_disagreements_all": shared - agree,
                "shared_completions_owl2dl": shared_dl,
                "relation_agreements_owl2dl": agree_dl,
                "relation_disagreements_owl2dl": shared_dl - agree_dl,
                "performance_on_relation_agreements_all": paired_performance(agreeing_pairs),
                "performance_on_relation_agreements_owl2dl": paired_performance(agreeing_pairs_dl),
            }

    performance = {}
    for baseline in BASELINES:
        okay = [records[o][baseline] for o in ontologies
                if records[o].get(baseline, {}).get("status") == "ok"]
        okay_dl = [records[o][baseline] for o in ontologies
                   if profiles[o]["OWL2DL"] and records[o].get(baseline, {}).get("status") == "ok"]
        performance[baseline] = {
            "all_own_completions": {
                "wall_s": summary([float(row["wall_s"]) for row in okay]),
                "peak_mb": summary([float(row["peak_mb"]) for row in okay]),
            },
            "owl2dl_own_completions": {
                "wall_s": summary([float(row["wall_s"]) for row in okay_dl]),
                "peak_mb": summary([float(row["peak_mb"]) for row in okay_dl]),
            },
        }

    strata = {"size": {}, "expressivity": {}}
    size_labels = [label for label, _, _ in SIZE_BINS]
    expressivity_labels = ["OWL 2 EL", "OWL 2 DL, non-EL", "outside OWL 2 DL"]
    membership = {
        "size": {ontology: size_bin(logical_axioms[ontology]) for ontology in ontologies},
        "expressivity": {ontology: expressivity_bin(profiles[ontology]) for ontology in ontologies},
    }
    for kind, labels in (("size", size_labels), ("expressivity", expressivity_labels)):
        for label in labels:
            population = [ontology for ontology in ontologies if membership[kind][ontology] == label]
            baseline_rows = {}
            for baseline in BASELINES:
                status = Counter(
                    records[ontology].get(baseline, {}).get("status", "missing")
                    for ontology in population
                )
                okay = [
                    records[ontology][baseline] for ontology in population
                    if records[ontology].get(baseline, {}).get("status") == "ok"
                ]
                baseline_rows[baseline] = {
                    "population": len(population),
                    "status_counts": dict(status),
                    "wall_s": summary([float(row["wall_s"]) for row in okay]),
                    "peak_mb": summary([float(row["peak_mb"]) for row in okay]),
                }
            strata[kind][label] = baseline_rows

    if not set(NAMED_OBO_CASES).issubset(ontologies):
        raise ValueError("named OBO hard cases are absent from the frozen corpus")
    named_cases = {}
    for ontology in NAMED_OBO_CASES:
        relation_groups: dict[str, list[str]] = defaultdict(list)
        for baseline in EXPRESSIVE:
            record = records[ontology].get(baseline)
            if record and record.get("status") == "ok":
                relation_groups[relation_keys[ontology][baseline]].append(baseline)
        named_cases[ontology] = {
            "profiles": profiles[ontology],
            "statuses": {
                baseline: records[ontology].get(baseline, {}).get("status", "missing")
                for baseline in BASELINES
            },
            "expressive_relation_groups": [
                {"baselines": sorted(names), "relation_sha256": relation_digest}
                for relation_digest, names in sorted(relation_groups.items())
            ],
            "consistency": {
                baseline: records[ontology][baseline].get("consistency")
                for baseline in CONSISTENCY_CAPABLE
                if records[ontology].get(baseline, {}).get("status") == "ok"
                and records[ontology][baseline].get("consistency") in {"true", "false"}
            },
        }

    missing_or_invalid = sum(counts.get("missing", 0) + counts.get("invalid", 0)
                             for counts in status_counts.values())
    if missing_or_invalid and not args.allow_incomplete:
        raise ValueError(f"refusing incomplete aggregate: {missing_or_invalid} missing or invalid records")

    output = {
        "schema": 1, "corpus": "OBO Foundry snapshot 2026-08-30",
        "eligible_ontologies": len(ontologies), "expected_runs": len(ontologies) * len(BASELINES),
        "status_counts": {key: dict(value) for key, value in status_counts.items()},
        "status_counts_owl2dl": {key: dict(value) for key, value in status_counts_dl.items()},
        "profile_counts": dict(profile_counts),
        "expressive_relation_agreement_all_inputs": dict(agreement_counts_all),
        "expressive_relation_agreement_owl2dl_inputs": dict(agreement_counts_dl),
        "consistency_agreement_all_inputs": dict(consistency_counts_all),
        "consistency_agreement_owl2dl_inputs": dict(consistency_counts_dl),
        "unanimously_inconsistent_relation_normalization": unanimously_inconsistent,
        "km_against_unanimous_external_consensus_all_inputs": dict(km_external_consensus_all),
        "km_against_unanimous_external_consensus_owl2dl_inputs": dict(km_external_consensus_dl),
        "pairwise_relation_agreement": pairwise, "performance_on_own_completions": performance,
        "named_obo_hard_cases": named_cases,
        "stratified_results": strata,
        "size_strata_logical_axioms": [
            {"label": label, "lower_inclusive": lower, "upper_exclusive": upper}
            for label, lower, upper in SIZE_BINS
        ],
        "missing_or_invalid_records": missing_or_invalid,
        "invalid_records": violations,
        "baseline_artifacts": {
            baseline: {
                "version_or_commit": baseline_manifest[baseline]["version_or_commit"],
                "artifact_sha256": baseline_manifest[baseline]["artifact_sha256"],
            }
            for baseline in BASELINES
        },
        "execution_bindings": {
            baseline: {
                "runner_sha256": expected_runner[baseline],
                "allowed_array_job_ids": sorted(allowed_jobs[baseline]),
            }
            for baseline in BASELINES
        },
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output_json) + ".part")
    temporary.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(args.output_json)
    args.disagreements_tsv.parent.mkdir(parents=True, exist_ok=True)
    temporary_tsv = Path(str(args.disagreements_tsv) + ".part")
    with temporary_tsv.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=("ontology", "owl2dl", "relation_category",
                                                     "relation_groups", "consistency_category",
                                                     "consistency_values"), delimiter="\t")
        writer.writeheader(); writer.writerows(disagreement_rows)
    temporary_tsv.replace(args.disagreements_tsv)
    print(json.dumps({"status": "ok", "missing_or_invalid": missing_or_invalid,
        "disagreements": len(disagreement_rows)}, sort_keys=True))


if __name__ == "__main__":
    main()
