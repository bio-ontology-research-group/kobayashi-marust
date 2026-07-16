#!/usr/bin/env python3
"""Validate KM expressivity against Konclude and materialize the feature table."""

import argparse
import csv
import glob
import json
import math
import os
import statistics
from collections import Counter


def percentile(values, fraction):
    if not values:
        return None
    ordered = sorted(values)
    index = min(len(ordered) - 1, math.ceil(fraction * len(ordered)) - 1)
    return ordered[max(0, index)]


def flatten(prefix, value, row):
    for key, item in value.items():
        name = f"{prefix}.{key}"
        if isinstance(item, (bool, int, float, str)) or item is None:
            row[name] = item


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--profiles")
    parser.add_argument("--output-dir")
    args = parser.parse_args()
    root = os.path.abspath(args.root)
    profiles_dir = os.path.abspath(args.profiles or os.path.join(root, "profiles"))
    output_dir = os.path.abspath(args.output_dir or root)
    os.makedirs(output_dir, exist_ok=True)

    official = {}
    for path in glob.glob(os.path.join(root, "konclude-expressivity", "*.json")):
        data = json.load(open(path, encoding="utf-8"))
        official[data["ont"]] = data

    rows = []
    errors = []
    for path in glob.glob(os.path.join(profiles_dir, "*.json")):
        data = json.load(open(path, encoding="utf-8"))
        fallback = os.path.basename(path)
        if fallback.endswith(".json"):
            fallback = fallback[:-5]
        ont = data.get("ont", fallback)
        if data.get("status") != "ok" or not data.get("profile"):
            errors.append({"ont": ont, "error": data.get("error", data.get("status"))})
            continue
        profile = data["profile"]
        row = {
            "ont": ont,
            "schema_version": profile["schema_version"],
            "positive_abox_tbox_separable": profile.get(
                "positive_abox_tbox_separable", False
            ),
            "el_rbox_safe": data.get("el_rbox_safe"),
            "konclude_expressivity": (official.get(ont) or {}).get("expressivity"),
        }
        flatten("expressivity", profile["expressivity"], row)
        flatten("source", profile["source"], row)
        flatten("clauses", profile["clauses"], row)
        # None => no Konclude expressivity reference for this ont. Do NOT fold
        # that into a mismatch (None == code is False), which would score an
        # ontology with no ground truth as a KM/Konclude disagreement. Only a
        # present-and-differing reference is a real mismatch.
        km_code = row["expressivity.code"]
        kon_code = row["konclude_expressivity"]
        row["expressivity_match"] = (
            None if kon_code is None else (kon_code == km_code)
        )
        row["source.axiom_types_json"] = json.dumps(
            profile["source"].get("axiom_types", {}), sort_keys=True, separators=(",", ":")
        )
        rows.append(row)

    rows.sort(key=lambda row: row["ont"])
    fields = sorted({key for row in rows for key in row}, key=lambda x: (x != "ont", x))
    table_path = os.path.join(output_dir, "profile-table.csv")
    with open(table_path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)

    mismatches = [
        {
            "ont": row["ont"],
            "konclude": row["konclude_expressivity"],
            "km": row["expressivity.code"],
        }
        for row in rows
        if row["expressivity_match"] is False
    ]
    unreferenced = [row["ont"] for row in rows if row["expressivity_match"] is None]
    numeric = {}
    for field in fields:
        values = [row[field] for row in rows if isinstance(row.get(field), (int, float))]
        if not values or field.startswith("expressivity."):
            continue
        numeric[field] = {
            "min": min(values),
            "median": statistics.median(values),
            "mean": sum(values) / len(values),
            "p95": percentile(values, 0.95),
            "max": max(values),
        }
    additive_fields = [
        "source.file_bytes",
        "source.ontology_children",
        "source.logical_axioms",
        "source.tbox_axioms",
        "source.rbox_axioms",
        "source.abox_axioms",
        "source.rule_axioms",
        "source.unsupported_rule_axioms",
        "source.declarations",
        "source.distinct_classes",
        "source.distinct_object_properties",
        "source.distinct_data_properties",
        "source.distinct_individuals",
        "source.concept_expressions",
        "clauses.clauses",
        "clauses.horn_clauses",
        "clauses.disjunctive_clauses",
    ]
    totals = {
        field: sum(row.get(field, 0) for row in rows)
        for field in additive_fields
    }
    summary = {
        "official_rows": len(official),
        "profile_rows": len(rows),
        "profile_errors": errors,
        "expressivity_matches": sum(
            1 for row in rows if row["expressivity_match"] is True
        ),
        "expressivity_mismatches": mismatches,
        "expressivity_unreferenced": unreferenced,
        "expressivity_distribution": dict(
            sorted(Counter(row["expressivity.code"] for row in rows).items())
        ),
        "el_rbox_safe": dict(
            Counter(str(bool(row.get("el_rbox_safe"))).lower() for row in rows)
        ),
        "totals": totals,
        "largest_by_file_bytes": [
            {"ont": row["ont"], "value": row.get("source.file_bytes")}
            for row in sorted(
                rows, key=lambda row: row.get("source.file_bytes", 0), reverse=True
            )[:20]
        ],
        "largest_by_logical_axioms": [
            {"ont": row["ont"], "value": row.get("source.logical_axioms")}
            for row in sorted(
                rows, key=lambda row: row.get("source.logical_axioms", 0), reverse=True
            )[:20]
        ],
        "largest_by_normalized_clauses": [
            {"ont": row["ont"], "value": row.get("clauses.clauses")}
            for row in sorted(rows, key=lambda row: row.get("clauses.clauses", 0), reverse=True)[
                :20
            ]
        ],
        "numeric_statistics": numeric,
    }
    summary_path = os.path.join(output_dir, "profile-summary.json")
    with open(summary_path, "w", encoding="utf-8") as handle:
        json.dump(summary, handle, indent=2, sort_keys=True)
        handle.write("\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "numeric_statistics"}, indent=2))


if __name__ == "__main__":
    main()
