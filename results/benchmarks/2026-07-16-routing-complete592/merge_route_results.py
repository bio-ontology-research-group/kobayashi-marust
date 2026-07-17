#!/usr/bin/env python3
"""Merge one validated 592-row production sweep into ontology-routes.tsv."""

import argparse
import csv
import glob
import json
import os
import statistics
import tempfile

from build_current_route_registry import FIELDS


TERMINAL = {"ok", "timeout", "memout", "unsupported"}


def load_sweep(result_dir, expected_sha):
    rows = {}
    for path in sorted(glob.glob(os.path.join(result_dir, "*.jsonl"))):
        with open(path, encoding="utf-8") as handle:
            values = [json.loads(line) for line in handle if line.strip()]
        if len(values) != 1:
            raise SystemExit(f"{path}: expected one JSON row, found {len(values)}")
        row = values[0]
        ontology = row.get("ont")
        if not ontology or ontology in rows:
            raise SystemExit(f"{path}: missing or duplicate ontology {ontology!r}")
        if row.get("status") not in TERMINAL:
            raise SystemExit(f"{path}: non-terminal status {row.get('status')!r}")
        if row.get("binary_sha256") != expected_sha:
            raise SystemExit(f"{path}: wrong binary SHA")
        rows[ontology] = (path, row)
    if len(rows) != 592:
        raise SystemExit(f"expected 592 unique sweep rows, found {len(rows)}")
    return rows


def as_record(path, row, evidence_root, evidence_prefix):
    verdict = row.get("verdict")
    if row.get("status") != "ok" or verdict not in {"match", "nogold"}:
        return None
    route = row.get("arm")
    if not route or row.get("requested_route") != route:
        raise SystemExit(f"{path}: invalid route contract")
    if not row.get("signature_sha256"):
        raise SystemExit(f"{path}: successful route lacks signature SHA")
    return {
        "ontology": row["ont"],
        "route": route,
        "state": "exact_gold" if verdict == "match" else "completed_unadjudicated",
        "verdict": verdict,
        "wall_s": row.get("wall_s", ""),
        "peak_mb": row.get("peak_mb", ""),
        "binary_sha256": row.get("binary_sha256", ""),
        "gold_kind": row.get("gold_kind", ""),
        "gold_sha256": row.get("gold_sha256", ""),
        "signature_sha256": row.get("signature_sha256", ""),
        "invocation": f"km classify --route {route} {row['ont']}",
        "evidence": os.path.join(
            evidence_prefix, os.path.relpath(path, evidence_root)
        ),
        "notes": "verified complete production sweep",
    }


def faster(left, right):
    return float(left.get("wall_s") or 1e30) <= float(right.get("wall_s") or 1e30)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("registry")
    parser.add_argument("result_dir")
    parser.add_argument("expected_sha")
    parser.add_argument("--evidence-root", default=".")
    parser.add_argument("--evidence-prefix", default="")
    parser.add_argument("--summary")
    args = parser.parse_args()

    with open(args.registry, encoding="utf-8", newline="") as handle:
        existing = list(csv.DictReader(handle, delimiter="\t"))
    if not existing or set(existing[0]) != set(FIELDS):
        raise SystemExit("registry schema does not match current route schema")

    merged = {
        (row["ontology"], row["route"]): row
        for row in existing
        if row["route"]
    }
    sweep = load_sweep(args.result_dir, args.expected_sha)
    added = replaced = 0
    for path, row in sweep.values():
        record = as_record(path, row, args.evidence_root, args.evidence_prefix)
        if record is None:
            continue
        key = (record["ontology"], record["route"])
        prior = merged.get(key)
        if prior is None:
            merged[key] = record
            added += 1
        elif not faster(prior, record):
            merged[key] = record
            replaced += 1

    by_ontology = {}
    for record in merged.values():
        by_ontology.setdefault(record["ontology"], []).append(record)
    ontologies = list(dict.fromkeys(row["ontology"] for row in existing))
    records = []
    for ontology in ontologies:
        routes = by_ontology.get(ontology, [])
        if routes:
            records.extend(sorted(routes, key=lambda row: row["route"]))
        else:
            unresolved = [
                row for row in existing if row["ontology"] == ontology and not row["route"]
            ]
            if len(unresolved) != 1:
                raise SystemExit(f"{ontology}: expected one unresolved row")
            records.extend(unresolved)

    exact_by_ontology = {}
    for record in records:
        if record["state"] == "exact_gold":
            exact_by_ontology.setdefault(record["ontology"], []).append(record)
    min_wall = [
        min(float(row["wall_s"]) for row in rows if row["wall_s"])
        for rows in exact_by_ontology.values()
    ]
    min_peak = [
        min(float(row["peak_mb"]) for row in rows if row["peak_mb"])
        for rows in exact_by_ontology.values()
    ]

    directory = os.path.dirname(os.path.abspath(args.registry))
    fd, temporary = tempfile.mkstemp(prefix="ontology-routes.", suffix=".tmp", dir=directory)
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n")
            writer.writeheader()
            writer.writerows(records)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, args.registry)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)

    summary = {
        "rows": len(records),
        "ontologies": len(ontologies),
        "exact_ontologies": len(
            {row["ontology"] for row in records if row["state"] == "exact_gold"}
        ),
        "completed_unadjudicated": len(
            {
                row["ontology"]
                for row in records
                if row["state"] == "completed_unadjudicated"
            }
        ),
        "production_rows_added": added,
        "production_rows_replaced": replaced,
        "production_route_rows": sum(
            row["route"] == "production_all" for row in records
        ),
        "production_route_exact": sum(
            row["route"] == "production_all" and row["state"] == "exact_gold"
            for row in records
        ),
        "union_min_wall_avg_s": statistics.fmean(min_wall),
        "union_min_wall_median_s": statistics.median(min_wall),
        "union_min_peak_avg_mb": statistics.fmean(min_peak),
        "union_min_peak_median_mb": statistics.median(min_peak),
        "unresolved": [row["ontology"] for row in records if row["state"] == "unresolved"],
    }
    if args.summary:
        with open(args.summary, "w", encoding="utf-8") as handle:
            json.dump(summary, handle, indent=2, sort_keys=True)
            handle.write("\n")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
