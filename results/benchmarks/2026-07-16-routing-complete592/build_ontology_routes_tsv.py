#!/usr/bin/env python3
"""Build the verified ontology-route registry from the current IBEX proof run."""

import argparse
import csv
import glob
import json
import os
from collections import Counter

ROUTES = (
    "auto default default8 default1 "
    "production_all production_all8 production_all1 "
    "cb_plain16 cb_plain8 cb_plain1 cb_absorb16 cb_absorb8 cb_absorb1 "
    "cb_trigger16 cb_trigger8 cb_trigger1 cb_absorb_portfolio16 "
    "elc elc_cert lean ht_general ht_qo ht_shoq ht_card ht_bridge "
    "ht_features ht_full ht_rules tableau tab_race card_fn nominals seq_on seq_off"
).split()

FIELDS = [
    "ontology",
    "route",
    "result_class",
    "status",
    "verdict",
    "wall_s",
    "peak_mb",
    "binary_sha256",
    "gold_kind",
    "gold_sha256",
    "signature_sha256",
    "subsumptions",
    "unsatisfiable",
    "invocation",
    "evidence_file",
]


def classify(row):
    if row.get("status") != "ok":
        return None
    if row.get("verdict") == "match":
        return "exact_gold"
    if row.get("verdict") == "nogold":
        return "completed_unadjudicated"
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("result_root")
    parser.add_argument("output")
    parser.add_argument("--summary")
    parser.add_argument(
        "--ontology-list",
        help="expected 592-entry ontology list; enables missing-ontology audit",
    )
    args = parser.parse_args()

    records = []
    seen = set()
    all_rows = {}
    binary_hashes = set()
    for path in sorted(glob.glob(os.path.join(args.result_root, "*", "*.jsonl"))):
        with open(path, encoding="utf-8") as handle:
            lines = [line for line in handle if line.strip()]
        if len(lines) != 1:
            raise SystemExit(f"{path}: expected one JSON row, found {len(lines)}")
        row = json.loads(lines[0])
        key = (row.get("ont"), row.get("arm"))
        if key in all_rows:
            raise SystemExit(f"duplicate result pair: {key}")
        all_rows[key] = row
        binary_hashes.add(row.get("binary_sha256"))
        if row.get("arm") not in ROUTES:
            raise SystemExit(f"{path}: unknown route {row.get('arm')!r}")
        if row.get("requested_route") != row.get("arm"):
            raise SystemExit(
                f"{path}: requested route {row.get('requested_route')!r} "
                f"does not match arm {row.get('arm')!r}"
            )
        if row.get("status") == "error":
            raise SystemExit(f"{path}: execution error row is not proof evidence")
        if row.get("status") == "ok" and not row.get("signature_sha256"):
            raise SystemExit(f"{path}: successful row lacks a canonical signature")
        result_class = classify(row)
        if result_class is None:
            continue
        if key in seen:
            raise SystemExit(f"duplicate successful pair: {key}")
        seen.add(key)
        records.append(
            {
                "ontology": row["ont"],
                "route": row["arm"],
                "result_class": result_class,
                "status": row["status"],
                "verdict": row["verdict"],
                "wall_s": row.get("wall_s", ""),
                "peak_mb": row.get("peak_mb", ""),
                "binary_sha256": row.get("binary_sha256", ""),
                "gold_kind": row.get("gold_kind", ""),
                "gold_sha256": row.get("gold_sha256", ""),
                "signature_sha256": row.get("signature_sha256", ""),
                "subsumptions": row.get("subsumptions", ""),
                "unsatisfiable": row.get("unsatisfiable", ""),
                "invocation": f"km classify --route {row['arm']} {row['ont']}",
                "evidence_file": os.path.relpath(path, args.result_root),
            }
        )

    records.sort(key=lambda row: (row["ontology"], row["route"]))
    with open(args.output, "w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS, delimiter="\t")
        writer.writeheader()
        writer.writerows(records)

    if args.summary:
        route_counts = Counter(row["route"] for row in records)
        ontology_counts = Counter(row["ontology"] for row in records)
        if not args.ontology_list:
            raise SystemExit("--summary requires --ontology-list for a strict audit")
        with open(args.ontology_list, encoding="utf-8") as handle:
            expected = {line.strip() for line in handle if line.strip()}
        expected_pairs = {(ontology, route) for ontology in expected for route in ROUTES}
        observed_pairs = set(all_rows)
        missing_pairs = sorted(expected_pairs - observed_pairs)
        extra_pairs = sorted(observed_pairs - expected_pairs)
        if missing_pairs or extra_pairs:
            raise SystemExit(
                f"incomplete proof matrix: missing={len(missing_pairs)} "
                f"extra={len(extra_pairs)}; missing sample={missing_pairs[:5]}, "
                f"extra sample={extra_pairs[:5]}"
            )
        if len(binary_hashes) != 1 or None in binary_hashes:
            raise SystemExit(f"expected one non-null binary hash, got {binary_hashes}")
        summary = {
            "attempted_rows": len(all_rows),
            "expected_rows": len(expected_pairs),
            "binary_sha256": next(iter(binary_hashes)),
            "rows": len(records),
            "ontologies_with_a_completing_route": len(ontology_counts),
            "routes_with_a_completion": len(route_counts),
            "result_classes": dict(Counter(row["result_class"] for row in records)),
            "route_counts": dict(sorted(route_counts.items())),
            "ontologies_without_a_completing_route": sorted(
                expected - set(ontology_counts)
            ),
        }
        with open(args.summary, "w", encoding="utf-8") as handle:
            json.dump(summary, handle, indent=2, sort_keys=True)
            handle.write("\n")


if __name__ == "__main__":
    main()
