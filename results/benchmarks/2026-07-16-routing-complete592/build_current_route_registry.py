#!/usr/bin/env python3
"""Create a complete ontology-to-working-route TSV from verified result rows."""

import argparse
import csv
import glob
import json
import os
from collections import defaultdict


FIELDS = [
    "ontology",
    "route",
    "state",
    "verdict",
    "wall_s",
    "peak_mb",
    "binary_sha256",
    "gold_kind",
    "gold_sha256",
    "signature_sha256",
    "invocation",
    "evidence",
    "notes",
]

HISTORICAL_RESTORATION = {
    "ore_ont_10702.owl": "historical exact: nominal ABox role-link augmentation; commit f985b97",
    "ore_ont_10908.owl": "historical exact: htforce/sequence-order routes",
    "ore_ont_11745.owl": "historical exact: role-chain domain recognition",
    "ore_ont_15672.owl": "historical exact: SHOQ/HT recognition route",
    "ore_ont_6934.owl": "historical exact: htforce measurement route",
    "ore_ont_7499.owl": "historical exact: first-class cardinality route",
    "ore_ont_9540.owl": "historical exact: first-class cardinality route",
    "ore_ont_9635.owl": "historical exact: validated tableau fallback",
    "ore_ont_3215.owl": "historical exact: Konclude KPSet phase barrier",
    "ore_ont_2669.owl": "adjudicated inconsistent: ht_rules; stored Konclude gold is stale",
    "ore_ont_15516.owl": "adjudicated inconsistent: ht_rules; stored Konclude gold is stale",
}


def load_rows(root):
    for path in sorted(glob.glob(os.path.join(root, "**", "*.jsonl"), recursive=True)):
        with open(path, encoding="utf-8") as handle:
            for line in handle:
                if line.strip():
                    yield path, json.loads(line)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("matrix_root")
    parser.add_argument("ontology_list")
    parser.add_argument("output")
    parser.add_argument("--supplemental-root")
    args = parser.parse_args()

    with open(args.ontology_list, encoding="utf-8") as handle:
        ontologies = [line.strip() for line in handle if line.strip()]
    expected = set(ontologies)

    accepted = {}
    candidates = defaultdict(list)
    roots = [args.matrix_root]
    if args.supplemental_root:
        roots.append(args.supplemental_root)

    for root in roots:
        for path, row in load_rows(root):
            ontology = row.get("ont")
            route = row.get("arm")
            if ontology not in expected or row.get("kind", "km") != "km" or not route:
                continue
            status = row.get("status")
            verdict = row.get("verdict")
            if status == "ok" and verdict == "match":
                state = "exact_gold"
            elif status == "ok" and verdict == "nogold":
                state = "completed_unadjudicated"
            else:
                candidates[ontology].append((route, status, verdict))
                continue
            key = (ontology, route)
            record = {
                "ontology": ontology,
                "route": route,
                "state": state,
                "verdict": verdict,
                "wall_s": row.get("wall_s", ""),
                "peak_mb": row.get("peak_mb", ""),
                "binary_sha256": row.get("binary_sha256", ""),
                "gold_kind": row.get("gold_kind", ""),
                "gold_sha256": row.get("gold_sha256", ""),
                "signature_sha256": row.get("signature_sha256", ""),
                "invocation": f"km classify --route {route} {ontology}",
                "evidence": os.path.relpath(path, root),
                "notes": "",
            }
            prior = accepted.get(key)
            if prior is None or float(record["wall_s"] or 1e30) < float(
                prior["wall_s"] or 1e30
            ):
                accepted[key] = record

    by_ontology = defaultdict(list)
    for record in accepted.values():
        by_ontology[record["ontology"]].append(record)

    records = []
    for ontology in ontologies:
        if by_ontology[ontology]:
            records.extend(sorted(by_ontology[ontology], key=lambda row: row["route"]))
            continue
        observed = sorted(set(candidates[ontology]))
        notes = "; ".join(
            f"{route}:{status}/{verdict}" for route, status, verdict in observed
        )
        records.append(
            {
                "ontology": ontology,
                "route": "",
                "state": "unresolved",
                "verdict": "",
                "wall_s": "",
                "peak_mb": "",
                "binary_sha256": "",
                "gold_kind": "",
                "gold_sha256": "",
                "signature_sha256": "",
                "invocation": "",
                "evidence": "",
                "notes": "; ".join(
                    part
                    for part in (
                        HISTORICAL_RESTORATION.get(ontology, ""),
                        notes or "no verified completing route in supplied evidence",
                    )
                    if part
                ),
            }
        )

    with open(args.output, "w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS, delimiter="\t")
        writer.writeheader()
        writer.writerows(records)

    print(
        json.dumps(
            {
                "rows": len(records),
                "ontologies": len({row["ontology"] for row in records}),
                "exact_ontologies": len(
                    {
                        row["ontology"]
                        for row in records
                        if row["state"] == "exact_gold"
                    }
                ),
                "completed_unadjudicated": len(
                    {
                        row["ontology"]
                        for row in records
                        if row["state"] == "completed_unadjudicated"
                    }
                ),
                "unresolved": [
                    row["ontology"] for row in records if row["state"] == "unresolved"
                ],
            },
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
