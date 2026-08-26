#!/usr/bin/env python3
"""Export one validated terminal row per ontology as a compact TSV ledger."""

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path


FIELDS = (
    "ontology",
    "status",
    "verdict",
    "signature_sha256",
    "wall_s",
    "peak_mib",
    "selected_route",
    "binary_sha256",
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--binary-sha256", required=True)
    args = parser.parse_args()
    temporary = sorted(args.root.rglob("*.tmp"))
    if temporary:
        raise SystemExit(f"temporary files remain: {temporary[:5]}")
    rows = []
    for path in sorted((args.root / "results").glob("ore_ont_*.owl.json")):
        row = json.loads(path.read_text())
        ontology = path.name[:-len(".json")]
        checkpoint = path.with_name(f"{ontology}.checkpoint.json")
        if checkpoint.read_bytes() != path.read_bytes():
            raise SystemExit(f"checkpoint differs: {ontology}")
        if row.get("ont") != ontology:
            raise SystemExit(f"path mismatch: {ontology}")
        if row.get("binary_sha256") != args.binary_sha256:
            raise SystemExit(f"binary mismatch: {ontology}")
        rows.append({
            "ontology": ontology,
            "status": row.get("status", ""),
            "verdict": row.get("verdict", ""),
            "signature_sha256": row.get("signature_sha256", ""),
            "wall_s": row.get("wall_s", ""),
            "peak_mib": row.get("peak_mb", ""),
            "selected_route": row.get("selected_route", ""),
            "binary_sha256": row.get("binary_sha256", ""),
        })
    if len(rows) != 592 or len({row["ontology"] for row in rows}) != 592:
        raise SystemExit(f"expected 592 unique rows, found {len(rows)}")
    writer = csv.DictWriter(sys.stdout, fieldnames=FIELDS, delimiter="\t", lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)


if __name__ == "__main__":
    main()
