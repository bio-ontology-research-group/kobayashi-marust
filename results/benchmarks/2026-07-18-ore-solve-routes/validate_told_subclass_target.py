#!/usr/bin/env python3
"""Check whether KM preserves told named-class subsumptions to one full IRI."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


SUBCLASS = re.compile(r"SubClassOf\(\s*<([^>]+)>\s+<([^>]+)>\s*\)")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ontology", type=Path, required=True)
    parser.add_argument("--km-output", type=Path, required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--ignore-reflexive",
        action="store_true",
        help="ignore Target SubClassOf Target because KM's public taxonomy omits self edges",
    )
    args = parser.parse_args()

    told_occurrences = 0
    told_lefts: set[str] = set()
    with args.ontology.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            for match in SUBCLASS.finditer(line):
                if match.group(2) == args.target:
                    told_occurrences += 1
                    told_lefts.add(match.group(1))

    data = json.loads(args.km_output.read_text(encoding="utf-8"))
    returned_lefts = {
        left
        for left, right in data.get("subsumptions", [])
        if right == args.target
    }
    compared_lefts = set(told_lefts)
    ignored_reflexive = args.target in compared_lefts and args.ignore_reflexive
    if ignored_reflexive:
        compared_lefts.remove(args.target)
    missing = sorted(compared_lefts - returned_lefts)
    record = {
        "schema_version": 1,
        "ontology": str(args.ontology),
        "ontology_sha256": sha256(args.ontology),
        "km_output": str(args.km_output),
        "km_output_sha256": sha256(args.km_output),
        "target": args.target,
        "told_occurrences": told_occurrences,
        "told_distinct_lefts": len(told_lefts),
        "told_compared_distinct_lefts": len(compared_lefts),
        "ignored_reflexive": ignored_reflexive,
        "km_returned_distinct_lefts": len(returned_lefts),
        "missing_told_subsumptions": len(missing),
        "unexpected_returned_lefts": len(returned_lefts - compared_lefts),
        "first_missing_left": missing[0] if missing else None,
        "first_missing_axiom": (
            f"SubClassOf(<{missing[0]}> <{args.target}>)" if missing else None
        ),
        "verdict": "incomplete" if missing else "preserved",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    temporary.replace(args.output)
    print(json.dumps(record, sort_keys=True))
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
