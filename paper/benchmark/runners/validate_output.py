#!/usr/bin/env python3
"""Fail-closed validation for the common full-IRI classification format."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    path = args.output
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit("missing or empty output")
    rows = path.read_text(encoding="utf-8").splitlines()
    if not rows or rows[-1] != "Z\tcomplete" or rows.count("Z\tcomplete") != 1:
        raise SystemExit("missing or duplicate terminal sentinel")
    consistency = [row for row in rows if row.startswith("C\t")]
    if len(consistency) != 1 or consistency[0] not in {"C\ttrue", "C\tfalse", "C\tunknown"}:
        raise SystemExit("invalid consistency record")
    unsat = [row for row in rows if row.startswith("U\t")]
    subs = [row for row in rows if row.startswith("S\t")]
    if unsat != sorted(set(unsat)) or subs != sorted(set(subs)):
        raise SystemExit("classification records are not sorted and unique")
    for row in unsat:
        if len(row.split("\t")) != 2:
            raise SystemExit(f"invalid unsatisfiable record: {row!r}")
    for row in subs:
        fields = row.split("\t")
        if len(fields) != 3 or fields[1] == fields[2]:
            raise SystemExit(f"invalid subsumption record: {row!r}")
    metadata = {}
    for row in rows:
        if row.startswith("M\t"):
            fields = row.split("\t", 2)
            if len(fields) != 3 or fields[1] in metadata:
                raise SystemExit(f"invalid or duplicate metadata: {row!r}")
            metadata[fields[1]] = fields[2]
    if metadata.get("schema") != "1":
        raise SystemExit("unsupported or missing schema")
    if int(metadata.get("unsatisfiable", "-1")) != len(unsat):
        raise SystemExit("unsatisfiable count mismatch")
    if int(metadata.get("subsumptions", "-1")) != len(subs):
        raise SystemExit("subsumption count mismatch")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    print(json.dumps({"bytes": path.stat().st_size, "consistent": consistency[0][2:],
                      "sha256": digest, "subsumptions": len(subs),
                      "unsatisfiable": len(unsat)}, sort_keys=True))


if __name__ == "__main__":
    main()
