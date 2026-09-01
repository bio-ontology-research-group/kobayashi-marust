#!/usr/bin/env python3
"""Verify every tag-qualified evidence path in the paper claims ledger."""

from __future__ import annotations

import csv
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "paper" / "claims-ledger.tsv"
TAGGED = re.compile(r"\b(v\d+\.\d+\.\d+):([A-Za-z0-9_./-]+)")


def main() -> None:
    with LEDGER.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    checked = set()
    for row in rows:
        for ref, path in TAGGED.findall(row["authoritative_evidence"]):
            key = (ref, path)
            if key in checked: continue
            checked.add(key)
            result = subprocess.run(["git", "cat-file", "-e", f"{ref}:{path}"], cwd=ROOT)
            if result.returncode != 0:
                raise SystemExit(f"missing tagged evidence {ref}:{path} for {row['claim_id']}")
    if not checked: raise SystemExit("no tag-qualified evidence found")
    print(f"TAGGED_EVIDENCE_OK\t{len(checked)}")


if __name__ == "__main__":
    main()
