#!/usr/bin/env python3
"""Bind paper-level formal claims to declarations in an exact git tree."""

from __future__ import annotations

import csv
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "paper" / "formal-claims.tsv"


def git(*arguments: str) -> str:
    return subprocess.check_output(["git", *arguments], cwd=ROOT, text=True)


def main() -> None:
    with LEDGER.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    if not rows:
        raise SystemExit("empty formal-claim ledger")
    seen = set()
    refs = {}
    for row in rows:
        key = (row["git_ref"], row["path"], row["declaration"])
        if key in seen: raise SystemExit(f"duplicate formal declaration: {key}")
        seen.add(key)
        commit = git("rev-parse", f"{row['git_ref']}^{{commit}}").strip()
        refs[row["git_ref"]] = commit
        source = git("show", f"{row['git_ref']}:{row['path']}")
        declaration = re.escape(row["declaration"])
        pattern = rf"(?m)^\s*(?:theorem|def|structure)\s+{declaration}(?:\s|$)"
        if re.search(pattern, source) is None:
            raise SystemExit(f"missing declaration {row['declaration']} in {row['git_ref']}:{row['path']}")
    for ref, commit in sorted(refs.items()):
        print(f"FORMAL_REF\t{ref}\t{commit}")
    print(f"FORMAL_CLAIMS_OK\t{len(rows)}")


if __name__ == "__main__":
    main()
