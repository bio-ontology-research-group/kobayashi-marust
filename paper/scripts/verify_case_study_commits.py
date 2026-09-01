#!/usr/bin/env python3
"""Verify that Methods case-study provenance matches the git object database."""

from __future__ import annotations

import csv
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "paper" / "generated" / "method-case-study-commits.tsv"


def git(*arguments: str) -> str:
    return subprocess.check_output(["git", *arguments], cwd=ROOT, text=True).rstrip("\n")


def main() -> None:
    with LEDGER.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    if not rows:
        raise SystemExit("empty case-study commit ledger")
    seen = set()
    for row in rows:
        commit = row["commit"]
        if commit in seen:
            raise SystemExit(f"duplicate commit in ledger: {commit}")
        seen.add(commit)
        actual_commit = git("rev-parse", f"{commit}^{{commit}}")
        actual_date = git("show", "-s", "--format=%cs", commit)
        actual_subject = git("show", "-s", "--format=%s", commit)
        expected = (commit, row["date"], row["subject"])
        actual = (actual_commit, actual_date, actual_subject)
        if actual != expected:
            raise SystemExit(f"case-study provenance mismatch for {commit}: {actual!r} != {expected!r}")
    print(f"CASE_STUDY_COMMITS_OK\t{len(rows)}")


if __name__ == "__main__":
    main()
