#!/usr/bin/env python3
"""Fail if manuscript citations, BibTeX, and the citation audit diverge."""

from __future__ import annotations

import csv
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    manuscript = (ROOT / "main.tex").read_text(encoding="utf-8")
    bibliography = (ROOT / "references.bib").read_text(encoding="utf-8")
    cited: set[str] = set()
    for block in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", manuscript):
        cited.update(key.strip() for key in block.split(",") if key.strip())
    bib = set(re.findall(r"^@[A-Za-z]+\{([^,]+),", bibliography, re.M))

    with (ROOT / "citation-audit.tsv").open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream, delimiter="\t"))
    audited = [row["citation_key"] for row in rows]
    if len(audited) != len(set(audited)):
        raise ValueError("duplicate citation-audit key")
    if cited - bib:
        raise ValueError(f"cited keys absent from bibliography: {sorted(cited - bib)}")
    if cited != set(audited):
        raise ValueError(
            f"citation audit mismatch: unaudited={sorted(cited - set(audited))}, "
            f"uncited_audit_rows={sorted(set(audited) - cited)}"
        )
    for row in rows:
        if row["status"] not in {"verified", "corrected"}:
            raise ValueError(f"unresolved citation audit: {row['citation_key']}")
        if not row["verification_source"].startswith("https://"):
            raise ValueError(f"citation lacks an HTTPS verification source: {row['citation_key']}")
    print(f"CITATIONS_OK\t{len(cited)}")


if __name__ == "__main__":
    main()
