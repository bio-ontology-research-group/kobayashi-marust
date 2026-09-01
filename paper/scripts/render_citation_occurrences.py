#!/usr/bin/env python3
"""Bind every manuscript citation occurrence to its audited primary source."""

from __future__ import annotations

import csv
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPT = ROOT / "main.tex"
KEY_AUDIT = ROOT / "citation-audit.tsv"
OUTPUT = ROOT / "generated/citation-occurrences.tsv"


def clean_context(text: str) -> str:
    text = re.sub(r"%.*", " ", text)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def main() -> None:
    manuscript = MANUSCRIPT.read_text(encoding="utf-8")
    with KEY_AUDIT.open(encoding="utf-8", newline="") as stream:
        audit = {row["citation_key"]: row for row in csv.DictReader(stream, delimiter="\t")}

    rows: list[dict[str, str | int]] = []
    command = re.compile(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}")
    for occurrence, match in enumerate(command.finditer(manuscript), start=1):
        line = manuscript.count("\n", 0, match.start()) + 1
        left = max(manuscript.rfind(". ", 0, match.start()), manuscript.rfind("\n\n", 0, match.start()))
        right_candidates = [
            position for position in (
                manuscript.find(". ", match.end()),
                manuscript.find("\n\n", match.end()),
            ) if position >= 0
        ]
        right = min(right_candidates) + 1 if right_candidates else min(len(manuscript), match.end() + 240)
        context = clean_context(manuscript[left + 1:right])
        for key in (item.strip() for item in match.group(1).split(",")):
            if key not in audit:
                raise ValueError(f"citation occurrence uses unaudited key {key!r} at line {line}")
            rows.append({
                "occurrence": occurrence,
                "line": line,
                "citation_key": key,
                "claim_context": context,
                "verification_source": audit[key]["verification_source"],
                "status": audit[key]["status"],
            })

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with OUTPUT.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(
            stream,
            fieldnames=("occurrence", "line", "citation_key", "claim_context", "verification_source", "status"),
            delimiter="\t",
            lineterminator="\n",
        )
        writer.writeheader()
        writer.writerows(rows)
    print(f"CITATION_OCCURRENCES_OK\t{len(rows)}\t{OUTPUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
