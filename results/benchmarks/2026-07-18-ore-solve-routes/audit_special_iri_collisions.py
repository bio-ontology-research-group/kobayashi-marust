#!/usr/bin/env python3
"""Find source classes that KM can confuse with owl:Thing or owl:Nothing."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re


DECLARED_CLASS = re.compile(
    rb"Declaration\(\s*Class\(\s*(<[^>]+>|[A-Za-z][A-Za-z0-9_.-]*:[A-Za-z0-9_.-]+)"
)
IRI_TOKEN = re.compile(
    rb"<[^>\r\n]+>|[A-Za-z][A-Za-z0-9_.-]*:(?:Thing|Nothing)\b"
)
OWL_SPECIALS = {
    "owl:Thing",
    "owl:Nothing",
    "http://www.w3.org/2002/07/owl#Thing",
    "http://www.w3.org/2002/07/owl#Nothing",
}


def short_base(name: str) -> str:
    if name.startswith("<") and name.endswith(">"):
        name = name[1:-1]
    if "#" in name:
        return name.rsplit("#", 1)[1]
    if name.startswith(":"):
        return name[1:]
    if name.startswith("owl:"):
        return name
    if "://" in name and "/" in name:
        return name.rsplit("/", 1)[1]
    if ":" in name:
        return name.split(":", 1)[1]
    return name


def scan(path: Path) -> dict:
    declarations: Counter[str] = Counter()
    occurrences: Counter[str] = Counter()
    with path.open("rb") as handle:
        for line in handle:
            for match in DECLARED_CLASS.finditer(line):
                token = match.group(1).decode("utf-8", errors="replace")
                iri = token[1:-1] if token.startswith("<") else token
                if iri not in OWL_SPECIALS and short_base(token) in ("Thing", "Nothing"):
                    declarations[iri] += 1
            for match in IRI_TOKEN.finditer(line):
                token = match.group(0).decode("utf-8", errors="replace")
                iri = token[1:-1] if token.startswith("<") else token
                if iri not in OWL_SPECIALS and short_base(token) in ("Thing", "Nothing"):
                    occurrences[iri] += 1
    return {
        "schema_version": 1,
        "ontology": path.name,
        "bytes": path.stat().st_size,
        "collision_count": len(occurrences),
        "collisions": [
            {
                "iri": iri,
                "occurrences": count,
                "declarations": declarations[iri],
            }
            for iri, count in sorted(occurrences.items())
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--task-index", type=int, required=True)
    parser.add_argument("--task-count", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    ontologies = sorted(args.corpus.glob("ore_ont_*.owl"))
    selected = ontologies[args.task_index :: args.task_count]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    with temporary.open("w", encoding="utf-8") as handle:
        for ontology in selected:
            handle.write(json.dumps(scan(ontology), sort_keys=True) + "\n")
    temporary.replace(args.output)
    print(
        json.dumps(
            {
                "task_index": args.task_index,
                "task_count": args.task_count,
                "corpus_ontologies": len(ontologies),
                "scanned": len(selected),
                "output": str(args.output),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
