#!/usr/bin/env python3
"""Summarize normalized clause shapes retained by a 10621 diagnostic run."""

from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import sys


def main() -> int:
    path = Path(sys.argv[1])
    clauses = json.loads(path.read_text())["clauses"]
    counts: Counter[tuple[object, ...]] = Counter()
    samples: dict[tuple[object, ...], dict[str, object]] = {}
    for clause in clauses:
        body = clause["body"]
        head = clause["head"]
        has_eq = any(atom["kind"] == "eq" for atom in body + head)
        key = (
            len(body),
            len(head),
            has_eq,
            tuple(atom["kind"] for atom in body),
            tuple(atom["kind"] for atom in head),
        )
        counts[key] += 1
        samples.setdefault(key, clause)
    print(f"total\t{len(clauses)}")
    for key, count in counts.most_common():
        sample = json.dumps(samples[key], separators=(",", ":"))
        print(f"{count}\t{key!r}\t{sample[:2000]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
