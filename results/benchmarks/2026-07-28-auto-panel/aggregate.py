#!/usr/bin/env python3
"""Aggregate and correctness-audit the six-arm automatic-policy panel."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from full_panel_contract import panel


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("run", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    arms = [row["arm"] for row in panel()]
    files = sorted(args.run.glob("results/*.jsonl"))
    rows = []
    for path in files:
        current = [json.loads(line) for line in path.read_text().splitlines() if line]
        if [row.get("arm") for row in current] != arms:
            raise SystemExit(f"contract mismatch: {path}")
        rows.extend(current)

    summary = {
        "schema_version": 1,
        "ontology_files": len(files),
        "rows": len(rows),
        "expected_ontologies": 592,
        "expected_rows": 592 * len(arms),
        "arms": {},
    }
    for arm in arms:
        selected = [row for row in rows if row["arm"] == arm]
        summary["arms"][arm] = {
            "rows": len(selected),
            "status": dict(Counter(row.get("status") for row in selected)),
            "correctness": dict(Counter(row.get("correctness") for row in selected)),
            "verdict": dict(Counter(row.get("verdict") for row in selected)),
            "solved_sound_complete": sum(
                row.get("sound") == "yes" and row.get("complete") == "yes"
                for row in selected
            ),
        }
    args.output.write_text(
        json.dumps(summary, sort_keys=True, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
