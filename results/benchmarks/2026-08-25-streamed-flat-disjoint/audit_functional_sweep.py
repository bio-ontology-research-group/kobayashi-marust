#!/usr/bin/env python3
"""Fail-closed progress and integrity audit for the functional sweep."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--expected", type=int, default=592)
    parser.add_argument("--ontology-list", type=Path)
    parser.add_argument("--binary-sha256")
    args = parser.parse_args()

    result_dir = args.root / "results"
    terminals = sorted(
        path
        for path in result_dir.glob("*.json")
        if not path.name.endswith(".checkpoint.json")
    )
    errors: list[str] = []
    rows: list[dict] = []
    ontology_names: list[str] = []

    for terminal in terminals:
        stem = terminal.name[: -len(".json")]
        checkpoint = terminal.with_name(
            stem + ".checkpoint.json"
        )
        if not checkpoint.is_file():
            errors.append(f"missing checkpoint: {terminal.name}")
        elif checkpoint.read_bytes() != terminal.read_bytes():
            errors.append(f"checkpoint differs: {terminal.name}")
        try:
            row = json.loads(terminal.read_text())
        except Exception as exc:  # fail closed on malformed/truncated output
            errors.append(f"invalid JSON {terminal.name}: {exc}")
            continue
        rows.append(row)
        ontology_names.append(stem)
        if row.get("ont") != stem:
            errors.append(f"ontology identity mismatch: {terminal.name}")
        if row.get("checkpointed") is not True:
            errors.append(f"checkpoint flag missing: {terminal.name}")
        if args.binary_sha256 and row.get("binary_sha256") != args.binary_sha256:
            errors.append(f"binary mismatch: {terminal.name}")
        if row.get("status") == "ok":
            required = (
                "wall_s",
                "peak_mb",
                "cpu_model",
                "host",
                "selected_route_trace",
                "signature_sha256",
            )
            missing = [key for key in required if row.get(key) in (None, "")]
            if missing:
                errors.append(
                    f"incomplete profile {terminal.name}: {', '.join(missing)}"
                )

    duplicates = sorted(name for name, count in Counter(ontology_names).items() if count != 1)
    if duplicates:
        errors.append("duplicate ontology records: " + ", ".join(duplicates))
    if len(terminals) > args.expected:
        errors.append(f"too many terminal records: {len(terminals)} > {args.expected}")
    if args.ontology_list:
        expected_names = {
            Path(line.strip()).name
            for line in args.ontology_list.read_text().splitlines()
            if line.strip()
        }
        observed_names = set(ontology_names)
        extra = sorted(observed_names - expected_names)
        if extra:
            errors.append("unexpected ontology records: " + ", ".join(extra))
        if len(terminals) == args.expected:
            missing_records = sorted(expected_names - observed_names)
            if missing_records:
                errors.append(
                    "missing ontology records at completion: " + ", ".join(missing_records)
                )
        if len(expected_names) != args.expected:
            errors.append(
                f"ontology list has {len(expected_names)} unique entries, expected {args.expected}"
            )

    print(f"terminal={len(terminals)}/{args.expected}")
    print("status=" + json.dumps(Counter(row.get("status") for row in rows), sort_keys=True))
    print("verdict=" + json.dumps(Counter(row.get("verdict") for row in rows), sort_keys=True))
    print(f"integrity_errors={len(errors)}")
    for error in errors:
        print(f"ERROR {error}")
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
