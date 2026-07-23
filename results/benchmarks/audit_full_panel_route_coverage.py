#!/usr/bin/env python3
"""Fail unless a panel contract includes every accepted historical KM config."""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import shlex


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def environment(items: list[str]) -> tuple[tuple[str, str], ...]:
    parsed: dict[str, str] = {}
    for item in items:
        if "=" not in item:
            raise ValueError(f"environment entry is not KEY=VALUE: {item!r}")
        key, value = item.split("=", 1)
        if not key or key in parsed:
            raise ValueError(f"invalid or duplicate environment key: {key!r}")
        parsed[key] = value
    return tuple(sorted(parsed.items()))


def load_contract(path: Path):
    specification = importlib.util.spec_from_file_location("_audited_panel_contract", path)
    if specification is None or specification.loader is None:
        raise SystemExit(f"cannot load contract: {path}")
    module = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(module)
    return module


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--contract", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    contract = load_contract(args.contract)
    public = {
        environment([f"KM_ROUTE={route}"]): f"public:{route}"
        for route in contract.KM_ROUTES
    }
    documented = {
        environment(entries): f"documented:{label}"
        for _arm, label, entries in contract.DOCUMENTED_SOLUTION_ROUTES
    }
    overlap = set(public).intersection(documented)
    if overlap:
        raise SystemExit(f"ambiguous public/documented environments: {sorted(overlap)}")
    covered = public | documented

    with args.ledger.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    # The ledger deliberately documents all 592 ontologies, including the
    # three negative claims.  An accepted historical solve is the semantic
    # claim, not a spelling convention in ``km_state``.
    accepted = [
        row
        for row in rows
        if row.get("km_sound") == "yes" and row.get("km_complete") == "yes"
    ]
    if len(rows) != 592 or len(accepted) != 589:
        raise SystemExit(
            f"unexpected ledger population: rows={len(rows)} accepted={len(accepted)}"
        )

    historical: dict[tuple[tuple[str, str], ...], list[str]] = {}
    for row in accepted:
        exact = environment(shlex.split(row["km_route_environment"]))
        historical.setdefault(exact, []).append(row["ontology"])
    missing = {
        exact: ontologies
        for exact, ontologies in historical.items()
        if exact not in covered
    }
    report = {
        "status": "complete" if not missing else "missing_historical_routes",
        "ledger": str(args.ledger),
        "ledger_sha256": sha256_file(args.ledger),
        "contract": str(args.contract),
        "contract_sha256": sha256_file(args.contract),
        "ledger_rows": len(rows),
        "accepted_rows": len(accepted),
        "unique_historical_environments": len(historical),
        "public_contract_routes": len(public),
        "documented_contract_environments": len(documented),
        "missing_environment_count": len(missing),
        "missing": [
            {
                "environment": [f"{key}={value}" for key, value in exact],
                "ontologies": sorted(ontologies),
            }
            for exact, ontologies in sorted(missing.items())
        ],
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    if missing:
        raise SystemExit(1)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
