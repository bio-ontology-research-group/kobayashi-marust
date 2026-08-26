#!/usr/bin/env python3
"""Audit a KM sweep against the strict per-ontology external targets.

This is the performance half of the v1.2 gate.  Semantic preservation remains
the responsibility of ``audit_release_candidate.py`` / ``audit_strict.py``.
The gate is deliberately fail-closed: incomplete sweeps, duplicate ontology
rows, non-successful KM answers, non-finite measurements, and missing target
rows are reported explicitly and prevent a pass.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from collections import Counter
from pathlib import Path


EXPECTED_ONTOLOGIES = 592


def load_results(root: Path) -> dict[str, dict]:
    paths = sorted((root / "results").glob("ore_ont_*.owl.json"))
    rows = [json.loads(path.read_text()) for path in paths]
    names = [row.get("ont") for row in rows]
    if len(rows) != EXPECTED_ONTOLOGIES:
        raise SystemExit(
            f"expected {EXPECTED_ONTOLOGIES} candidate rows, found {len(rows)}"
        )
    duplicates = sorted(name for name, count in Counter(names).items() if count > 1)
    if duplicates:
        raise SystemExit(f"duplicate candidate ontologies: {duplicates}")
    return dict(zip(names, rows))


def load_targets(path: Path) -> dict[str, dict]:
    with path.open(newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    names = [row["ontology"] for row in rows]
    duplicates = sorted(name for name, count in Counter(names).items() if count > 1)
    if duplicates:
        raise SystemExit(f"duplicate target ontologies: {duplicates}")
    return dict(zip(names, rows))


def positive_finite(row: dict, field: str) -> float:
    value = float(row[field])
    if not math.isfinite(value) or value <= 0:
        raise ValueError(f"{field} is not positive and finite: {value!r}")
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("candidate", type=Path, help="completed sweep root")
    parser.add_argument("targets", type=Path, help="external target TSV")
    parser.add_argument("--binary-sha256")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    candidate = load_results(args.candidate.resolve())
    targets = load_targets(args.targets.resolve())
    unexpected_targets = sorted(set(targets) - set(candidate))
    if unexpected_targets:
        raise SystemExit(f"target ontologies absent from candidate: {unexpected_targets}")

    if args.binary_sha256:
        hashes = {row.get("binary_sha256") for row in candidate.values()}
        if hashes != {args.binary_sha256}:
            raise SystemExit(f"mixed or unexpected candidate hashes: {sorted(hashes)}")

    details = []
    invalid = []
    for ontology, target in sorted(targets.items()):
        row = candidate[ontology]
        try:
            wall = positive_finite(row, "wall_s")
            peak = positive_finite(row, "peak_mb")
            wall_target = positive_finite(target, "wall_target_s_exclusive")
            peak_target = positive_finite(target, "peak_target_mib_exclusive")
        except (KeyError, TypeError, ValueError) as error:
            invalid.append({"ontology": ontology, "reason": str(error)})
            continue
        # ``solved`` is false for a successfully classified ontology that KM
        # adjudicates as inconsistent.  Terminal success is represented by
        # ``status == "ok"``; semantic validity is checked by the companion
        # release/strict auditors.
        if row.get("status") != "ok":
            invalid.append(
                {
                    "ontology": ontology,
                    "reason": f"candidate status={row.get('status')!r}",
                }
            )
            continue
        wall_pass = wall < wall_target
        peak_pass = peak < peak_target
        details.append(
            {
                "ontology": ontology,
                "wall_s": wall,
                "wall_target_s_exclusive": wall_target,
                "wall_target_arm": target["wall_target_arm"],
                "wall_ratio": wall / wall_target,
                "wall_pass": wall_pass,
                "peak_mib": peak,
                "peak_target_mib_exclusive": peak_target,
                "peak_target_arm": target["peak_target_arm"],
                "peak_ratio": peak / peak_target,
                "peak_pass": peak_pass,
                "both_pass": wall_pass and peak_pass,
            }
        )

    categories = Counter(
        "both"
        if row["both_pass"]
        else "wall_only"
        if row["wall_pass"]
        else "memory_only"
        if row["peak_pass"]
        else "neither"
        for row in details
    )
    failures = [row for row in details if not row["both_pass"]]
    failures.sort(key=lambda row: max(row["wall_ratio"], row["peak_ratio"]), reverse=True)
    unadjudicated = sorted(set(candidate) - set(targets))
    passed = not invalid and not failures and not unadjudicated
    report = {
        "candidate_rows": len(candidate),
        "eligible_external_targets": len(targets),
        "categories": dict(sorted(categories.items())),
        "invalid": invalid,
        "failures": failures,
        "unadjudicated": unadjudicated,
        "strict_all_592_pass": passed,
        "note": (
            "An ontology without a correct external completion remains "
            "unadjudicated and prevents the all-592 v1.2 gate from passing."
        ),
    }
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
    raise SystemExit(0 if passed else 1)


if __name__ == "__main__":
    main()
