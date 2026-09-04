#!/usr/bin/env python3
"""Verify the copied compact portion of the 2026-09-04 impact extension."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def main() -> None:
    expected: dict[Path, str] = {}
    for raw in (ROOT / "SHA256SUMS").read_text(encoding="utf-8").splitlines():
        wanted, name = raw.split("  ", 1)
        path = ROOT / name.removeprefix("./")
        if path in expected:
            raise ValueError(f"duplicate manifest path: {name}")
        expected[path] = wanted
    actual = {
        path
        for path in ROOT.rglob("*")
        if path.is_file() and path.name not in {"SHA256SUMS", "verify_compact.py"}
    }
    if actual != set(expected):
        raise ValueError(
            f"manifest set mismatch: missing={sorted(map(str, expected.keys() - actual))}, "
            f"extra={sorted(map(str, actual - expected.keys()))}"
        )
    for path, wanted in expected.items():
        if digest(path) != wanted:
            raise ValueError(f"digest mismatch: {path.relative_to(ROOT)}")

    summary = json.loads((ROOT / "summary.json").read_text(encoding="utf-8"))
    if summary.get("status") != "validated":
        raise ValueError("summary is not validated")
    product = summary["product_configuration"]
    if product["full_control"]["unsatisfiable"] != []:
        raise ValueError("product control is not coherent")
    if product["full_conflict"]["unsatisfiable"] != [
        "http://example.org/km-impact/configuration#DualSensorSurveyDrone"
    ]:
        raise ValueError("product conflict changed")
    if not all(
        product[key]
        for key in (
            "hermit_agreement",
            "el_projection_km_elk_exact",
            "control_and_conflict_el_semantics_equal",
            "explanation_feature_gate",
        )
    ):
        raise ValueError("product validation gate changed")

    galen = summary["galen"]
    expected_galen = {
        "source_axioms": 61782,
        "removed_axioms": 1149,
        "projection_subsumptions": 453710,
        "full_subsumptions": 457090,
        "full_only_subsumptions": 3380,
        "projection_only_subsumptions": 0,
    }
    if any(galen.get(key) != value for key, value in expected_galen.items()):
        raise ValueError("GALEN counts changed")
    if not galen["projection_km_elk_exact"] or not galen["projection_subset_of_full"]:
        raise ValueError("GALEN comparator gate changed")

    final = {}
    for raw in (ROOT / "FINAL_RECEIPT.tsv").read_text(encoding="utf-8").splitlines():
        if "\t" in raw:
            key, value = raw.split("\t", 1)
            if key:
                final[key] = value
    if final.get("status") != "validated" or final.get("terminal_marker") != "VALIDATION_COMPLETE":
        raise ValueError("final receipt is not terminal")
    if final.get("summary_sha256") != digest(ROOT / "summary.json"):
        raise ValueError("summary is not bound by final receipt")
    print("IMPACT_COMPACT_OK\tfiles=%d\tgalen_full_only=3380" % len(actual))


if __name__ == "__main__":
    main()
