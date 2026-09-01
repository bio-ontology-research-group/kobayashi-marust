#!/usr/bin/env python3
"""Fail-closed verification of the archived STATO_0000073 adjudication."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


EXPECTED = {
    "module.ofn": "2e6e66e653c377c416ddf611051c424eba88474698616cebb23c82c66d1d464f",
    "hermit-query.tsv": "71714c35ce0dc2f8640d91b59db141ef1ce9171f620287efe623a45b01ce5468",
    "jfact-bottom.tsv": "353f0cef6162f67ccf7f3b02f4e646be9a9e4834216558da59adad7bfca03016",
    "results/jfact/stato-0000073-module.result.json":
        "d15298400a4590558cc13d6064eb1b22a54300f7c6cefc8b27117fed16164311",
    "results/openllet/stato-0000073-module.result.json":
        "ac289f9ed825d4805b899a2e612f411f866cd6a1f92bda380e727f4bf1768f7c",
}
SOURCE_SHA256 = "bf310eeeeade2d8f9042acf00a9f187678f2203ed9a3d9790ac3ac9abd719aad"
TARGET = "http://purl.obolibrary.org/obo/STATO_0000073"
BOTTOM = "http://www.w3.org/2002/07/owl#Nothing"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_provenance(path: Path) -> dict[str, str]:
    rows = path.read_text(encoding="utf-8").splitlines()
    if not rows or rows[-1] != "Z\tcomplete":
        raise ValueError("incomplete STATO provenance")
    values: dict[str, str] = {}
    for line in rows[:-1]:
        fields = line.split("\t", 2)
        if len(fields) != 3 or fields[0] != "M" or fields[1] in values:
            raise ValueError(f"malformed STATO provenance row: {line}")
        values[fields[1]] = fields[2]
    return values


def verify(root: Path) -> dict:
    for name, expected in EXPECTED.items():
        actual = digest(root / name)
        if actual != expected:
            raise ValueError(f"STATO evidence digest mismatch for {name}: {actual}")
    provenance = read_provenance(root / "provenance.tsv")
    if provenance.get("source_sha256") != SOURCE_SHA256:
        raise ValueError("STATO source digest mismatch")
    if provenance.get("module_sha256") != EXPECTED["module.ofn"]:
        raise ValueError("STATO provenance does not bind the archived module")
    if provenance.get("query") != f"{TARGET} < {BOTTOM}":
        raise ValueError("STATO provenance query mismatch")

    query = {}
    for line in (root / "hermit-query.tsv").read_text(encoding="utf-8").splitlines():
        fields = line.split("\t")
        if len(fields) == 3 and fields[0] == "M":
            query[fields[1]] = fields[2]
    if query != {"module_logical_axioms": "443", "module_axioms": "2072",
                 "entailed": "false", "explanation_axioms": "0"}:
        raise ValueError(f"unexpected HermiT query receipt: {query}")
    if (root / "jfact-bottom.tsv").read_text(encoding="utf-8") != f"U\t{TARGET}\n":
        raise ValueError("unexpected JFact bottom witness")

    records = {}
    for baseline in ("jfact", "openllet"):
        path = root / "results" / baseline / "stato-0000073-module.result.json"
        record = json.loads(path.read_text(encoding="utf-8"))
        expected_runtime = provenance[f"{baseline}_runtime_sha256"]
        required = {
            "baseline": baseline,
            "ontology_id": "stato-0000073-module",
            "ontology_sha256": EXPECTED["module.ofn"],
            "runtime_sha256": expected_runtime,
            "status": "ok",
            "consistency": "true",
        }
        for key, value in required.items():
            if record.get(key) != value:
                raise ValueError(f"unexpected {baseline} {key}: {record.get(key)!r}")
        records[baseline] = record
    if records["jfact"].get("unsatisfiable") != 1:
        raise ValueError("JFact did not retain exactly one unsatisfiable class")
    if records["openllet"].get("unsatisfiable") != 0:
        raise ValueError("Openllet did not retain zero unsatisfiable classes")
    return {
        "schema": 1,
        "source_sha256": SOURCE_SHA256,
        "module_sha256": EXPECTED["module.ofn"],
        "module_axioms": 2072,
        "module_logical_axioms": 443,
        "hermit_bottom_entailed": False,
        "jfact_unsatisfiable": 1,
        "openllet_unsatisfiable": 0,
        "status": "jfact-only-bottom-reproduced",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence-root", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = verify(args.evidence_root)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print("STATO_ADJUDICATION_OK\t443\t2")


if __name__ == "__main__":
    main()
