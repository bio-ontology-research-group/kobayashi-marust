#!/usr/bin/env python3
"""Replay the representative UO singleton-nominal equality witness."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


EXPECTED_SOURCE = "b6f4a0fa082b6357dd34801d09bbf4041667698374aaf8474b900f819f15ffa7"
EQUIV = re.compile(r"EquivalentClasses\(<([^>]+)> ObjectOneOf\(<([^>]+)>\)\)")
SUB = re.compile(r"SubClassOf\(<([^>]+)> <([^>]+)>\)")


def verify(path: Path, source: Path | None = None) -> dict:
    rows = path.read_text(encoding="utf-8").splitlines()
    if not rows or rows[-1] != "Z\tcomplete":
        raise ValueError("incomplete UO witness")
    metadata: dict[str, str] = {}
    axioms: list[str] = []
    for row in rows[:-1]:
        fields = row.split("\t", 2)
        if len(fields) == 3 and fields[0] == "M":
            if fields[1] in metadata:
                raise ValueError(f"duplicate UO metadata: {fields[1]}")
            metadata[fields[1]] = fields[2]
        elif len(fields) == 2 and fields[0] == "A":
            axioms.append(fields[1])
        else:
            raise ValueError(f"malformed UO witness row: {row}")
    if metadata.get("schema") != "1" or metadata.get("source_sha256") != EXPECTED_SOURCE:
        raise ValueError("UO source metadata mismatch")
    if len(axioms) != 3 or len(set(axioms)) != 3:
        raise ValueError("UO witness must contain three distinct axioms")

    singletons: dict[str, str] = {}
    subclass = None
    for axiom in axioms:
        match = EQUIV.fullmatch(axiom)
        if match:
            cls, individual = match.groups()
            if cls != individual:
                raise ValueError("UO witness does not use legal class/individual punning")
            singletons[cls] = individual
            continue
        match = SUB.fullmatch(axiom)
        if match:
            if subclass is not None:
                raise ValueError("multiple UO subclass premises")
            subclass = match.groups()
            continue
        raise ValueError(f"unsupported UO witness axiom: {axiom}")
    if subclass is None:
        raise ValueError("missing UO subclass premise")
    sub, sup = subclass
    if set(singletons) != {sub, sup}:
        raise ValueError("UO singleton and subclass signatures differ")
    expected_query = f"{sup} < {sub}"
    if metadata.get("query") != expected_query:
        raise ValueError("UO query is not the reverse singleton inclusion")

    source_verified = False
    if source is not None:
        actual = hashlib.sha256(source.read_bytes()).hexdigest()
        if actual != EXPECTED_SOURCE:
            raise ValueError(f"UO source digest mismatch: {actual}")
        source_lines = set(source.read_text(encoding="utf-8").splitlines())
        missing = [axiom for axiom in axioms if axiom not in source_lines]
        if missing:
            raise ValueError(f"UO source omits witness axioms: {missing}")
        source_verified = True
    return {
        "schema": 1,
        "status": "entailed",
        "query": [sup, sub],
        "source_sha256": EXPECTED_SOURCE,
        "premise_count": 3,
        "source_verified": source_verified,
        "derivation": [
            "the subclass singleton's individual belongs to the superclass singleton",
            "singleton membership forces the two individual denotations equal",
            "the two singleton class extensions are equal, giving the reverse inclusion",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--witness", required=True, type=Path)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    report = verify(args.witness, args.source)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print(f"UO_NOMINAL_WITNESS_OK\t3\t{str(report['source_verified']).lower()}")


if __name__ == "__main__":
    main()
