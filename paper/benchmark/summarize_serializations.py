#!/usr/bin/env python3
"""Validate and summarize source-bound XML views used by Konclude."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path


def rows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def receipt(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    terminal = None
    with path.open(encoding="utf-8") as stream:
        for raw in stream:
            fields = raw.rstrip("\n").split("\t")
            if len(fields) == 3 and fields[0] == "M":
                if fields[1] in values:
                    raise ValueError(f"duplicate {fields[1]} in {path}")
                values[fields[1]] = fields[2]
            elif len(fields) == 4 and fields[0] == "I" and all(fields[1:]):
                # Import provenance is validated by the freeze receipt.  It is
                # not a scalar metadata key needed by this summary.
                continue
            elif fields == ["Z", "complete"]:
                terminal = "complete"
            else:
                raise ValueError(f"invalid row in {path}: {raw.rstrip()}")
    if terminal != "complete":
        raise ValueError(f"incomplete receipt {path}")
    return values


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--import-receipts", required=True, type=Path)
    parser.add_argument("--serialization-receipts", required=True, type=Path)
    parser.add_argument("--preparation-artifacts", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--output-tex", type=Path)
    parser.add_argument("--expected-count", type=int, default=189)
    args = parser.parse_args()

    identifiers = [row["id"] for row in rows(args.manifest) if row["eligible"] == "true"]
    if len(identifiers) != args.expected_count or len(set(identifiers)) != len(identifiers):
        raise ValueError("eligible ontology population mismatch")
    artifacts = {row["id"]: row for row in rows(args.preparation_artifacts)}
    converter = artifacts.get("verified-xml-converter", {}).get("runtime_sha256", "")
    if len(converter) != 64:
        raise ValueError("converter artifact binding absent")

    serialization_counts: Counter[str] = Counter()
    alpha_renamed_rules = 0
    alpha_renamed_ontologies = 0
    annotation_delta_counts: Counter[int] = Counter()
    ledger = hashlib.sha256()
    for identifier in identifiers:
        canonical = receipt(args.import_receipts / f"{identifier}.tsv")["merged_sha256"]
        converted = receipt(args.serialization_receipts / f"{identifier}.tsv")
        required = {
            "schema", "conversion", "converter_sha256", "serialization", "source_sha256",
            "output_sha256", "roundtrip_logical_axioms_equal",
            "roundtrip_alpha_renamed_rules", "roundtrip_annotation_axiom_delta",
            "roundtrip_signature_equal",
        }
        if not required.issubset(converted):
            raise ValueError(f"incomplete conversion evidence for {identifier}")
        if converted["schema"] != "1" or converted["conversion"] != "konclude-compatible-serialization-v2":
            raise ValueError(f"wrong conversion contract for {identifier}")
        if converted["converter_sha256"] != converter or converted["source_sha256"] != canonical:
            raise ValueError(f"artifact/source mismatch for {identifier}")
        if converted["serialization"] not in {"owlxml", "functional"}:
            raise ValueError(f"unknown serialization for {identifier}")
        if converted["roundtrip_logical_axioms_equal"] != "true" \
                or converted["roundtrip_signature_equal"] != "true":
            raise ValueError(f"failed semantic round trip for {identifier}")
        renamed = int(converted["roundtrip_alpha_renamed_rules"])
        delta = int(converted["roundtrip_annotation_axiom_delta"])
        serialization_counts[converted["serialization"]] += 1
        alpha_renamed_rules += renamed
        alpha_renamed_ontologies += renamed > 0
        annotation_delta_counts[delta] += 1
        for value in (identifier, canonical, converted["output_sha256"], converted["serialization"]):
            encoded = value.encode("utf-8")
            ledger.update(len(encoded).to_bytes(8, "big")); ledger.update(encoded)

    summary = {
        "schema": 1,
        "contract": "konclude-compatible-serialization-v2",
        "ontologies": len(identifiers),
        "converter_sha256": converter,
        "serialization_counts": dict(sorted(serialization_counts.items())),
        "alpha_renamed_rule_axioms": alpha_renamed_rules,
        "alpha_renamed_ontologies": alpha_renamed_ontologies,
        "annotation_axiom_delta_counts": {
            str(key): value for key, value in sorted(annotation_delta_counts.items())
        },
        "source_output_ledger_sha256": ledger.hexdigest(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output) + ".part")
    temporary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(args.output)
    if args.output_tex:
        tex = (
            "% Generated by summarize_serializations.py; do not edit.\n"
            f"\\newcommand{{\\KMSerializationCount}}{{{len(identifiers)}}}\n"
            f"\\newcommand{{\\KMSerializationOWLXML}}{{{serialization_counts['owlxml']}}}\n"
            f"\\newcommand{{\\KMSerializationFunctional}}{{{serialization_counts['functional']}}}\n"
            f"\\newcommand{{\\KMSerializationAlphaOntologies}}{{{alpha_renamed_ontologies}}}\n"
            f"\\newcommand{{\\KMSerializationAlphaRules}}{{{alpha_renamed_rules}}}\n"
            f"\\newcommand{{\\KMSerializationLedger}}{{\\texttt{{{ledger.hexdigest()}}}}}\n"
        )
        args.output_tex.parent.mkdir(parents=True, exist_ok=True)
        tex_temporary = Path(str(args.output_tex) + ".part")
        tex_temporary.write_text(tex, encoding="utf-8")
        tex_temporary.replace(args.output_tex)
    print(f"SERIALIZATIONS_OK\t{len(identifiers)}\t{ledger.hexdigest()}")


if __name__ == "__main__":
    main()
