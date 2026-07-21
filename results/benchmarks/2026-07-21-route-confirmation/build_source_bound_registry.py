#!/usr/bin/env python3
"""Build the 592-row current replay registry from verified inputs only."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import re


ACCEPTED_TARGETS = {"ore_ont_10621.owl"}
TARGETED_ROWS = {"ore_ont_4669.owl", "ore_ont_10621.owl"}


def sha256_file(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--frozen-registry", type=Path, required=True)
    parser.add_argument("--frozen-registry-sha256", required=True)
    parser.add_argument("--corpus-table", type=Path, required=True)
    parser.add_argument("--corpus-table-sha256", required=True)
    parser.add_argument("--targeted-registry", type=Path, required=True)
    parser.add_argument("--targeted-registry-sha256", required=True)
    parser.add_argument(
        "--target-result", type=Path, action="append", required=True
    )
    parser.add_argument("--expected-binary-sha256", required=True)
    parser.add_argument("--expected-source-manifest-sha256", required=True)
    parser.add_argument("--expected-build-receipt-sha256", required=True)
    parser.add_argument("--expected-konclude-sha256", required=True)
    parser.add_argument(
        "--expected-konclude-build-receipt-sha256", required=True
    )
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def read_tsv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        return list(reader.fieldnames or []), list(reader)


def check_hash(path: Path, expected: str) -> None:
    observed = sha256_file(path)
    if observed != expected:
        raise ValueError(
            f"hash mismatch for {path}: expected {expected}, observed {observed}"
        )


def verified_target_record(
    path: Path, args: argparse.Namespace
) -> tuple[str, dict, dict]:
    result = json.loads(path.read_text(encoding="utf-8"))
    ontology = result.get("ontology", "")
    run_root = path.parent.parent
    acceptance_path = run_root / "ACCEPTANCE.json"
    acceptance = json.loads(acceptance_path.read_text(encoding="utf-8"))
    route = result.get("route_specification") or {}
    reference = result.get("reference_route_specification") or {}
    checks = {
        "target": ontology in ACCEPTED_TARGETS,
        "protocol": result.get("validation_protocol")
        == "reproducible-current-selected-full-iri-v2",
        "confirmed": result.get("confirmed") is True
        and result.get("confirmation_status") == "confirmed_exact_full_iri",
        "acceptance": acceptance.get("status") == "accepted"
        and bool(acceptance.get("checks"))
        and all(acceptance["checks"].values()),
        "all_checks": bool(result.get("checks"))
        and all(result["checks"].values()),
        "route": result.get("effective_route_request") == "ht_bridge"
        and result.get("selected_route_trace") == "ht_bridge"
        and result.get("selected_route_trace_count") == 1,
        "binary": result.get("actual_binary_sha256")
        == args.expected_binary_sha256
        and route.get("binary_sha256") == args.expected_binary_sha256,
        "source": result.get("executed_source_manifest_sha256")
        == args.expected_source_manifest_sha256,
        "receipt": result.get("executed_build_receipt_sha256")
        == args.expected_build_receipt_sha256,
        "konclude": result.get("reference_binary_sha256")
        == args.expected_konclude_sha256
        and reference.get("binary_sha256") == args.expected_konclude_sha256,
        "konclude_receipt": result.get("reference_build_receipt_sha256")
        == args.expected_konclude_build_receipt_sha256
        and reference.get("build_receipt_sha256")
        == args.expected_konclude_build_receipt_sha256,
        "km_limits": route.get("timeout_s") == 240.0
        and route.get("memory_limit_mb") == 20480,
    }
    if not all(checks.values()):
        failed = [name for name, passed in checks.items() if not passed]
        raise ValueError(f"target record {path} failed checks: {failed}")
    return ontology, result, acceptance


def main() -> int:
    args = parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    check_hash(args.frozen_registry, args.frozen_registry_sha256)
    check_hash(args.corpus_table, args.corpus_table_sha256)
    check_hash(args.targeted_registry, args.targeted_registry_sha256)

    original_fields, original_rows = read_tsv(args.frozen_registry)
    if len(original_rows) != 592:
        raise ValueError(f"expected 592 historical rows, found {len(original_rows)}")
    original_names = [row["ontology"] for row in original_rows]
    if len(set(original_names)) != 592:
        raise ValueError("historical registry repeats ontology names")

    _, corpus_rows = read_tsv(args.corpus_table)
    corpus_hashes = {row["ontology"]: row["sha256"] for row in corpus_rows}
    if set(corpus_hashes) != set(original_names):
        raise ValueError("corpus table and historical registry name different inputs")
    if any(
        re.fullmatch(r"[0-9a-f]{64}", value) is None
        for value in corpus_hashes.values()
    ):
        raise ValueError("corpus table contains an invalid SHA-256")

    _, targeted_rows = read_tsv(args.targeted_registry)
    targeted = {row["ontology"]: row for row in targeted_rows}
    if set(targeted) != TARGETED_ROWS:
        raise ValueError("targeted registry must contain exactly 4669 and 10621")
    records = {}
    for path in args.target_result:
        ontology, result, acceptance = verified_target_record(path, args)
        if ontology in records:
            raise ValueError(f"duplicate targeted result: {ontology}")
        records[ontology] = (path, result, acceptance)
    if set(records) != ACCEPTED_TARGETS:
        raise ValueError("exactly the accepted 10621 targeted record is required")

    output_fields = ["ontology", "ontology_sha256"] + [
        field for field in original_fields if field != "ontology"
    ]
    output_rows = []
    for old in original_rows:
        ontology = old["ontology"]
        if ontology not in ACCEPTED_TARGETS:
            row = dict(old)
            row["ontology_sha256"] = corpus_hashes[ontology]
            output_rows.append(row)
            continue

        path, result, _ = records[ontology]
        row = {field: targeted[ontology].get(field, "") for field in output_fields}
        km_run = result["km_run"]
        km_fingerprint = result["km_fingerprint"]
        reference_fingerprint = result["reference_fingerprint"]
        row.update(
            ontology=ontology,
            ontology_sha256=corpus_hashes[ontology],
            state="exact_gold",
            route="ht_bridge",
            route_kind="reproduced_current_full_iri",
            within_limits="yes",
            verdict="match",
            wall_s=str(km_run["wall_s"]),
            peak_mb=str(km_run["peak_mb"]),
            timeout_s="240",
            memory_limit_mb="20480",
            cpus="16",
            binary_sha256=args.expected_binary_sha256,
            binary_locator=f"ibex:{result['executed_binary']}",
            source_revision=(
                f"source-manifest:{args.expected_source_manifest_sha256}"
            ),
            route_environment="KM_ROUTE=ht_bridge",
            invocation=f"km classify {ontology}",
            gold_kind="fresh twice-built official-source Konclude full-IRI",
            gold_sha256=reference_fingerprint["taxonomy_sha256"],
            signature_sha256=km_fingerprint["taxonomy_sha256"],
            evidence=(
                f"ibex:{path}; ibex:{path.parent.parent / 'ACCEPTANCE.json'}"
            ),
            notes=(
                "Fresh capsule-10 replay selected exactly one ht_bridge route "
                "and matched the source-built Konclude named-class taxonomy by "
                "complete IRI within the KM benchmark limits."
            ),
        )
        if row["ontology_sha256"] != targeted[ontology]["ontology_sha256"]:
            raise ValueError(f"targeted corpus hash mismatch: {ontology}")
        output_rows.append(row)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=output_fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(output_rows)
    print(
        json.dumps(
            {
                "output": str(args.output),
                "rows": len(output_rows),
                "sha256": sha256_file(args.output),
                "accepted_targets": sorted(ACCEPTED_TARGETS),
                "open_targeted_rows": sorted(TARGETED_ROWS - ACCEPTED_TARGETS),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
