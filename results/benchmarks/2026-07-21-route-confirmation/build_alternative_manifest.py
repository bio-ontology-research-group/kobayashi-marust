#!/usr/bin/env python3
"""Join every documented alternative-route claim to its frozen evidence row."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path


EXPECTED_CLAIMS = 10_755


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selected-registry", type=Path, required=True)
    parser.add_argument("--selected-registry-sha256", required=True)
    parser.add_argument("--frozen-registry", type=Path, required=True)
    parser.add_argument("--frozen-registry-sha256", required=True)
    parser.add_argument("--selected-result-dir", type=Path, required=True)
    parser.add_argument("--selected-summary-json", type=Path, required=True)
    parser.add_argument("--selected-summary-sha256", required=True)
    parser.add_argument("--current-binary-locator", required=True)
    parser.add_argument("--current-binary-sha256", required=True)
    parser.add_argument("--current-source-manifest-sha256", required=True)
    parser.add_argument("--current-build-receipt-locator", required=True)
    parser.add_argument("--current-build-receipt-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    return parser.parse_args()


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def require_ibex_absolute_locator(value: str, field: str) -> str:
    prefix = "ibex:"
    if not value.startswith(prefix):
        raise SystemExit(f"{field} must use an ibex: host-qualified locator")
    path = Path(value[len(prefix) :])
    if not path.is_absolute():
        raise SystemExit(f"{field} must contain an absolute path")
    return value


def historical_locator(binary_sha: str, ontology: str) -> tuple[str, str]:
    root = "ibex:/ibex/scratch/hohndor/km/routing_20260715"
    if binary_sha.startswith("c229366f"):
        return (
            f"{root}/km-source-symbol-c229366f",
            f"{root}/matrix-results-c229366f/{ontology}.jsonl",
        )
    if binary_sha.startswith("534d5e0b"):
        return (
            "missing:formerly-ibex:/ibex/scratch/hohndor/km/"
            "routing_20260715/km-current-remaining14",
            f"{root}/cb-absorb-portfolio16-full/{ontology}.jsonl",
        )
    if binary_sha.startswith("60f147d5"):
        return (
            f"{root}/candidates/a0d0148816c5/km",
            f"{root}/production-sweeps/candidate-a0d0148/results/{ontology}.jsonl",
        )
    raise ValueError(f"unknown historical binary hash {binary_sha}")


def main() -> int:
    args = parse_args()
    current_binary_locator = require_ibex_absolute_locator(
        args.current_binary_locator, "--current-binary-locator"
    )
    current_build_receipt_locator = require_ibex_absolute_locator(
        args.current_build_receipt_locator,
        "--current-build-receipt-locator",
    )
    current_binary = Path(current_binary_locator.removeprefix("ibex:"))
    current_build_receipt = Path(
        current_build_receipt_locator.removeprefix("ibex:")
    )
    if sha256_file(current_binary) != args.current_binary_sha256:
        raise SystemExit("current binary differs from its pinned SHA-256")
    if sha256_file(current_build_receipt) != args.current_build_receipt_sha256:
        raise SystemExit("current build receipt differs from its pinned SHA-256")
    selected = read_tsv(args.selected_registry)
    frozen = read_tsv(args.frozen_registry)
    if len(selected) != 592:
        raise SystemExit(f"selected registry has {len(selected)} rows, expected 592")
    selected_ontologies = [row["ontology"] for row in selected]
    if len(set(selected_ontologies)) != len(selected_ontologies):
        raise SystemExit("selected registry repeats ontology names")
    selected_registry_sha256 = sha256_file(args.selected_registry)
    if selected_registry_sha256 != args.selected_registry_sha256:
        raise SystemExit("selected registry differs from its pinned hash")
    frozen_registry_sha256 = sha256_file(args.frozen_registry)
    if frozen_registry_sha256 != args.frozen_registry_sha256:
        raise SystemExit("frozen route matrix differs from its pinned hash")
    if sha256_file(args.selected_summary_json) != args.selected_summary_sha256:
        raise SystemExit("selected aggregate summary differs from its pinned hash")
    selected_summary = json.loads(
        args.selected_summary_json.read_text(encoding="utf-8")
    )
    selected_record_payload = bytearray()
    selected_record_count = 0
    for selected_row in selected:
        relative = Path("results") / f"{selected_row['ontology']}.json"
        path = args.selected_result_dir / relative
        if not path.is_file():
            raise SystemExit(f"missing selected result: {path}")
        selected_record_payload.extend(
            f"{sha256_file(path)}  {relative}\n".encode("utf-8")
        )
        selected_record_count += 1
    selected_record_manifest_sha256 = hashlib.sha256(
        selected_record_payload
    ).hexdigest()
    expected_summary = {
        "registry_sha256": selected_registry_sha256,
        "registry_rows": len(selected),
        "result_records": selected_record_count,
        "result_record_manifest_count": selected_record_count,
        "result_record_manifest_sha256": selected_record_manifest_sha256,
    }
    mismatched_summary = [
        key
        for key, value in expected_summary.items()
        if selected_summary.get(key) != value
    ]
    if mismatched_summary:
        raise SystemExit(
            "selected aggregate does not bind the exact result stream: "
            f"{mismatched_summary}"
        )

    frozen_by_key: dict[tuple[str, str], dict[str, str]] = {}
    duplicates = []
    for row in frozen:
        key = (row["ontology"], row["route"])
        if key in frozen_by_key:
            duplicates.append(key)
        frozen_by_key[key] = row
    if duplicates:
        raise SystemExit(f"duplicate frozen keys: {duplicates[:10]}")

    output_rows = []
    missing = []
    reference_hashes: dict[str, str] = {}
    for selected_row in selected:
        routes = [
            route
            for route in selected_row["other_verified_exact_routes"].split(",")
            if route
        ]
        for route in routes:
            key = (selected_row["ontology"], route)
            historical = frozen_by_key.get(key)
            if historical is None:
                missing.append(key)
                continue
            if historical["state"] != "exact_gold" or historical["verdict"] != "match":
                raise SystemExit(f"alternative claim is not exact in frozen row: {key}")
            if historical["signature_sha256"] != selected_row["signature_sha256"]:
                raise SystemExit(f"signature changed between frozen and selected row: {key}")
            if historical.get("ontology_sha256") and (
                historical["ontology_sha256"] != selected_row["ontology_sha256"]
            ):
                raise SystemExit(
                    f"ontology bytes changed between frozen and selected row: {key}"
                )
            old_binary, evidence = historical_locator(
                historical["binary_sha256"], historical["ontology"]
            )
            reference_relative = "results/" + historical["ontology"] + ".json"
            reference_path = args.selected_result_dir / reference_relative
            if historical["ontology"] not in reference_hashes:
                if not reference_path.is_file():
                    raise SystemExit(f"missing selected result: {reference_path}")
                reference = json.loads(reference_path.read_text(encoding="utf-8"))
                if (
                    reference.get("documented_state") != "exact_gold"
                    or reference.get("reference_ready") is not True
                    or reference.get("ontology_sha256")
                    != selected_row["ontology_sha256"]
                ):
                    raise SystemExit(
                        f"selected result lacks exact fresh reference: {reference_path}"
                    )
                reference_hashes[historical["ontology"]] = sha256_file(
                    reference_path
                )
            output_rows.append(
                {
                    "task_index": len(output_rows),
                    "ontology": historical["ontology"],
                    "ontology_sha256": selected_row["ontology_sha256"],
                    "route": route,
                    "route_environment": f"KM_ROUTE={route}",
                    "current_binary_locator": current_binary_locator,
                    "current_binary_sha256": args.current_binary_sha256,
                    "current_source_manifest_sha256": (
                        args.current_source_manifest_sha256
                    ),
                    "current_build_receipt_locator": (
                        current_build_receipt_locator
                    ),
                    "current_build_receipt_sha256": (
                        args.current_build_receipt_sha256
                    ),
                    "historical_binary_locator": old_binary,
                    "historical_binary_sha256": historical["binary_sha256"],
                    "historical_wall_s": historical["wall_s"],
                    "historical_peak_mb": historical["peak_mb"],
                    "historical_gold_kind": historical["gold_kind"],
                    "historical_gold_sha256": historical["gold_sha256"],
                    "historical_signature_sha256": historical[
                        "signature_sha256"
                    ],
                    "historical_invocation": historical["invocation"],
                    "historical_evidence": evidence,
                    "historical_notes": historical["notes"],
                    "fresh_reference_record": reference_relative,
                    "fresh_reference_record_sha256": reference_hashes[
                        historical["ontology"]
                    ],
                    "selected_registry_sha256": selected_registry_sha256,
                    "frozen_registry_sha256": frozen_registry_sha256,
                    "selected_summary_sha256": args.selected_summary_sha256,
                    "selected_result_manifest_sha256": (
                        selected_record_manifest_sha256
                    ),
                    "comparison_scope": "fresh_full_iri_taxonomy",
                }
            )

    if missing:
        raise SystemExit(f"missing frozen rows: {missing[:10]}")
    if len(output_rows) != EXPECTED_CLAIMS:
        raise SystemExit(
            f"joined {len(output_rows)} claims, expected {EXPECTED_CLAIMS}"
        )
    output_keys = [(row["ontology"], row["route"]) for row in output_rows]
    if len(set(output_keys)) != len(output_keys):
        raise SystemExit("joined alternative manifest repeats claim pairs")

    fieldnames = list(output_rows[0])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, delimiter="\t")
        writer.writeheader()
        writer.writerows(output_rows)
    receipt = {
        "schema_version": 1,
        "status": "source_bound_alternative_manifest",
        "claim_rows": len(output_rows),
        "generator": str(Path(__file__).resolve()),
        "generator_sha256": sha256_file(Path(__file__)),
        "selected_registry": str(args.selected_registry.resolve()),
        "selected_registry_sha256": selected_registry_sha256,
        "frozen_registry": str(args.frozen_registry.resolve()),
        "frozen_registry_sha256": frozen_registry_sha256,
        "selected_summary": str(args.selected_summary_json.resolve()),
        "selected_summary_sha256": args.selected_summary_sha256,
        "selected_result_manifest_sha256": selected_record_manifest_sha256,
        "current_binary_locator": current_binary_locator,
        "current_binary_sha256": args.current_binary_sha256,
        "current_source_manifest_sha256": args.current_source_manifest_sha256,
        "current_build_receipt_locator": current_build_receipt_locator,
        "current_build_receipt_sha256": args.current_build_receipt_sha256,
        "output": str(args.output.resolve()),
        "output_sha256": sha256_file(args.output),
    }
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(f"wrote {len(output_rows)} alternative claims to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
