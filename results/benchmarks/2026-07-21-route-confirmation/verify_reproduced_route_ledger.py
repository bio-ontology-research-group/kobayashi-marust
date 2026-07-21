#!/usr/bin/env python3
"""Verify the committed ORE route ledger and its external receipt."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
import re


EXPECTED_STATES = {
    "not_a_documented_solve_claim": 3,
    "reproduced_adjudicated_inconsistent": 2,
    "reproduced_exact_full_iri": 579,
    "reproduced_exact_source_candidate_full_iri": 3,
    "reproduced_exact_source_historical_full_iri": 5,
}
EXPECTED_ORIGINS = {
    "current_alternative_route": 3,
    "current_selected_route": 578,
    "exact_source_candidate_route": 3,
    "exact_source_historical_route": 5,
    "none": 3,
}
EXPECTED_NONCLAIMS = {
    "ore_ont_10860.owl",
    "ore_ont_1194.owl",
    "ore_ont_4669.owl",
}
HASH_FIELDS = (
    "ontology_sha256",
    "binary_sha256",
    "source_manifest_sha256",
    "build_receipt_sha256",
    "source_archive_sha256",
    "cargo_lock_sha256",
    "build_input_archive_sha256",
    "build_input_manifest_sha256",
    "rustc_sha256",
    "cargo_sha256",
    "rustup_sha256",
    "build_driver_sha256",
    "km_runtime_manifest_sha256",
    "ldd_sha256",
    "route_specification_sha256",
    "validator_sha256",
    "validation_driver_sha256",
    "runner_sha256",
    "fingerprint_tool_sha256",
    "km_taxonomy_sha256",
    "reference_taxonomy_sha256",
    "reference_binary_sha256",
    "reference_source_sha256",
    "reference_route_specification_sha256",
    "reference_runtime_manifest_sha256",
    "evidence_sha256",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ledger", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--expected-ledger-sha256", required=True)
    parser.add_argument("--expected-receipt-sha256", required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    require(
        sha256(args.ledger) == args.expected_ledger_sha256,
        "ledger SHA-256 does not match the external expected value",
    )
    require(
        sha256(args.receipt) == args.expected_receipt_sha256,
        "receipt SHA-256 does not match the external expected value",
    )

    receipt = json.loads(args.receipt.read_text(encoding="utf-8"))
    require(
        receipt.get("status") == "verified_complete_reproduced_route_ledger",
        "receipt status is not verified",
    )
    require(
        receipt.get("ledger_sha256") == args.expected_ledger_sha256,
        "receipt does not bind the expected ledger",
    )
    require(
        bool(receipt.get("checks"))
        and all(receipt["checks"].values()),
        "one or more IBEX receipt checks failed",
    )

    with args.ledger.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    states = Counter(row["current_state"] for row in rows)
    origins = Counter(row["chosen_origin"] or "none" for row in rows)
    nonclaims = {
        row["ontology"]
        for row in rows
        if row["current_state"] == "not_a_documented_solve_claim"
    }
    reproduced = [
        row for row in rows if row["current_state"].startswith("reproduced_")
    ]

    require(len(rows) == 592, "ledger does not contain 592 rows")
    require(
        len({row["ontology"] for row in rows}) == 592,
        "ledger ontology identifiers are not unique",
    )
    require(dict(states) == EXPECTED_STATES, "unexpected state counts")
    require(dict(origins) == EXPECTED_ORIGINS, "unexpected origin counts")
    require(nonclaims == EXPECTED_NONCLAIMS, "unexpected nonclaim set")
    require(len(reproduced) == 589, "expected 589 reproduced claims")
    require(receipt.get("states") == EXPECTED_STATES, "receipt state mismatch")
    require(
        receipt.get("chosen_origins") == EXPECTED_ORIGINS,
        "receipt origin mismatch",
    )

    failures: dict[str, list[str]] = {}
    for row in reproduced:
        row_errors = []
        for field in HASH_FIELDS:
            if re.fullmatch(r"[0-9a-f]{64}", row.get(field, "")) is None:
                row_errors.append(field)
        if re.fullmatch(
            r"sha256:[0-9a-f]{64}", row.get("container_image_digest", "")
        ) is None:
            row_errors.append("container_image_digest")
        for field in (
            "rustc_version",
            "rustc_path",
            "cargo_version",
            "cargo_path",
            "rustup_path",
        ):
            if not row.get(field):
                row_errors.append(field)
        try:
            command = json.loads(row["command_json"])
            reference_command = json.loads(row["reference_command_json"])
        except (KeyError, json.JSONDecodeError):
            command = reference_command = []
        if not isinstance(command, list) or len(command) < 3:
            row_errors.append("command_json")
        if not isinstance(reference_command, list) or not reference_command:
            row_errors.append("reference_command_json")
        policy = row.get("route_observation_policy")
        identity = row.get("observed_route_identity", "")
        if policy == "runtime-trace":
            if not identity or identity != row.get("selected_route_trace"):
                row_errors.append("runtime_route_identity")
            if identity != row.get("requested_route"):
                row_errors.append("requested_route_identity")
        elif policy == "closed-manual-environment":
            if not identity.startswith("manual@sha256:"):
                row_errors.append("manual_route_identity")
        else:
            row_errors.append("route_observation_policy")
        if row.get("reference_kind") not in {
            "konclude_full_ontology",
            "hermit_full_ontology",
        }:
            row_errors.append("reference_kind")
        if not row.get("evidence_locator", "").startswith("ibex:"):
            row_errors.append("evidence_locator")
        try:
            if float(row["timeout_s"]) != 240.0:
                row_errors.append("timeout_s")
            if int(row["memory_limit_mb"]) != 20480:
                row_errors.append("memory_limit_mb")
            if int(row["cpus"]) != 16:
                row_errors.append("cpus")
            if float(row["reference_timeout_s"]) != 240.0:
                row_errors.append("reference_timeout_s")
            if int(row["reference_memory_limit_mb"]) != 20480:
                row_errors.append("reference_memory_limit_mb")
        except (KeyError, TypeError, ValueError):
            row_errors.append("limits")
        if row["chosen_origin"] in {
            "exact_source_candidate_route",
            "exact_source_historical_route",
        }:
            if not row.get("source_revision", "").startswith("git:"):
                row_errors.append("source_revision")
            for field in (
                "source_identity_receipt_sha256",
                "test_receipt_sha256",
            ):
                if re.fullmatch(r"[0-9a-f]{64}", row.get(field, "")) is None:
                    row_errors.append(field)
        if row_errors:
            failures[row["ontology"]] = sorted(set(row_errors))
    require(not failures, f"reproduced-row failures: {failures}")

    print(
        json.dumps(
            {
                "ledger_sha256": args.expected_ledger_sha256,
                "nonclaims": sorted(nonclaims),
                "origins": dict(origins),
                "reproduced_claims": len(reproduced),
                "rows": len(rows),
                "states": dict(states),
                "status": "verified",
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
