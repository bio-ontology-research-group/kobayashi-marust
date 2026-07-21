#!/usr/bin/env python3
"""Create source-bound replay rows for the retained 0d20dd1 routes."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import tempfile


TARGETS = {
    "ore_ont_2669.owl": "ht_rules",
    "ore_ont_6934.owl": "htforce_race",
    "ore_ont_7499.owl": "card_race",
    "ore_ont_9540.owl": "card_race",
    "ore_ont_9635.owl": "legacy_tab_race",
    "ore_ont_10702.owl": "nomlink_default",
    "ore_ont_10908.owl": "shoq_race",
    "ore_ont_15516.owl": "ht_rules",
    "ore_ont_15672.owl": "shoq_race",
}
ADJUDICATED = {"ore_ont_2669.owl", "ore_ont_15516.owl"}
COMMIT = "0d20dd13312c16dec4ff256852979fb4c927556a"
HISTORICAL_BINARY = (
    "dce27171c9d9d2753c55672266289ccec3e8ab74f7f47d75b20f8375e0c84aee"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selected-registry", type=Path, required=True)
    parser.add_argument("--selected-registry-sha256", required=True)
    parser.add_argument("--capsule-root", type=Path, required=True)
    parser.add_argument("--binary-sha256", required=True)
    parser.add_argument("--source-manifest-sha256", required=True)
    parser.add_argument("--build-receipt-sha256", required=True)
    parser.add_argument("--test-receipt-sha256", required=True)
    parser.add_argument("--source-identity", type=Path, required=True)
    parser.add_argument("--source-identity-sha256", required=True)
    parser.add_argument("--runtime-summary", type=Path, required=True)
    parser.add_argument("--runtime-summary-sha256", required=True)
    parser.add_argument("--runtime-manifest-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    return parser.parse_args()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def runtime_fields(path: Path) -> dict[str, str]:
    rows = read_tsv(path)
    return {row["field"]: row["value"] for row in rows}


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=path.parent,
        prefix=path.name + ".tmp.",
        delete=False,
    ) as handle:
        temporary = Path(handle.name)
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, path)


def main() -> int:
    args = parse_args()
    if sha256_file(args.selected_registry) != args.selected_registry_sha256:
        raise SystemExit("selected registry differs from its pinned SHA-256")
    selected = read_tsv(args.selected_registry)
    if len(selected) != 592:
        raise SystemExit(f"selected registry has {len(selected)} rows, expected 592")
    by_ontology = {row["ontology"]: row for row in selected}
    if len(by_ontology) != len(selected):
        raise SystemExit("selected registry repeats ontology names")

    capsule = args.capsule_root.resolve()
    binary = capsule / "capsule" / "km-build-a"
    peer = capsule / "capsule" / "km-build-b"
    build_receipt_path = capsule / "capsule" / "build-receipt.json"
    test_receipt_path = capsule / "tests" / "test-receipt.json"
    observed = {
        "binary": sha256_file(binary),
        "peer": sha256_file(peer),
        "build_receipt": sha256_file(build_receipt_path),
        "test_receipt": sha256_file(test_receipt_path),
        "source_identity": sha256_file(args.source_identity),
        "runtime_summary": sha256_file(args.runtime_summary),
    }
    expected = {
        "binary": args.binary_sha256,
        "peer": args.binary_sha256,
        "build_receipt": args.build_receipt_sha256,
        "test_receipt": args.test_receipt_sha256,
        "source_identity": args.source_identity_sha256,
        "runtime_summary": args.runtime_summary_sha256,
    }
    if observed != expected:
        raise SystemExit(
            "rebuild artifact mismatch: "
            f"{[key for key in expected if observed[key] != expected[key]]}"
        )
    if binary.read_bytes() != peer.read_bytes():
        raise SystemExit("the two rebuilt executables are not byte-identical")

    build_receipt = load_json(build_receipt_path)
    test_receipt = load_json(test_receipt_path)
    source_identity = load_json(args.source_identity)
    runtime = runtime_fields(args.runtime_summary)
    receipt_checks = {
        "build_verified": build_receipt.get("status")
        == "verified_reproducible",
        "builds_identical": build_receipt.get("outputs", {}).get(
            "byte_identical"
        )
        is True,
        "build_binary": build_receipt.get("outputs", {}).get("binary_sha256")
        == args.binary_sha256,
        "build_source": build_receipt.get("source", {}).get("manifest_sha256")
        == args.source_manifest_sha256,
        "tests_verified": test_receipt.get("status") == "verified_full_tests",
        "tests_passed": test_receipt.get("passed") == 1390
        and test_receipt.get("failed") == 0,
        "tests_bind_build": test_receipt.get("capsule_build_receipt_sha256")
        == args.build_receipt_sha256,
        "source_exact": source_identity.get("status")
        == "verified_exact_git_source",
        "source_commit": source_identity.get("commit") == COMMIT,
        "source_manifest": source_identity.get("source_manifest_sha256")
        == args.source_manifest_sha256,
        "runtime_captured": runtime.get("status")
        == "captured_for_later_independent_recheck",
        "runtime_binary": runtime.get("binary_sha256") == args.binary_sha256,
        "runtime_source": runtime.get("source_manifest_sha256")
        == args.source_manifest_sha256,
        "runtime_manifest": runtime.get("runtime_library_manifest_sha256")
        == args.runtime_manifest_sha256,
    }
    if not all(receipt_checks.values()):
        raise SystemExit(
            "rebuild receipt checks failed: "
            f"{[key for key, passed in receipt_checks.items() if not passed]}"
        )

    output_rows = []
    extra_fields = [
        "historical_binary_sha256",
        "historical_binary_locator",
        "historical_source_revision",
        "historical_route_environment",
        "historical_invocation",
        "rebuild_source_commit",
        "rebuild_source_manifest_sha256",
        "rebuild_build_receipt_sha256",
        "rebuild_test_receipt_sha256",
        "rebuild_source_identity_sha256",
        "rebuild_runtime_manifest_sha256",
        "selected_registry_sha256",
    ]
    for ontology, route in TARGETS.items():
        if ontology not in by_ontology:
            raise SystemExit(f"selected registry lacks {ontology}")
        original = by_ontology[ontology]
        expected_state = (
            "adjudicated_correct_stale_gold"
            if ontology in ADJUDICATED
            else "exact_gold"
        )
        if (
            original["state"] != expected_state
            or original["route"] != route
            or original["binary_sha256"] != HISTORICAL_BINARY
            or original["source_revision"] != "git:0d20dd1"
        ):
            raise SystemExit(f"historical route identity changed for {ontology}")
        route_environment = original["route_environment"]
        if not any(
            value.startswith("KM_ROUTE=")
            for value in route_environment.split()
        ):
            route_environment = f"KM_ROUTE=manual {route_environment}"
        row = dict(original)
        row.update(
            binary_sha256=args.binary_sha256,
            binary_locator=f"ibex:{binary}",
            source_revision=f"git:{COMMIT}",
            route_environment=route_environment,
            invocation=(
                f"env {route_environment} $KM_BIN classify "
                f"$ORE_CORPUS/{ontology}"
            ),
            evidence=(
                f"{original['evidence']} -> source-built replay; "
                f"build_receipt_sha256={args.build_receipt_sha256}; "
                f"source_identity_sha256={args.source_identity_sha256}"
            ),
            notes=(
                f"{original['notes']} Historical executable {HISTORICAL_BINARY} "
                "is provenance only and is not executed. Replay uses two "
                f"byte-identical builds from exact commit {COMMIT}."
            ),
            historical_binary_sha256=original["binary_sha256"],
            historical_binary_locator=original["binary_locator"],
            historical_source_revision=original["source_revision"],
            historical_route_environment=original["route_environment"],
            historical_invocation=original["invocation"],
            rebuild_source_commit=COMMIT,
            rebuild_source_manifest_sha256=args.source_manifest_sha256,
            rebuild_build_receipt_sha256=args.build_receipt_sha256,
            rebuild_test_receipt_sha256=args.test_receipt_sha256,
            rebuild_source_identity_sha256=args.source_identity_sha256,
            rebuild_runtime_manifest_sha256=args.runtime_manifest_sha256,
            selected_registry_sha256=args.selected_registry_sha256,
        )
        output_rows.append(row)

    fieldnames = list(selected[0]) + extra_fields
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, delimiter="\t")
        writer.writeheader()
        writer.writerows(output_rows)
    receipt = {
        "schema_version": 1,
        "status": "source_bound_rebuilt_historical_registry",
        "rows": len(output_rows),
        "ontologies": list(TARGETS),
        "routes": TARGETS,
        "generator_sha256": sha256_file(Path(__file__)),
        "selected_registry_sha256": args.selected_registry_sha256,
        "binary_sha256": args.binary_sha256,
        "source_commit": COMMIT,
        "source_manifest_sha256": args.source_manifest_sha256,
        "build_receipt_sha256": args.build_receipt_sha256,
        "test_receipt_sha256": args.test_receipt_sha256,
        "source_identity_sha256": args.source_identity_sha256,
        "runtime_summary_sha256": args.runtime_summary_sha256,
        "runtime_manifest_sha256": args.runtime_manifest_sha256,
        "output_sha256": sha256_file(args.output),
        "checks": receipt_checks,
    }
    atomic_json(args.receipt, receipt)
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
