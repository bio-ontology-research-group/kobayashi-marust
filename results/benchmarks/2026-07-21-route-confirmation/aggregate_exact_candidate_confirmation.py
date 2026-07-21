#!/usr/bin/env python3
"""Aggregate five route replays from three exact historical Git sources."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path


PROTOCOL = "reproducible-exact-candidate-selected-full-iri-v1"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json_sha256(value: object) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def complete_checks(value: object) -> bool:
    return isinstance(value, dict) and bool(value) and all(value.values())


def record_manifest(
    rows: list[dict[str, str]], paths: dict[str, Path], root: Path
) -> tuple[int, str]:
    payload = bytearray()
    count = 0
    for row in rows:
        path = paths.get(row["ontology"])
        if path is None:
            continue
        payload.extend(
            f"{sha256_file(path)}  {path.relative_to(root)}\n".encode("utf-8")
        )
        count += 1
    return count, hashlib.sha256(payload).hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--registry-sha256", required=True)
    parser.add_argument("--registry-receipt", type=Path, required=True)
    parser.add_argument("--registry-receipt-sha256", required=True)
    parser.add_argument("--registry-generator-sha256", required=True)
    parser.add_argument("--candidate-capsules", type=Path, required=True)
    parser.add_argument("--candidate-capsules-sha256", required=True)
    parser.add_argument("--candidate-capsules-receipt", type=Path, required=True)
    parser.add_argument("--candidate-capsules-receipt-sha256", required=True)
    parser.add_argument("--candidate-capsules-generator-sha256", required=True)
    parser.add_argument("--expected-source-verifier-sha256", required=True)
    parser.add_argument("--expected-runtime-driver-sha256", required=True)
    parser.add_argument("--result-dir", type=Path, required=True)
    parser.add_argument("--summary-json", type=Path, required=True)
    parser.add_argument("--summary-tsv", type=Path, required=True)
    parser.add_argument("--expected-selected-registry-sha256", required=True)
    parser.add_argument("--expected-slurm-array-job-id", required=True)
    parser.add_argument("--expected-timeout", type=float, required=True)
    parser.add_argument("--expected-memcap-mb", type=int, required=True)
    parser.add_argument("--expected-ldd-sha256", required=True)
    parser.add_argument("--expected-validator-sha256", required=True)
    parser.add_argument("--expected-validation-driver-sha256", required=True)
    parser.add_argument("--expected-runner-sha256", required=True)
    parser.add_argument("--expected-fingerprint-tool-sha256", required=True)
    parser.add_argument("--expected-konclude-sha256", required=True)
    parser.add_argument("--expected-konclude-runtime-sha256", required=True)
    parser.add_argument("--expected-konclude-build-receipt-sha256", required=True)
    parser.add_argument("--expected-konclude-source-manifest-sha256", required=True)
    parser.add_argument("--expected-konclude-build-driver-sha256", required=True)
    parser.add_argument("--strict", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.expected_timeout <= 0 or args.expected_memcap_mb <= 0:
        raise SystemExit("expected limits must be positive")
    if sha256_file(args.registry) != args.registry_sha256:
        raise SystemExit("replay registry differs from its pinned hash")
    if sha256_file(args.registry_receipt) != args.registry_receipt_sha256:
        raise SystemExit("replay registry receipt differs from its pinned hash")
    if sha256_file(args.candidate_capsules) != args.candidate_capsules_sha256:
        raise SystemExit("candidate capsule registry differs from its pinned hash")
    if (
        sha256_file(args.candidate_capsules_receipt)
        != args.candidate_capsules_receipt_sha256
    ):
        raise SystemExit("candidate capsule receipt differs from its pinned hash")

    rows = read_tsv(args.registry)
    if len(rows) != 5 or len({row["ontology"] for row in rows}) != 5:
        raise SystemExit("replay registry must contain five unique ontologies")
    candidates = read_tsv(args.candidate_capsules)
    if len(candidates) != 3:
        raise SystemExit("candidate capsule registry must contain three rows")
    by_candidate = {row["candidate"]: row for row in candidates}
    if len(by_candidate) != len(candidates):
        raise SystemExit("candidate capsule registry repeats labels")
    if any(row["rebuild_candidate"] not in by_candidate for row in rows):
        raise SystemExit("replay registry names an unknown candidate")

    candidate_receipt = read_json(args.candidate_capsules_receipt)
    candidate_receipt_expected = {
        "status": "source_bound_exact_candidate_capsules_with_runtime",
        "rows": 3,
        "generator_sha256": args.candidate_capsules_generator_sha256,
        "output_sha256": args.candidate_capsules_sha256,
        "expected_source_verifier_sha256": (
            args.expected_source_verifier_sha256
        ),
        "expected_runtime_driver_sha256": args.expected_runtime_driver_sha256,
        "expected_ldd_sha256": args.expected_ldd_sha256,
    }
    candidate_receipt_failures = [
        key
        for key, value in candidate_receipt_expected.items()
        if candidate_receipt.get(key) != value
    ]
    candidate_checks = candidate_receipt.get("checks") or {}
    if (
        candidate_receipt_failures
        or set(candidate_checks) != set(by_candidate)
        or any(not complete_checks(value) for value in candidate_checks.values())
    ):
        raise SystemExit(
            "candidate capsule receipt failed: "
            f"{candidate_receipt_failures}"
        )

    registry_receipt = read_json(args.registry_receipt)
    registry_receipt_expected = {
        "status": "source_bound_exact_candidate_replay_registry",
        "rows": 5,
        "generator_sha256": args.registry_generator_sha256,
        "selected_registry_sha256": args.expected_selected_registry_sha256,
        "candidate_capsules_sha256": args.candidate_capsules_sha256,
        "output_sha256": args.registry_sha256,
    }
    registry_receipt_failures = [
        key
        for key, value in registry_receipt_expected.items()
        if registry_receipt.get(key) != value
    ]
    if registry_receipt_failures or any(
        not complete_checks(value)
        for value in (registry_receipt.get("candidate_checks") or {}).values()
    ):
        raise SystemExit(
            f"replay registry receipt failed: {registry_receipt_failures}"
        )

    records = {}
    paths = {}
    missing = []
    for row in rows:
        path = args.result_dir / "results" / f"{row['ontology']}.json"
        if not path.is_file():
            missing.append(row["ontology"])
            continue
        records[row["ontology"]] = read_json(path)
        paths[row["ontology"]] = path

    failures_by_ontology: dict[str, list[str]] = {}
    for row_index, row in enumerate(rows):
        record = records.get(row["ontology"])
        if record is None:
            continue
        candidate = by_candidate[row["rebuild_candidate"]]
        run = record.get("km_run") or {}
        run_launcher = run.get("launcher") or {}
        route_spec = record.get("route_specification")
        reference_spec = record.get("reference_route_specification")
        km_fingerprint = record.get("km_fingerprint") or {}
        reference_fingerprint = record.get("reference_fingerprint") or {}
        expected_command = [
            candidate["binary"],
            "classify",
            run.get("ontology", ""),
        ]
        expected = {
            "protocol": record.get("validation_protocol") == PROTOCOL,
            "registry": record.get("registry_sha256") == args.registry_sha256,
            "row_index": record.get("row_index") == row_index,
            "row_count": record.get("row_count") == len(rows),
            "ontology": record.get("ontology") == row["ontology"],
            "ontology_sha256": record.get("ontology_sha256")
            == record.get("expected_ontology_sha256")
            == row["ontology_sha256"],
            "documented_state": record.get("documented_state") == "exact_gold",
            "documented_route": record.get("documented_route")
            == "production_all",
            "documented_binary": record.get("documented_binary_sha256")
            == candidate["binary_sha256"],
            "documented_source": record.get("documented_source_revision")
            == f"git:{candidate['commit']}",
            "binary": record.get("actual_binary_sha256")
            == candidate["binary_sha256"],
            "source": record.get("executed_source_manifest_sha256")
            == candidate["source_manifest_sha256"],
            "build_receipt": record.get("executed_build_receipt_sha256")
            == candidate["build_receipt_sha256"],
            "runtime": (record.get("km_runtime") or {}).get(
                "runtime_library_manifest_sha256"
            )
            == candidate["runtime_manifest_sha256"],
            "runtime_count": (record.get("km_runtime") or {}).get(
                "runtime_library_count"
            )
            == int(candidate["runtime_library_count"]),
            "runtime_ldd": (record.get("km_runtime") or {}).get("ldd_sha256")
            == args.expected_ldd_sha256,
            "runtime_checks": complete_checks(record.get("km_runtime_checks")),
            "validator": record.get("validator_sha256")
            == args.expected_validator_sha256,
            "validation_driver": record.get("validation_driver_sha256")
            == args.expected_validation_driver_sha256
            and record.get("validation_driver_check") is True,
            "runner": record.get("runner_sha256")
            == args.expected_runner_sha256,
            "fingerprint_tool": record.get("fingerprint_tool_sha256")
            == args.expected_fingerprint_tool_sha256,
            "validator_environment": complete_checks(
                record.get("validator_environment_checks")
            ),
            "slurm_array_job": str(record.get("slurm_array_job_id", ""))
            == args.expected_slurm_array_job_id,
            "slurm_array_task": str(record.get("slurm_array_task_id", ""))
            == str(row_index),
            "route_policy": record.get("route_observation_policy")
            == "runtime-trace",
            "route_kind": record.get("route_observation_kind")
            == "runtime_trace",
            "route_request": record.get("effective_route_request")
            == "production_all",
            "route_label": record.get("current_route_label")
            == "production_all",
            "route_trace": record.get("selected_route_trace_count") == 1
            and record.get("selected_route_trace") == "production_all"
            and record.get("selected_route_traces") == ["production_all"],
            "route_identity": record.get("observed_route_identity")
            == "production_all",
            "semantic_environment": record.get("parsed_environment")
            == ["KM_ROUTE=production_all"],
            "executed_environment": record.get("executed_environment")
            == ["KM_ROUTE=production_all", "KM_TIMING=1"],
            "route_specification": isinstance(route_spec, dict)
            and record.get("route_specification_sha256")
            == canonical_json_sha256(route_spec),
            "route_spec_binary": (route_spec or {}).get("binary_sha256")
            == candidate["binary_sha256"],
            "route_spec_source": (route_spec or {}).get(
                "source_manifest_sha256"
            )
            == candidate["source_manifest_sha256"],
            "route_spec_build": (route_spec or {}).get("build_receipt_sha256")
            == candidate["build_receipt_sha256"],
            "route_spec_runtime": (route_spec or {}).get(
                "runtime_library_manifest_sha256"
            )
            == candidate["runtime_manifest_sha256"],
            "route_spec_environment": (route_spec or {}).get(
                "semantic_environment"
            )
            == {"KM_ROUTE": "production_all"},
            "route_spec_instrumentation": (route_spec or {}).get(
                "instrumentation_environment"
            )
            == {"KM_TIMING": "1"},
            "route_spec_limits": (route_spec or {}).get("timeout_s")
            == args.expected_timeout
            and (route_spec or {}).get("memory_limit_mb")
            == args.expected_memcap_mb
            and (route_spec or {}).get("cpus") == 16,
            "run_status": run.get("status") == "ok"
            and run.get("return_code") == 0,
            "run_binary": run.get("binary_sha256")
            == candidate["binary_sha256"],
            "run_ontology": run.get("ontology_sha256")
            == row["ontology_sha256"],
            "run_command": run.get("command") == expected_command
            and run.get("command") == (route_spec or {}).get("command"),
            "run_environment": run.get("environment")
            == {"KM_ROUTE": "production_all", "KM_TIMING": "1"},
            "run_limits": run.get("timeout_s") == args.expected_timeout
            and run.get("memory_limit_mb") == args.expected_memcap_mb
            and run.get("cpus") == 16,
            "run_launcher": run_launcher.get("status") == "verified"
            and complete_checks(run_launcher.get("checks"))
            and run_launcher.get("wrapper_sha256")
            == args.expected_runner_sha256
            and run_launcher.get("working_directory") == "/",
            "reference_ready": record.get("reference_ready") is True,
            "reference_binary": record.get("reference_binary_sha256")
            == args.expected_konclude_sha256,
            "reference_build": record.get("reference_build_receipt_sha256")
            == args.expected_konclude_build_receipt_sha256
            and complete_checks(record.get("reference_build_checks")),
            "reference_runtime": (record.get("reference_runtime") or {}).get(
                "runtime_library_manifest_sha256"
            )
            == args.expected_konclude_runtime_sha256
            and (record.get("reference_runtime") or {}).get("ldd_sha256")
            == args.expected_ldd_sha256
            and complete_checks(record.get("reference_runtime_checks")),
            "reference_specification": isinstance(reference_spec, dict)
            and record.get("reference_route_specification_sha256")
            == canonical_json_sha256(reference_spec),
            "reference_build_identity": (reference_spec or {}).get(
                "build_receipt_sha256"
            )
            == args.expected_konclude_build_receipt_sha256
            and (reference_spec or {}).get("source_manifest_sha256")
            == args.expected_konclude_source_manifest_sha256
            and (reference_spec or {}).get("build_driver_sha256")
            == args.expected_konclude_build_driver_sha256,
            "fingerprints": km_fingerprint.get("status") == "ok"
            and reference_fingerprint.get("status") == "ok"
            and km_fingerprint.get("source_ontology_sha256")
            == reference_fingerprint.get("source_ontology_sha256")
            == row["ontology_sha256"]
            and km_fingerprint.get("taxonomy_sha256")
            == reference_fingerprint.get("taxonomy_sha256"),
            "acceptance_checks": complete_checks(record.get("checks")),
            "confirmation": record.get("confirmation_status")
            == "confirmed_exact_full_iri"
            and record.get("confirmed") is True
            and record.get("phase") == "complete",
        }
        failures = [key for key, value in expected.items() if not value]
        if failures:
            failures_by_ontology[row["ontology"]] = failures

    status_counts = Counter(
        record.get("confirmation_status", "missing")
        for record in records.values()
    )
    record_count, record_manifest_sha = record_manifest(rows, paths, args.result_dir)
    successful = (
        not missing
        and len(records) == 5
        and status_counts["confirmed_exact_full_iri"] == 5
        and not failures_by_ontology
    )
    summary = {
        "schema_version": 1,
        "status": "verified_exact_candidate_replays" if successful else "failed",
        "validation_protocol": PROTOCOL,
        "aggregator_sha256": sha256_file(Path(__file__)),
        "registry_sha256": args.registry_sha256,
        "registry_receipt_sha256": args.registry_receipt_sha256,
        "registry_rows": len(rows),
        "candidate_capsules_sha256": args.candidate_capsules_sha256,
        "candidate_capsules_receipt_sha256": (
            args.candidate_capsules_receipt_sha256
        ),
        "candidate_binary_sha256": {
            label: row["binary_sha256"] for label, row in by_candidate.items()
        },
        "candidate_source_manifest_sha256": {
            label: row["source_manifest_sha256"]
            for label, row in by_candidate.items()
        },
        "candidate_build_receipt_sha256": {
            label: row["build_receipt_sha256"]
            for label, row in by_candidate.items()
        },
        "candidate_test_receipt_sha256": {
            label: row["test_receipt_sha256"]
            for label, row in by_candidate.items()
        },
        "candidate_source_identity_sha256": {
            label: row["source_identity_sha256"]
            for label, row in by_candidate.items()
        },
        "candidate_runtime_manifest_sha256": {
            label: row["runtime_manifest_sha256"]
            for label, row in by_candidate.items()
        },
        "result_records": len(records),
        "result_record_manifest_count": record_count,
        "result_record_manifest_sha256": record_manifest_sha,
        "missing_records": missing,
        "confirmation_status_counts": dict(sorted(status_counts.items())),
        "confirmed_exact_full_iri": status_counts["confirmed_exact_full_iri"],
        "provenance_failures": failures_by_ontology,
        "expected_selected_registry_sha256": (
            args.expected_selected_registry_sha256
        ),
        "expected_slurm_array_job_id": args.expected_slurm_array_job_id,
        "expected_timeout": args.expected_timeout,
        "expected_memcap_mb": args.expected_memcap_mb,
        "expected_ldd_sha256": args.expected_ldd_sha256,
        "expected_source_verifier_sha256": (
            args.expected_source_verifier_sha256
        ),
        "expected_runtime_driver_sha256": args.expected_runtime_driver_sha256,
        "expected_validator_sha256": args.expected_validator_sha256,
        "expected_validation_driver_sha256": (
            args.expected_validation_driver_sha256
        ),
        "expected_runner_sha256": args.expected_runner_sha256,
        "expected_fingerprint_tool_sha256": (
            args.expected_fingerprint_tool_sha256
        ),
        "expected_konclude_sha256": args.expected_konclude_sha256,
        "expected_konclude_runtime_sha256": (
            args.expected_konclude_runtime_sha256
        ),
        "expected_konclude_build_receipt_sha256": (
            args.expected_konclude_build_receipt_sha256
        ),
        "expected_konclude_source_manifest_sha256": (
            args.expected_konclude_source_manifest_sha256
        ),
        "expected_konclude_build_driver_sha256": (
            args.expected_konclude_build_driver_sha256
        ),
        "successful": successful,
    }
    args.summary_json.parent.mkdir(parents=True, exist_ok=True)
    args.summary_json.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    fields = [
        "ontology",
        "candidate",
        "commit",
        "route",
        "confirmation_status",
        "confirmed",
        "wall_s",
        "peak_mb",
        "binary_sha256",
        "source_manifest_sha256",
        "build_receipt_sha256",
        "test_receipt_sha256",
        "source_identity_sha256",
        "runtime_manifest_sha256",
        "route_specification_sha256",
        "taxonomy_sha256",
        "reference_taxonomy_sha256",
        "record_sha256",
        "slurm_array_task_id",
    ]
    with args.summary_tsv.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        for row in rows:
            record = records.get(row["ontology"], {})
            candidate = by_candidate[row["rebuild_candidate"]]
            run = record.get("km_run") or {}
            writer.writerow(
                {
                    "ontology": row["ontology"],
                    "candidate": row["rebuild_candidate"],
                    "commit": candidate["commit"],
                    "route": row["route"],
                    "confirmation_status": record.get(
                        "confirmation_status", "missing"
                    ),
                    "confirmed": str(record.get("confirmed", False)).lower(),
                    "wall_s": run.get("wall_s", ""),
                    "peak_mb": run.get("peak_mb", ""),
                    "binary_sha256": candidate["binary_sha256"],
                    "source_manifest_sha256": candidate[
                        "source_manifest_sha256"
                    ],
                    "build_receipt_sha256": candidate[
                        "build_receipt_sha256"
                    ],
                    "test_receipt_sha256": candidate["test_receipt_sha256"],
                    "source_identity_sha256": candidate[
                        "source_identity_sha256"
                    ],
                    "runtime_manifest_sha256": candidate[
                        "runtime_manifest_sha256"
                    ],
                    "route_specification_sha256": record.get(
                        "route_specification_sha256", ""
                    ),
                    "taxonomy_sha256": (record.get("km_fingerprint") or {}).get(
                        "taxonomy_sha256", ""
                    ),
                    "reference_taxonomy_sha256": (
                        record.get("reference_fingerprint") or {}
                    ).get("taxonomy_sha256", ""),
                    "record_sha256": (
                        sha256_file(paths[row["ontology"]])
                        if row["ontology"] in paths
                        else ""
                    ),
                    "slurm_array_task_id": record.get(
                        "slurm_array_task_id", ""
                    ),
                }
            )
    print(json.dumps(summary, sort_keys=True))
    return 1 if args.strict and not successful else 0


if __name__ == "__main__":
    raise SystemExit(main())
