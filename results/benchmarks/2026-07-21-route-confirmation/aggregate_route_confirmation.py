#!/usr/bin/env python3
"""Aggregate the fresh documented-route confirmation records."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path


CLAIMED = {"exact_gold", "adjudicated_correct_stale_gold"}


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


def record_manifest_sha256(
    rows: list[dict[str, str]], record_paths: dict[str, Path], root: Path
) -> tuple[int, str]:
    """Hash the exact result-record set consumed by this aggregation."""
    payload = bytearray()
    count = 0
    for row in rows:
        path = record_paths.get(row["ontology"])
        if path is None:
            continue
        relative = path.relative_to(root)
        payload.extend(f"{sha256_file(path)}  {relative}\n".encode("utf-8"))
        count += 1
    return count, hashlib.sha256(payload).hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--result-dir", type=Path, required=True)
    parser.add_argument("--summary-json", type=Path, required=True)
    parser.add_argument("--summary-tsv", type=Path, required=True)
    parser.add_argument("--expected-registry-sha256", required=True)
    parser.add_argument("--expected-registry-row-count", type=int, default=592)
    parser.add_argument(
        "--expected-validation-protocol",
        default="reproducible-current-selected-full-iri-v2",
    )
    parser.add_argument(
        "--expected-route-observation-policy",
        choices=("runtime-trace", "closed-manual-environment"),
        default="runtime-trace",
    )
    parser.add_argument("--expected-slurm-array-job-id", required=True)
    parser.add_argument("--expected-timeout", type=float, required=True)
    parser.add_argument("--expected-memcap-mb", type=int, required=True)
    parser.add_argument("--expected-binary-sha256", required=True)
    parser.add_argument("--expected-source-manifest-sha256", required=True)
    parser.add_argument("--expected-build-receipt-sha256", required=True)
    parser.add_argument("--expected-km-runtime-sha256", required=True)
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
    parser.add_argument("--expected-hermit-oracle-sha256", required=True)
    parser.add_argument("--expected-hermit-java-sha256", required=True)
    parser.add_argument("--expected-hermit-build-receipt-sha256", required=True)
    parser.add_argument("--expected-hermit-classpath-sha256", required=True)
    parser.add_argument("--expected-hermit-jdk-sha256", required=True)
    parser.add_argument("--expected-hermit-jdk-symlinks-sha256", required=True)
    parser.add_argument("--expected-hermit-runtime-sha256", required=True)
    parser.add_argument("--strict", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    with args.registry.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    if len(rows) != args.expected_registry_row_count:
        raise SystemExit(
            f"expected {args.expected_registry_row_count} registry rows, "
            f"found {len(rows)}"
        )
    ontology_names = [row["ontology"] for row in rows]
    if len(set(ontology_names)) != len(ontology_names):
        raise SystemExit("registry repeats ontology names")
    registry_sha = sha256_file(args.registry)
    if registry_sha != args.expected_registry_sha256:
        raise SystemExit(
            "registry hash mismatch: expected "
            f"{args.expected_registry_sha256}, observed {registry_sha}"
        )
    if args.expected_timeout <= 0 or args.expected_memcap_mb <= 0:
        raise SystemExit("expected KM limits must be positive")

    records = {}
    record_paths = {}
    missing = []
    for row in rows:
        path = args.result_dir / "results" / f"{row['ontology']}.json"
        if not path.is_file():
            missing.append(row["ontology"])
            continue
        records[row["ontology"]] = json.loads(path.read_text(encoding="utf-8"))
        record_paths[row["ontology"]] = path

    status_counts = Counter(
        record.get("confirmation_status", "missing_status")
        for record in records.values()
    )
    confirmed_by_route = Counter()
    failed_claims = []
    provenance_failures: dict[str, list[str]] = {}
    for row_index, row in enumerate(rows):
        record = records.get(row["ontology"])
        failures = []
        if record is not None:
            common_expected = {
                "registry": record.get("registry_sha256") == registry_sha,
                "protocol": record.get("validation_protocol")
                == args.expected_validation_protocol,
                "route_observation_policy": record.get(
                    "route_observation_policy"
                )
                == args.expected_route_observation_policy,
                "row_index": record.get("row_index") == row_index,
                "row_count": record.get("row_count") == len(rows),
                "ontology_name": record.get("ontology") == row["ontology"],
                "ontology_sha256": record.get("ontology_sha256")
                == row["ontology_sha256"],
                "expected_ontology_sha256": record.get(
                    "expected_ontology_sha256"
                )
                == row["ontology_sha256"],
                "slurm_array_job_id": str(
                    record.get("slurm_array_job_id", "")
                )
                == args.expected_slurm_array_job_id,
                "slurm_array_task_id": str(
                    record.get("slurm_array_task_id", "")
                )
                == str(row_index),
                "validator": record.get("validator_sha256")
                == args.expected_validator_sha256,
                "validation_driver": record.get("validation_driver_sha256")
                == args.expected_validation_driver_sha256
                and record.get("validation_driver_check") is True,
                "runner": record.get("runner_sha256")
                == args.expected_runner_sha256,
                "fingerprint_tool": record.get("fingerprint_tool_sha256")
                == args.expected_fingerprint_tool_sha256,
                "validator_environment": bool(
                    record.get("validator_environment_checks")
                )
                and all(record["validator_environment_checks"].values()),
            }
            failures.extend(
                name for name, passed in common_expected.items() if not passed
            )
            if row["state"] in CLAIMED:
                route_specification = record.get("route_specification")
                semantic_environment = (
                    route_specification.get("semantic_environment")
                    if isinstance(route_specification, dict)
                    else None
                )
                semantic_environment_sha256 = (
                    canonical_json_sha256(semantic_environment)
                    if isinstance(semantic_environment, dict)
                    else ""
                )
                expected_current_route_label = record.get(
                    "effective_route_request", ""
                )
                if expected_current_route_label == "manual":
                    expected_current_route_label = (
                        f"manual@sha256:{semantic_environment_sha256}"
                    )
                claimed_expected = {
                    "binary": record.get("actual_binary_sha256")
                    == args.expected_binary_sha256,
                    "source": record.get("executed_source_manifest_sha256")
                    == args.expected_source_manifest_sha256,
                    "receipt": record.get("executed_build_receipt_sha256")
                    == args.expected_build_receipt_sha256,
                    "km_runtime": (
                        (record.get("km_runtime") or {}).get(
                            "runtime_library_manifest_sha256"
                        )
                        == args.expected_km_runtime_sha256
                        and (record.get("km_runtime") or {}).get("ldd_sha256")
                        == args.expected_ldd_sha256
                        and bool(record.get("km_runtime_checks"))
                        and all(record["km_runtime_checks"].values())
                    ),
                    "route_specification": isinstance(route_specification, dict)
                    and record.get("route_specification_sha256")
                    == canonical_json_sha256(route_specification),
                    "semantic_environment": isinstance(
                        semantic_environment, dict
                    )
                    and record.get("semantic_environment_sha256")
                    == semantic_environment_sha256,
                    "current_route_label": record.get("current_route_label")
                    == expected_current_route_label,
                    "km_timeout": route_specification.get("timeout_s")
                    == args.expected_timeout,
                    "km_memory": route_specification.get("memory_limit_mb")
                    == args.expected_memcap_mb,
                    "km_ontology": route_specification.get("ontology_sha256")
                    == row["ontology_sha256"],
                    "km_run_timeout": (record.get("km_run") or {}).get(
                        "timeout_s"
                    )
                    == args.expected_timeout,
                    "km_run_memory": (record.get("km_run") or {}).get(
                        "memory_limit_mb"
                    )
                    == args.expected_memcap_mb,
                    "all_acceptance_checks": bool(record.get("checks"))
                    and all(record["checks"].values()),
                }
                if row["state"] == "exact_gold":
                    reference_specification = record.get(
                        "reference_route_specification"
                    )
                    claimed_expected.update(
                        {
                            "reference_ready": record.get("reference_ready")
                            is True,
                            "konclude_binary": record.get(
                                "reference_binary_sha256"
                            )
                            == args.expected_konclude_sha256,
                            "konclude_build_receipt": record.get(
                                "reference_build_receipt_sha256"
                            )
                            == args.expected_konclude_build_receipt_sha256,
                            "konclude_build_checks": bool(
                                record.get("reference_build_checks")
                            )
                            and all(record["reference_build_checks"].values()),
                            "konclude_runtime": (
                                record.get("reference_runtime") or {}
                            ).get("runtime_library_manifest_sha256")
                            == args.expected_konclude_runtime_sha256,
                            "konclude_ldd": (
                                record.get("reference_runtime") or {}
                            ).get("ldd_sha256")
                            == args.expected_ldd_sha256,
                            "reference_route_specification": isinstance(
                                reference_specification, dict
                            )
                            and record.get(
                                "reference_route_specification_sha256"
                            )
                            == canonical_json_sha256(reference_specification),
                            "reference_route_build_receipt": (
                                reference_specification or {}
                            ).get("build_receipt_sha256")
                            == args.expected_konclude_build_receipt_sha256,
                            "reference_route_source_manifest": (
                                reference_specification or {}
                            ).get("source_manifest_sha256")
                            == args.expected_konclude_source_manifest_sha256,
                            "reference_route_build_driver": (
                                reference_specification or {}
                            ).get("build_driver_sha256")
                            == args.expected_konclude_build_driver_sha256,
                        }
                    )
                else:
                    hermit_specification = record.get(
                        "hermit_route_specification"
                    )
                    claimed_expected.update(
                        {
                            "hermit_oracle": record.get(
                                "hermit_oracle_sha256"
                            )
                            == args.expected_hermit_oracle_sha256,
                            "hermit_java": record.get("hermit_java_sha256")
                            == args.expected_hermit_java_sha256,
                            "hermit_build_receipt": record.get(
                                "hermit_build_receipt_sha256"
                            )
                            == args.expected_hermit_build_receipt_sha256,
                            "hermit_classpath": record.get(
                                "hermit_classpath_manifest_sha256"
                            )
                            == args.expected_hermit_classpath_sha256,
                            "hermit_jdk": record.get(
                                "hermit_jdk_manifest_sha256"
                            )
                            == args.expected_hermit_jdk_sha256,
                            "hermit_jdk_symlinks": record.get(
                                "hermit_jdk_symlinks_sha256"
                            )
                            == args.expected_hermit_jdk_symlinks_sha256,
                            "hermit_runtime": record.get(
                                "hermit_runtime_stream_sha256"
                            )
                            == args.expected_hermit_runtime_sha256,
                            "hermit_ldd": (
                                record.get("hermit_runtime") or {}
                            ).get("ldd_sha256")
                            == args.expected_ldd_sha256,
                            "hermit_route_specification": isinstance(
                                hermit_specification, dict
                            )
                            and record.get(
                                "hermit_route_specification_sha256"
                            )
                            == canonical_json_sha256(hermit_specification),
                            "hermit_full_ontology": isinstance(
                                hermit_specification, dict
                            )
                            and hermit_specification.get("ontology_sha256")
                            == row["ontology_sha256"]
                            and record.get("hermit_ontology_sha256")
                            == row["ontology_sha256"]
                            and (record.get("hermit_run") or {}).get(
                                "ontology_sha256"
                            )
                            == row["ontology_sha256"],
                        }
                    )
                failures.extend(
                    name for name, passed in claimed_expected.items() if not passed
                )
        if failures:
            provenance_failures[row["ontology"]] = failures
        if row["state"] not in CLAIMED:
            continue
        if record and record.get("confirmed") is True and not failures:
            confirmed_by_route[record.get("current_route_label", "")] += 1
        else:
            failed_claims.append(row["ontology"])

    fieldnames = [
        "ontology",
        "documented_state",
        "documented_route",
        "current_route_label",
        "semantic_environment_sha256",
        "route_environment",
        "effective_route_request",
        "selected_route_trace",
        "route_observation_policy",
        "route_observation_kind",
        "observed_route_identity",
        "confirmation_status",
        "confirmed",
        "km_wall_s",
        "km_peak_mb",
        "reference_wall_s",
        "reference_peak_mb",
        "km_taxonomy_sha256",
        "reference_taxonomy_sha256",
        "binary_sha256",
        "source_manifest_sha256",
        "build_receipt_sha256",
        "km_runtime_manifest_sha256",
        "ldd_sha256",
        "ontology_sha256",
        "route_specification_sha256",
        "reference_route_specification_sha256",
        "reference_command_json",
        "reference_timeout_s",
        "reference_memory_limit_mb",
        "reference_runtime_manifest_sha256",
        "validator_sha256",
        "validation_driver_sha256",
        "runner_sha256",
        "fingerprint_tool_sha256",
        "slurm_array_job_id",
        "slurm_array_task_id",
    ]
    args.summary_tsv.parent.mkdir(parents=True, exist_ok=True)
    with args.summary_tsv.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, delimiter="\t")
        writer.writeheader()
        for row in rows:
            record = records.get(row["ontology"], {})
            km_run = record.get("km_run") or {}
            reference_run = record.get("reference_run") or record.get("hermit_run") or {}
            km_fingerprint = record.get("km_fingerprint") or {}
            reference_fingerprint = (
                record.get("reference_fingerprint")
                or record.get("hermit_fingerprint")
                or {}
            )
            writer.writerow(
                {
                    "ontology": row["ontology"],
                    "documented_state": row["state"],
                    "documented_route": row["route"],
                    "current_route_label": record.get(
                        "current_route_label", ""
                    ),
                    "semantic_environment_sha256": record.get(
                        "semantic_environment_sha256", ""
                    ),
                    "route_environment": row["route_environment"],
                    "effective_route_request": record.get(
                        "effective_route_request", ""
                    ),
                    "selected_route_trace": record.get(
                        "selected_route_trace", ""
                    ),
                    "route_observation_policy": record.get(
                        "route_observation_policy", ""
                    ),
                    "route_observation_kind": record.get(
                        "route_observation_kind", ""
                    ),
                    "observed_route_identity": record.get(
                        "observed_route_identity", ""
                    ),
                    "confirmation_status": record.get("confirmation_status", "missing"),
                    "confirmed": str(record.get("confirmed", False)).lower(),
                    "km_wall_s": km_run.get("wall_s", ""),
                    "km_peak_mb": km_run.get("peak_mb", ""),
                    "reference_wall_s": reference_run.get("wall_s", ""),
                    "reference_peak_mb": reference_run.get("peak_mb", ""),
                    "km_taxonomy_sha256": km_fingerprint.get("taxonomy_sha256", ""),
                    "reference_taxonomy_sha256": reference_fingerprint.get(
                        "taxonomy_sha256", ""
                    ),
                    "binary_sha256": record.get("actual_binary_sha256", ""),
                    "source_manifest_sha256": record.get(
                        "executed_source_manifest_sha256", ""
                    ),
                    "build_receipt_sha256": record.get(
                        "executed_build_receipt_sha256", ""
                    ),
                    "km_runtime_manifest_sha256": (
                        (record.get("km_runtime") or {}).get(
                            "runtime_library_manifest_sha256", ""
                        )
                    ),
                    "ldd_sha256": (record.get("km_runtime") or {}).get(
                        "ldd_sha256", ""
                    ),
                    "ontology_sha256": record.get("ontology_sha256", ""),
                    "route_specification_sha256": record.get(
                        "route_specification_sha256", ""
                    ),
                    "reference_route_specification_sha256": record.get(
                        "reference_route_specification_sha256",
                        record.get("hermit_route_specification_sha256", ""),
                    ),
                    "reference_command_json": json.dumps(
                        (
                            record.get("reference_route_specification")
                            or record.get("hermit_route_specification")
                            or {}
                        ).get("command", []),
                        separators=(",", ":"),
                    ),
                    "reference_timeout_s": (
                        record.get("reference_route_specification")
                        or record.get("hermit_route_specification")
                        or {}
                    ).get("timeout_s", ""),
                    "reference_memory_limit_mb": (
                        record.get("reference_route_specification")
                        or record.get("hermit_route_specification")
                        or {}
                    ).get("memory_limit_mb", ""),
                    "reference_runtime_manifest_sha256": (
                        (record.get("reference_runtime") or {}).get(
                            "runtime_library_manifest_sha256", ""
                        )
                        or (record.get("hermit_runtime") or {}).get(
                            "runtime_library_manifest_sha256", ""
                        )
                    ),
                    "validator_sha256": record.get("validator_sha256", ""),
                    "validation_driver_sha256": record.get(
                        "validation_driver_sha256", ""
                    ),
                    "runner_sha256": record.get("runner_sha256", ""),
                    "fingerprint_tool_sha256": record.get(
                        "fingerprint_tool_sha256", ""
                    ),
                    "slurm_array_job_id": record.get("slurm_array_job_id", ""),
                    "slurm_array_task_id": record.get("slurm_array_task_id", ""),
                }
            )

    exact_expected = sum(row["state"] == "exact_gold" for row in rows)
    adjudicated_expected = sum(
        row["state"] == "adjudicated_correct_stale_gold" for row in rows
    )
    exact_confirmed = status_counts["confirmed_exact_full_iri"]
    adjudicated_confirmed = status_counts["confirmed_adjudicated_inconsistent"]
    complete = not missing
    successful = (
        complete
        and exact_confirmed == exact_expected
        and adjudicated_confirmed == adjudicated_expected
        and not failed_claims
        and not provenance_failures
    )
    result_record_count, result_record_manifest_sha = record_manifest_sha256(
        rows, record_paths, args.result_dir
    )
    summary = {
        "schema_version": 1,
        "validation_protocol": "fresh-paired-full-iri-v2",
        "aggregator_sha256": sha256_file(Path(__file__)),
        "registry": str(args.registry),
        "registry_sha256": registry_sha,
        "registry_rows": len(rows),
        "expected_validation_protocol": args.expected_validation_protocol,
        "expected_route_observation_policy": (
            args.expected_route_observation_policy
        ),
        "result_records": len(records),
        "result_record_manifest_count": result_record_count,
        "result_record_manifest_sha256": result_record_manifest_sha,
        "missing_records": missing,
        "confirmation_status_counts": dict(sorted(status_counts.items())),
        "confirmed_by_route": dict(sorted(confirmed_by_route.items())),
        "failed_claims": failed_claims,
        "provenance_failures": provenance_failures,
        "expected_binary_sha256": args.expected_binary_sha256,
        "expected_slurm_array_job_id": args.expected_slurm_array_job_id,
        "expected_timeout": args.expected_timeout,
        "expected_memcap_mb": args.expected_memcap_mb,
        "expected_source_manifest_sha256": (
            args.expected_source_manifest_sha256
        ),
        "expected_build_receipt_sha256": args.expected_build_receipt_sha256,
        "expected_km_runtime_sha256": args.expected_km_runtime_sha256,
        "expected_ldd_sha256": args.expected_ldd_sha256,
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
        "expected_hermit_oracle_sha256": args.expected_hermit_oracle_sha256,
        "expected_hermit_java_sha256": args.expected_hermit_java_sha256,
        "expected_hermit_build_receipt_sha256": (
            args.expected_hermit_build_receipt_sha256
        ),
        "expected_hermit_classpath_sha256": (
            args.expected_hermit_classpath_sha256
        ),
        "expected_hermit_jdk_sha256": args.expected_hermit_jdk_sha256,
        "expected_hermit_jdk_symlinks_sha256": (
            args.expected_hermit_jdk_symlinks_sha256
        ),
        "expected_hermit_runtime_sha256": (
            args.expected_hermit_runtime_sha256
        ),
        "expected_exact_full_iri": exact_expected,
        "expected_adjudicated_inconsistent": adjudicated_expected,
        "confirmed_exact_full_iri": exact_confirmed,
        "confirmed_adjudicated_inconsistent": adjudicated_confirmed,
        "confirmed_total": exact_confirmed + adjudicated_confirmed,
        "successful": successful,
    }
    args.summary_json.parent.mkdir(parents=True, exist_ok=True)
    args.summary_json.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, sort_keys=True))
    return 1 if args.strict and not successful else 0


if __name__ == "__main__":
    raise SystemExit(main())
