#!/usr/bin/env python3
"""Aggregate the 10,755 current alternative-route validation records.

Campaign completeness and route confirmation are deliberately separate.  A
provenance-valid terminal timeout, unsupported route or full-IRI mismatch is a
complete negative experiment, but it is never a confirmed solve route.
"""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path


EXPECTED = 10_755


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
    rows: list[dict[str, str]], record_paths: dict[int, Path], root: Path
) -> tuple[int, str]:
    """Hash the exact alternative-result set consumed by this aggregation."""
    payload = bytearray()
    count = 0
    for row in rows:
        index = int(row["task_index"])
        path = record_paths.get(index)
        if path is None:
            continue
        relative = path.relative_to(root)
        payload.extend(f"{sha256_file(path)}  {relative}\n".encode("utf-8"))
        count += 1
    return count, hashlib.sha256(payload).hexdigest()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--result-dir", type=Path, required=True)
    parser.add_argument("--summary-json", type=Path, required=True)
    parser.add_argument("--summary-tsv", type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--expected-binary-sha256", required=True)
    parser.add_argument("--expected-source-manifest-sha256", required=True)
    parser.add_argument("--expected-build-receipt-sha256", required=True)
    parser.add_argument("--expected-konclude-sha256", required=True)
    parser.add_argument("--expected-konclude-runtime-sha256", required=True)
    parser.add_argument("--expected-konclude-build-receipt-sha256", required=True)
    parser.add_argument("--expected-konclude-source-manifest-sha256", required=True)
    parser.add_argument("--expected-konclude-build-driver-sha256", required=True)
    parser.add_argument("--expected-selected-registry-sha256", required=True)
    parser.add_argument("--expected-selected-summary-sha256", required=True)
    parser.add_argument(
        "--expected-selected-result-manifest-sha256", required=True
    )
    parser.add_argument(
        "--expected-slurm-array-job-id", action="append", required=True
    )
    parser.add_argument("--expected-timeout", type=float, required=True)
    parser.add_argument("--expected-memcap-mb", type=int, required=True)
    parser.add_argument("--expected-validator-sha256", required=True)
    parser.add_argument("--expected-shared-validator-sha256", required=True)
    parser.add_argument("--expected-validation-driver-sha256", required=True)
    parser.add_argument("--expected-selected-driver-sha256", required=True)
    parser.add_argument("--expected-runner-sha256", required=True)
    parser.add_argument("--expected-fingerprint-tool-sha256", required=True)
    parser.add_argument("--expected-km-runtime-sha256", required=True)
    parser.add_argument("--expected-ldd-sha256", required=True)
    parser.add_argument("--strict", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    with args.manifest.open(newline="", encoding="utf-8") as handle:
        manifest = list(csv.DictReader(handle, delimiter="\t"))
    if len(manifest) != EXPECTED:
        raise SystemExit(f"manifest has {len(manifest)} rows, expected {EXPECTED}")
    manifest_sha = sha256_file(args.manifest)
    if manifest_sha != args.expected_manifest_sha256:
        raise SystemExit(
            "manifest hash mismatch: expected "
            f"{args.expected_manifest_sha256}, observed {manifest_sha}"
        )
    manifest_indices = [int(row["task_index"]) for row in manifest]
    if manifest_indices != list(range(EXPECTED)):
        raise SystemExit("manifest task indices are not exactly 0..10754")
    manifest_keys = [(row["ontology"], row["route"]) for row in manifest]
    if len(set(manifest_keys)) != len(manifest_keys):
        raise SystemExit("manifest repeats ontology/route claim pairs")
    for row in manifest:
        if (
            row["current_binary_sha256"] != args.expected_binary_sha256
            or row["current_source_manifest_sha256"]
            != args.expected_source_manifest_sha256
            or row["current_build_receipt_sha256"]
            != args.expected_build_receipt_sha256
            or row["selected_registry_sha256"]
            != args.expected_selected_registry_sha256
            or row["selected_summary_sha256"]
            != args.expected_selected_summary_sha256
            or row["selected_result_manifest_sha256"]
            != args.expected_selected_result_manifest_sha256
        ):
            raise SystemExit(
                "manifest mixes current capsule or selected-campaign identities"
            )
    if args.expected_timeout <= 0 or args.expected_memcap_mb <= 0:
        raise SystemExit("expected KM limits must be positive")

    record_paths: dict[int, Path] = {}
    for path in (args.result_dir / "alternative-results").glob("*/*.json"):
        prefix, separator, _ = path.name.partition("__")
        if (
            not separator
            or len(prefix) != 5
            or not prefix.isdigit()
            or int(prefix) not in range(EXPECTED)
        ):
            raise SystemExit(f"invalid alternative result filename: {path.name}")
        index = int(prefix)
        if index in record_paths:
            raise SystemExit(f"duplicate result index {index}")
        record_paths[index] = path

    statuses = Counter()
    confirmed_by_route = Counter()
    missing = [index for index in range(EXPECTED) if index not in record_paths]
    failures = []
    nonterminal = []
    route_observation_failures: dict[int, str] = {}
    provenance_failures: dict[int, list[str]] = {}
    for row in manifest:
        index = int(row["task_index"])
        path = record_paths.get(index)
        if path is None:
            continue
        record = json.loads(path.read_text(encoding="utf-8"))
        statuses[record.get("confirmation_status", "missing_status")] += 1
        if record.get("confirmed") is True:
            confirmed_by_route[record.get("route", "missing_route")] += 1
        else:
            failures.append(index)
        if record.get("phase") != "complete":
            nonterminal.append(index)
        route_specification = record.get("route_specification")
        km_run = record.get("km_run") or {}
        km_launcher = km_run.get("launcher") or {}
        route_environment = {"KM_ROUTE": row["route"], "KM_TIMING": "1"}
        expected = {
            "manifest": record.get("manifest_sha256") == manifest_sha,
            "expected_manifest": record.get("expected_manifest_sha256")
            == manifest_sha,
            "protocol": record.get("validation_protocol")
            == "reproducible-current-alternative-full-iri-v2",
            "task_index": record.get("task_index") == index,
            "ontology": record.get("ontology") == row["ontology"],
            "ontology_sha256": record.get("ontology_sha256")
            == record.get("expected_ontology_sha256")
            == row["ontology_sha256"],
            "route": record.get("route") == row["route"],
            "slurm_job": str(record.get("slurm_array_job_id", ""))
            in args.expected_slurm_array_job_id,
            "slurm_task_binding": record.get("slurm_task_matches_row") is True,
            "selected_campaign": record.get("selected_campaign_matches")
            is True
            and record.get("selected_registry_sha256")
            == args.expected_selected_registry_sha256
            and record.get("selected_summary_sha256")
            == args.expected_selected_summary_sha256
            and record.get("selected_result_manifest_sha256")
            == args.expected_selected_result_manifest_sha256,
            "binary": record.get("actual_binary_sha256")
            == row["current_binary_sha256"]
            == args.expected_binary_sha256,
            "source": record.get("current_source_manifest_sha256")
            == row["current_source_manifest_sha256"]
            == args.expected_source_manifest_sha256,
            "receipt": record.get("executed_build_receipt_sha256")
            == row["current_build_receipt_sha256"]
            == args.expected_build_receipt_sha256,
            "validator": record.get("validator_sha256")
            == args.expected_validator_sha256,
            "shared_validator": record.get("shared_validator_sha256")
            == args.expected_shared_validator_sha256,
            "validation_driver": record.get("validation_driver_sha256")
            == args.expected_validation_driver_sha256
            and record.get("validation_driver_check") is True,
            "selected_validation_driver": record.get(
                "reference_validation_driver_sha256"
            )
            == args.expected_selected_driver_sha256,
            "runner": record.get("runner_sha256")
            == args.expected_runner_sha256,
            "fingerprint_tool": record.get("fingerprint_tool_sha256")
            == args.expected_fingerprint_tool_sha256,
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
            "reference_record": record.get("reference_record_sha256")
            == row["fresh_reference_record_sha256"],
            "reference_provenance": bool(
                record.get("reference_provenance_checks")
            )
            and all(record["reference_provenance_checks"].values()),
            "reference_konclude_binary": record.get(
                "reference_binary_sha256"
            )
            == args.expected_konclude_sha256,
            "reference_konclude_build_receipt": record.get(
                "reference_build_receipt_sha256"
            )
            == args.expected_konclude_build_receipt_sha256,
            "reference_konclude_build_checks": bool(
                record.get("reference_build_checks")
            )
            and all(record["reference_build_checks"].values()),
            "reference_konclude_runtime": (
                record.get("reference_runtime") or {}
            ).get("runtime_library_manifest_sha256")
            == args.expected_konclude_runtime_sha256
            and (record.get("reference_runtime") or {}).get("ldd_sha256")
            == args.expected_ldd_sha256,
            "reference_route_specification": isinstance(
                record.get("reference_route_specification"), dict
            )
            and record.get("reference_route_specification_sha256")
            == canonical_json_sha256(
                record["reference_route_specification"]
            ),
            "reference_route_build_receipt": (
                record.get("reference_route_specification") or {}
            ).get("build_receipt_sha256")
            == args.expected_konclude_build_receipt_sha256,
            "reference_route_source_manifest": (
                record.get("reference_route_specification") or {}
            ).get("source_manifest_sha256")
            == args.expected_konclude_source_manifest_sha256,
            "reference_route_build_driver": (
                record.get("reference_route_specification") or {}
            ).get("build_driver_sha256")
            == args.expected_konclude_build_driver_sha256,
            "record_terminal": record.get("phase") == "complete",
            "route_specification_binary": (route_specification or {}).get(
                "binary_sha256"
            )
            == args.expected_binary_sha256,
            "route_specification_source": (route_specification or {}).get(
                "source_manifest_sha256"
            )
            == args.expected_source_manifest_sha256,
            "route_specification_receipt": (route_specification or {}).get(
                "build_receipt_sha256"
            )
            == args.expected_build_receipt_sha256,
            "route_specification_runtime": (route_specification or {}).get(
                "runtime_library_manifest_sha256"
            )
            == args.expected_km_runtime_sha256,
            "route_specification_ontology": (route_specification or {}).get(
                "ontology_sha256"
            )
            == row["ontology_sha256"],
            "route_specification_route": (route_specification or {}).get(
                "semantic_environment"
            )
            == {"KM_ROUTE": row["route"]},
            "route_specification_instrumentation": (
                route_specification or {}
            ).get("instrumentation_environment")
            == {"KM_TIMING": "1"},
            "route_specification_closed_environment": (
                route_specification or {}
            ).get("closed_base_environment")
            == {
                "PATH": "/usr/bin:/bin",
                "LC_ALL": "C",
                "PYTHONHASHSEED": "0",
            },
            "km_timeout": (route_specification or {}).get("timeout_s")
            == args.expected_timeout,
            "km_memory": (route_specification or {}).get("memory_limit_mb")
            == args.expected_memcap_mb,
            "km_run_timeout": (record.get("km_run") or {}).get("timeout_s")
            == args.expected_timeout,
            "km_run_memory": (record.get("km_run") or {}).get(
                "memory_limit_mb"
            )
            == args.expected_memcap_mb,
            "km_run_record": isinstance(record.get("km_run"), dict),
            "km_run_binary": km_run.get("binary_sha256")
            == args.expected_binary_sha256,
            "km_run_ontology": km_run.get("ontology_sha256")
            == row["ontology_sha256"],
            "km_run_command": km_run.get("command")
            == (route_specification or {}).get("command"),
            "km_run_environment": km_run.get("environment")
            == route_environment,
            "km_run_cpus": km_run.get("cpus") == 16,
            "launcher_verified": km_launcher.get("status") == "verified"
            and bool(km_launcher.get("checks"))
            and all(km_launcher["checks"].values()),
            "launcher_wrapper": km_launcher.get("wrapper_sha256")
            == args.expected_runner_sha256,
            "launcher_working_directory": km_launcher.get("working_directory")
            == "/",
            "launcher_environment": (
                km_launcher.get("environment") or {}
            ).get("PATH")
            == "/usr/bin:/bin"
            and (km_launcher.get("environment") or {}).get("LC_ALL") == "C"
            and (km_launcher.get("environment") or {}).get("PYTHONHASHSEED")
            == "0",
            "validator_environment": bool(
                record.get("validator_environment_checks")
            )
            and all(record["validator_environment_checks"].values()),
            "route_specification": isinstance(route_specification, dict)
            and record.get("route_specification_sha256")
            == canonical_json_sha256(route_specification),
        }
        trace_count = record.get("selected_route_trace_count")
        trace = record.get("selected_route_trace")
        if trace_count != 1 or trace != row["route"]:
            route_observation_failures[index] = (
                f"count={trace_count!r}, observed={trace!r}, "
                f"requested={row['route']!r}"
            )
        failed = [name for name, passed in expected.items() if not passed]
        if failed:
            provenance_failures[index] = failed
            if index not in failures:
                failures.append(index)

    fields = [
        "task_index",
        "ontology",
        "route",
        "route_environment",
        "selected_route_trace",
        "selected_route_trace_count",
        "confirmation_status",
        "confirmed",
        "phase",
        "provenance_valid",
        "route_observed",
        "wall_s",
        "peak_mb",
        "current_binary_sha256",
        "current_source_manifest_sha256",
        "current_build_receipt_sha256",
        "km_runtime_manifest_sha256",
        "ldd_sha256",
        "ontology_sha256",
        "route_specification_sha256",
        "validator_sha256",
        "validation_driver_sha256",
        "shared_validator_sha256",
        "runner_sha256",
        "fingerprint_tool_sha256",
        "historical_binary_sha256",
        "km_taxonomy_sha256",
        "reference_taxonomy_sha256",
        "slurm_array_job_id",
        "slurm_array_task_id",
    ]
    args.summary_tsv.parent.mkdir(parents=True, exist_ok=True)
    with args.summary_tsv.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        for row in manifest:
            index = int(row["task_index"])
            path = record_paths.get(index)
            record = (
                json.loads(path.read_text(encoding="utf-8"))
                if path is not None
                else {}
            )
            run = record.get("km_run") or {}
            fingerprint = record.get("km_fingerprint") or {}
            reference = record.get("reference_fingerprint") or {}
            writer.writerow(
                {
                    "task_index": index,
                    "ontology": row["ontology"],
                    "route": row["route"],
                    "route_environment": row["route_environment"],
                    "selected_route_trace": record.get(
                        "selected_route_trace", ""
                    ),
                    "selected_route_trace_count": record.get(
                        "selected_route_trace_count", ""
                    ),
                    "confirmation_status": record.get(
                        "confirmation_status", "missing"
                    ),
                    "confirmed": str(record.get("confirmed", False)).lower(),
                    "phase": record.get("phase", "missing"),
                    "provenance_valid": str(
                        index in record_paths
                        and index not in provenance_failures
                    ).lower(),
                    "route_observed": str(
                        index in record_paths
                        and index not in route_observation_failures
                    ).lower(),
                    "wall_s": run.get("wall_s", ""),
                    "peak_mb": run.get("peak_mb", ""),
                    "current_binary_sha256": record.get(
                        "actual_binary_sha256", ""
                    ),
                    "current_source_manifest_sha256": row[
                        "current_source_manifest_sha256"
                    ],
                    "current_build_receipt_sha256": row[
                        "current_build_receipt_sha256"
                    ],
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
                    "validator_sha256": record.get("validator_sha256", ""),
                    "validation_driver_sha256": record.get(
                        "validation_driver_sha256", ""
                    ),
                    "shared_validator_sha256": record.get(
                        "shared_validator_sha256", ""
                    ),
                    "runner_sha256": record.get("runner_sha256", ""),
                    "fingerprint_tool_sha256": record.get(
                        "fingerprint_tool_sha256", ""
                    ),
                    "historical_binary_sha256": row[
                        "historical_binary_sha256"
                    ],
                    "km_taxonomy_sha256": fingerprint.get(
                        "taxonomy_sha256", ""
                    ),
                    "reference_taxonomy_sha256": reference.get(
                        "taxonomy_sha256", ""
                    ),
                    "slurm_array_job_id": record.get(
                        "slurm_array_job_id", ""
                    ),
                    "slurm_array_task_id": record.get(
                        "slurm_array_task_id", ""
                    ),
                }
            )

    all_routes_confirmed = (
        len(record_paths) == EXPECTED
        and statuses["confirmed_current_full_iri"] == EXPECTED
        and not missing
        and not failures
        and not provenance_failures
    )
    campaign_complete = (
        len(record_paths) == EXPECTED
        and not missing
        and not nonterminal
        and not provenance_failures
    )
    result_record_count, result_record_manifest_sha = record_manifest_sha256(
        manifest, record_paths, args.result_dir
    )
    summary = {
        "schema_version": 1,
        "validation_protocol": "reproducible-current-alternative-full-iri-v2",
        "aggregator_sha256": sha256_file(Path(__file__)),
        "manifest": str(args.manifest),
        "manifest_sha256": manifest_sha,
        "manifest_rows": len(manifest),
        "result_records": len(record_paths),
        "result_record_manifest_count": result_record_count,
        "result_record_manifest_sha256": result_record_manifest_sha,
        "confirmation_status_counts": dict(sorted(statuses.items())),
        "confirmed_by_route": dict(sorted(confirmed_by_route.items())),
        "missing_indices": missing,
        "nonterminal_indices": sorted(nonterminal),
        "failed_indices": sorted(failures),
        "route_observation_failures": {
            str(index): value
            for index, value in sorted(route_observation_failures.items())
        },
        "provenance_failures": {
            str(index): value
            for index, value in sorted(provenance_failures.items())
        },
        "expected_validator_sha256": args.expected_validator_sha256,
        "expected_binary_sha256": args.expected_binary_sha256,
        "expected_source_manifest_sha256": (
            args.expected_source_manifest_sha256
        ),
        "expected_build_receipt_sha256": args.expected_build_receipt_sha256,
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
        "expected_selected_registry_sha256": (
            args.expected_selected_registry_sha256
        ),
        "expected_selected_summary_sha256": (
            args.expected_selected_summary_sha256
        ),
        "expected_selected_result_manifest_sha256": (
            args.expected_selected_result_manifest_sha256
        ),
        "expected_slurm_array_job_ids": sorted(
            args.expected_slurm_array_job_id
        ),
        "expected_timeout": args.expected_timeout,
        "expected_memcap_mb": args.expected_memcap_mb,
        "expected_shared_validator_sha256": (
            args.expected_shared_validator_sha256
        ),
        "expected_validation_driver_sha256": (
            args.expected_validation_driver_sha256
        ),
        "expected_selected_driver_sha256": (
            args.expected_selected_driver_sha256
        ),
        "expected_runner_sha256": args.expected_runner_sha256,
        "expected_fingerprint_tool_sha256": (
            args.expected_fingerprint_tool_sha256
        ),
        "expected_km_runtime_sha256": args.expected_km_runtime_sha256,
        "expected_ldd_sha256": args.expected_ldd_sha256,
        "confirmed_total": statuses["confirmed_current_full_iri"],
        "terminal_records": len(record_paths) - len(nonterminal),
        "campaign_complete": campaign_complete,
        "all_routes_confirmed": all_routes_confirmed,
        "successful": campaign_complete,
        "successful_definition": (
            "all manifest rows have terminal provenance-valid records; "
            "individual solves require confirmed_current_full_iri"
        ),
    }
    args.summary_json.parent.mkdir(parents=True, exist_ok=True)
    args.summary_json.write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, sort_keys=True))
    return 1 if args.strict and not campaign_complete else 0


if __name__ == "__main__":
    raise SystemExit(main())
