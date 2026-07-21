#!/usr/bin/env python3
"""Validate one documented alternative route with the current KM candidate."""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import math
import os
from pathlib import Path
import shutil
import sys
import tempfile
import traceback

# ``-I`` deliberately removes the script directory from sys.path.  Re-add only
# this resolved, driver-pinned sibling directory before importing the shared
# validator implementation.
SCRIPT_DIRECTORY = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIRECTORY))

from validate_documented_route import (
    atomic_json,
    binary_from_locator,
    copy_failure_metadata,
    executable_runtime_identity,
    fingerprint_checks,
    load_json,
    preserve_fingerprint_artifacts,
    run_checks,
    run_fingerprint,
    run_retained,
    route_environment,
    selected_routes_from_stderr,
    semantic_checks,
    sha256_file,
    canonical_json_sha256,
    verify_build_receipt,
    verify_current_route_environment,
    validator_environment_checks,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--row-index", type=int, required=True)
    parser.add_argument("--task-offset", type=int, default=0)
    parser.add_argument("--km-root", type=Path, required=True)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--fingerprint", type=Path, required=True)
    parser.add_argument("--validation-driver", type=Path, required=True)
    parser.add_argument("--validation-driver-sha256", required=True)
    parser.add_argument("--selected-validation-driver-sha256", required=True)
    parser.add_argument("--selected-registry-sha256", required=True)
    parser.add_argument("--selected-summary-sha256", required=True)
    parser.add_argument("--selected-result-manifest-sha256", required=True)
    parser.add_argument("--selected-result-dir", type=Path, required=True)
    parser.add_argument("--result-dir", type=Path, required=True)
    parser.add_argument("--ldd-sha256", required=True)
    parser.add_argument("--km-runtime-count", type=int, required=True)
    parser.add_argument("--km-runtime-stream-sha256", required=True)
    parser.add_argument("--konclude-sha256", required=True)
    parser.add_argument("--konclude-runtime-count", type=int, required=True)
    parser.add_argument("--konclude-runtime-stream-sha256", required=True)
    parser.add_argument("--konclude-build-receipt-sha256", required=True)
    parser.add_argument("--konclude-source-manifest-sha256", required=True)
    parser.add_argument("--konclude-build-driver-sha256", required=True)
    parser.add_argument("--timeout", type=float, default=240.0)
    parser.add_argument("--memcap-mb", type=int, default=20480)
    return parser.parse_args()


def read_manifest_row(path: Path, index: int) -> dict[str, str]:
    if index < 0:
        raise IndexError(index)
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        row = next(itertools.islice(reader, index, index + 1), None)
    if row is None:
        raise IndexError(f"manifest row {index} does not exist")
    if int(row["task_index"]) != index:
        raise ValueError(
            f"manifest index mismatch: requested {index}, row has {row['task_index']}"
        )
    return row


def main() -> int:
    args = parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        raise ValueError("--timeout must be a finite positive number")
    if args.memcap_mb <= 0:
        raise ValueError("--memcap-mb must be positive")
    if args.task_offset < 0:
        raise ValueError("--task-offset must be non-negative")
    actual_manifest_sha256 = sha256_file(args.manifest)
    if actual_manifest_sha256 != args.manifest_sha256:
        raise ValueError(
            "alternative manifest hash mismatch: expected "
            f"{args.manifest_sha256}, observed {actual_manifest_sha256}"
        )
    validator_environment, validator_environment_status = (
        validator_environment_checks()
    )
    row = read_manifest_row(args.manifest, args.row_index)
    ontology_name = row["ontology"]
    route = row["route"]
    expected_ontology_sha256 = row.get("ontology_sha256", "")
    if len(expected_ontology_sha256) != 64 or any(
        character not in "0123456789abcdef"
        for character in expected_ontology_sha256
    ):
        raise ValueError(
            f"manifest row lacks an exact ontology SHA-256: {ontology_name}"
        )
    slurm_task_text = os.environ.get("SLURM_ARRAY_TASK_ID", "")
    slurm_task_matches = (
        slurm_task_text.isdigit()
        and int(slurm_task_text) + args.task_offset == args.row_index
    )
    selected_campaign_matches = (
        row.get("selected_registry_sha256")
        == args.selected_registry_sha256
        and row.get("selected_summary_sha256")
        == args.selected_summary_sha256
        and row.get("selected_result_manifest_sha256")
        == args.selected_result_manifest_sha256
    )
    bucket = f"{args.row_index // 1000:02d}"
    result_path = (
        args.result_dir
        / "alternative-results"
        / bucket
        / f"{args.row_index:05d}__{ontology_name}__{route}.json"
    )
    actual_validation_driver_sha256 = (
        sha256_file(args.validation_driver)
        if args.validation_driver.is_file()
        else ""
    )
    validation_driver_check = (
        actual_validation_driver_sha256 == args.validation_driver_sha256
    )
    record = {
        "schema_version": 1,
        "validation_protocol": "reproducible-current-alternative-full-iri-v2",
        "phase": "initialised",
        "confirmation_status": "running",
        "confirmed": False,
        "task_index": args.row_index,
        "ontology": ontology_name,
        "route": route,
        "manifest_sha256": actual_manifest_sha256,
        "expected_manifest_sha256": args.manifest_sha256,
        "expected_ontology_sha256": expected_ontology_sha256,
        "task_offset": args.task_offset,
        "slurm_task_matches_row": slurm_task_matches,
        "selected_campaign_matches": selected_campaign_matches,
        "selected_registry_sha256": args.selected_registry_sha256,
        "selected_summary_sha256": args.selected_summary_sha256,
        "selected_result_manifest_sha256": (
            args.selected_result_manifest_sha256
        ),
        "validator_sha256": sha256_file(Path(__file__)),
        "shared_validator_sha256": sha256_file(
            Path(__file__).with_name("validate_documented_route.py")
        ),
        "runner_sha256": sha256_file(args.runner),
        "fingerprint_tool_sha256": sha256_file(args.fingerprint),
        "validation_driver": str(args.validation_driver),
        "validation_driver_sha256": actual_validation_driver_sha256,
        "validation_driver_check": validation_driver_check,
        "current_binary_locator": row["current_binary_locator"],
        "current_binary_sha256": row["current_binary_sha256"],
        "current_source_manifest_sha256": row[
            "current_source_manifest_sha256"
        ],
        "current_build_receipt_locator": row[
            "current_build_receipt_locator"
        ],
        "current_build_receipt_sha256": row[
            "current_build_receipt_sha256"
        ],
        "historical_binary_locator": row["historical_binary_locator"],
        "historical_binary_sha256": row["historical_binary_sha256"],
        "historical_wall_s": row["historical_wall_s"],
        "historical_peak_mb": row["historical_peak_mb"],
        "historical_evidence": row["historical_evidence"],
        "slurm_job_id": os.environ.get("SLURM_JOB_ID"),
        "slurm_array_job_id": os.environ.get("SLURM_ARRAY_JOB_ID"),
        "slurm_array_task_id": os.environ.get("SLURM_ARRAY_TASK_ID"),
        "host": os.uname().nodename,
        "validator_environment": validator_environment,
        "validator_environment_checks": validator_environment_status,
    }
    atomic_json(result_path, record)

    if not all(validator_environment_status.values()):
        record.update(
            phase="complete",
            confirmation_status="validator_environment_mismatch",
            confirmed=False,
        )
        atomic_json(result_path, record)
        return 1

    if not slurm_task_matches:
        record.update(
            phase="complete",
            confirmation_status="slurm_task_mismatch",
            confirmed=False,
        )
        atomic_json(result_path, record)
        return 1

    if not selected_campaign_matches:
        record.update(
            phase="complete",
            confirmation_status="selected_campaign_mismatch",
            confirmed=False,
        )
        atomic_json(result_path, record)
        return 1

    if not validation_driver_check:
        record.update(
            phase="complete",
            confirmation_status="validation_driver_mismatch",
            confirmed=False,
        )
        atomic_json(result_path, record)
        return 1

    temporary_root = Path(
        tempfile.mkdtemp(
            prefix=f"km-alt-{args.row_index:05d}-",
            dir=os.environ.get("SLURM_TMPDIR") or None,
        )
    )
    try:
        reference_path = (
            args.selected_result_dir / row["fresh_reference_record"]
        )
        reference_sha256 = sha256_file(reference_path)
        if reference_sha256 != row["fresh_reference_record_sha256"]:
            raise ValueError(
                "selected reference record hash mismatch: "
                f"expected {row['fresh_reference_record_sha256']}, "
                f"observed {reference_sha256}"
            )
        reference_record = load_json(reference_path)
        if reference_record.get("documented_state") != "exact_gold":
            raise ValueError(
                "alternative route lacks an exact-gold reference row: "
                f"{reference_path}"
            )
        if reference_record.get("reference_ready") is not True:
            raise ValueError(
                "alternative route lacks a successful fresh Konclude full-IRI "
                f"reference: {reference_path}"
            )
        reference_fingerprint = reference_record.get("reference_fingerprint")
        if not isinstance(reference_fingerprint, dict):
            raise ValueError(f"reference fingerprint is absent: {reference_path}")
        reference_artifact_checks: dict[str, bool] = {}
        for path_key, hash_key in (
            ("node_fingerprints", "node_fingerprints_sha256"),
            ("unsatisfiable_names", "unsatisfiable_names_sha256"),
        ):
            artifact_text = reference_fingerprint.get(path_key, "")
            expected_artifact_sha256 = reference_fingerprint.get(hash_key, "")
            artifact = Path(artifact_text) if artifact_text else Path()
            reference_artifact_checks[path_key] = (
                bool(artifact_text)
                and bool(expected_artifact_sha256)
                and artifact.is_file()
                and sha256_file(artifact) == expected_artifact_sha256
            )
        reference_route_specification = reference_record.get(
            "reference_route_specification"
        ) or {}
        reference_runtime = reference_record.get("reference_runtime") or {}
        reference_run = reference_record.get("reference_run") or {}
        expected_reference_provenance = {
            "validation_protocol": reference_record.get("validation_protocol")
            == "reproducible-current-selected-full-iri-v2",
            "selected_registry": reference_record.get("registry_sha256")
            == args.selected_registry_sha256,
            "ontology": reference_record.get("ontology_sha256")
            == expected_ontology_sha256,
            "binary": reference_record.get("actual_binary_sha256")
            == row["current_binary_sha256"],
            "source": reference_record.get(
                "executed_source_manifest_sha256"
            )
            == row["current_source_manifest_sha256"],
            "receipt": reference_record.get(
                "executed_build_receipt_sha256"
            )
            == row["current_build_receipt_sha256"],
            "fingerprinter": reference_record.get("fingerprint_tool_sha256")
            == sha256_file(args.fingerprint),
            "shared_validator": reference_record.get("validator_sha256")
            == sha256_file(
                Path(__file__).with_name("validate_documented_route.py")
            ),
            "selected_validation_driver": reference_record.get(
                "validation_driver_sha256"
            )
            == args.selected_validation_driver_sha256
            and reference_record.get("validation_driver_check") is True,
            "runner": reference_record.get("runner_sha256")
            == sha256_file(args.runner),
            "km_runtime": bool(reference_record.get("km_runtime_checks"))
            and all(reference_record["km_runtime_checks"].values())
            and (reference_record.get("km_runtime") or {}).get(
                "runtime_library_manifest_sha256"
            )
            == args.km_runtime_stream_sha256,
            "reference_runtime": bool(
                reference_record.get("reference_runtime_checks")
            )
            and all(reference_record["reference_runtime_checks"].values()),
            "reference_source_build": bool(
                reference_record.get("reference_build_checks")
            )
            and all(reference_record["reference_build_checks"].values()),
            "reference_build_receipt": reference_record.get(
                "reference_build_receipt_sha256"
            )
            == args.konclude_build_receipt_sha256,
            "reference_run": bool(reference_record.get("reference_checks"))
            and all(reference_record["reference_checks"].values()),
            "reference_route_specification_hash": bool(
                reference_route_specification
            )
            and canonical_json_sha256(reference_route_specification)
            == reference_record.get("reference_route_specification_sha256"),
            "reference_route_ontology": reference_route_specification.get(
                "ontology_sha256"
            )
            == expected_ontology_sha256,
            "reference_route_binary": reference_route_specification.get(
                "binary_sha256"
            )
            == args.konclude_sha256,
            "reference_route_build_receipt": reference_route_specification.get(
                "build_receipt_sha256"
            )
            == args.konclude_build_receipt_sha256,
            "reference_route_source_manifest": reference_route_specification.get(
                "source_manifest_sha256"
            )
            == args.konclude_source_manifest_sha256,
            "reference_route_build_driver": reference_route_specification.get(
                "build_driver_sha256"
            )
            == args.konclude_build_driver_sha256,
            "reference_runtime_binary": reference_runtime.get("binary_sha256")
            == args.konclude_sha256,
            "reference_runtime_count": reference_runtime.get(
                "runtime_library_count"
            )
            == args.konclude_runtime_count,
            "reference_runtime_hash": reference_runtime.get(
                "runtime_library_manifest_sha256"
            )
            == args.konclude_runtime_stream_sha256,
            "reference_run_binary": reference_run.get("binary_sha256")
            == args.konclude_sha256,
            "reference_run_ontology": reference_run.get("ontology_sha256")
            == expected_ontology_sha256,
            **{
                f"reference_artifact_{key}": value
                for key, value in reference_artifact_checks.items()
            },
            "validator_environment": bool(
                reference_record.get("validator_environment_checks")
            )
            and all(reference_record["validator_environment_checks"].values()),
        }
        failed_reference_provenance = [
            name for name, passed in expected_reference_provenance.items() if not passed
        ]
        if failed_reference_provenance:
            raise ValueError(
                "selected reference belongs to another capsule/tool set: "
                f"{failed_reference_provenance}"
            )
        ontology_source = args.km_root / "corpus" / ontology_name
        if not ontology_source.is_file():
            raise FileNotFoundError(ontology_source)
        ontology = temporary_root / ontology_name
        shutil.copy2(ontology_source, ontology)
        if sha256_file(ontology) != expected_ontology_sha256:
            raise ValueError("ontology hash differs from the frozen manifest")

        binary = binary_from_locator(row["current_binary_locator"])
        if not binary.is_file():
            raise FileNotFoundError(binary)
        binary_sha = sha256_file(binary)
        if binary_sha != row["current_binary_sha256"]:
            raise ValueError(
                f"current binary hash mismatch: expected {row['current_binary_sha256']}, "
                f"observed {binary_sha}"
            )
        receipt_path = binary_from_locator(row["current_build_receipt_locator"])
        receipt_sha, receipt = verify_build_receipt(
            receipt_path,
            row["current_build_receipt_sha256"],
            binary_sha,
            row["current_source_manifest_sha256"],
        )
        km_runtime = executable_runtime_identity(
            binary=binary,
            environment={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
            expected_ldd_sha256=args.ldd_sha256,
        )
        km_runtime_checks = {
            "binary_sha256": km_runtime.get("binary_sha256") == binary_sha,
            "ldd_sha256": km_runtime.get("ldd_sha256") == args.ldd_sha256,
            "runtime_library_count": km_runtime.get("runtime_library_count")
            == args.km_runtime_count,
            "runtime_library_manifest_sha256": km_runtime.get(
                "runtime_library_manifest_sha256"
            )
            == args.km_runtime_stream_sha256,
        }
        if not all(km_runtime_checks.values()):
            raise ValueError(
                "KM runtime closure failed checks: "
                f"{[key for key, passed in km_runtime_checks.items() if not passed]}"
            )
        route_environment_values = route_environment(row["route_environment"])
        if route_environment_values != [f"KM_ROUTE={route}"]:
            raise ValueError(
                "alternative route environment differs from its named route: "
                f"{route_environment_values!r}"
            )
        verify_current_route_environment(route_environment_values)
        instrumentation_environment = ["KM_TIMING=1"]
        environment = route_environment_values + instrumentation_environment
        ontology_sha256 = sha256_file(ontology)
        route_specification = {
            "schema_version": 2,
            "binary_sha256": binary_sha,
            "source_manifest_sha256": row["current_source_manifest_sha256"],
            "build_receipt_sha256": receipt_sha,
            "runtime_library_manifest_sha256": (
                args.km_runtime_stream_sha256
            ),
            "runtime_library_count": args.km_runtime_count,
            "ontology_sha256": ontology_sha256,
            "command": [str(binary), "classify", str(ontology)],
            "semantic_environment": {"KM_ROUTE": route},
            "instrumentation_environment": {"KM_TIMING": "1"},
            "closed_base_environment": {
                "PATH": "/usr/bin:/bin",
                "LC_ALL": "C",
                "PYTHONHASHSEED": "0",
            },
            "validator_sha256": sha256_file(Path(__file__)),
            "shared_validator_sha256": sha256_file(
                Path(__file__).with_name("validate_documented_route.py")
            ),
            "runner_wrapper_sha256": sha256_file(args.runner),
            "fingerprint_tool_sha256": sha256_file(args.fingerprint),
            "validation_driver_sha256": actual_validation_driver_sha256,
            "cpus": 16,
            "timeout_s": args.timeout,
            "memory_limit_mb": args.memcap_mb,
        }
        record.update(
            phase="provenance_verified",
            ontology_sha256=ontology_sha256,
            actual_binary_sha256=binary_sha,
            reference_record=str(reference_path),
            reference_record_sha256=reference_sha256,
            reference_provenance_checks=expected_reference_provenance,
            reference_validation_protocol=reference_record.get(
                "validation_protocol"
            ),
            reference_validation_driver_sha256=reference_record.get(
                "validation_driver_sha256"
            ),
            reference_binary_sha256=args.konclude_sha256,
            reference_build_receipt_sha256=(
                args.konclude_build_receipt_sha256
            ),
            reference_build_checks=reference_record.get(
                "reference_build_checks"
            ),
            reference_runtime=reference_runtime,
            reference_run=reference_run,
            reference_route_specification=reference_route_specification,
            reference_route_specification_sha256=reference_record.get(
                "reference_route_specification_sha256"
            ),
            reference_fingerprint=reference_fingerprint,
            parsed_environment=route_environment_values,
            instrumentation_environment=instrumentation_environment,
            executed_environment=environment,
            route_specification=route_specification,
            route_specification_sha256=canonical_json_sha256(
                route_specification
            ),
            executed_build_receipt=str(receipt_path),
            executed_build_receipt_sha256=receipt_sha,
            build_receipt=receipt,
            km_runtime=km_runtime,
            km_runtime_checks=km_runtime_checks,
        )
        atomic_json(result_path, record)

        km_dir = temporary_root / "km"
        runner_rc, runner_stdout, runner_stderr, km_run = run_retained(
            runner=args.runner,
            kind="km",
            label=f"alternative_{route}_{ontology_name}",
            ontology=ontology,
            binary=binary,
            output_dir=km_dir,
            timeout=args.timeout,
            memcap_mb=args.memcap_mb,
            environment=environment,
            workers=16,
        )
        checks = run_checks(
            km_run,
            binary_sha,
            args.timeout,
            args.memcap_mb,
            sha256_file(args.runner),
            [str(binary), "classify", str(ontology)],
        )
        checks.update(
            {
                f"reference_provenance_{key}": value
                for key, value in expected_reference_provenance.items()
            }
        )
        checks.update(
            {
                f"runtime_{key}": value
                for key, value in km_runtime_checks.items()
            }
        )
        checks["requested_route_recorded"] = (
            km_run is not None
            and (km_run.get("environment") or {}).get("KM_ROUTE") == route
        )
        checks["validation_driver_hash"] = validation_driver_check
        checks["timing_instrumentation_recorded"] = (
            km_run is not None
            and (km_run.get("environment") or {}).get("KM_TIMING") == "1"
        )
        expected_run_environment = dict(
            value.split("=", 1) for value in environment
        )
        checks["complete_execution_environment"] = (
            km_run is not None
            and (km_run.get("environment") or {}) == expected_run_environment
        )
        selected_route_traces = selected_routes_from_stderr(
            km_dir / "stderr.log"
        )
        selected_route = (
            selected_route_traces[0]
            if len(selected_route_traces) == 1
            else ""
        )
        checks["exactly_one_route_trace"] = len(selected_route_traces) == 1
        checks["selected_route_traced"] = selected_route == route
        record.update(
            phase="km_finished",
            km_runner_return_code=runner_rc,
            km_runner_stdout=runner_stdout[-4000:],
            km_runner_stderr=runner_stderr[-4000:],
            km_run=km_run,
            selected_route_trace=selected_route,
            selected_route_traces=selected_route_traces,
            selected_route_trace_count=len(selected_route_traces),
            km_checks=checks,
        )
        atomic_json(result_path, record)
        if km_run is None or km_run.get("status") != "ok":
            raise RuntimeError(f"KM alternative route failed: {km_run!r}")

        prefix = temporary_root / "fingerprints" / "km"
        fp_rc, fp_stdout, fp_stderr, km_fingerprint = run_fingerprint(
            script=args.fingerprint,
            primary_output=Path(km_run["primary_output"]),
            output_format="json",
            source_ontology=ontology,
            output_prefix=prefix,
        )
        preserve_fingerprint_artifacts(
            km_fingerprint,
            result_dir=args.result_dir,
            ontology=ontology_name,
            label=f"alternative-{args.row_index:05d}-{route}",
        )
        checks.update(fingerprint_checks(km_fingerprint))
        checks.update(semantic_checks(km_fingerprint, reference_fingerprint))
        confirmed = all(checks.values()) and fp_rc == 0
        record.update(
            phase="complete",
            km_fingerprint_return_code=fp_rc,
            km_fingerprint_stdout=fp_stdout[-4000:],
            km_fingerprint_stderr=fp_stderr[-4000:],
            km_fingerprint=km_fingerprint,
            checks=checks,
            confirmed=confirmed,
            confirmation_status=(
                "confirmed_current_full_iri"
                if confirmed
                else "current_full_iri_mismatch_or_limit_failure"
            ),
        )
        atomic_json(result_path, record)
        if not confirmed:
            copy_failure_metadata(
                temporary_root,
                args.result_dir
                / "alternative-failures"
                / bucket
                / f"{args.row_index:05d}__{ontology_name}__{route}",
            )
        return 0 if confirmed else 1
    except Exception as error:  # noqa: BLE001 - publish every terminal state
        record.update(
            phase="complete",
            confirmation_status="validation_error",
            confirmed=False,
            error=repr(error),
            traceback=traceback.format_exc()[-12000:],
        )
        atomic_json(result_path, record)
        copy_failure_metadata(
            temporary_root,
            args.result_dir
            / "alternative-failures"
            / bucket
            / f"{args.row_index:05d}__{ontology_name}__{route}",
        )
        return 1
    finally:
        shutil.rmtree(temporary_root, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
