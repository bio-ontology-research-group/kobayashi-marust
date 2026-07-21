#!/usr/bin/env python3
"""Generate the per-ontology ledger from reproducible evidence only.

Current-source routes take precedence.  An older route may populate a row only
after rebuilding its exact Git revision twice, verifying the source identity,
capturing the runtime closure and reproducing a fresh full-IRI oracle result.
Opaque historical binaries remain provenance only.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path
import shlex


SELECTED_SUCCESS = {
    "confirmed_exact_full_iri": "reproduced_exact_full_iri",
    "confirmed_adjudicated_inconsistent": (
        "reproduced_adjudicated_inconsistent"
    ),
}
ALTERNATIVE_SUCCESS = "confirmed_current_full_iri"
SELECTED_PROTOCOL = "fresh-paired-full-iri-v2"
ALTERNATIVE_PROTOCOL = "reproducible-current-alternative-full-iri-v2"
REBUILT_HISTORICAL_PROTOCOL = (
    "reproducible-rebuilt-historical-full-iri-v1"
)
EXACT_CANDIDATE_PROTOCOL = (
    "reproducible-exact-candidate-selected-full-iri-v1"
)
SELECTED_CLAIMED_STATES = {
    "exact_gold",
    "adjudicated_correct_stale_gold",
}


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


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def all_recorded_checks_pass(record: dict) -> bool:
    return all_check_group_passes(record, "checks")


def all_check_group_passes(record: dict, key: str) -> bool:
    checks = record.get(key)
    return (
        isinstance(checks, dict)
        and bool(checks)
        and all(value is True for value in checks.values())
    )


def route_specification_is_intact(record: dict) -> bool:
    return named_specification_is_intact(record, "route_specification")


def current_route_label_is_intact(record: dict) -> bool:
    specification = record.get("route_specification") or {}
    semantic_environment = specification.get("semantic_environment")
    if not isinstance(semantic_environment, dict):
        return False
    environment_sha256 = canonical_json_sha256(semantic_environment)
    requested = record.get("effective_route_request")
    expected_label = requested
    if requested == "manual":
        expected_label = f"manual@sha256:{environment_sha256}"
    return (
        record.get("semantic_environment_sha256") == environment_sha256
        and record.get("current_route_label") == expected_label
    )


def ledger_route_observation(
    record: dict, chosen_origin: str
) -> tuple[str, str, str]:
    """Return the verified route-observation fields for the unified ledger."""
    if chosen_origin in {
        "current_selected_route",
        "current_alternative_route",
    }:
        expected = (
            record.get("effective_route_request")
            if chosen_origin == "current_selected_route"
            else record.get("route")
        )
        trace = record.get("selected_route_trace")
        if record.get("selected_route_trace_count") == 1 and trace == expected:
            return "runtime-trace", "runtime_trace", trace
    return (
        record.get("route_observation_policy", ""),
        record.get("route_observation_kind", ""),
        record.get("observed_route_identity", ""),
    )


def named_specification_is_intact(record: dict, key: str) -> bool:
    specification = record.get(key)
    return (
        isinstance(specification, dict)
        and record.get(f"{key}_sha256")
        == canonical_json_sha256(specification)
    )


def capsule_matches(
    record: dict, *, binary: str, source: str, receipt: str
) -> bool:
    return (
        record.get("actual_binary_sha256") == binary
        and (
            record.get("executed_source_manifest_sha256")
            or record.get("current_source_manifest_sha256")
        )
        == source
        and (
            record.get("executed_build_receipt_sha256")
            or record.get("current_build_receipt_sha256")
        )
        == receipt
    )


def km_runtime_matches(record: dict, expected: str, expected_ldd: str) -> bool:
    runtime = record.get("km_runtime") or {}
    return (
        runtime.get("runtime_library_manifest_sha256") == expected
        and runtime.get("ldd_sha256") == expected_ldd
        and all_check_group_passes(record, "km_runtime_checks")
    )


def selected_tool_provenance_matches(
    record: dict,
    *,
    validator: str,
    validation_driver: str,
    runner: str,
    fingerprint: str,
) -> bool:
    return (
        record.get("validation_protocol")
        == "reproducible-current-selected-full-iri-v2"
        and record.get("validator_sha256") == validator
        and record.get("validation_driver_sha256") == validation_driver
        and record.get("validation_driver_check") is True
        and record.get("runner_sha256") == runner
        and record.get("fingerprint_tool_sha256") == fingerprint
        and all_check_group_passes(record, "validator_environment_checks")
    )


def selected_reference_is_current(
    record: dict,
    *,
    binary: str,
    source: str,
    receipt: str,
    km_runtime: str,
    ldd: str,
    validator: str,
    validation_driver: str,
    runner: str,
    fingerprint: str,
    konclude: str,
    konclude_runtime: str,
    konclude_receipt: str,
    konclude_source: str,
    konclude_driver: str,
) -> bool:
    runtime = record.get("reference_runtime") or {}
    specification = record.get("reference_route_specification") or {}
    return (
        record.get("documented_state") == "exact_gold"
        and capsule_matches(record, binary=binary, source=source, receipt=receipt)
        and km_runtime_matches(record, km_runtime, ldd)
        and selected_tool_provenance_matches(
            record,
            validator=validator,
            validation_driver=validation_driver,
            runner=runner,
            fingerprint=fingerprint,
        )
        and record.get("reference_ready") is True
        and record.get("reference_binary_sha256") == konclude
        and record.get("reference_build_receipt_sha256")
        == konclude_receipt
        and all_check_group_passes(record, "reference_build_checks")
        and specification.get("binary_sha256") == konclude
        and specification.get("build_receipt_sha256") == konclude_receipt
        and specification.get("source_manifest_sha256") == konclude_source
        and specification.get("build_driver_sha256") == konclude_driver
        and specification.get("ontology_sha256")
        == record.get("ontology_sha256")
        and runtime.get("runtime_library_manifest_sha256")
        == konclude_runtime
        and runtime.get("ldd_sha256") == ldd
        and named_specification_is_intact(
            record, "reference_route_specification"
        )
        and all_check_group_passes(record, "reference_runtime_checks")
        and all_check_group_passes(record, "reference_checks")
        and all_check_group_passes(record, "reference_fingerprint_checks")
        and isinstance(record.get("reference_fingerprint"), dict)
    )


def source_built_konclude_reference_is_current(
    record: dict,
    *,
    konclude: str,
    konclude_runtime: str,
    konclude_receipt: str,
    konclude_source: str,
    konclude_driver: str,
    ldd: str,
) -> bool:
    runtime = record.get("reference_runtime") or {}
    specification = record.get("reference_route_specification") or {}
    return (
        record.get("documented_state") == "exact_gold"
        and record.get("reference_ready") is True
        and record.get("reference_binary_sha256") == konclude
        and record.get("reference_build_receipt_sha256") == konclude_receipt
        and all_check_group_passes(record, "reference_build_checks")
        and specification.get("binary_sha256") == konclude
        and specification.get("build_receipt_sha256") == konclude_receipt
        and specification.get("source_manifest_sha256") == konclude_source
        and specification.get("build_driver_sha256") == konclude_driver
        and specification.get("ontology_sha256") == record.get("ontology_sha256")
        and runtime.get("runtime_library_manifest_sha256") == konclude_runtime
        and runtime.get("ldd_sha256") == ldd
        and named_specification_is_intact(record, "reference_route_specification")
        and all_check_group_passes(record, "reference_runtime_checks")
        and all_check_group_passes(record, "reference_checks")
        and all_check_group_passes(record, "reference_fingerprint_checks")
        and isinstance(record.get("reference_fingerprint"), dict)
    )


def rebuilt_historical_is_success(
    record: dict,
    *,
    registry_row: dict[str, str],
    binary: str,
    source: str,
    receipt: str,
    test_receipt: str,
    source_identity: str,
    km_runtime: str,
    ldd: str,
    validator: str,
    validation_driver: str,
    runner: str,
    fingerprint: str,
    konclude: str,
    konclude_runtime: str,
    konclude_receipt: str,
    konclude_source: str,
    konclude_driver: str,
    hermit_oracle: str,
    hermit_java: str,
    hermit_build_receipt: str,
    hermit_classpath: str,
    hermit_jdk: str,
    hermit_jdk_symlinks: str,
    hermit_runtime: str,
) -> bool:
    parsed_environment = shlex.split(registry_row["route_environment"])
    state = registry_row["state"]
    expected_confirmation = {
        "exact_gold": "confirmed_exact_full_iri",
        "adjudicated_correct_stale_gold": (
            "confirmed_adjudicated_inconsistent"
        ),
    }.get(state)
    common = (
        record.get("confirmed") is True
        and record.get("confirmation_status") == expected_confirmation
        and record.get("validation_protocol") == REBUILT_HISTORICAL_PROTOCOL
        and record.get("documented_state") == state
        and record.get("documented_route") == registry_row["route"]
        and record.get("documented_source_revision")
        == registry_row["source_revision"]
        and record.get("ontology") == registry_row["ontology"]
        and record.get("ontology_sha256") == registry_row["ontology_sha256"]
        and capsule_matches(record, binary=binary, source=source, receipt=receipt)
        and registry_row.get("binary_sha256") == binary
        and registry_row.get("rebuild_source_manifest_sha256") == source
        and registry_row.get("rebuild_build_receipt_sha256") == receipt
        and registry_row.get("rebuild_test_receipt_sha256") == test_receipt
        and registry_row.get("rebuild_source_identity_sha256") == source_identity
        and registry_row.get("rebuild_runtime_manifest_sha256") == km_runtime
        and km_runtime_matches(record, km_runtime, ldd)
        and record.get("validator_sha256") == validator
        and record.get("validation_driver_sha256") == validation_driver
        and record.get("validation_driver_check") is True
        and record.get("runner_sha256") == runner
        and record.get("fingerprint_tool_sha256") == fingerprint
        and all_check_group_passes(record, "validator_environment_checks")
        and route_specification_is_intact(record)
        and current_route_label_is_intact(record)
        and record.get("route_observation_policy")
        == "closed-manual-environment"
        and (record.get("route_specification") or {}).get(
            "route_observation_policy"
        )
        == "closed-manual-environment"
        and record.get("route_observation_kind")
        == "closed_semantic_environment"
        and record.get("selected_route_trace_count") == 0
        and record.get("selected_route_trace") == ""
        and record.get("observed_route_identity")
        == record.get("current_route_label")
        and record.get("effective_route_request") == "manual"
        and record.get("parsed_environment") == parsed_environment
        and all_recorded_checks_pass(record)
    )
    if not common:
        return False
    if state == "exact_gold":
        return source_built_konclude_reference_is_current(
            record,
            konclude=konclude,
            konclude_runtime=konclude_runtime,
            konclude_receipt=konclude_receipt,
            konclude_source=konclude_source,
            konclude_driver=konclude_driver,
            ldd=ldd,
        )
    return state == "adjudicated_correct_stale_gold" and hermit_provenance_matches(
        record,
        oracle=hermit_oracle,
        java=hermit_java,
        build_receipt=hermit_build_receipt,
        classpath=hermit_classpath,
        jdk=hermit_jdk,
        jdk_symlinks=hermit_jdk_symlinks,
        runtime=hermit_runtime,
        ldd=ldd,
    )


def exact_candidate_is_success(
    record: dict,
    *,
    registry_row: dict[str, str],
    candidate: dict[str, str],
    ldd: str,
    validator: str,
    validation_driver: str,
    runner: str,
    fingerprint: str,
    konclude: str,
    konclude_runtime: str,
    konclude_receipt: str,
    konclude_source: str,
    konclude_driver: str,
) -> bool:
    parsed_environment = shlex.split(registry_row["route_environment"])
    return (
        record.get("confirmed") is True
        and record.get("confirmation_status") == "confirmed_exact_full_iri"
        and record.get("validation_protocol") == EXACT_CANDIDATE_PROTOCOL
        and record.get("documented_state") == "exact_gold"
        and record.get("documented_route") == registry_row["route"]
        and record.get("documented_source_revision")
        == registry_row["source_revision"]
        and record.get("ontology") == registry_row["ontology"]
        and record.get("ontology_sha256") == registry_row["ontology_sha256"]
        and capsule_matches(
            record,
            binary=candidate["binary_sha256"],
            source=candidate["source_manifest_sha256"],
            receipt=candidate["build_receipt_sha256"],
        )
        and registry_row.get("binary_sha256") == candidate["binary_sha256"]
        and registry_row.get("rebuild_candidate") == candidate["candidate"]
        and registry_row.get("rebuild_source_commit") == candidate["commit"]
        and registry_row.get("rebuild_source_manifest_sha256")
        == candidate["source_manifest_sha256"]
        and registry_row.get("rebuild_build_receipt_sha256")
        == candidate["build_receipt_sha256"]
        and registry_row.get("rebuild_test_receipt_sha256")
        == candidate["test_receipt_sha256"]
        and registry_row.get("rebuild_source_identity_sha256")
        == candidate["source_identity_sha256"]
        and registry_row.get("rebuild_runtime_manifest_sha256")
        == candidate["runtime_manifest_sha256"]
        and km_runtime_matches(
            record, candidate["runtime_manifest_sha256"], ldd
        )
        and record.get("validator_sha256") == validator
        and record.get("validation_driver_sha256") == validation_driver
        and record.get("validation_driver_check") is True
        and record.get("runner_sha256") == runner
        and record.get("fingerprint_tool_sha256") == fingerprint
        and all_check_group_passes(record, "validator_environment_checks")
        and route_specification_is_intact(record)
        and current_route_label_is_intact(record)
        and record.get("route_observation_policy") == "runtime-trace"
        and (record.get("route_specification") or {}).get(
            "route_observation_policy"
        )
        == "runtime-trace"
        and record.get("route_observation_kind") == "runtime_trace"
        and record.get("selected_route_trace_count") == 1
        and record.get("selected_route_trace") == registry_row["route"]
        and record.get("selected_route_traces") == [registry_row["route"]]
        and record.get("observed_route_identity") == registry_row["route"]
        and record.get("effective_route_request") == registry_row["route"]
        and record.get("parsed_environment") == parsed_environment
        and all_recorded_checks_pass(record)
        and source_built_konclude_reference_is_current(
            record,
            konclude=konclude,
            konclude_runtime=konclude_runtime,
            konclude_receipt=konclude_receipt,
            konclude_source=konclude_source,
            konclude_driver=konclude_driver,
            ldd=ldd,
        )
    )


def hermit_provenance_matches(
    record: dict,
    *,
    oracle: str,
    java: str,
    build_receipt: str,
    classpath: str,
    jdk: str,
    jdk_symlinks: str,
    runtime: str,
    ldd: str,
) -> bool:
    specification = record.get("hermit_route_specification") or {}
    return (
        record.get("hermit_oracle_sha256") == oracle
        and record.get("hermit_java_sha256") == java
        and record.get("hermit_build_receipt_sha256") == build_receipt
        and record.get("hermit_classpath_manifest_sha256") == classpath
        and record.get("hermit_jdk_manifest_sha256") == jdk
        and record.get("hermit_jdk_symlinks_sha256") == jdk_symlinks
        and record.get("hermit_runtime_stream_sha256") == runtime
        and (record.get("hermit_runtime") or {}).get("ldd_sha256") == ldd
        and named_specification_is_intact(record, "hermit_route_specification")
        and specification.get("ontology_sha256")
        == record.get("ontology_sha256")
        and record.get("hermit_ontology_sha256")
        == record.get("ontology_sha256")
        and (record.get("hermit_run") or {}).get("ontology_sha256")
        == record.get("ontology_sha256")
        and all_check_group_passes(record, "hermit_build_checks")
        and all_check_group_passes(record, "hermit_runtime_checks")
        and all_check_group_passes(record, "hermit_run_checks")
    )


def selected_is_current_success(
    record: dict,
    *,
    binary: str,
    source: str,
    receipt: str,
    km_runtime: str,
    ldd: str,
    validator: str,
    validation_driver: str,
    runner: str,
    fingerprint: str,
    konclude: str,
    konclude_runtime: str,
    konclude_receipt: str,
    konclude_source: str,
    konclude_driver: str,
    hermit_oracle: str,
    hermit_java: str,
    hermit_build_receipt: str,
    hermit_classpath: str,
    hermit_jdk: str,
    hermit_jdk_symlinks: str,
    hermit_runtime: str,
) -> bool:
    common = (
        record.get("confirmed") is True
        and record.get("confirmation_status") in SELECTED_SUCCESS
        and capsule_matches(record, binary=binary, source=source, receipt=receipt)
        and km_runtime_matches(record, km_runtime, ldd)
        and selected_tool_provenance_matches(
            record,
            validator=validator,
            validation_driver=validation_driver,
            runner=runner,
            fingerprint=fingerprint,
        )
        and route_specification_is_intact(record)
        and current_route_label_is_intact(record)
        and all_recorded_checks_pass(record)
        and record.get("selected_route_trace_count") == 1
        and record.get("selected_route_trace")
        == record.get("effective_route_request")
    )
    if not common:
        return False
    if record.get("confirmation_status") == "confirmed_exact_full_iri":
        return selected_reference_is_current(
            record,
            binary=binary,
            source=source,
            receipt=receipt,
            km_runtime=km_runtime,
            ldd=ldd,
            validator=validator,
            validation_driver=validation_driver,
            runner=runner,
            fingerprint=fingerprint,
            konclude=konclude,
            konclude_runtime=konclude_runtime,
            konclude_receipt=konclude_receipt,
            konclude_source=konclude_source,
            konclude_driver=konclude_driver,
        )
    return (
        record.get("documented_state") == "adjudicated_correct_stale_gold"
        and hermit_provenance_matches(
            record,
            oracle=hermit_oracle,
            java=hermit_java,
            build_receipt=hermit_build_receipt,
            classpath=hermit_classpath,
            jdk=hermit_jdk,
            jdk_symlinks=hermit_jdk_symlinks,
            runtime=hermit_runtime,
            ldd=ldd,
        )
    )


def alternative_is_current_success(
    record: dict,
    *,
    manifest_row: dict[str, str],
    manifest_sha256: str,
    selected_reference: dict,
    selected_reference_sha256: str,
    binary: str,
    source: str,
    receipt: str,
    km_runtime: str,
    ldd: str,
    validator: str,
    validation_driver: str,
    selected_validation_driver: str,
    shared_validator: str,
    runner: str,
    fingerprint: str,
    konclude: str,
    konclude_runtime: str,
    konclude_receipt: str,
    konclude_source: str,
    konclude_driver: str,
    slurm_array_job_ids: set[str],
) -> bool:
    return (
        record.get("confirmed") is True
        and record.get("confirmation_status") == ALTERNATIVE_SUCCESS
        and record.get("validation_protocol") == ALTERNATIVE_PROTOCOL
        and record.get("manifest_sha256") == manifest_sha256
        and record.get("expected_manifest_sha256") == manifest_sha256
        and record.get("selected_campaign_matches") is True
        and record.get("selected_registry_sha256")
        == manifest_row.get("selected_registry_sha256")
        and record.get("selected_summary_sha256")
        == manifest_row.get("selected_summary_sha256")
        and record.get("selected_result_manifest_sha256")
        == manifest_row.get("selected_result_manifest_sha256")
        and int(record.get("task_index", -1))
        == int(manifest_row["task_index"])
        and str(record.get("slurm_array_job_id", ""))
        in slurm_array_job_ids
        and record.get("ontology") == manifest_row["ontology"]
        and record.get("ontology_sha256")
        == record.get("expected_ontology_sha256")
        == manifest_row.get("ontology_sha256")
        and record.get("route") == manifest_row["route"]
        and record.get("validator_sha256") == validator
        and record.get("validation_driver_sha256") == validation_driver
        and record.get("validation_driver_check") is True
        and record.get("shared_validator_sha256") == shared_validator
        and record.get("runner_sha256") == runner
        and record.get("fingerprint_tool_sha256") == fingerprint
        and capsule_matches(record, binary=binary, source=source, receipt=receipt)
        and km_runtime_matches(record, km_runtime, ldd)
        and manifest_row.get("current_binary_sha256") == binary
        and manifest_row.get("current_source_manifest_sha256") == source
        and manifest_row.get("current_build_receipt_sha256") == receipt
        and record.get("reference_record_sha256")
        == manifest_row.get("fresh_reference_record_sha256")
        == selected_reference_sha256
        and record.get("ontology_sha256")
        == selected_reference.get("ontology_sha256")
        and record.get("reference_fingerprint")
        == selected_reference.get("reference_fingerprint")
        and record.get("reference_binary_sha256") == konclude
        and (record.get("reference_runtime") or {}).get(
            "runtime_library_manifest_sha256"
        )
        == konclude_runtime
        and named_specification_is_intact(
            record, "reference_route_specification"
        )
        and selected_reference_is_current(
            selected_reference,
            binary=binary,
            source=source,
            receipt=receipt,
            km_runtime=km_runtime,
            ldd=ldd,
            validator=shared_validator,
            validation_driver=selected_validation_driver,
            runner=runner,
            fingerprint=fingerprint,
            konclude=konclude,
            konclude_runtime=konclude_runtime,
            konclude_receipt=konclude_receipt,
            konclude_source=konclude_source,
            konclude_driver=konclude_driver,
        )
        and all_check_group_passes(record, "validator_environment_checks")
        and all_check_group_passes(record, "reference_provenance_checks")
        and route_specification_is_intact(record)
        and all_recorded_checks_pass(record)
        and record.get("selected_route_trace_count") == 1
        and record.get("selected_route_trace") == record.get("route")
        and record.get("parsed_environment")
        == [f"KM_ROUTE={record.get('route')}"]
    )


def result_record_manifest_sha256(
    paths: list[Path], *, root: Path
) -> tuple[int, str]:
    payload = bytearray()
    for path in paths:
        relative = path.relative_to(root)
        payload.extend(f"{sha256_file(path)}  {relative}\n".encode("utf-8"))
    return len(paths), hashlib.sha256(payload).hexdigest()


def load_bound_summary(path: Path, expected_sha256: str) -> tuple[dict, str]:
    observed = sha256_file(path)
    if observed != expected_sha256:
        raise SystemExit(
            f"aggregate summary hash mismatch for {path}: "
            f"expected {expected_sha256}, observed {observed}"
        )
    summary = load_json(path)
    if not isinstance(summary, dict):
        raise SystemExit(f"aggregate summary is not an object: {path}")
    return summary, observed


def require_summary_fields(summary: dict, expected: dict[str, object], label: str) -> None:
    failed = [
        key for key, value in expected.items() if summary.get(key) != value
    ]
    if failed:
        detail = {key: summary.get(key) for key in failed}
        raise SystemExit(f"{label} aggregate summary mismatch: {detail}")


def selected_structural_provenance_failures(summary: dict) -> set[str]:
    """Separate old aggregate terminology from actual provenance failures.

    The immutable selected summary used ``all_acceptance_checks`` for a
    provenance-valid negative route result.  No other marker is reclassified.
    """
    reported = summary.get("provenance_failures") or {}
    failed_claims = set(summary.get("failed_claims") or [])
    return {
        ontology
        for ontology, failures in reported.items()
        if failures != ["all_acceptance_checks"] or ontology not in failed_claims
    }


def terminal_route_attempt_detail(record: dict | None) -> dict:
    """Return a compact, machine-readable account of one negative attempt."""
    if record is None:
        return {"confirmation_status": "missing_fresh_record"}
    run = record.get("km_run") or {}
    stderr_tail = str(run.get("stderr_tail") or "").strip()
    error = str(record.get("error") or "").strip()
    detail = {
        "confirmation_status": record.get("confirmation_status", "unknown"),
        "run_status": run.get("status", ""),
        "return_code": run.get("return_code", ""),
        "wall_s": run.get("wall_s", ""),
        "peak_mb": run.get("peak_mb", ""),
    }
    if stderr_tail:
        detail["stderr_tail"] = stderr_tail[-1000:]
    elif error:
        detail["error_tail"] = error[-1000:]
    return detail


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--selected-result-dir", type=Path, required=True)
    parser.add_argument("--selected-summary-json", type=Path, required=True)
    parser.add_argument("--selected-summary-sha256", required=True)
    parser.add_argument("--selected-aggregator", type=Path, required=True)
    parser.add_argument("--alternative-result-dir", type=Path)
    parser.add_argument("--alternative-manifest", type=Path)
    parser.add_argument("--alternative-summary-json", type=Path)
    parser.add_argument("--alternative-summary-sha256")
    parser.add_argument("--alternative-aggregator", type=Path)
    parser.add_argument("--exact-candidate-result-dir", type=Path)
    parser.add_argument("--exact-candidate-registry", type=Path)
    parser.add_argument("--exact-candidate-registry-receipt", type=Path)
    parser.add_argument("--exact-candidate-capsules", type=Path)
    parser.add_argument("--exact-candidate-capsules-receipt", type=Path)
    parser.add_argument("--exact-candidate-summary-json", type=Path)
    parser.add_argument("--exact-candidate-summary-sha256")
    parser.add_argument("--exact-candidate-aggregator", type=Path)
    parser.add_argument("--rebuilt-historical-result-dir", type=Path)
    parser.add_argument("--rebuilt-historical-registry", type=Path)
    parser.add_argument("--rebuilt-historical-summary-json", type=Path)
    parser.add_argument("--rebuilt-historical-summary-sha256")
    parser.add_argument("--rebuilt-historical-aggregator", type=Path)
    parser.add_argument("--expected-binary-sha256", required=True)
    parser.add_argument("--expected-source-manifest-sha256", required=True)
    parser.add_argument("--expected-build-receipt-sha256", required=True)
    parser.add_argument("--expected-km-runtime-sha256", required=True)
    parser.add_argument("--expected-ldd-sha256", required=True)
    parser.add_argument("--expected-selected-validator-sha256", required=True)
    parser.add_argument("--expected-alternative-validator-sha256", required=True)
    parser.add_argument("--expected-selected-driver-sha256", required=True)
    parser.add_argument("--expected-alternative-driver-sha256", required=True)
    parser.add_argument("--expected-runner-sha256", required=True)
    parser.add_argument("--expected-fingerprint-tool-sha256", required=True)
    parser.add_argument("--expected-selected-aggregator-sha256", required=True)
    parser.add_argument("--expected-alternative-aggregator-sha256", required=True)
    parser.add_argument(
        "--expected-alternative-slurm-array-job-id", action="append"
    )
    parser.add_argument("--expected-exact-candidate-aggregator-sha256")
    parser.add_argument("--expected-exact-candidate-registry-generator-sha256")
    parser.add_argument("--expected-exact-candidate-capsules-generator-sha256")
    parser.add_argument("--expected-exact-candidate-source-verifier-sha256")
    parser.add_argument("--expected-exact-candidate-runtime-driver-sha256")
    parser.add_argument("--expected-exact-candidate-validator-sha256")
    parser.add_argument("--expected-exact-candidate-driver-sha256")
    parser.add_argument("--expected-exact-candidate-slurm-array-job-id")
    parser.add_argument("--expected-rebuilt-historical-binary-sha256")
    parser.add_argument("--expected-rebuilt-historical-source-manifest-sha256")
    parser.add_argument("--expected-rebuilt-historical-build-receipt-sha256")
    parser.add_argument("--expected-rebuilt-historical-test-receipt-sha256")
    parser.add_argument("--expected-rebuilt-historical-source-identity-sha256")
    parser.add_argument("--expected-rebuilt-historical-km-runtime-sha256")
    parser.add_argument("--expected-rebuilt-historical-validator-sha256")
    parser.add_argument("--expected-rebuilt-historical-driver-sha256")
    parser.add_argument("--expected-rebuilt-historical-aggregator-sha256")
    parser.add_argument("--expected-rebuilt-historical-slurm-array-job-id")
    parser.add_argument("--expected-selected-slurm-array-job-id", required=True)
    parser.add_argument("--expected-timeout", type=float, required=True)
    parser.add_argument("--expected-memcap-mb", type=int, required=True)
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
    parser.add_argument("--evidence-locator-prefix", default="")
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def evidence_locator(prefix: str, path: Path) -> str:
    return prefix + str(path)


def main() -> int:
    args = parse_args()
    with args.registry.open(newline="", encoding="utf-8") as handle:
        registry = list(csv.DictReader(handle, delimiter="\t"))
    if len(registry) != 592:
        raise SystemExit(f"registry has {len(registry)} rows, expected 592")
    if len({row["ontology"] for row in registry}) != len(registry):
        raise SystemExit("registry repeats ontology names")
    registry_sha = sha256_file(args.registry)

    selected_aggregator = args.selected_aggregator
    if sha256_file(selected_aggregator) != args.expected_selected_aggregator_sha256:
        raise SystemExit("selected aggregator differs from its pinned hash")
    selected_paths = [
        args.selected_result_dir / "results" / f"{row['ontology']}.json"
        for row in registry
    ]
    selected_present = [path for path in selected_paths if path.is_file()]
    selected_record_count, selected_record_manifest_sha = (
        result_record_manifest_sha256(
            selected_present, root=args.selected_result_dir
        )
    )
    selected_summary, selected_summary_sha = load_bound_summary(
        args.selected_summary_json, args.selected_summary_sha256
    )
    require_summary_fields(
        selected_summary,
        {
            "validation_protocol": SELECTED_PROTOCOL,
            "aggregator_sha256": args.expected_selected_aggregator_sha256,
            "registry_sha256": registry_sha,
            "registry_rows": len(registry),
            "result_records": selected_record_count,
            "result_record_manifest_count": selected_record_count,
            "result_record_manifest_sha256": selected_record_manifest_sha,
            "expected_binary_sha256": args.expected_binary_sha256,
            "expected_slurm_array_job_id": (
                args.expected_selected_slurm_array_job_id
            ),
            "expected_timeout": args.expected_timeout,
            "expected_memcap_mb": args.expected_memcap_mb,
            "expected_source_manifest_sha256": (
                args.expected_source_manifest_sha256
            ),
            "expected_build_receipt_sha256": args.expected_build_receipt_sha256,
            "expected_km_runtime_sha256": args.expected_km_runtime_sha256,
            "expected_ldd_sha256": args.expected_ldd_sha256,
            "expected_validator_sha256": (
                args.expected_selected_validator_sha256
            ),
            "expected_validation_driver_sha256": (
                args.expected_selected_driver_sha256
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
            "expected_hermit_oracle_sha256": (
                args.expected_hermit_oracle_sha256
            ),
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
        },
        "selected",
    )
    selected_failed_claims = set(selected_summary.get("failed_claims") or [])
    # The frozen selected-campaign aggregator predates the distinction between
    # provenance and a negative semantic result.  It reported an otherwise
    # provenance-valid timeout/limit result as ``all_acceptance_checks``.  Keep
    # the frozen summary binding used by the alternative campaign, but only
    # reinterpret that one exact marker for the same failed claim.
    selected_provenance_failures = selected_structural_provenance_failures(
        selected_summary
    )
    selected_claim_count = sum(
        row["state"] in SELECTED_CLAIMED_STATES for row in registry
    )
    if args.require_complete and (
        selected_summary.get("result_records") != len(registry)
        or selected_summary.get("confirmed_total")
        != selected_claim_count - len(selected_failed_claims)
        or selected_summary.get("missing_records")
        or selected_provenance_failures
    ):
        raise SystemExit("selected aggregate is not a complete provenance-valid replay")

    alternative_options = [
        args.alternative_result_dir,
        args.alternative_manifest,
        args.alternative_summary_json,
        args.alternative_summary_sha256,
        args.alternative_aggregator,
        args.expected_alternative_slurm_array_job_id,
    ]
    if any(value is not None for value in alternative_options) and not all(
        value is not None for value in alternative_options
    ):
        raise SystemExit(
            "alternative result directory, manifest, summary and summary hash "
            "must be supplied together"
        )
    if args.require_complete and not all(
        value is not None for value in alternative_options
    ):
        raise SystemExit("complete ledger requires alternative replay evidence")

    alternatives: dict[str, list[tuple[Path, dict[str, str]]]] = {}
    alternative_claims_by_ontology: dict[str, list[dict[str, str]]] = {}
    alternative_record_paths_by_index: dict[int, Path] = {}
    alternative_summary_sha = ""
    alternative_manifest_sha = ""
    alternative_provenance_failures: set[int] = set()
    alternative_failed_indices: set[int] = set()
    if args.alternative_result_dir is not None:
        alternative_aggregator = args.alternative_aggregator
        if (
            sha256_file(alternative_aggregator)
            != args.expected_alternative_aggregator_sha256
        ):
            raise SystemExit("alternative aggregator differs from its pinned hash")
        with args.alternative_manifest.open(
            newline="", encoding="utf-8"
        ) as handle:
            alternative_manifest = list(csv.DictReader(handle, delimiter="\t"))
        alternative_manifest_sha = sha256_file(args.alternative_manifest)
        manifest_by_index: dict[int, dict[str, str]] = {}
        for row in alternative_manifest:
            index = int(row["task_index"])
            if index in manifest_by_index:
                raise SystemExit(f"duplicate alternative task index: {index}")
            manifest_by_index[index] = row
            alternative_claims_by_ontology.setdefault(
                row["ontology"], []
            ).append(row)
        if sorted(manifest_by_index) != list(range(len(alternative_manifest))):
            raise SystemExit("alternative task indices are not contiguous from zero")

        alternative_paths: dict[int, Path] = {}
        result_root = args.alternative_result_dir
        for path in sorted(
            (result_root / "alternative-results").glob("*/*.json")
        ):
            prefix, separator, _ = path.name.partition("__")
            if not separator or len(prefix) != 5 or not prefix.isdigit():
                raise SystemExit(f"invalid alternative result filename: {path}")
            index = int(prefix)
            if index in alternative_paths:
                raise SystemExit(f"duplicate alternative result index: {index}")
            manifest_row = manifest_by_index.get(index)
            if manifest_row is None:
                raise SystemExit(f"alternative result has unknown index: {index}")
            alternative_paths[index] = path
            alternative_record_paths_by_index[index] = path
            alternatives.setdefault(manifest_row["ontology"], []).append(
                (path, manifest_row)
            )
        ordered_alternative_paths = [
            alternative_paths[index]
            for index in range(len(alternative_manifest))
            if index in alternative_paths
        ]
        alternative_record_count, alternative_record_manifest_sha = (
            result_record_manifest_sha256(
                ordered_alternative_paths, root=result_root
            )
        )
        alternative_summary, alternative_summary_sha = load_bound_summary(
            args.alternative_summary_json, args.alternative_summary_sha256
        )
        require_summary_fields(
            alternative_summary,
            {
                "validation_protocol": ALTERNATIVE_PROTOCOL,
                "aggregator_sha256": (
                    args.expected_alternative_aggregator_sha256
                ),
                "manifest_sha256": alternative_manifest_sha,
                "manifest_rows": len(alternative_manifest),
                "result_records": alternative_record_count,
                "result_record_manifest_count": alternative_record_count,
                "result_record_manifest_sha256": (
                    alternative_record_manifest_sha
                ),
                "expected_validator_sha256": (
                    args.expected_alternative_validator_sha256
                ),
                "expected_shared_validator_sha256": (
                    args.expected_selected_validator_sha256
                ),
                "expected_validation_driver_sha256": (
                    args.expected_alternative_driver_sha256
                ),
                "expected_selected_driver_sha256": (
                    args.expected_selected_driver_sha256
                ),
                "expected_runner_sha256": args.expected_runner_sha256,
                "expected_fingerprint_tool_sha256": (
                    args.expected_fingerprint_tool_sha256
                ),
                "expected_km_runtime_sha256": (
                    args.expected_km_runtime_sha256
                ),
                "expected_ldd_sha256": args.expected_ldd_sha256,
                "expected_binary_sha256": args.expected_binary_sha256,
                "expected_source_manifest_sha256": (
                    args.expected_source_manifest_sha256
                ),
                "expected_build_receipt_sha256": (
                    args.expected_build_receipt_sha256
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
                "expected_timeout": args.expected_timeout,
                "expected_memcap_mb": args.expected_memcap_mb,
                "expected_selected_registry_sha256": registry_sha,
                "expected_selected_summary_sha256": selected_summary_sha,
                "expected_selected_result_manifest_sha256": (
                    selected_record_manifest_sha
                ),
                "expected_slurm_array_job_ids": sorted(
                    args.expected_alternative_slurm_array_job_id
                ),
            },
            "alternative",
        )
        alternative_provenance_failures = {
            int(index)
            for index in (
                alternative_summary.get("provenance_failures") or {}
            )
        }
        alternative_failed_indices = {
            int(index)
            for index in (alternative_summary.get("failed_indices") or [])
        }
        if args.require_complete and (
            alternative_summary.get("campaign_complete") is not True
            or alternative_summary.get("result_records")
            != len(alternative_manifest)
            or alternative_summary.get("terminal_records")
            != len(alternative_manifest)
            or alternative_summary.get("missing_indices")
            or alternative_summary.get("nonterminal_indices")
            or alternative_summary.get("provenance_failures")
        ):
            raise SystemExit(
                "alternative aggregate is not a complete provenance-valid replay"
            )

    exact_candidate_options = [
        args.exact_candidate_result_dir,
        args.exact_candidate_registry,
        args.exact_candidate_registry_receipt,
        args.exact_candidate_capsules,
        args.exact_candidate_capsules_receipt,
        args.exact_candidate_summary_json,
        args.exact_candidate_summary_sha256,
        args.exact_candidate_aggregator,
        args.expected_exact_candidate_aggregator_sha256,
        args.expected_exact_candidate_registry_generator_sha256,
        args.expected_exact_candidate_capsules_generator_sha256,
        args.expected_exact_candidate_source_verifier_sha256,
        args.expected_exact_candidate_runtime_driver_sha256,
        args.expected_exact_candidate_validator_sha256,
        args.expected_exact_candidate_driver_sha256,
        args.expected_exact_candidate_slurm_array_job_id,
    ]
    if any(value is not None for value in exact_candidate_options) and not all(
        value is not None for value in exact_candidate_options
    ):
        raise SystemExit(
            "exact-candidate result, registry, capsule, summary and all "
            "expected tool identities must be supplied together"
        )
    if args.require_complete and not all(
        value is not None for value in exact_candidate_options
    ):
        raise SystemExit(
            "complete ledger requires exact-candidate replay evidence"
        )

    exact_candidate_by_ontology: dict[
        str, tuple[Path, dict, dict[str, str], dict[str, str]]
    ] = {}
    exact_candidate_summary_sha = ""
    exact_candidate_registry_sha = ""
    exact_candidate_registry_receipt_sha = ""
    exact_candidate_capsules_sha = ""
    exact_candidate_capsules_receipt_sha = ""
    exact_candidate_summary: dict = {}
    exact_candidate_index_by_ontology: dict[str, int] = {}
    exact_candidate_provenance_failures: set[str] = set()
    if args.exact_candidate_result_dir is not None:
        if (
            sha256_file(args.exact_candidate_aggregator)
            != args.expected_exact_candidate_aggregator_sha256
        ):
            raise SystemExit(
                "exact-candidate aggregator differs from its pinned hash"
            )
        exact_candidate_registry_sha = sha256_file(
            args.exact_candidate_registry
        )
        exact_candidate_capsules_sha = sha256_file(
            args.exact_candidate_capsules
        )
        exact_candidate_registry_receipt_sha = sha256_file(
            args.exact_candidate_registry_receipt
        )
        exact_candidate_capsules_receipt_sha = sha256_file(
            args.exact_candidate_capsules_receipt
        )
        with args.exact_candidate_registry.open(
            newline="", encoding="utf-8"
        ) as handle:
            exact_candidate_registry = list(
                csv.DictReader(handle, delimiter="\t")
            )
        with args.exact_candidate_capsules.open(
            newline="", encoding="utf-8"
        ) as handle:
            exact_candidate_capsules = list(
                csv.DictReader(handle, delimiter="\t")
            )
        if len(exact_candidate_registry) != 5:
            raise SystemExit(
                "exact-candidate replay registry must contain five rows"
            )
        if len(exact_candidate_capsules) != 3:
            raise SystemExit(
                "exact-candidate capsule registry must contain three rows"
            )
        exact_candidate_names = [
            row["ontology"] for row in exact_candidate_registry
        ]
        if len(set(exact_candidate_names)) != len(exact_candidate_names):
            raise SystemExit("exact-candidate replay registry repeats ontologies")
        candidate_by_label = {
            row["candidate"]: row for row in exact_candidate_capsules
        }
        if len(candidate_by_label) != len(exact_candidate_capsules):
            raise SystemExit("exact-candidate capsule registry repeats labels")
        main_by_name = {row["ontology"]: row for row in registry}
        for row in exact_candidate_registry:
            historical = main_by_name.get(row["ontology"])
            if historical is None:
                raise SystemExit(
                    f"exact-candidate registry has unknown ontology {row['ontology']}"
                )
            candidate = candidate_by_label.get(row["rebuild_candidate"])
            if candidate is None:
                raise SystemExit(
                    f"exact-candidate registry has unknown capsule "
                    f"{row['rebuild_candidate']}"
                )
            if (
                historical["state"] != "exact_gold"
                or row["state"] != historical["state"]
                or row["route"] != historical["route"]
                or row["historical_binary_sha256"]
                != historical["binary_sha256"]
                or row["historical_binary_locator"]
                != historical["binary_locator"]
                or row["historical_source_revision"]
                != historical["source_revision"]
                or row["historical_route_environment"]
                != historical["route_environment"]
                or row["historical_invocation"] != historical["invocation"]
                or row["selected_registry_sha256"] != registry_sha
                or row["rebuild_source_commit"] != candidate["commit"]
            ):
                raise SystemExit(
                    f"exact-candidate registry changed historical identity for "
                    f"{row['ontology']}"
                )

        exact_registry_receipt = load_json(
            args.exact_candidate_registry_receipt
        )
        exact_capsule_receipt = load_json(
            args.exact_candidate_capsules_receipt
        )
        require_summary_fields(
            exact_registry_receipt,
            {
                "status": "source_bound_exact_candidate_replay_registry",
                "rows": 5,
                "generator_sha256": (
                    args.expected_exact_candidate_registry_generator_sha256
                ),
                "selected_registry_sha256": registry_sha,
                "candidate_capsules_sha256": exact_candidate_capsules_sha,
                "output_sha256": exact_candidate_registry_sha,
            },
            "exact-candidate registry receipt",
        )
        require_summary_fields(
            exact_capsule_receipt,
            {
                "status": (
                    "source_bound_exact_candidate_capsules_with_runtime"
                ),
                "rows": 3,
                "generator_sha256": (
                    args.expected_exact_candidate_capsules_generator_sha256
                ),
                "output_sha256": exact_candidate_capsules_sha,
                "expected_source_verifier_sha256": (
                    args.expected_exact_candidate_source_verifier_sha256
                ),
                "expected_runtime_driver_sha256": (
                    args.expected_exact_candidate_runtime_driver_sha256
                ),
                "expected_ldd_sha256": args.expected_ldd_sha256,
            },
            "exact-candidate capsule receipt",
        )
        exact_capsule_checks = exact_capsule_receipt.get("checks") or {}
        if set(exact_capsule_checks) != set(candidate_by_label) or any(
            not isinstance(checks, dict)
            or not checks
            or not all(value is True for value in checks.values())
            for checks in exact_capsule_checks.values()
        ):
            raise SystemExit("exact-candidate capsule checks are incomplete")

        exact_candidate_paths = []
        for row_index, row in enumerate(exact_candidate_registry):
            path = (
                args.exact_candidate_result_dir
                / "results"
                / f"{row['ontology']}.json"
            )
            if not path.is_file():
                continue
            record = load_json(path)
            candidate = candidate_by_label[row["rebuild_candidate"]]
            exact_candidate_paths.append(path)
            exact_candidate_by_ontology[row["ontology"]] = (
                path,
                record,
                row,
                candidate,
            )
            exact_candidate_index_by_ontology[row["ontology"]] = row_index
        exact_record_count, exact_record_manifest_sha = (
            result_record_manifest_sha256(
                exact_candidate_paths,
                root=args.exact_candidate_result_dir,
            )
        )
        exact_candidate_summary, exact_candidate_summary_sha = (
            load_bound_summary(
                args.exact_candidate_summary_json,
                args.exact_candidate_summary_sha256,
            )
        )
        require_summary_fields(
            exact_candidate_summary,
            {
                "status": "verified_exact_candidate_replays",
                "validation_protocol": EXACT_CANDIDATE_PROTOCOL,
                "aggregator_sha256": (
                    args.expected_exact_candidate_aggregator_sha256
                ),
                "registry_sha256": exact_candidate_registry_sha,
                "registry_receipt_sha256": (
                    exact_candidate_registry_receipt_sha
                ),
                "registry_rows": len(exact_candidate_registry),
                "candidate_capsules_sha256": exact_candidate_capsules_sha,
                "candidate_capsules_receipt_sha256": (
                    exact_candidate_capsules_receipt_sha
                ),
                "candidate_binary_sha256": {
                    label: row["binary_sha256"]
                    for label, row in candidate_by_label.items()
                },
                "candidate_source_manifest_sha256": {
                    label: row["source_manifest_sha256"]
                    for label, row in candidate_by_label.items()
                },
                "candidate_build_receipt_sha256": {
                    label: row["build_receipt_sha256"]
                    for label, row in candidate_by_label.items()
                },
                "candidate_test_receipt_sha256": {
                    label: row["test_receipt_sha256"]
                    for label, row in candidate_by_label.items()
                },
                "candidate_source_identity_sha256": {
                    label: row["source_identity_sha256"]
                    for label, row in candidate_by_label.items()
                },
                "candidate_runtime_manifest_sha256": {
                    label: row["runtime_manifest_sha256"]
                    for label, row in candidate_by_label.items()
                },
                "result_records": exact_record_count,
                "result_record_manifest_count": exact_record_count,
                "result_record_manifest_sha256": exact_record_manifest_sha,
                "confirmed_exact_full_iri": len(exact_candidate_registry),
                "expected_selected_registry_sha256": registry_sha,
                "expected_slurm_array_job_id": (
                    args.expected_exact_candidate_slurm_array_job_id
                ),
                "expected_timeout": args.expected_timeout,
                "expected_memcap_mb": args.expected_memcap_mb,
                "expected_ldd_sha256": args.expected_ldd_sha256,
                "expected_source_verifier_sha256": (
                    args.expected_exact_candidate_source_verifier_sha256
                ),
                "expected_runtime_driver_sha256": (
                    args.expected_exact_candidate_runtime_driver_sha256
                ),
                "expected_validator_sha256": (
                    args.expected_exact_candidate_validator_sha256
                ),
                "expected_validation_driver_sha256": (
                    args.expected_exact_candidate_driver_sha256
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
                "successful": True,
            },
            "exact-candidate",
        )
        exact_candidate_provenance_failures = set(
            (exact_candidate_summary.get("provenance_failures") or {}).keys()
        )
        if args.require_complete and (
            exact_record_count != len(exact_candidate_registry)
            or exact_candidate_summary.get("missing_records")
            or exact_candidate_provenance_failures
        ):
            raise SystemExit(
                "exact-candidate aggregate is not a complete successful replay"
            )

    rebuilt_options = [
        args.rebuilt_historical_result_dir,
        args.rebuilt_historical_registry,
        args.rebuilt_historical_summary_json,
        args.rebuilt_historical_summary_sha256,
        args.rebuilt_historical_aggregator,
        args.expected_rebuilt_historical_binary_sha256,
        args.expected_rebuilt_historical_source_manifest_sha256,
        args.expected_rebuilt_historical_build_receipt_sha256,
        args.expected_rebuilt_historical_test_receipt_sha256,
        args.expected_rebuilt_historical_source_identity_sha256,
        args.expected_rebuilt_historical_km_runtime_sha256,
        args.expected_rebuilt_historical_validator_sha256,
        args.expected_rebuilt_historical_driver_sha256,
        args.expected_rebuilt_historical_aggregator_sha256,
        args.expected_rebuilt_historical_slurm_array_job_id,
    ]
    if any(value is not None for value in rebuilt_options) and not all(
        value is not None for value in rebuilt_options
    ):
        raise SystemExit(
            "rebuilt historical result, registry, summary, aggregator and "
            "all expected capsule hashes must be supplied together"
        )
    if args.require_complete and not all(
        value is not None for value in rebuilt_options
    ):
        raise SystemExit(
            "complete ledger requires exact-source historical replay evidence"
        )

    rebuilt_by_ontology: dict[str, tuple[Path, dict, dict[str, str]]] = {}
    rebuilt_index_by_ontology: dict[str, int] = {}
    rebuilt_summary_sha = ""
    rebuilt_registry_sha = ""
    rebuilt_provenance_failures: set[str] = set()
    if args.rebuilt_historical_result_dir is not None:
        if (
            sha256_file(args.rebuilt_historical_aggregator)
            != args.expected_rebuilt_historical_aggregator_sha256
        ):
            raise SystemExit(
                "rebuilt historical aggregator differs from its pinned hash"
            )
        with args.rebuilt_historical_registry.open(
            newline="", encoding="utf-8"
        ) as handle:
            rebuilt_registry = list(csv.DictReader(handle, delimiter="\t"))
        if len(rebuilt_registry) != 9:
            raise SystemExit(
                f"rebuilt historical registry has {len(rebuilt_registry)} "
                "rows, expected 9"
            )
        rebuilt_names = [row["ontology"] for row in rebuilt_registry]
        if len(set(rebuilt_names)) != len(rebuilt_names):
            raise SystemExit("rebuilt historical registry repeats ontologies")
        main_names = {row["ontology"] for row in registry}
        if not set(rebuilt_names).issubset(main_names):
            raise SystemExit("rebuilt historical registry has unknown ontology")
        rebuilt_exact = sum(
            row["state"] == "exact_gold" for row in rebuilt_registry
        )
        rebuilt_adjudicated = sum(
            row["state"] == "adjudicated_correct_stale_gold"
            for row in rebuilt_registry
        )
        if (rebuilt_exact, rebuilt_adjudicated) != (7, 2):
            raise SystemExit(
                "rebuilt historical registry must contain seven exact and "
                "two adjudicated rows"
            )
        rebuilt_registry_sha = sha256_file(args.rebuilt_historical_registry)
        rebuilt_paths = []
        for row_index, row in enumerate(rebuilt_registry):
            path = (
                args.rebuilt_historical_result_dir
                / "results"
                / f"{row['ontology']}.json"
            )
            if not path.is_file():
                continue
            record = load_json(path)
            if row["ontology"] in rebuilt_by_ontology:
                raise SystemExit(
                    f"duplicate rebuilt result: {row['ontology']}"
                )
            rebuilt_paths.append(path)
            rebuilt_by_ontology[row["ontology"]] = (path, record, row)
            rebuilt_index_by_ontology[row["ontology"]] = row_index
        rebuilt_record_count, rebuilt_record_manifest_sha = (
            result_record_manifest_sha256(
                rebuilt_paths, root=args.rebuilt_historical_result_dir
            )
        )
        rebuilt_summary, rebuilt_summary_sha = load_bound_summary(
            args.rebuilt_historical_summary_json,
            args.rebuilt_historical_summary_sha256,
        )
        require_summary_fields(
            rebuilt_summary,
            {
                "validation_protocol": SELECTED_PROTOCOL,
                "aggregator_sha256": (
                    args.expected_rebuilt_historical_aggregator_sha256
                ),
                "registry_sha256": rebuilt_registry_sha,
                "registry_rows": len(rebuilt_registry),
                "result_records": rebuilt_record_count,
                "result_record_manifest_count": rebuilt_record_count,
                "result_record_manifest_sha256": (
                    rebuilt_record_manifest_sha
                ),
                "expected_validation_protocol": (
                    REBUILT_HISTORICAL_PROTOCOL
                ),
                "expected_route_observation_policy": (
                    "closed-manual-environment"
                ),
                "expected_binary_sha256": (
                    args.expected_rebuilt_historical_binary_sha256
                ),
                "expected_source_manifest_sha256": (
                    args.expected_rebuilt_historical_source_manifest_sha256
                ),
                "expected_build_receipt_sha256": (
                    args.expected_rebuilt_historical_build_receipt_sha256
                ),
                "expected_km_runtime_sha256": (
                    args.expected_rebuilt_historical_km_runtime_sha256
                ),
                "expected_ldd_sha256": args.expected_ldd_sha256,
                "expected_validator_sha256": (
                    args.expected_rebuilt_historical_validator_sha256
                ),
                "expected_validation_driver_sha256": (
                    args.expected_rebuilt_historical_driver_sha256
                ),
                "expected_runner_sha256": args.expected_runner_sha256,
                "expected_fingerprint_tool_sha256": (
                    args.expected_fingerprint_tool_sha256
                ),
                "expected_slurm_array_job_id": (
                    args.expected_rebuilt_historical_slurm_array_job_id
                ),
                "expected_timeout": args.expected_timeout,
                "expected_memcap_mb": args.expected_memcap_mb,
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
                "expected_exact_full_iri": rebuilt_exact,
                "expected_adjudicated_inconsistent": rebuilt_adjudicated,
                "confirmed_exact_full_iri": rebuilt_exact,
                "confirmed_adjudicated_inconsistent": rebuilt_adjudicated,
            },
            "rebuilt historical",
        )
        rebuilt_provenance_failures = set(
            (rebuilt_summary.get("provenance_failures") or {}).keys()
        )
        if args.require_complete and (
            rebuilt_summary.get("successful") is not True
            or rebuilt_summary.get("confirmed_total") != len(rebuilt_registry)
            or rebuilt_summary.get("missing_records")
            or rebuilt_summary.get("failed_claims")
            or rebuilt_summary.get("provenance_failures")
        ):
            raise SystemExit(
                "rebuilt historical aggregate is not a complete successful replay"
            )

    output_rows = []
    for row_index, historical in enumerate(registry):
        ontology = historical["ontology"]
        selected_path = args.selected_result_dir / "results" / f"{ontology}.json"
        selected = load_json(selected_path) if selected_path.is_file() else None
        selected_success = (
            selected is not None
            and ontology not in selected_provenance_failures
            and selected.get("registry_sha256") == registry_sha
            and selected.get("row_index") == row_index
            and selected.get("row_count") == len(registry)
            and selected.get("ontology") == ontology
            and selected.get("ontology_sha256") == historical["ontology_sha256"]
            and selected.get("expected_ontology_sha256")
            == historical["ontology_sha256"]
            and selected.get("documented_state") == historical["state"]
            and selected.get("documented_route") == historical["route"]
            and selected_is_current_success(
                selected,
                binary=args.expected_binary_sha256,
                source=args.expected_source_manifest_sha256,
                receipt=args.expected_build_receipt_sha256,
                km_runtime=args.expected_km_runtime_sha256,
                ldd=args.expected_ldd_sha256,
                validator=args.expected_selected_validator_sha256,
                validation_driver=args.expected_selected_driver_sha256,
                runner=args.expected_runner_sha256,
                fingerprint=args.expected_fingerprint_tool_sha256,
                konclude=args.expected_konclude_sha256,
                konclude_runtime=args.expected_konclude_runtime_sha256,
                konclude_receipt=(
                    args.expected_konclude_build_receipt_sha256
                ),
                konclude_source=(
                    args.expected_konclude_source_manifest_sha256
                ),
                konclude_driver=(
                    args.expected_konclude_build_driver_sha256
                ),
                hermit_oracle=args.expected_hermit_oracle_sha256,
                hermit_java=args.expected_hermit_java_sha256,
                hermit_build_receipt=(
                    args.expected_hermit_build_receipt_sha256
                ),
                hermit_classpath=args.expected_hermit_classpath_sha256,
                hermit_jdk=args.expected_hermit_jdk_sha256,
                hermit_jdk_symlinks=(
                    args.expected_hermit_jdk_symlinks_sha256
                ),
                hermit_runtime=args.expected_hermit_runtime_sha256,
            )
        )

        rebuilt_item = rebuilt_by_ontology.get(ontology)
        rebuilt_path = rebuilt_record = rebuilt_row = None
        rebuilt_success = False
        if rebuilt_item is not None:
            rebuilt_path, rebuilt_record, rebuilt_row = rebuilt_item
            rebuilt_index = rebuilt_index_by_ontology[ontology]
            rebuilt_success = (
                ontology not in rebuilt_provenance_failures
                and rebuilt_record.get("registry_sha256")
                == rebuilt_registry_sha
                and rebuilt_record.get("row_index") == rebuilt_index
                and rebuilt_record.get("row_count") == len(rebuilt_registry)
                and rebuilt_row.get("state") == historical.get("state")
                and rebuilt_row.get("route") == historical.get("route")
                and rebuilt_row.get("historical_route_environment")
                == historical.get("route_environment")
                and rebuilt_row.get("historical_invocation")
                == historical.get("invocation")
                and rebuilt_row.get("historical_binary_sha256")
                == historical.get("binary_sha256")
                and rebuilt_row.get("historical_binary_locator")
                == historical.get("binary_locator")
                and rebuilt_row.get("historical_source_revision")
                == historical.get("source_revision")
                and rebuilt_historical_is_success(
                    rebuilt_record,
                    registry_row=rebuilt_row,
                    binary=(
                        args.expected_rebuilt_historical_binary_sha256
                    ),
                    source=(
                        args.expected_rebuilt_historical_source_manifest_sha256
                    ),
                    receipt=(
                        args.expected_rebuilt_historical_build_receipt_sha256
                    ),
                    test_receipt=(
                        args.expected_rebuilt_historical_test_receipt_sha256
                    ),
                    source_identity=(
                        args.expected_rebuilt_historical_source_identity_sha256
                    ),
                    km_runtime=(
                        args.expected_rebuilt_historical_km_runtime_sha256
                    ),
                    ldd=args.expected_ldd_sha256,
                    validator=(
                        args.expected_rebuilt_historical_validator_sha256
                    ),
                    validation_driver=(
                        args.expected_rebuilt_historical_driver_sha256
                    ),
                    runner=args.expected_runner_sha256,
                    fingerprint=args.expected_fingerprint_tool_sha256,
                    konclude=args.expected_konclude_sha256,
                    konclude_runtime=args.expected_konclude_runtime_sha256,
                    konclude_receipt=(
                        args.expected_konclude_build_receipt_sha256
                    ),
                    konclude_source=(
                        args.expected_konclude_source_manifest_sha256
                    ),
                    konclude_driver=(
                        args.expected_konclude_build_driver_sha256
                    ),
                    hermit_oracle=args.expected_hermit_oracle_sha256,
                    hermit_java=args.expected_hermit_java_sha256,
                    hermit_build_receipt=(
                        args.expected_hermit_build_receipt_sha256
                    ),
                    hermit_classpath=args.expected_hermit_classpath_sha256,
                    hermit_jdk=args.expected_hermit_jdk_sha256,
                    hermit_jdk_symlinks=(
                        args.expected_hermit_jdk_symlinks_sha256
                    ),
                    hermit_runtime=args.expected_hermit_runtime_sha256,
                )
            )

        exact_candidate_item = exact_candidate_by_ontology.get(ontology)
        exact_candidate_path = None
        exact_candidate_record = None
        exact_candidate_row = None
        exact_candidate_capsule = None
        exact_candidate_success = False
        if exact_candidate_item is not None:
            (
                exact_candidate_path,
                exact_candidate_record,
                exact_candidate_row,
                exact_candidate_capsule,
            ) = exact_candidate_item
            exact_candidate_index = exact_candidate_index_by_ontology[ontology]
            exact_candidate_success = (
                ontology not in exact_candidate_provenance_failures
                and exact_candidate_record.get("registry_sha256")
                == exact_candidate_registry_sha
                and exact_candidate_record.get("row_index")
                == exact_candidate_index
                and exact_candidate_record.get("row_count") == 5
                and exact_candidate_is_success(
                    exact_candidate_record,
                    registry_row=exact_candidate_row,
                    candidate=exact_candidate_capsule,
                    ldd=args.expected_ldd_sha256,
                    validator=(
                        args.expected_exact_candidate_validator_sha256
                    ),
                    validation_driver=(
                        args.expected_exact_candidate_driver_sha256
                    ),
                    runner=args.expected_runner_sha256,
                    fingerprint=args.expected_fingerprint_tool_sha256,
                    konclude=args.expected_konclude_sha256,
                    konclude_runtime=args.expected_konclude_runtime_sha256,
                    konclude_receipt=(
                        args.expected_konclude_build_receipt_sha256
                    ),
                    konclude_source=(
                        args.expected_konclude_source_manifest_sha256
                    ),
                    konclude_driver=(
                        args.expected_konclude_build_driver_sha256
                    ),
                )
            )

        valid_alternatives = []
        alternative_records_for_ontology: dict[int, dict] = {}
        for path, manifest_row in alternatives.get(ontology, []):
            task_index = int(manifest_row["task_index"])
            record = load_json(path)
            alternative_records_for_ontology[task_index] = record
            if (
                selected is None
                or task_index in alternative_provenance_failures
                or task_index in alternative_failed_indices
            ):
                continue
            if alternative_is_current_success(
                record,
                manifest_row=manifest_row,
                manifest_sha256=alternative_manifest_sha,
                selected_reference=selected,
                selected_reference_sha256=sha256_file(selected_path),
                binary=args.expected_binary_sha256,
                source=args.expected_source_manifest_sha256,
                receipt=args.expected_build_receipt_sha256,
                km_runtime=args.expected_km_runtime_sha256,
                ldd=args.expected_ldd_sha256,
                validator=args.expected_alternative_validator_sha256,
                validation_driver=args.expected_alternative_driver_sha256,
                selected_validation_driver=(
                    args.expected_selected_driver_sha256
                ),
                shared_validator=args.expected_selected_validator_sha256,
                runner=args.expected_runner_sha256,
                fingerprint=args.expected_fingerprint_tool_sha256,
                konclude=args.expected_konclude_sha256,
                konclude_runtime=args.expected_konclude_runtime_sha256,
                konclude_receipt=(
                    args.expected_konclude_build_receipt_sha256
                ),
                konclude_source=(
                    args.expected_konclude_source_manifest_sha256
                ),
                konclude_driver=(
                    args.expected_konclude_build_driver_sha256
                ),
                slurm_array_job_ids=set(
                    args.expected_alternative_slurm_array_job_id
                ),
            ):
                valid_alternatives.append((path, record))
        valid_alternatives.sort(
            key=lambda item: (
                float((item[1].get("km_run") or {}).get("wall_s", 1e30)),
                item[1].get("route", ""),
            )
        )
        valid_alternative_indices = {
            int(record["task_index"]) for _, record in valid_alternatives
        }
        alternative_failures = []
        alternative_failure_details = []
        for claim in alternative_claims_by_ontology.get(ontology, []):
            task_index = int(claim["task_index"])
            if task_index in valid_alternative_indices:
                continue
            failed_record = alternative_records_for_ontology.get(task_index)
            if failed_record is None:
                failed_path = alternative_record_paths_by_index.get(task_index)
                failed_record = (
                    load_json(failed_path) if failed_path is not None else None
                )
            status = (
                failed_record.get("confirmation_status", "unknown")
                if failed_record is not None
                else "missing_fresh_record"
            )
            alternative_failures.append(f"{claim['route']}:{status}")
            detail = {
                "task_index": task_index,
                "route": claim["route"],
                **terminal_route_attempt_detail(failed_record),
            }
            alternative_failure_details.append(detail)

        chosen_path = None
        chosen = None
        state = (
            "not_a_documented_solve_claim"
            if selected is not None
            and selected.get("confirmation_status")
            == "not_a_documented_solve_claim"
            else "not_reproduced"
        )
        route_label = ""
        requested_route = ""
        route_environment = ""
        chosen_origin = ""
        if selected_success:
            chosen_path = selected_path
            chosen = selected
            state = SELECTED_SUCCESS[selected["confirmation_status"]]
            route_label = selected.get("current_route_label", "")
            requested_route = selected.get("effective_route_request", "")
            route_environment = " ".join(selected.get("parsed_environment") or [])
            chosen_origin = "current_selected_route"
        elif valid_alternatives:
            chosen_path, chosen = valid_alternatives[0]
            state = "reproduced_exact_full_iri"
            route_label = chosen.get("route", "")
            requested_route = route_label
            route_environment = " ".join(chosen.get("parsed_environment") or [])
            chosen_origin = "current_alternative_route"
        elif exact_candidate_success:
            chosen_path, chosen = exact_candidate_path, exact_candidate_record
            state = "reproduced_exact_source_candidate_full_iri"
            route_label = chosen.get("current_route_label", "")
            requested_route = chosen.get("effective_route_request", "")
            route_environment = " ".join(chosen.get("parsed_environment") or [])
            chosen_origin = "exact_source_candidate_route"
        elif rebuilt_success:
            chosen_path, chosen = rebuilt_path, rebuilt_record
            state = (
                "reproduced_exact_source_historical_adjudicated_inconsistent"
                if chosen.get("confirmation_status")
                == "confirmed_adjudicated_inconsistent"
                else "reproduced_exact_source_historical_full_iri"
            )
            route_label = chosen.get("current_route_label", "")
            requested_route = chosen.get("effective_route_request", "")
            route_environment = " ".join(chosen.get("parsed_environment") or [])
            chosen_origin = "exact_source_historical_route"

        run = (chosen or {}).get("km_run") or {}
        build_receipt = (chosen or {}).get("build_receipt") or {}
        receipt_source = build_receipt.get("source") or {}
        receipt_input = build_receipt.get("build_input") or {}
        receipt_container = build_receipt.get("container") or {}
        receipt_toolchain = build_receipt.get("toolchain") or {}
        receipt_build = build_receipt.get("build") or {}
        km_fingerprint = (chosen or {}).get("km_fingerprint") or {}
        reference_fingerprint = (
            (chosen or {}).get("reference_fingerprint")
            or (chosen or {}).get("hermit_fingerprint")
            or {}
        )
        if chosen is not None and not reference_fingerprint and selected is not None:
            reference_fingerprint = selected.get("reference_fingerprint") or {}
        command = run.get("command") or []
        alternative_routes = [
            record.get("route", "") for _, record in valid_alternatives
        ]
        alternative_route_details = []
        for path, record in valid_alternatives:
            alternative_run = record.get("km_run") or {}
            alternative_route_details.append(
                {
                    "task_index": record.get("task_index", ""),
                    "route": record.get("route", ""),
                    "semantic_environment": record.get(
                        "parsed_environment", []
                    ),
                    "selected_route_trace": record.get(
                        "selected_route_trace", ""
                    ),
                    "route_specification_sha256": record.get(
                        "route_specification_sha256", ""
                    ),
                    "wall_s": alternative_run.get("wall_s", ""),
                    "peak_mb": alternative_run.get("peak_mb", ""),
                    "evidence_relative_path": str(
                        path.relative_to(args.alternative_result_dir)
                    ),
                }
            )
        failure_status = ""
        failure_detail = ""
        if chosen is None:
            if selected is None:
                failure_status = "missing_fresh_selected_record"
            else:
                failure_status = selected.get("confirmation_status", "unknown")
                failure_detail = selected.get("error", "")
            detail_parts = []
            if failure_detail:
                detail_parts.append(str(failure_detail))
            if alternative_failures:
                detail_parts.append(
                    "alternative routes: " + ",".join(alternative_failures)
                )
            if (
                exact_candidate_record is not None
                and not exact_candidate_success
            ):
                detail_parts.append(
                    "exact-source candidate replay: "
                    + exact_candidate_record.get(
                        "confirmation_status", "unknown"
                    )
                )
            if rebuilt_record is not None and not rebuilt_success:
                detail_parts.append(
                    "exact-source historical replay: "
                    + rebuilt_record.get("confirmation_status", "unknown")
                )
            failure_detail = "; ".join(detail_parts)
        adjudicated = (
            chosen is not None
            and chosen.get("confirmation_status")
            == "confirmed_adjudicated_inconsistent"
        )
        rebuilt_record_sha = (
            sha256_file(rebuilt_path) if rebuilt_path is not None else ""
        )
        rebuilt_confirmation_status = (
            rebuilt_record.get("confirmation_status", "")
            if rebuilt_record is not None
            else ""
        )
        exact_candidate_record_sha = (
            sha256_file(exact_candidate_path)
            if exact_candidate_path is not None
            else ""
        )
        exact_candidate_confirmation_status = (
            exact_candidate_record.get("confirmation_status", "")
            if exact_candidate_record is not None
            else ""
        )
        (
            route_observation_policy,
            route_observation_kind,
            observed_route_identity,
        ) = ledger_route_observation(chosen or {}, chosen_origin)

        output_rows.append(
            {
                "ontology": ontology,
                "ontology_sha256": (chosen or selected or {}).get(
                    "ontology_sha256", ""
                ),
                "current_state": state,
                "chosen_origin": chosen_origin,
                "route_label": route_label,
                "requested_route": requested_route,
                "selected_route_trace": (chosen or {}).get(
                    "selected_route_trace", ""
                ),
                "route_observation_policy": route_observation_policy,
                "route_observation_kind": route_observation_kind,
                "observed_route_identity": observed_route_identity,
                "route_environment": route_environment,
                "command_json": json.dumps(command, separators=(",", ":")),
                "route_specification_sha256": (chosen or {}).get(
                    "route_specification_sha256", ""
                ),
                "wall_s": run.get("wall_s", ""),
                "peak_mb": run.get("peak_mb", ""),
                "timeout_s": run.get("timeout_s", ""),
                "memory_limit_mb": run.get("memory_limit_mb", ""),
                "cpus": run.get("cpus", ""),
                "binary_sha256": (chosen or {}).get(
                    "actual_binary_sha256", ""
                ),
                "source_manifest_sha256": (chosen or {}).get(
                    "executed_source_manifest_sha256",
                    (chosen or {}).get("current_source_manifest_sha256", ""),
                ),
                "build_receipt_sha256": (chosen or {}).get(
                    "executed_build_receipt_sha256",
                    (chosen or {}).get("current_build_receipt_sha256", ""),
                ),
                "source_revision": (chosen or {}).get(
                    "documented_source_revision",
                    receipt_source.get("revision", ""),
                ),
                "source_identity_receipt_sha256": (
                    exact_candidate_capsule["source_identity_sha256"]
                    if chosen_origin == "exact_source_candidate_route"
                    else (
                        args.expected_rebuilt_historical_source_identity_sha256
                        if chosen_origin == "exact_source_historical_route"
                        else ""
                    )
                ),
                "test_receipt_sha256": (
                    exact_candidate_capsule["test_receipt_sha256"]
                    if chosen_origin == "exact_source_candidate_route"
                    else (
                        args.expected_rebuilt_historical_test_receipt_sha256
                        if chosen_origin == "exact_source_historical_route"
                        else ""
                    )
                ),
                "km_runtime_manifest_sha256": (
                    ((chosen or {}).get("km_runtime") or {}).get(
                        "runtime_library_manifest_sha256", ""
                    )
                ),
                "ldd_sha256": (
                    ((chosen or {}).get("km_runtime") or {}).get(
                        "ldd_sha256", ""
                    )
                ),
                "source_archive_sha256": receipt_source.get(
                    "archive_sha256", ""
                ),
                "cargo_lock_sha256": receipt_source.get(
                    "cargo_lock_sha256", ""
                ),
                "build_input_archive_sha256": receipt_input.get(
                    "archive_sha256", ""
                ),
                "build_input_manifest_sha256": receipt_input.get(
                    "manifest_sha256", ""
                ),
                "container_image_digest": receipt_container.get(
                    "image_digest", ""
                ),
                "rustc_version": str(
                    receipt_toolchain.get("rustc_version_verbose", "")
                ).splitlines()[0]
                if receipt_toolchain.get("rustc_version_verbose")
                else "",
                "rustc_path": receipt_toolchain.get("rustc_path", ""),
                "rustc_sha256": receipt_toolchain.get("rustc_sha256", ""),
                "cargo_version": str(
                    receipt_toolchain.get("cargo_version_verbose", "")
                ).splitlines()[0]
                if receipt_toolchain.get("cargo_version_verbose")
                else "",
                "cargo_path": receipt_toolchain.get("cargo_path", ""),
                "cargo_sha256": receipt_toolchain.get("cargo_sha256", ""),
                "rustup_path": receipt_toolchain.get("rustup_path", ""),
                "rustup_sha256": receipt_toolchain.get("rustup_sha256", ""),
                "build_driver_sha256": receipt_build.get(
                    "driver_sha256", ""
                ),
                "validator_sha256": (chosen or {}).get(
                    "validator_sha256", ""
                ),
                "validation_driver_sha256": (chosen or {}).get(
                    "validation_driver_sha256", ""
                ),
                "shared_validator_sha256": (chosen or {}).get(
                    "shared_validator_sha256", ""
                ),
                "runner_sha256": (chosen or {}).get("runner_sha256", ""),
                "fingerprint_tool_sha256": (chosen or {}).get(
                    "fingerprint_tool_sha256", ""
                ),
                "km_taxonomy_sha256": km_fingerprint.get(
                    "taxonomy_sha256", ""
                ),
                "reference_taxonomy_sha256": reference_fingerprint.get(
                    "taxonomy_sha256", ""
                ),
                "reference_kind": (
                    "hermit_full_ontology"
                    if adjudicated
                    else ("konclude_full_ontology" if chosen is not None else "")
                ),
                "reference_binary_sha256": (
                    chosen.get("hermit_oracle_sha256", "")
                    if adjudicated
                    else (
                        (chosen or {}).get("reference_binary_sha256")
                        or (selected or {}).get("reference_binary_sha256", "")
                    )
                ),
                "reference_source_sha256": (
                    chosen.get("hermit_ontology_sha256", "")
                    if adjudicated
                    else (chosen or {}).get("ontology_sha256", "")
                ),
                "reference_route_specification_sha256": (
                    (chosen or {}).get("hermit_route_specification_sha256", "")
                    if adjudicated
                    else (
                        (chosen or {}).get(
                            "reference_route_specification_sha256", ""
                        )
                        or (selected or {}).get(
                            "reference_route_specification_sha256", ""
                        )
                    )
                ),
                "reference_command_json": json.dumps(
                    (
                        (chosen or {}).get("hermit_route_specification", {})
                        if adjudicated
                        else (
                            (chosen or {}).get(
                                "reference_route_specification", {}
                            )
                            or (selected or {}).get(
                                "reference_route_specification", {}
                            )
                        )
                    ).get("command", []),
                    separators=(",", ":"),
                ),
                "reference_timeout_s": (
                    (
                        (chosen or {}).get("hermit_route_specification", {})
                        if adjudicated
                        else (
                            (chosen or {}).get(
                                "reference_route_specification", {}
                            )
                            or (selected or {}).get(
                                "reference_route_specification", {}
                            )
                        )
                    ).get("timeout_s", "")
                ),
                "reference_memory_limit_mb": (
                    (
                        (chosen or {}).get("hermit_route_specification", {})
                        if adjudicated
                        else (
                            (chosen or {}).get(
                                "reference_route_specification", {}
                            )
                            or (selected or {}).get(
                                "reference_route_specification", {}
                            )
                        )
                    ).get("memory_limit_mb", "")
                ),
                "reference_runtime_manifest_sha256": (
                    (chosen or {}).get("hermit_runtime_stream_sha256", "")
                    if adjudicated
                    else (
                        ((chosen or {}).get("reference_runtime") or {}).get(
                            "runtime_library_manifest_sha256", ""
                        )
                        or ((selected or {}).get("reference_runtime") or {}).get(
                            "runtime_library_manifest_sha256", ""
                        )
                    )
                ),
                "fresh_alternative_route_count": len(valid_alternatives),
                "fresh_alternative_routes": ",".join(alternative_routes),
                "fresh_alternative_route_details_json": json.dumps(
                    alternative_route_details, separators=(",", ":")
                ),
                "documented_alternative_route_count": len(
                    alternative_claims_by_ontology.get(ontology, [])
                ),
                "fresh_alternative_failure_count": len(alternative_failures),
                "fresh_alternative_failures": ",".join(
                    alternative_failures
                ),
                "fresh_alternative_failure_details_json": json.dumps(
                    alternative_failure_details, separators=(",", ":")
                ),
                "exact_candidate_route": (
                    exact_candidate_row.get("route", "")
                    if exact_candidate_row is not None
                    else ""
                ),
                "exact_candidate_route_environment": (
                    exact_candidate_row.get("route_environment", "")
                    if exact_candidate_row is not None
                    else ""
                ),
                "exact_candidate_confirmation_status": (
                    exact_candidate_confirmation_status
                ),
                "exact_candidate_confirmed": str(
                    exact_candidate_success
                ).lower(),
                "exact_candidate_label": (
                    exact_candidate_capsule.get("candidate", "")
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_commit": (
                    exact_candidate_capsule.get("commit", "")
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_record_sha256": exact_candidate_record_sha,
                "exact_candidate_registry_sha256": (
                    exact_candidate_registry_sha
                ),
                "exact_candidate_registry_receipt_sha256": (
                    exact_candidate_registry_receipt_sha
                ),
                "exact_candidate_capsules_sha256": exact_candidate_capsules_sha,
                "exact_candidate_capsules_receipt_sha256": (
                    exact_candidate_capsules_receipt_sha
                ),
                "exact_candidate_aggregate_summary_sha256": (
                    exact_candidate_summary_sha
                ),
                "exact_candidate_source_verifier_sha256": (
                    args.expected_exact_candidate_source_verifier_sha256 or ""
                ),
                "exact_candidate_runtime_driver_sha256": (
                    args.expected_exact_candidate_runtime_driver_sha256 or ""
                ),
                "exact_candidate_binary_sha256": (
                    exact_candidate_capsule.get("binary_sha256", "")
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_source_manifest_sha256": (
                    exact_candidate_capsule.get(
                        "source_manifest_sha256", ""
                    )
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_build_receipt_sha256": (
                    exact_candidate_capsule.get(
                        "build_receipt_sha256", ""
                    )
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_test_receipt_sha256": (
                    exact_candidate_capsule.get("test_receipt_sha256", "")
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_source_identity_sha256": (
                    exact_candidate_capsule.get(
                        "source_identity_sha256", ""
                    )
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_runtime_manifest_sha256": (
                    exact_candidate_capsule.get(
                        "runtime_manifest_sha256", ""
                    )
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_retained_source_archive_sha256": (
                    exact_candidate_capsule.get(
                        "retained_source_archive_sha256", ""
                    )
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_retained_git_archive_sha256": (
                    exact_candidate_capsule.get(
                        "retained_git_archive_sha256", ""
                    )
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "exact_candidate_capsule_git_archive_sha256": (
                    exact_candidate_capsule.get(
                        "capsule_git_archive_sha256", ""
                    )
                    if exact_candidate_capsule is not None
                    else ""
                ),
                "rebuilt_historical_route": (
                    rebuilt_row.get("route", "")
                    if rebuilt_row is not None
                    else ""
                ),
                "rebuilt_historical_route_environment": (
                    rebuilt_row.get("route_environment", "")
                    if rebuilt_row is not None
                    else ""
                ),
                "rebuilt_historical_confirmation_status": (
                    rebuilt_confirmation_status
                ),
                "rebuilt_historical_confirmed": str(
                    rebuilt_success
                ).lower(),
                "rebuilt_historical_record_sha256": rebuilt_record_sha,
                "rebuilt_historical_registry_sha256": rebuilt_registry_sha,
                "rebuilt_historical_aggregate_summary_sha256": (
                    rebuilt_summary_sha
                ),
                "rebuilt_historical_binary_sha256": (
                    args.expected_rebuilt_historical_binary_sha256
                    if rebuilt_row is not None
                    else ""
                ),
                "rebuilt_historical_source_manifest_sha256": (
                    args.expected_rebuilt_historical_source_manifest_sha256
                    if rebuilt_row is not None
                    else ""
                ),
                "rebuilt_historical_build_receipt_sha256": (
                    args.expected_rebuilt_historical_build_receipt_sha256
                    if rebuilt_row is not None
                    else ""
                ),
                "rebuilt_historical_test_receipt_sha256": (
                    args.expected_rebuilt_historical_test_receipt_sha256
                    if rebuilt_row is not None
                    else ""
                ),
                "rebuilt_historical_source_identity_sha256": (
                    args.expected_rebuilt_historical_source_identity_sha256
                    if rebuilt_row is not None
                    else ""
                ),
                "rebuilt_historical_runtime_manifest_sha256": (
                    args.expected_rebuilt_historical_km_runtime_sha256
                    if rebuilt_row is not None
                    else ""
                ),
                "selected_aggregate_summary_sha256": selected_summary_sha,
                "alternative_aggregate_summary_sha256": (
                    alternative_summary_sha
                ),
                "alternative_manifest_sha256": alternative_manifest_sha,
                "fresh_selected_record_sha256": (
                    sha256_file(selected_path) if selected is not None else ""
                ),
                "fresh_selected_confirmation_status": (
                    selected.get("confirmation_status", "")
                    if selected is not None
                    else ""
                ),
                "fresh_reference_record_sha256": (
                    (chosen or {}).get("reference_record_sha256", "")
                    if chosen_origin == "current_alternative_route"
                    else ""
                ),
                "evidence_locator": (
                    evidence_locator(args.evidence_locator_prefix, chosen_path)
                    if chosen_path is not None
                    else ""
                ),
                "evidence_sha256": (
                    sha256_file(chosen_path) if chosen_path is not None else ""
                ),
                "failure_status": failure_status,
                "failure_detail": failure_detail,
                "historical_state": historical["state"],
                "historical_route": historical["route"],
                "historical_route_kind": historical["route_kind"],
                "historical_route_environment": historical[
                    "route_environment"
                ],
                "historical_invocation": historical["invocation"],
                "historical_binary_sha256": historical["binary_sha256"],
                "historical_binary_locator": historical["binary_locator"],
                "historical_source_revision": historical["source_revision"],
                "historical_evidence": historical["evidence"],
            }
        )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = list(output_rows[0])
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, delimiter="\t")
        writer.writeheader()
        writer.writerows(output_rows)

    counts: dict[str, int] = {}
    for row in output_rows:
        counts[row["current_state"]] = counts.get(row["current_state"], 0) + 1
    print(json.dumps({"rows": len(output_rows), "states": counts}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
