#!/usr/bin/env python3
"""Fail-closed local audit for compact receipts from the frozen 80-case panels.

The adapter-specific Slurm compactor should emit one JSONL row per case using
KM-V151-COMPACT-CASE-V1 (see ``compact_row`` below). It must bind raw panel,
wrapper, fixture, and measurement-record hashes while omitting taxonomy bodies.
This script audits all 80 CLI rows and all 80 OWLAPI rows together. It never
opens reasoner output or semantic sidecars; those remain a separate Slurm audit.
"""
import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path


ARMS = (
    "candidate_retained",
    "candidate_fresh",
    "released_baseline_retained",
    "released_baseline_fresh",
)
ORDERS = (
    ARMS,
    (ARMS[1], ARMS[2], ARMS[3], ARMS[0]),
    (ARMS[2], ARMS[3], ARMS[0], ARMS[1]),
    (ARMS[3], ARMS[0], ARMS[1], ARMS[2]),
    (ARMS[0], ARMS[3], ARMS[1], ARMS[2]),
)
PROTOCOL_SHA256 = "fce89e1db19b49176ac2d389f73fc5f4cb41ad90dcd027f1660e7278c8210143"
SELECTION_SHA256 = "d51dff7640b82a84ccf22857532817c39c1952c9b6c7e2acd00ad4df6ab246e7"
MAX_UPDATE_RATIO = 0.8


def sha256(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def read_jsonl(path):
    rows = []
    with Path(path).open(encoding="utf-8") as stream:
        for line_no, line in enumerate(stream, 1):
            if line.strip():
                try:
                    rows.append(json.loads(line))
                except Exception as error:
                    raise ValueError(f"{path}:{line_no}: invalid JSONL row: {error}") from error
    return rows


def finite_wall(value):
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def valid_sha256(value):
    return (isinstance(value, str) and len(value) == 64
            and all(ch in "0123456789abcdef" for ch in value))


def effective_config_hash(projection):
    encoded = json.dumps(projection, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    return hashlib.sha256(encoded).hexdigest()


def compact_row(adapter, index, ontology, attempts, *, panel_status,
                semantic_audit_status, pins, limits, evidence,
                balanced_arm_orders=None):
    """Documented row shape for Slurm-side extraction; contains no taxonomies."""
    return {
        "schema": "km-v151-compact-case-v1",
        "adapter": adapter,
        "task_index": index,
        "fixture_id": ontology,
        "panel_status": panel_status,
        "semantic_audit_status": semantic_audit_status,
        "pins": pins,
        "limits": limits,
        "evidence": evidence,
        "balanced_arm_orders": balanced_arm_orders,
        "attempts": attempts,
    }


def audit_case(row, expected, pins, protocol_sha256=PROTOCOL_SHA256):
    """Validate one normalized case and recompute all timing acceptance rows."""
    errors = []

    def require(condition, reason):
        if not condition:
            errors.append(reason)

    adapter = row.get("adapter")
    require(adapter in ("cli", "owlapi"), "unknown adapter")
    require(row.get("schema") == "km-v151-compact-case-v1", "compact receipt schema mismatch")
    require(row.get("task_index") == expected["index"], "task index mismatch")
    require(row.get("fixture_id") == expected["id"], "ontology mapping mismatch")
    require(row.get("panel_status") in ("complete_execution_and_semantic_audit", "complete_execution_and_parity"),
            "panel execution/semantic status is not complete")
    require(row.get("compaction_errors", []) == [], "Slurm compactor recorded source/measurement integrity errors")
    require(row.get("semantic_audit_status") == "driver_reported_complete",
            "driver did not report completed semantic audit")
    require(row.get("pins", {}).get("protocol_sha256") == protocol_sha256, "protocol pin mismatch")
    require(row.get("pins", {}).get("candidate_binary_sha256") == pins["candidate"]["binary_sha256"],
            "candidate binary pin mismatch")
    require(row.get("pins", {}).get("candidate_source_manifest_sha256") == pins["candidate"]["source_manifest_sha256"],
            "candidate source pin mismatch")
    require(row.get("pins", {}).get("released_binary_sha256") == pins["released_baseline"]["binary_sha256"],
            "released binary pin mismatch")
    require(row.get("pins", {}).get("released_source_manifest_sha256") == pins["released_baseline"]["source_manifest_sha256"],
            "released source pin mismatch")
    for name in ("candidate", "released_baseline"):
        require(valid_sha256(pins.get(name, {}).get("binary_sha256")),
                f"missing valid {name} binary pin")
        require(valid_sha256(pins.get(name, {}).get("source_manifest_sha256")),
                f"missing valid {name} source-manifest pin")
    limits = row.get("limits", {})
    require(limits.get("cpu_threads") == 1 and limits.get("memory_mib") == 20480
            and limits.get("timeout_s") == 240, "runtime limits mismatch")
    evidence = row.get("evidence", {})
    for field in ("panel_sha256", "wrapper_record_sha256", "fixture_manifest_sha256",
                  "timing_summary_sha256", "binary_inventory_sha256", "input_plan_sha256"):
        require(valid_sha256(evidence.get(field)), f"missing or invalid evidence hash: {field}")
    expected_inventory = pins.get("inventory_sha256_by_adapter", {}).get(adapter)
    if expected_inventory:
        require(evidence.get("binary_inventory_sha256") == expected_inventory,
                "binary inventory evidence hash mismatch")
    if pins.get("input_plan_sha256"):
        require(evidence.get("input_plan_sha256") == pins["input_plan_sha256"],
                "materialized full80 input plan hash mismatch")

    revisions = expected["revisions"]
    require(len(revisions) == 9, "expected nine frozen revisions")
    require(all(r.get("expected_valid") is True for r in revisions),
            "full80 timing case contains an invalid revision")
    require(all(valid_sha256(r.get("raw_sha256")) for r in revisions),
            "full80 revision plan lacks a valid raw input hash")
    attempts = row.get("attempts", [])
    keys = [(a.get("arm"), a.get("repetition")) for a in attempts]
    wanted = {(arm, rep) for arm in ARMS for rep in range(5)}
    require(len(keys) == 20 and len(set(keys)) == 20 and set(keys) == wanted,
            "expected exactly 20 distinct attempts: four arms by five repetitions")
    wanted_orders = [list(order) for order in ORDERS]
    require(row.get("balanced_arm_orders") == wanted_orders,
            "recorded balanced arm orders do not match the frozen counterbalanced schedule")
    expected_sequence = [
        (rep, arm, order_position)
        for rep, order in enumerate(ORDERS)
        for order_position, arm in enumerate(order)
    ]
    actual_sequence = [(a.get("repetition"), a.get("arm"), a.get("order_position"))
                       for a in attempts]
    require(actual_sequence == expected_sequence,
            "attempt rows do not follow the frozen counterbalanced order and positions")
    by_key = {(a.get("arm"), a.get("repetition")): a for a in attempts}
    step_walls = {arm: [[] for _ in revisions] for arm in ARMS}
    session_walls = {arm: [] for arm in ARMS}
    attempt_summaries = []
    effective_configs = set()

    for arm in ARMS:
        for rep in range(5):
            attempt = by_key.get((arm, rep))
            if attempt is None:
                continue
            variant = "candidate" if arm.startswith("candidate_") else "released_baseline"
            require(attempt.get("binary_sha256") == pins[variant]["binary_sha256"],
                    f"{arm}/{rep}: binary hash mismatch")
            require(attempt.get("status") == "executed_unvalidated" and attempt.get("exit_code") == 0,
                    f"{arm}/{rep}: process did not exit successfully")
            require(attempt.get("remaining_processes") == [], f"{arm}/{rep}: remaining process tree")
            require(valid_sha256(attempt.get("measurement_record_sha256")),
                    f"{arm}/{rep}: missing measurement-record hash")
            require(valid_sha256(attempt.get("raw_output_sha256")),
                    f"{arm}/{rep}: missing raw-output hash")
            config_sha = attempt.get("effective_config_sha256")
            require(valid_sha256(config_sha), f"{arm}/{rep}: missing effective-config hash")
            config = attempt.get("effective_config_projection")
            require(isinstance(config, dict), f"{arm}/{rep}: missing normalized effective-config projection")
            if isinstance(config, dict):
                require(config_sha == effective_config_hash(config),
                        f"{arm}/{rep}: effective-config hash does not bind its recorded projection")
                require(config.get("km") == {"KM_ROUTE": "auto", "KM_THREADS": "1"},
                        f"{arm}/{rep}: KM environment differs from frozen explicit overrides")
                require(config.get("threading") == {"OMP_NUM_THREADS": "1", "RAYON_NUM_THREADS": "1"},
                        f"{arm}/{rep}: thread environment differs from frozen one-CPU config")
                require(config.get("java_opts") is None and
                        config.get("inherited_km_variables") == "stripped before applying explicit KM_CONFIG",
                        f"{arm}/{rep}: effective environment does not prove inherited switches were stripped")
                require(config.get("limits") == limits,
                        f"{arm}/{rep}: effective-config projection limits mismatch")
                if valid_sha256(config_sha):
                    effective_configs.add(config_sha)
            require(finite_wall(attempt.get("whole_session_wall_s")), f"{arm}/{rep}: invalid whole-session wall")
            session_walls[arm].append(attempt.get("whole_session_wall_s"))
            stages = attempt.get("revisions", [])
            require(len(stages) == len(revisions), f"{arm}/{rep}: missing revision rows")
            if len(stages) != len(revisions):
                attempt_summaries.append({"arm": arm, "repetition": rep, "valid": False})
                continue
            for index, (stage, expected_revision) in enumerate(zip(stages, revisions)):
                raw_hash = expected_revision.get("raw_sha256")
                require(stage.get("revision") == index, f"{arm}/{rep}: revision order mismatch at {index}")
                require(stage.get("expected_valid") is True, f"{arm}/{rep}/{index}: unexpected invalid revision")
                require(stage.get("status") == "executed_unvalidated" and stage.get("exit_code") == 0,
                        f"{arm}/{rep}/{index}: classification failed or incomplete")
                require(stage.get("source_sha256") == raw_hash, f"{arm}/{rep}/{index}: input hash mismatch")
                require(valid_sha256(stage.get("measurement_record_sha256")),
                        f"{arm}/{rep}/{index}: missing measurement-record hash")
                require(valid_sha256(stage.get("raw_output_sha256")),
                        f"{arm}/{rep}/{index}: missing raw-output hash")
                require(finite_wall(stage.get("wall_s")), f"{arm}/{rep}/{index}: invalid update wall")
                if finite_wall(stage.get("wall_s")):
                    step_walls[arm][index].append(stage["wall_s"])
            attempt_summaries.append({"arm": arm, "repetition": rep, "valid": True})

    update_rows = []
    require(len(effective_configs) == 1,
            "effective runtime configuration differs between arms/repetitions or is missing")
    for index, revision in enumerate(revisions):
        medians = {}
        pair_ratios = []
        counts = {arm: len(step_walls[arm][index]) for arm in ARMS}
        for arm in ARMS:
            values = step_walls[arm][index]
            medians[arm] = statistics.median(values) if len(values) == 5 else None
        retained = step_walls["candidate_retained"][index]
        fresh = step_walls["candidate_fresh"][index]
        if len(retained) == len(fresh) == 5 and all(finite_wall(x) for x in fresh) and all(x > 0 for x in fresh):
            pair_ratios = [a / b for a, b in zip(retained, fresh)]
        ratio = statistics.median(pair_ratios) if len(pair_ratios) == 5 else None
        # The criterion covers every non-initial revision, including additions,
        # deletions, restores, and mixed/successive transactions.
        applies = index > 0
        passed = (ratio is not None and ratio <= MAX_UPDATE_RATIO) if applies else None
        update_rows.append({
            "revision": index,
            "operation": revision.get("operation", "init" if index == 0 else "replace"),
            "update_threshold_applies": applies,
            "attempt_count_by_arm": counts,
            "median_wall_s_by_arm": medians,
            "candidate_retained_over_candidate_fresh_ratio_per_pair": pair_ratios,
            "median_candidate_retained_over_candidate_fresh_ratio": ratio,
            "passes_le_0_8": passed,
        })
        if applies:
            require(passed is True, f"revision {index}: candidate retained/fresh median exceeds 0.80 or is incomplete")

    session_medians = {
        arm: statistics.median(values) if len(values) == 5 and all(finite_wall(x) for x in values) else None
        for arm, values in session_walls.items()
    }
    cr = session_medians["candidate_retained"]
    cf = session_medians["candidate_fresh"]
    rf = session_medians["released_baseline_fresh"]
    whole_session_pass = cr is not None and cf is not None and rf is not None and cr < cf and cr < rf
    require(whole_session_pass, "candidate retained whole session does not beat both fresh arms or lacks five pairs")
    rr = session_medians["released_baseline_retained"]
    return {
        "adapter": adapter,
        "task_index": expected["index"],
        "fixture_id": expected["id"],
        "status": "pass" if not errors else "fail_or_unproven",
        "errors": errors,
        "attempts": attempt_summaries,
        "effective_config_sha256": next(iter(effective_configs)) if len(effective_configs) == 1 else None,
        "per_revision": update_rows,
        "whole_session_median_s_by_arm": session_medians,
        "candidate_retained_over_released_retained_session_ratio": cr / rr if cr is not None and rr else None,
        "whole_session_below_both_fresh": whole_session_pass,
        "semantic_evidence": "driver-reported only; semantic sidecars are not independently reprocessed by this compact audit",
    }


def audit_dataset(selection, input_plan, cli_rows, owl_rows, pins, protocol_sha256=PROTOCOL_SHA256):
    selected = selection.get("selected", [])
    expected_count = 80
    problems = []
    if input_plan.get("selection_sha256") != SELECTION_SHA256:
        problems.append("input plan does not bind frozen selection SHA-256")
    if len(selected) != expected_count or len({r.get("ontology") for r in selected}) != expected_count:
        problems.append("frozen selection must contain exactly 80 unique ontologies")
    planned = input_plan.get("fixtures", [])
    if len(planned) != expected_count or [r.get("index") for r in planned] != list(range(expected_count)):
        problems.append("input plan must bind all 80 ordered task indices")
    expected = []
    for index, selected_row in enumerate(selected):
        if index >= len(planned):
            continue
        plan_row = planned[index]
        ontology = selected_row.get("ontology")
        if plan_row.get("id") != ontology or plan_row.get("index") != index:
            problems.append(f"input plan selection mismatch at index {index}")
        expected.append({"index": index, "id": ontology, "revisions": plan_row.get("revisions", [])})

    def index_rows(rows, adapter):
        mapping = {}
        for row in rows:
            idx = row.get("task_index")
            if type(idx) is not int or idx in mapping:
                problems.append(f"{adapter}: invalid or duplicate compact row index {idx!r}")
            else:
                if row.get("adapter") != adapter:
                    problems.append(f"{adapter}: compact row {idx} claims adapter {row.get('adapter')!r}")
                mapping[idx] = row
        missing = sorted(set(range(expected_count)) - set(mapping))
        extra = sorted(set(mapping) - set(range(expected_count)))
        if missing:
            problems.append(f"{adapter}: missing case indices {missing}")
        if extra:
            problems.append(f"{adapter}: unexpected case indices {extra}")
        return mapping

    indexed = {"cli": index_rows(cli_rows, "cli"), "owlapi": index_rows(owl_rows, "owlapi")}
    cases = []
    for adapter in ("cli", "owlapi"):
        for item in expected:
            row = indexed[adapter].get(item["index"])
            if row is None:
                continue
            result = audit_case(row, item, pins, protocol_sha256)
            cases.append(result)
            if result["status"] != "pass":
                problems.append({"adapter": adapter, "index": item["index"], "fixture_id": item["id"],
                                 "errors": result["errors"]})
    expected_case_count = 2 * expected_count
    if len(cases) != expected_case_count:
        problems.append(f"audited {len(cases)} of {expected_case_count} adapter/case rows")
    update_rows = [r for c in cases for r in c["per_revision"] if r["update_threshold_applies"]]
    passed_updates = sum(r["passes_le_0_8"] is True for r in update_rows)
    return {
        "schema": 1,
        "status": "pass_provisional_timing_only" if not problems and len(update_rows) == 2 * 80 * 8 else "fail_or_unproven",
        "scope": "80 fixed ontologies, CLI and OWLAPI, five paired repetitions, four arms, nine revisions",
        "protocol_sha256": protocol_sha256,
        "selection_sha256": input_plan.get("selection_sha256"),
        "case_count_by_adapter": {"cli": len(cli_rows), "owlapi": len(owl_rows)},
        "update_rows_expected": 2 * 80 * 8,
        "update_rows_passed": passed_updates,
        "whole_session_rows_passed": sum(c["whole_session_below_both_fresh"] for c in cases),
        "cases": cases,
        "problems": problems,
        "semantic_limit": "Timing only: the compact audit checks driver-reported semantic completion but does not independently reopen taxonomy/rollback sidecars. Slurm-side semantic verification must pass before any correctness conclusion.",
    }


def normalize_inventory_pins(cli_inventory, owl_bindings):
    """Read and compare explicit CLI/OWLAPI binary and native-source pins."""
    cli_arms = cli_inventory.get("arms", cli_inventory.get("variants", {}))
    owl_arms = owl_bindings.get("variants", owl_bindings.get("arms", {}))

    def pin(arms, name, *, owl=False):
        raw = arms.get(name, {})
        binary = raw.get("sha256", raw.get("binary_sha256"))
        source = raw.get("source_manifest_sha256", raw.get("native_source_manifest_sha256"))
        # Some OWLAPI inventories bind the native source hash only through a
        # path/hash pair in `files`; resolve that exact manifest file rather
        # than borrowing the CLI arm's hash.
        if owl:
            source_path = raw.get("native_source_manifest", raw.get("source_manifest_path"))
            files = owl_bindings.get("files", {})
            if isinstance(source_path, str) and isinstance(files, dict) and source_path in files:
                mapped_source = files[source_path]
                if source and source != mapped_source:
                    raise ValueError(f"OWLAPI {name} source hash conflicts with its bound files-map entry")
                if not source:
                    source = mapped_source
        return {"binary_sha256": binary, "source_manifest_sha256": source}

    cli_candidate = pin(cli_arms, "candidate")
    cli_release = pin(cli_arms, "released_baseline")
    owl_candidate = pin(owl_arms, "candidate", owl=True)
    owl_release = pin(owl_arms, "released_baseline", owl=True)
    all_pins = (("CLI candidate", cli_candidate), ("CLI release", cli_release),
                ("OWLAPI candidate", owl_candidate), ("OWLAPI release", owl_release))
    for label, binding in all_pins:
        if not valid_sha256(binding.get("binary_sha256")):
            raise ValueError(f"{label} binding lacks an explicit valid binary SHA-256")
        if not valid_sha256(binding.get("source_manifest_sha256")):
            raise ValueError(f"{label} binding lacks an explicit verified source-manifest SHA-256")
    if cli_candidate != owl_candidate or cli_release != owl_release:
        raise ValueError("CLI and OWLAPI bindings do not refer to the same binaries and source manifests")
    return {"candidate": cli_candidate, "released_baseline": cli_release}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--input-plan", type=Path, required=True)
    parser.add_argument("--protocol", type=Path, required=True)
    parser.add_argument("--cli-inventory", type=Path, required=True)
    parser.add_argument("--owlapi-bindings", type=Path, required=True)
    parser.add_argument("--cli-jsonl", type=Path, required=True,
                        help="80 compact rows emitted by Slurm-side CLI extraction")
    parser.add_argument("--owlapi-jsonl", type=Path, required=True,
                        help="80 compact rows emitted by Slurm-side OWLAPI extraction")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    protocol_sha = sha256(args.protocol)
    if protocol_sha != PROTOCOL_SHA256:
        raise SystemExit(f"unexpected frozen acceptance protocol hash {protocol_sha}")
    if sha256(args.selection) != SELECTION_SHA256:
        raise SystemExit("unexpected frozen 80-case selection file hash")
    cli_inventory = read_json(args.cli_inventory)
    owl_bindings = read_json(args.owlapi_bindings)
    try:
        normalized_pins = normalize_inventory_pins(cli_inventory, owl_bindings)
    except ValueError as error:
        raise SystemExit(str(error)) from error
    pins = {**normalized_pins,
            "inventory_sha256_by_adapter": {"cli": sha256(args.cli_inventory),
                                             "owlapi": sha256(args.owlapi_bindings)},
            "input_plan_sha256": sha256(args.input_plan)}
    result = audit_dataset(read_json(args.selection), read_json(args.input_plan),
                           read_jsonl(args.cli_jsonl), read_jsonl(args.owlapi_jsonl), pins, protocol_sha)
    if result.get("selection_sha256") != SELECTION_SHA256:
        raise SystemExit("input plan does not bind the frozen 80-case selection")
    result["input_plan_sha256"] = sha256(args.input_plan)
    if args.output.exists():
        raise SystemExit(f"refusing to overwrite existing audit output: {args.output}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "cases": result["case_count_by_adapter"],
                      "updates_passed": result["update_rows_passed"],
                      "updates_expected": result["update_rows_expected"],
                      "whole_session_passed": result["whole_session_rows_passed"],
                      "output": str(args.output)}, sort_keys=True))
    if result["status"] != "pass_provisional_timing_only":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
