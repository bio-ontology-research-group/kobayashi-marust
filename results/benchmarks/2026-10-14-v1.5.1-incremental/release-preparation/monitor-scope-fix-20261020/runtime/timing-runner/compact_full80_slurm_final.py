#!/usr/bin/env python3
"""Stream compact full80 panel evidence on Slurm compute nodes.

This producer reads the real CLI and OWLAPI panel/measurement schemas. It
extracts timing and environment fields, checks the recorded arm schedule, and
streams hashes of output/semantic artifacts. It never parses taxonomy vectors
and does not turn driver status flags into an independent semantic proof.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from audit_full80_compact import (ARMS, ORDERS, PROTOCOL_SHA256, SELECTION_SHA256,
                                 compact_row, effective_config_hash, read_json,
                                 sha256, valid_sha256)


PANEL_FIELDS = {
    "status", "balanced_arm_orders", "repetitions", "protocol_sha256",
    "binary_inventory_sha256", "fixture_manifest_sha256", "km_overrides",
    "cpu_threads", "memory_mib", "timeout_s", "binding_sha256", "fixtures_sha256",
    "attempts",
}
ATTEMPT_FIELDS = {
    "arm", "repetition", "fixture_id", "output", "status", "measurement_path",
    "measurement_sha256", "binary_sha256", "binary_path", "binary_inventory_binding",
    "order_position", "record_sha256",
}
COMPLETED_PANEL_STATES = {
    "complete_execution_and_semantic_audit", "complete_execution_and_parity",
}


class JsonStream:
    """Minimal streaming JSON reader with selective object-field retention."""
    def __init__(self, path):
        self.stream = Path(path).open("rb")
        self.chunk = b""
        self.offset = 0

    def _fill(self):
        if self.offset >= len(self.chunk):
            self.chunk = self.stream.read(1 << 16)
            self.offset = 0
            return bool(self.chunk)
        return True

    def peek(self):
        return self.chunk[self.offset:self.offset + 1] if self._fill() else b""

    def get(self):
        if not self._fill():
            return b""
        out = self.chunk[self.offset:self.offset + 1]
        self.offset += 1
        return out

    def ws(self):
        while self.peek() in (b" ", b"\t", b"\r", b"\n"):
            self.get()

    def read_string(self):
        if self.get() != b'"':
            raise ValueError("expected JSON string")
        parts = [b'"']
        escaped = False
        while True:
            if not self._fill():
                raise ValueError("truncated JSON string")
            # Search within the current buffer, handling escapes without
            # copying unrelated large values into memory.
            buf = self.chunk
            i = self.offset
            while i < len(buf):
                c = buf[i]
                i += 1
                if escaped:
                    escaped = False
                elif c == 0x5c:
                    escaped = True
                elif c == 0x22:
                    parts.append(buf[self.offset:i])
                    self.offset = i
                    return json.loads(b"".join(parts))
            parts.append(buf[self.offset:])
            self.offset = len(buf)

    def skip_string_tail(self):
        escaped = False
        while True:
            if not self._fill():
                raise ValueError("truncated JSON string")
            buf = self.chunk
            i = self.offset
            while i < len(buf):
                c = buf[i]
                i += 1
                if escaped:
                    escaped = False
                elif c == 0x5c:
                    escaped = True
                elif c == 0x22:
                    self.offset = i
                    return
            self.offset = len(buf)

    def skip_value(self):
        self.ws()
        first = self.peek()
        if first == b'"':
            self.get()
            self.skip_string_tail()
            return
        if first in (b"{", b"["):
            stack = [b"}" if first == b"{" else b"]"]
            self.get()
            in_string = False
            escaped = False
            while stack:
                if not self._fill():
                    raise ValueError("truncated nested JSON value")
                buf = self.chunk
                start = self.offset
                if in_string and escaped:
                    # This byte is the character escaped by the preceding slash.
                    self.offset += 1
                    escaped = False
                    continue
                needles = b'"\\' if in_string else b'"{}[]'
                positions = [pos for needle in needles
                             if (pos := buf.find(bytes([needle]), start)) >= 0]
                if not positions:
                    self.offset = len(buf)
                    continue
                pos = min(positions)
                c = buf[pos:pos + 1]
                self.offset = pos + 1
                if in_string and c == b"\\":
                    escaped = True
                elif in_string and c == b'"':
                    in_string = False
                elif not in_string and c == b'"':
                    in_string = True
                elif not in_string and c == b"{":
                    stack.append(b"}")
                elif not in_string and c == b"[":
                    stack.append(b"]")
                elif not in_string and c in (b"}", b"]"):
                    if not stack or c != stack[-1]:
                        raise ValueError("mismatched JSON delimiter")
                    stack.pop()
            return
        while self.peek() and self.peek() not in (b",", b"]", b"}", b" ", b"\t", b"\r", b"\n"):
            self.get()

    def value(self):
        self.ws()
        first = self.peek()
        if first == b'"':
            return self.read_string()
        if first == b"{":
            self.get()
            result = {}
            self.ws()
            if self.peek() == b"}":
                self.get()
                return result
            while True:
                self.ws()
                key = self.read_string()
                self.ws()
                if self.get() != b":":
                    raise ValueError("expected colon in JSON object")
                result[key] = self.value()
                self.ws()
                sep = self.get()
                if sep == b"}":
                    return result
                if sep != b",":
                    raise ValueError("expected comma in JSON object")
        if first == b"[":
            self.get()
            result = []
            self.ws()
            if self.peek() == b"]":
                self.get()
                return result
            while True:
                result.append(self.value())
                self.ws()
                sep = self.get()
                if sep == b"]":
                    return result
                if sep != b",":
                    raise ValueError("expected comma in JSON array")
        token = bytearray()
        while self.peek() and self.peek() not in (b",", b"]", b"}", b" ", b"\t", b"\r", b"\n"):
            token.extend(self.get())
        if not token:
            raise ValueError("expected JSON value")
        return json.loads(bytes(token))

    def selected_object(self, keep, *, attempt=False):
        if self.get() != b"{":
            raise ValueError("expected JSON object")
        result = {}
        self.ws()
        if self.peek() == b"}":
            self.get()
            return result
        while True:
            self.ws()
            key = self.read_string()
            self.ws()
            if self.get() != b":":
                raise ValueError("expected colon in JSON object")
            if key in keep:
                result[key] = self.value()
            else:
                self.skip_value()
            self.ws()
            sep = self.get()
            if sep == b"}":
                return result
            if sep != b",":
                raise ValueError("expected comma in JSON object")

    def attempts_array(self):
        self.ws()
        if self.get() != b"[":
            raise ValueError("attempts must be an array")
        rows = []
        self.ws()
        if self.peek() == b"]":
            self.get()
            return rows
        while True:
            self.ws()
            rows.append(self.selected_object(ATTEMPT_FIELDS, attempt=True))
            self.ws()
            sep = self.get()
            if sep == b"]":
                return rows
            if sep != b",":
                raise ValueError("expected comma in attempts array")

    def panel(self):
        if self.get() != b"{":
            raise ValueError("panel must be an object")
        result = {}
        self.ws()
        if self.peek() == b"}":
            self.get()
            return result
        while True:
            self.ws()
            key = self.read_string()
            self.ws()
            if self.get() != b":":
                raise ValueError("expected colon in panel")
            if key == "attempts":
                result[key] = self.attempts_array()
            elif key in PANEL_FIELDS:
                result[key] = self.value()
            else:
                self.skip_value()
            self.ws()
            sep = self.get()
            if sep == b"}":
                return result
            if sep != b",":
                raise ValueError("expected comma in panel")


def stream_panel(path):
    scanner = JsonStream(path)
    try:
        value = scanner.panel()
        scanner.ws()
        if scanner.peek():
            raise ValueError("trailing bytes after panel JSON")
        return value
    finally:
        scanner.stream.close()


def hash_file(path):
    digest = hashlib.sha256()
    size = 0
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
            size += len(block)
    return {"path": str(Path(path).resolve()), "bytes": size, "sha256": digest.hexdigest()}


def canonical_hash(value):
    raw = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
    return hashlib.sha256(raw).hexdigest()


def resolved(value, manifest_path):
    path = Path(value)
    return path.resolve() if path.is_absolute() else (Path(manifest_path).resolve().parent / path).resolve()


def adapter_pins(adapter, inventory):
    if adapter == "cli":
        rows = inventory.get("arms", inventory.get("variants", {}))
        file_map = {}
    else:
        rows = inventory.get("variants", inventory.get("arms", {}))
        file_map = inventory.get("files", {})
    result = {}
    for variant in ("candidate", "released_baseline"):
        row = rows.get(variant, {})
        binary = row.get("sha256", row.get("binary_sha256"))
        source = row.get("source_manifest_sha256", row.get("native_source_manifest_sha256"))
        source_path = row.get("native_source_manifest", row.get("source_manifest_path"))
        if adapter == "owlapi" and isinstance(source_path, str) and isinstance(file_map, dict) and source_path in file_map:
            map_hash = file_map[source_path]
            if source and source != map_hash:
                raise ValueError(f"{variant}: source manifest SHA conflicts with bound files map")
            source = source or map_hash
        if not valid_sha256(binary) or not valid_sha256(source):
            raise ValueError(f"{adapter} inventory has incomplete {variant} binary/source pins")
        result[variant] = {"binary_sha256": binary, "source_manifest_sha256": source}
    return result


def env_projection(environment, record, adapter):
    if not isinstance(environment, dict):
        raise ValueError("measurement record has no captured effective environment")
    if adapter == "owlapi":
        cpu_threads = 1 if type(record.get("cpu")) is int else None
        timeout = record.get("timeout_per_revision_s")
    else:
        cpu_threads = record.get("cpu_threads")
        if cpu_threads is None and isinstance(record.get("cpu_affinity"), list):
            cpu_threads = len(record["cpu_affinity"])
        timeout = record.get("timeout_per_revision_s", record.get("timeout_s"))
    limits = {"cpu_threads": cpu_threads, "memory_mib": record.get("memory_mib"), "timeout_s": timeout}
    projection = {key: environment.get(key) for key in
                  ("km", "threading", "java_opts", "inherited_km_variables")}
    projection["limits"] = limits
    # These settings affect the public adapter workload while avoiding binary
    # and classpath paths, which are pinned separately by immutable hashes.
    if adapter == "owlapi":
        projection["adapter_runtime"] = {"adapter": "owlapi", "heap": record.get("heap")}
    else:
        projection["adapter_runtime"] = {"adapter": "cli"}
    return projection


def finite_wall(value):
    return type(value) in (float, int) and math.isfinite(value) and value >= 0


def load_measurement_record(adapter, attempt, output_path, revision, label):
    arm = attempt.get("arm", "")
    retained = arm.endswith("_retained")
    if adapter == "owlapi":
        path = output_path / "record.json"
    elif retained:
        value = attempt.get("measurement_path")
        path = Path(value) if value else output_path / "record.json"
    else:
        path = output_path / f"revision-{revision:03d}-{label}" / "record.json"
    if not path.is_file():
        return None, path
    return read_json(path), path


def raw_artifact_path(adapter, attempt, output_path, revision, label):
    if adapter == "owlapi":
        return output_path / "session" / f"{revision:03d}.taxonomy.tsv"
    if attempt.get("arm", "").endswith("_retained"):
        return output_path / f"{revision:03d}.response.json"
    return output_path / f"revision-{revision:03d}-{label}" / "taxonomy.raw"


def get_stage(adapter, attempt, session_record, fresh_records, revision):
    if attempt.get("arm", "").endswith("_retained") or adapter == "owlapi":
        rows = session_record.get("revisions", []) if session_record else []
        return next((row for row in rows if row.get("revision") == revision), None)
    return fresh_records[revision] if revision < len(fresh_records) else None


def verify_and_fill_order_positions(panel):
    """Derive omitted positions only from the exact recorded execution order."""
    attempts = panel.get("attempts", [])
    expected_orders = [list(order) for order in ORDERS]
    errors = []
    if panel.get("balanced_arm_orders") != expected_orders:
        return attempts, ["panel schedule does not equal frozen counterbalanced orders"]
    expected_sequence = [(rep, arm, position)
                         for rep, order in enumerate(ORDERS)
                         for position, arm in enumerate(order)]
    if len(attempts) != len(expected_sequence):
        return attempts, [f"panel has {len(attempts)} attempts, expected {len(expected_sequence)} ordered attempts"]
    cooked = []
    for index, (attempt, (rep, arm, position)) in enumerate(zip(attempts, expected_sequence)):
        if attempt.get("repetition") != rep or attempt.get("arm") != arm:
            errors.append(f"panel sequential attempt {index} does not match frozen order")
            cooked.append(attempt)
            continue
        recorded = attempt.get("order_position")
        if recorded is not None and recorded != position:
            errors.append(f"panel attempt {index} has a conflicting recorded order position")
            cooked.append(attempt)
            continue
        if recorded is None:
            attempt = dict(attempt)
            attempt["order_position"] = position
            attempt["order_position_basis"] = "derived from verified sequential array and frozen ORDERS"
        cooked.append(attempt)
    return cooked, errors


def subreaper_cleanup_proven(record):
    """Require the v3 tree proof; an empty list alone is not a certificate."""
    if not isinstance(record, dict):
        return False
    cleanup = record.get("child_tree_cleanup")
    return (isinstance(cleanup, dict)
            and cleanup.get("status") == "confirmed_empty_after_cleanup"
            and cleanup.get("remaining_processes") == []
            and cleanup.get("subreaper_restored") is True
            and record.get("remaining_processes") == [])


def owlapi_cleanup_proven(record):
    """Require OWLAPI's full v3 nested proof and its final group/error checks."""
    return (record.get("schema") == 2
            and record.get("runner_version") == "owlapi_cleanup_v3"
            and subreaper_cleanup_proven(record)
            and record.get("remaining_process_tree_or_group") == []
            and record.get("cleanup_errors") == [])


def compact_attempt(adapter, attempt, fixture, panel_path, pins, inventory_sha):
    arm = attempt.get("arm")
    rep = attempt.get("repetition")
    if arm not in ARMS or type(rep) is not int or not 0 <= rep < 5:
        raise ValueError("attempt has invalid arm/repetition")
    variant = "candidate" if arm.startswith("candidate_") else "released_baseline"
    output_path = Path(attempt.get("output", ""))
    if not output_path.is_absolute():
        output_path = (panel_path.resolve().parent / output_path).resolve()
    else:
        output_path = output_path.resolve()
    errors = []
    if not output_path.is_dir():
        errors.append(f"attempt output directory missing: {output_path}")

    records, record_paths, record_hashes = [], [], []
    for index, revision in enumerate(fixture["revisions"]):
        row, path = load_measurement_record(adapter, attempt, output_path, index, revision["label"])
        records.append(row)
        record_paths.append(path)
        record_hashes.append(hash_file(path)["sha256"] if path.is_file() else None)
    session = records[0] if arm.endswith("_retained") or adapter == "owlapi" else None
    fresh_rows = records if not arm.endswith("_retained") and adapter == "cli" else []
    if adapter == "owlapi":
        session = records[0]
    env = None
    if session:
        env = session.get("environment") if adapter == "owlapi" else session.get("effective_environment")
    elif fresh_rows:
        env = fresh_rows[0].get("explicit_environment")
    projections = []
    if adapter == "cli" and not arm.endswith("_retained"):
        for row in fresh_rows:
            try:
                projections.append(env_projection(row.get("explicit_environment"), row, adapter))
            except Exception as error:
                errors.append(f"fresh revision effective config unavailable: {error!r}")
    elif session:
        try:
            projections.append(env_projection(env, session, adapter))
        except Exception as error:
            errors.append(f"effective config unavailable: {error!r}")
    projection = projections[0] if projections else None
    if any(item != projection for item in projections[1:]):
        errors.append("effective runtime config changed within attempt")
        projection = None
    config_sha = effective_config_hash(projection) if projection else None

    stage_rows, artifacts = [], []
    all_success = True
    stage_walls = []
    for index, revision in enumerate(fixture["revisions"]):
        measurement = records[0] if arm.endswith("_retained") or adapter == "owlapi" else records[index]
        stage = get_stage(adapter, attempt, session, fresh_rows, index)
        status = stage.get("status") if isinstance(stage, dict) else "missing_measurement"
        exit_code = measurement.get("exit_code", measurement.get("actual_exit_code")) if isinstance(measurement, dict) else None
        if adapter == "cli" and not arm.endswith("_retained") and isinstance(measurement, dict):
            if type(exit_code) is not int:
                exit_code = measurement.get("exit_code")
        if adapter == "owlapi":
            exit_code = measurement.get("actual_exit_code") if isinstance(measurement, dict) else None
        source_sha = (stage.get("sha256", stage.get("source_sha256")) if isinstance(stage, dict) else None)
        if adapter == "cli" and not arm.endswith("_retained") and isinstance(measurement, dict):
            source_sha = measurement.get("source_sha256", source_sha)
        expected_sha = revision.get("raw_sha256", revision.get("sha256"))
        wall = stage.get("wall_s") if isinstance(stage, dict) else None
        valid = (revision.get("expected_valid") is True and status == "executed_unvalidated"
                 and type(exit_code) is int and exit_code == 0 and source_sha == expected_sha
                 and finite_wall(wall))
        all_success &= valid
        stage_walls.append(wall if finite_wall(wall) else None)
        raw_path = raw_artifact_path(adapter, attempt, output_path, index, revision["label"])
        artifact = hash_file(raw_path) if raw_path.is_file() else None
        if artifact:
            artifacts.append({"revision": index, "kind": "raw_semantic_output", **artifact})
        stage_rows.append({
            "revision": index,
            "expected_valid": revision.get("expected_valid"),
            "status": status,
            "exit_code": exit_code,
            "source_sha256": source_sha,
            "measurement_record_sha256": record_hashes[index],
            "raw_output_sha256": artifact["sha256"] if artifact else None,
            "wall_s": wall,
            "wall_s_basis": stage.get("wall_s_basis") if isinstance(stage, dict) else None,
        })

    cleanup_proof = None
    if adapter == "owlapi":
        whole = session.get("comparable_whole_sequence_wall_s") if session else None
        cleanup = session.get("remaining_process_tree_or_group") if session else None
    elif arm.endswith("_retained"):
        whole = session.get("comparable_whole_session_wall_s") if session else None
        cleanup = None
    else:
        whole = sum(stage_walls) if len(stage_walls) == 9 and all(finite_wall(x) for x in stage_walls) else None
        cleanup = None
    if adapter == "owlapi":
        attempt_exit = session.get("actual_exit_code") if session else None
        actual_status = session.get("status") if session else "missing_record"
    elif arm.endswith("_retained"):
        attempt_exit = session.get("exit_code") if session else None
        actual_status = session.get("status") if session else "missing_record"
    else:
        codes = [r.get("exit_code") if isinstance(r, dict) else None for r in fresh_rows]
        attempt_exit = 0 if len(codes) == 9 and all(code == 0 for code in codes) else next((x for x in codes if x not in (0, None)), None)
        actual_status = "executed_unvalidated" if all_success else "partial_or_failed"
    if adapter == "cli":
        cleanup_records = [session] if arm.endswith("_retained") else fresh_rows
        cleanup_checks = [
            {"measurement_index": index,
             "status": ((row.get("child_tree_cleanup") or {}).get("status")
                        if isinstance(row, dict) else None),
             "subreaper_restored": ((row.get("child_tree_cleanup") or {}).get("subreaper_restored")
                                    if isinstance(row, dict) else None),
             "remaining_processes": (row.get("remaining_processes") if isinstance(row, dict) else None),
             "proven": subreaper_cleanup_proven(row)}
            for index, row in enumerate(cleanup_records)
        ]
        cleanup_ok = bool(cleanup_checks) and all(row["proven"] for row in cleanup_checks)
        cleanup_proof = {"status": "confirmed_empty_after_cleanup" if cleanup_ok else "cleanup_unproven",
                         "subreaper_restored": cleanup_ok,
                         "measurements": cleanup_checks}
        cleanup = [] if cleanup_ok else None
        if not cleanup_ok:
            errors.append("subreaper process-tree cleanup proof missing, incomplete, or un-restored")
            all_success = False
            actual_status = "cleanup_unproven"
    elif adapter == "owlapi":
        cleanup_ok = owlapi_cleanup_proven(session)
        cleanup_proof = {
            "status": "confirmed_empty_after_cleanup" if cleanup_ok else "cleanup_unproven",
            "subreaper_restored": ((session.get("child_tree_cleanup") or {}).get("subreaper_restored")
                                    if isinstance(session, dict) else None),
            "nested_child_tree_cleanup": (session.get("child_tree_cleanup")
                                          if isinstance(session, dict) else None),
            "remaining_process_tree_or_group": (session.get("remaining_process_tree_or_group")
                                                 if isinstance(session, dict) else None),
            "cleanup_errors": (session.get("cleanup_errors") if isinstance(session, dict) else None),
        }
        cleanup = [] if cleanup_ok else None
        if not cleanup_ok:
            errors.append("OWLAPI subreaper cleanup proof missing, incomplete, unrestored, or reported errors")
            all_success = False
            actual_status = "cleanup_unproven"
    raw_manifest = [{"revision": row["revision"], "sha256": row["raw_output_sha256"]} for row in stage_rows]
    aggregate_raw_hash = canonical_hash(raw_manifest)
    record_manifest = [{"revision": i, "sha256": value} for i, value in enumerate(record_hashes)]
    aggregate_measurement_hash = canonical_hash(record_manifest) if all(record_hashes) else None
    measurement_hash = (record_hashes[0] if arm.endswith("_retained") or adapter == "owlapi"
                        else aggregate_measurement_hash)
    if arm.endswith("_retained") and attempt.get("measurement_sha256"):
        if record_hashes[0] != attempt.get("measurement_sha256"):
            errors.append("retained measurement record hash differs from panel binding")
    if adapter == "owlapi" and attempt.get("record_sha256"):
        if record_hashes[0] != attempt.get("record_sha256"):
            errors.append("OWLAPI record hash differs from panel binding")
    if attempt.get("binary_sha256") and attempt.get("binary_sha256") != pins[variant]["binary_sha256"]:
        raise ValueError("panel attempt binary hash differs from inventory")
    binding = attempt.get("binary_inventory_binding") or (session or {}).get("binding") or {}
    if isinstance(binding, dict):
        bound_sha = binding.get("sha256", binding.get("binary_sha256"))
        if bound_sha and bound_sha != pins[variant]["binary_sha256"]:
            errors.append("measurement binary binding differs from inventory")
        bound_source = binding.get("source_manifest_sha256", binding.get("native_source_manifest_sha256"))
        if bound_source and bound_source != pins[variant]["source_manifest_sha256"]:
            errors.append("measurement source binding differs from inventory")
    # Bind the actual record-level artifact fields for every revision. A panel
    # inventory hash alone is not evidence that this particular process used it.
    for index, record in enumerate(records):
        if not isinstance(record, dict):
            errors.append(f"revision {index}: measurement record missing or malformed")
            continue
        if adapter == "owlapi":
            actual_binary = (record.get("binding") or {}).get("binary_sha256")
        else:
            actual_binary = record.get("artifact_sha256")
        if actual_binary != pins[variant]["binary_sha256"]:
            errors.append(f"revision {index}: record binary SHA does not match pinned inventory")
    if errors and all_success:
        actual_status = "provenance_mismatch"
    return {
        "arm": arm,
        "repetition": rep,
        "order_position": attempt.get("order_position"),
        "binary_sha256": pins[variant]["binary_sha256"],
        "status": "executed_unvalidated" if all_success and actual_status in ("executed_unvalidated", "terminal_steps_recorded") else actual_status,
        "exit_code": attempt_exit,
        "remaining_processes": cleanup,
        "cleanup_proof": cleanup_proof,
        "measurement_record_sha256": measurement_hash,
        "measurement_record_sha256_by_revision": record_hashes,
        "raw_output_sha256": aggregate_raw_hash,
        "effective_config_sha256": config_sha,
        "effective_config_projection": projection,
        "whole_session_wall_s": whole,
        "revisions": stage_rows,
        "semantic_artifacts": artifacts,
        "cleanup_evidence": ("subreaper ancestry proof validated for every CLI measurement"
                             if adapter == "cli" and cleanup is not None
                             else "nested subreaper proof, process-group check, and empty cleanup_errors validated"
                             if adapter == "owlapi" and cleanup is not None
                             else "recorded by adapter or unknown; not upgraded to complete-tree proof"),
        "attempt_output_path": str(output_path),
        "effective_config_sha256_by_revision": [effective_config_hash(x) for x in projections],
        "provenance_errors": errors,
    }


def select_manifest_row(manifest, index, ontology):
    for row in manifest.get("fixtures", []):
        if row.get("index") == index and row.get("id", row.get("ontology")) == ontology:
            return row
    raise ValueError(f"manifest has no exact row for {index}/{ontology}")


def compact_task(adapter, task, task_manifest_path, selection, input_plan, inventory,
                 inventory_pins, inventory_sha, input_plan_sha, protocol_sha):
    index = task.get("index")
    if type(index) is not int or index < 0 or index >= 80:
        raise ValueError("task index outside frozen 80-case range")
    ontology = selection["selected"][index]["ontology"]
    panel_path = resolved(task["panel_path"], task_manifest_path)
    wrapper_path = resolved(task["wrapper_record_path"], task_manifest_path)
    fixture_path = resolved(task["fixture_manifest_path"], task_manifest_path)
    panel = stream_panel(panel_path)
    panel_sha = sha256(panel_path)
    wrapper = read_json(wrapper_path)
    fixture_manifest = read_json(fixture_path)
    task_errors = []
    fixture = select_manifest_row(fixture_manifest, index, ontology)
    planned = select_manifest_row(input_plan, index, ontology)
    revisions = fixture.get("revisions", [])
    planned_revisions = planned.get("revisions", [])
    if len(revisions) != 9 or len(planned_revisions) != 9:
        task_errors.append(f"{ontology}: expected nine revisions in runner and frozen input plan")
    if [r.get("revision", i) for i, r in enumerate(revisions)] != list(range(9)):
        task_errors.append(f"{ontology}: fixture revision order malformed")
    for i, (runner_rev, plan_rev) in enumerate(zip(revisions, planned_revisions)):
        if runner_rev.get("sha256", runner_rev.get("raw_sha256")) != plan_rev.get("raw_sha256"):
            task_errors.append(f"{ontology}: runner/input-plan revision hash mismatch at {i}")
        if runner_rev.get("expected_valid") is not plan_rev.get("expected_valid"):
            task_errors.append(f"{ontology}: runner/input-plan validity mismatch at {i}")
    if panel.get("protocol_sha256") not in (None, protocol_sha):
        task_errors.append(f"{ontology}: panel protocol hash mismatch")
    panel_inventory_sha = panel.get("binary_inventory_sha256", panel.get("binding_sha256"))
    if panel_inventory_sha not in (None, inventory_sha):
        task_errors.append(f"{ontology}: panel binary binding hash mismatch")
    if panel.get("fixture_manifest_sha256", panel.get("fixtures_sha256")) not in (None, sha256(fixture_path)):
        task_errors.append(f"{ontology}: panel fixture manifest hash mismatch")
    if wrapper.get("binary_inventory_sha256", wrapper.get("binding_sha256")) not in (None, inventory_sha):
        task_errors.append(f"{ontology}: wrapper inventory binding hash mismatch")
    if wrapper.get("protocol_sha256") not in (None, protocol_sha):
        task_errors.append(f"{ontology}: wrapper protocol hash mismatch")

    attempts = []
    semantic_audit_files = []
    if adapter == "cli":
        audit_root = panel_path.resolve().parent / ontology
        for rep in range(5):
            path = audit_root / f"semantic-audit-repetition-{rep:02d}.json"
            if path.is_file():
                semantic_audit_files.append(hash_file(path))
    verified_attempts, order_errors = verify_and_fill_order_positions(panel)
    task_errors.extend(order_errors)
    for attempt in verified_attempts:
        if attempt.get("fixture_id", ontology) != ontology:
            continue
        try:
            attempts.append(compact_attempt(adapter, attempt, fixture, panel_path,
                                            inventory_pins, inventory_sha))
        except Exception as error:
            # Keep the scheduler/driver's actual attempt identity and outcome
            # even when a referenced detail is malformed or absent.
            attempts.append({
                "arm": attempt.get("arm"),
                "repetition": attempt.get("repetition"),
                "order_position": attempt.get("order_position"),
                "binary_sha256": attempt.get("binary_sha256"),
                "status": attempt.get("status", "compaction_error"),
                "exit_code": attempt.get("exit_code"),
                "remaining_processes": None,
                "measurement_record_sha256": attempt.get("measurement_sha256", attempt.get("record_sha256")),
                "raw_output_sha256": None,
                "effective_config_sha256": None,
                "effective_config_projection": None,
                "whole_session_wall_s": None,
                "revisions": [],
                "semantic_artifacts": [],
                "cleanup_evidence": "unknown; compaction failed",
                "attempt_output_path": attempt.get("output"),
                "provenance_errors": [repr(error)],
            })
    status = panel.get("status", "missing_status")
    semantic_complete = status in COMPLETED_PANEL_STATES
    if adapter == "cli":
        semantic_complete = semantic_complete and len(semantic_audit_files) == 5
    # OWLAPI stores its semantic-audit booleans in panel.json and output
    # taxonomies on disk; those are pinned but not independently re-parsed.
    semantic_status = "driver_reported_complete" if semantic_complete else "driver_reported_incomplete_or_missing"
    timing_path = panel_path.resolve().parent / ontology / "timing-summary.json"
    if timing_path.is_file():
        timing_hash = sha256(timing_path)
        timing_basis = "on_disk_driver_timing_summary"
    else:
        timing_hash = canonical_hash([{k: a.get(k) for k in ("arm", "repetition", "whole_session_wall_s", "revisions")}
                                      for a in attempts])
        timing_basis = "canonical_projection_of_measurement_records"
    evidence = {
        "panel_sha256": panel_sha,
        "wrapper_record_sha256": sha256(wrapper_path),
        "fixture_manifest_sha256": sha256(fixture_path),
        "timing_summary_sha256": timing_hash,
        "timing_summary_basis": timing_basis,
        "binary_inventory_sha256": inventory_sha,
        "input_plan_sha256": input_plan_sha,
        "semantic_audit_artifacts": semantic_audit_files,
        "semantic_claim_limit": "driver-reported only; panel status and artifact hashes do not constitute an independent semantic audit",
        "wrapper_status": wrapper.get("status"),
        "wrapper_driver_panel_status": wrapper.get("driver_panel_status"),
    }
    pins = {
        "protocol_sha256": protocol_sha,
        "candidate_binary_sha256": inventory_pins["candidate"]["binary_sha256"],
        "candidate_source_manifest_sha256": inventory_pins["candidate"]["source_manifest_sha256"],
        "released_binary_sha256": inventory_pins["released_baseline"]["binary_sha256"],
        "released_source_manifest_sha256": inventory_pins["released_baseline"]["source_manifest_sha256"],
    }
    limits = {"cpu_threads": 1, "memory_mib": 20480, "timeout_s": 240}
    row = compact_row(adapter, index, ontology, attempts, panel_status=status,
                      semantic_audit_status=semantic_status, pins=pins, limits=limits,
                      evidence=evidence, balanced_arm_orders=panel.get("balanced_arm_orders"))
    row["runner_binding"] = {
        "panel_path": str(panel_path), "wrapper_record_path": str(wrapper_path),
        "fixture_manifest_path": str(fixture_path), "task_manifest_path": str(Path(task_manifest_path).resolve()),
        "task_manifest_sha256": sha256(task_manifest_path), "panel_repetitions": panel.get("repetitions"),
        "top_level_cpu_threads": panel.get("cpu_threads"), "top_level_memory_mib": panel.get("memory_mib"),
        "top_level_timeout_s": panel.get("timeout_s"),
        "semantic_evidence": "hashes and runner status only; not semantic proof",
    }
    row["compaction_errors"] = []
    row["compaction_errors"].extend(task_errors)
    if not attempts:
        row["compaction_errors"].append("no attempts for selected fixture")
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--adapter", choices=("cli", "owlapi"), required=True)
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--input-plan", type=Path, required=True)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--task-manifest", type=Path, required=True,
                        help="JSON {schema:1,tasks:[{index,panel_path,wrapper_record_path,fixture_manifest_path}]} with 80 rows")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not os.environ.get("SLURM_JOB_ID"):
        raise SystemExit("this artifact compactor is Slurm-compute-only; SLURM_JOB_ID is absent")
    if args.output.exists():
        raise SystemExit(f"refusing to overwrite existing output: {args.output}")
    if sha256(args.selection) != SELECTION_SHA256:
        raise SystemExit("frozen selection SHA mismatch")
    protocol_sha = PROTOCOL_SHA256
    selection = read_json(args.selection)
    input_plan = read_json(args.input_plan)
    task_manifest = read_json(args.task_manifest)
    if task_manifest.get("schema") != 1 or not isinstance(task_manifest.get("tasks"), list):
        raise SystemExit("task manifest schema mismatch")
    if len(task_manifest["tasks"]) != 80 or sorted(t.get("index") for t in task_manifest["tasks"]) != list(range(80)):
        raise SystemExit("task manifest must contain exactly one row for each index 0..79")
    inventory = read_json(args.inventory)
    pins = adapter_pins(args.adapter, inventory)
    inv_sha = sha256(args.inventory)
    plan_sha = sha256(args.input_plan)
    output_rows = []
    for task in sorted(task_manifest["tasks"], key=lambda item: item["index"]):
        try:
            output_rows.append(compact_task(args.adapter, task, args.task_manifest,
                                            selection, input_plan, inventory, pins,
                                            inv_sha, plan_sha, protocol_sha))
        except Exception as error:
            idx = task.get("index")
            ontology = selection.get("selected", [{}])[idx].get("ontology", "unknown") if type(idx) is int and 0 <= idx < 80 else "unknown"
            output_rows.append(compact_row(
                args.adapter, idx, ontology, [], panel_status="compaction_failed",
                semantic_audit_status="unavailable", pins={
                    "protocol_sha256": protocol_sha,
                    "candidate_binary_sha256": pins["candidate"]["binary_sha256"],
                    "candidate_source_manifest_sha256": pins["candidate"]["source_manifest_sha256"],
                    "released_binary_sha256": pins["released_baseline"]["binary_sha256"],
                    "released_source_manifest_sha256": pins["released_baseline"]["source_manifest_sha256"]},
                limits={"cpu_threads": 1, "memory_mib": 20480, "timeout_s": 240},
                evidence={"panel_sha256": None, "wrapper_record_sha256": None,
                          "fixture_manifest_sha256": None, "timing_summary_sha256": None,
                          "binary_inventory_sha256": inv_sha, "input_plan_sha256": plan_sha},
                balanced_arm_orders=None))
            output_rows[-1]["compaction_errors"] = [repr(error)]
    temporary = args.output.with_suffix(args.output.suffix + ".part")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with temporary.open("x", encoding="utf-8") as stream:
        for row in output_rows:
            stream.write(json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(args.output)
    print(json.dumps({"adapter": args.adapter, "rows": len(output_rows),
                      "rows_with_compaction_errors": sum(bool(r.get("compaction_errors")) for r in output_rows),
                      "output": str(args.output), "output_sha256": sha256(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()
