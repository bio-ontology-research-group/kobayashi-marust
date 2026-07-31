#!/usr/bin/env python3
"""Validate a 592-task sweep and recover only independently proven OOM rows."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

TERMINAL = {"ok", "timeout", "memout", "error", "unsupported"}
OOM_RE = re.compile(
    r"(Detected\s+\d+\s+oom_kill|oom[-_ ]kill|out of memory)",
    re.IGNORECASE,
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_terminal(path: Path, ontology: str, index: int) -> dict:
    with path.open(encoding="utf-8") as handle:
        row = json.load(handle)
    if row.get("ont") != ontology:
        raise ValueError(f"{path}: ontology mismatch: {row.get('ont')!r}")
    if row.get("slurm_array_task_id") != str(index):
        raise ValueError(
            f"{path}: task mismatch: {row.get('slurm_array_task_id')!r}"
        )
    if row.get("status") not in TERMINAL:
        raise ValueError(f"{path}: invalid terminal status: {row.get('status')!r}")
    return row


def validate_profile(path: Path, ontology: str) -> None:
    with path.open(encoding="utf-8") as handle:
        row = json.load(handle)
    if row.get("ont") != ontology:
        raise ValueError(f"{path}: ontology mismatch: {row.get('ont')!r}")
    if row.get("status") != "ok":
        raise ValueError(f"{path}: invalid profile status: {row.get('status')!r}")
    if not row.get("selected_route"):
        raise ValueError(f"{path}: missing selected route")


def atomic_json(path: Path, row: dict) -> None:
    tmp = path.with_name(f"{path.name}.audit-{os.getpid()}.tmp")
    with tmp.open("w", encoding="utf-8") as handle:
        json.dump(row, handle, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(tmp, path)


def recovered_memout(
    *,
    ontology: str,
    index: int,
    array_job_id: str,
    binary: Path,
    log: Path,
) -> dict:
    return {
        "ont": ontology,
        "arm": "km_route_auto_integrated_main_exclusive",
        "kind": "km",
        "status": "memout",
        "verdict": "memout",
        "solved": False,
        "rc": None,
        "wall_s": None,
        "peak_mb": 20480.0,
        "peak_mb_is_lower_bound": True,
        "memcap_mb": 20480,
        "checkpointed": True,
        "posthoc_terminal_recovery": True,
        "recovery_basis": "slurm_oom_kill_marker",
        "slurm_log": str(log),
        "slurm_job_id": array_job_id,
        "slurm_array_job_id": array_job_id,
        "slurm_array_task_id": str(index),
        "ontology_index": str(index),
        "binary_path": str(binary.resolve()),
        "binary_sha256": sha256(binary),
        "requested_route": "auto",
        "extra": 0,
        "missing": 0,
        "extra_unsat": 0,
        "missing_unsat": 0,
        "consistency_mismatch": False,
        "signature_sha256": None,
        "output_path": None,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--ontology-list", type=Path, required=True)
    parser.add_argument("--array-job-id", required=True)
    parser.add_argument("--binary", type=Path, required=True)
    args = parser.parse_args()

    ontologies = args.ontology_list.read_text(encoding="utf-8").splitlines()
    if len(ontologies) != 592 or len(set(ontologies)) != 592:
        raise SystemExit("ontology list must contain 592 unique rows")

    results = args.root / "results"
    profiles = args.root / "profiles"
    binary_sha256 = sha256(args.binary)
    recovered = []
    failures = []
    counts = {}
    for index, ontology in enumerate(ontologies):
        final = results / f"{ontology}.json"
        checkpoint = results / f"{ontology}.checkpoint.json"
        try:
            row = load_terminal(final, ontology, index)
        except (OSError, ValueError, json.JSONDecodeError) as final_error:
            try:
                row = load_terminal(checkpoint, ontology, index)
                atomic_json(final, row)
                recovered.append((ontology, "checkpoint"))
            except (OSError, ValueError, json.JSONDecodeError):
                log = args.root / f"slurm-{args.array_job_id}_{index}.out"
                try:
                    log_text = log.read_text(encoding="utf-8", errors="replace")
                except OSError:
                    log_text = ""
                if not OOM_RE.search(log_text):
                    failures.append(f"{ontology}: {final_error}; no OOM marker in {log}")
                    continue
                row = recovered_memout(
                    ontology=ontology,
                    index=index,
                    array_job_id=args.array_job_id,
                    binary=args.binary,
                    log=log,
                )
                atomic_json(final, row)
                atomic_json(checkpoint, row)
                recovered.append((ontology, "slurm_oom_kill_marker"))
        if row.get("binary_sha256") != binary_sha256:
            failures.append(
                f"{ontology}: binary mismatch: "
                f"{row.get('binary_sha256')!r} != {binary_sha256!r}"
            )
        try:
            checkpoint_row = load_terminal(checkpoint, ontology, index)
            if checkpoint_row != row:
                failures.append(f"{ontology}: final/checkpoint row mismatch")
        except (OSError, ValueError, json.JSONDecodeError) as error:
            failures.append(f"{ontology}: invalid checkpoint: {error}")
        try:
            validate_profile(profiles / f"{ontology}.json", ontology)
        except (OSError, ValueError, json.JSONDecodeError) as error:
            failures.append(f"{ontology}: invalid profile: {error}")
        counts[row["status"]] = counts.get(row["status"], 0) + 1

    if failures:
        for failure in failures:
            print(f"AUDIT_FAILURE {failure}", file=sys.stderr)
        print(
            f"SWEEP_AUDIT_FAILED terminal={sum(counts.values())} "
            f"missing_or_invalid={len(failures)}",
            file=sys.stderr,
        )
        return 1

    print(json.dumps({"counts": counts, "recovered": recovered}, sort_keys=True))
    print(f"SWEEP_AUDIT_COMPLETE terminal={sum(counts.values())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
