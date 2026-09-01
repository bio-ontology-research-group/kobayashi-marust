#!/usr/bin/env python3
"""Measure one isolated Java baseline and publish a fail-closed result row."""

from __future__ import annotations

import argparse
import functools
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

import tree_watchdog as watchdog


def sha256(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + f".part.{os.getpid()}")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--factory", required=True)
    parser.add_argument("--jar", required=True, type=Path)
    parser.add_argument("--ontology", required=True, type=Path)
    parser.add_argument("--ontology-id", required=True)
    parser.add_argument("--output-root", required=True, type=Path)
    parser.add_argument("--tools-root", required=True, type=Path)
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--memcap-mb", type=int, default=32768)
    args = parser.parse_args()
    for path in (args.jar, args.ontology):
        if not path.is_file() or path.stat().st_size == 0: raise SystemExit(f"missing artifact: {path}")

    prefix = args.output_root / args.baseline / args.ontology_id
    result_path = prefix.with_suffix(".result.json")
    output_path = prefix.with_suffix(".taxonomy.tsv")
    stderr_path = prefix.with_suffix(".stderr")
    time_path = prefix.with_suffix(".time")
    prefix.parent.mkdir(parents=True, exist_ok=True)
    for path in (output_path, Path(str(output_path) + ".part"), stderr_path, time_path):
        try: path.unlink()
        except FileNotFoundError: pass

    main_class = "org.kmbenchmark.FullIriClassifier3" if args.baseline == "more" else None
    heap_mb = min(28672, max(256, args.memcap_mb - 2048))
    command = ["/usr/bin/java", "--add-opens=java.base/java.lang=ALL-UNNAMED", f"-Xmx{heap_mb}m"]
    if main_class:
        command += ["-cp", str(args.jar), main_class, args.factory, str(args.ontology), str(output_path)]
    else:
        command += ["-jar", str(args.jar), args.factory, str(args.ontology), str(output_path)]
    measured_command = ["/usr/bin/time", "-v", "-o", str(time_path)] + command
    record = {
        "schema": 1, "baseline": args.baseline, "ontology_id": args.ontology_id,
        "ontology": str(args.ontology), "ontology_sha256": sha256(args.ontology),
        "runtime": str(args.jar), "runtime_sha256": sha256(args.jar),
        "runner_sha256": sha256(Path(__file__)), "command": command,
        "measured_command": measured_command,
        "timeout_s": args.timeout, "memory_limit_mb": args.memcap_mb,
        "host": os.uname().nodename, "slurm_job_id": os.getenv("SLURM_JOB_ID"),
        "slurm_array_job_id": os.getenv("SLURM_ARRAY_JOB_ID"),
        "slurm_array_task_id": os.getenv("SLURM_ARRAY_TASK_ID"),
        "status": "running", "checkpointed": False,
    }
    atomic_json(result_path, record)
    started = time.monotonic()
    watchdog.protect_supervisor()
    stderr = stderr_path.open("wb")
    process = subprocess.Popen(measured_command, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                               stderr=stderr, preexec_fn=watchdog.child_preexec)

    def on_trip(status: str, peak: int) -> None:
        checkpoint = dict(record)
        checkpoint.update(status=status, wall_s=round(time.monotonic() - started, 4),
                          peak_mb=round(peak / 2**20, 2), checkpointed=True)
        atomic_json(result_path, checkpoint)

    measured = watchdog.monitor(process, timeout=args.timeout,
                                memcap_bytes=args.memcap_mb * 2**20,
                                sample_interval=0.02, on_trip=on_trip)
    stderr.close()
    direct_peak = 0
    if time_path.is_file():
        for line in time_path.read_text(encoding="utf-8", errors="replace").splitlines():
            if "Maximum resident set size" in line:
                direct_peak = int(line.rsplit(":", 1)[1].strip()) * 1024
                break
    peak = max(measured.peak_bytes, direct_peak)
    record.update(status=measured.status, rc=process.returncode,
                  wall_s=round(measured.wall_s, 4), peak_mb=round(peak / 2**20, 2),
                  stderr_sha256=sha256(stderr_path), checkpointed=True)
    stderr_text = stderr_path.read_text(encoding="utf-8", errors="replace").lower()
    if record["status"] == "ok" and process.returncode != 0:
        record["status"] = "unsupported" if any(token in stderr_text for token in
            ("unsupported", "not supported", "not in the profile", "outside the profile")) else "error"
    if record["status"] == "ok":
        validator = subprocess.run([sys.executable, str(args.tools_root / "validate_output.py"), str(output_path)],
                                   text=True, capture_output=True)
        if validator.returncode != 0:
            record.update(status="output_error", validation_error=validator.stderr[-1000:])
        else:
            fingerprint = subprocess.run([
                sys.executable, str(args.tools_root / "fingerprint_common.py"),
                "--input", str(output_path), "--output-prefix", str(prefix) + ".fingerprint"],
                text=True, capture_output=True)
            if fingerprint.returncode != 0:
                record.update(status="fingerprint_error", fingerprint_error=fingerprint.stderr[-1000:])
            else:
                fp = json.loads(fingerprint.stdout)
                record.update(status="ok", output_sha256=sha256(output_path),
                              consistency=fp["consistent"], subsumptions=fp["subsumptions"],
                              unsatisfiable=fp["unsatisfiable"], taxonomy_sha256=fp["taxonomy_sha256"],
                              relation_sha256=fp["relation_sha256"],
                              fingerprint_wall_s=fp["wall_s"], fingerprint_peak_mb=fp["peak_mb"])
    atomic_json(result_path, record)
    print(json.dumps(record, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
