#!/usr/bin/env python3
"""Run one ORE tail validation arm and retain its complete raw evidence.

Classification and canonical comparison are separate phases so a large
comparison cannot erase or mislabel a successful reasoner run.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time


UNSUPPORTED_MARKERS = (
    "unsupported",
    "not supported",
    "not in the profile",
    "outside the profile",
    "owlprofileviolation",
    "cannot handle",
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def process_group_rss(pgid: int, page_size: int) -> int:
    total = 0
    try:
        entries = os.listdir("/proc")
    except OSError:
        return 0
    for entry in entries:
        if not entry.isdigit():
            continue
        try:
            fields = Path(f"/proc/{entry}/stat").read_text(encoding="ascii").split()
            if int(fields[4]) == pgid:
                total += int(fields[23]) * page_size
        except (OSError, IndexError, ValueError):
            pass
    return total


def first_cpu_model() -> str:
    try:
        with Path("/proc/cpuinfo").open(encoding="ascii", errors="replace") as handle:
            for line in handle:
                if line.startswith("model name"):
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return "unknown"


def tail_text(path: Path, limit: int = 4000) -> str:
    try:
        data = path.read_bytes()
    except OSError:
        return ""
    return data[-limit:].decode("utf-8", errors="replace")


def direct_peak_bytes(time_path: Path) -> int:
    try:
        text = time_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return 0
    match = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", text)
    return int(match.group(1)) * 1024 if match else 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--kind", choices=("km", "konclude", "elk", "hermit"), required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--ontology", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--java", type=Path, default=Path("/usr/bin/java"))
    parser.add_argument("--java-heap", default="-Xmx16g")
    parser.add_argument("--classpath", default="")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=240.0)
    parser.add_argument("--memcap-mb", type=int, default=20480)
    parser.add_argument("--env", action="append", default=[])
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)

    stdout_path = args.output_dir / "stdout.log"
    stderr_path = args.output_dir / "stderr.log"
    time_path = args.output_dir / "time.txt"
    if args.kind in ("km", "hermit"):
        primary_output = stdout_path
        output_format = "json"
    else:
        primary_output = args.output_dir / "taxonomy.owl"
        output_format = "functional" if args.kind == "elk" else "owlxml"

    env = dict(os.environ)
    for key in list(env):
        if key.startswith("KM_"):
            del env[key]
    explicit_env: dict[str, str] = {}
    for item in args.env:
        if "=" not in item:
            raise ValueError(f"invalid --env value: {item!r}")
        key, value = item.split("=", 1)
        explicit_env[key] = value
        env[key] = value

    if args.kind == "km":
        argv = [str(args.binary), "classify", str(args.ontology)]
    elif args.kind == "konclude":
        # The source-bound outer validator supplies the exact library path as
        # an explicit --env value. Do not inject a historical private-library
        # directory here: that would make the executed route differ from the
        # recorded runtime closure.
        argv = [
            str(args.binary), "classification", "-w", str(args.workers), "-v",
            "-i", str(args.ontology), "-o", str(primary_output),
        ]
    elif args.kind == "elk":
        argv = [
            str(args.java), args.java_heap, "-jar", str(args.binary), "-c", "-q",
            "-i", str(args.ontology), "-o", str(primary_output),
        ]
    else:
        argv = [
            str(args.java), args.java_heap, "-cp", args.classpath, "Oracle",
            str(args.ontology),
        ]

    wrapped = ["/usr/bin/time", "-v", "-o", str(time_path), *argv]
    started = time.monotonic()
    peak = 0
    status = "ok"
    with stdout_path.open("wb") as stdout_handle, stderr_path.open("wb") as stderr_handle:
        proc = subprocess.Popen(
            wrapped,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=stdout_handle,
            stderr=stderr_handle,
            start_new_session=True,
        )
        pgid = os.getpgid(proc.pid)
        page_size = os.sysconf("SC_PAGE_SIZE")
        memcap = args.memcap_mb * 1024 * 1024
        while proc.poll() is None:
            peak = max(peak, process_group_rss(pgid, page_size))
            if time.monotonic() - started > args.timeout:
                status = "timeout"
                break
            if peak > memcap:
                status = "memout"
                break
            time.sleep(0.04)
        if status != "ok":
            try:
                os.killpg(pgid, signal.SIGKILL)
            except OSError:
                pass
        try:
            proc.wait(timeout=15)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(pgid, signal.SIGKILL)
            except OSError:
                pass
            proc.wait()

    wall = time.monotonic() - started
    peak = max(peak, direct_peak_bytes(time_path))
    stderr_tail = tail_text(stderr_path)
    if status == "ok" and proc.returncode != 0:
        lowered = stderr_tail.lower()
        if (args.kind == "km" and proc.returncode == 3) or any(
            marker in lowered for marker in UNSUPPORTED_MARKERS
        ):
            status = "unsupported"
        else:
            status = "error"

    record = {
        "schema_version": 1,
        "label": args.label,
        "kind": args.kind,
        "status": status,
        "return_code": proc.returncode,
        "wall_s": round(wall, 4),
        "peak_mb": round(peak / 1024 / 1024, 2),
        "timeout_s": args.timeout,
        "memory_limit_mb": args.memcap_mb,
        "host": os.uname().nodename,
        "cpu_model": first_cpu_model(),
        "cpus": int(os.environ.get("SLURM_CPUS_PER_TASK", os.cpu_count() or 1)),
        "slurm_job_id": os.environ.get("SLURM_JOB_ID"),
        "slurm_array_job_id": os.environ.get("SLURM_ARRAY_JOB_ID"),
        "slurm_array_task_id": os.environ.get("SLURM_ARRAY_TASK_ID"),
        "ontology": str(args.ontology),
        "ontology_sha256": sha256_file(args.ontology),
        "binary": str(args.binary),
        "binary_sha256": sha256_file(args.binary),
        "runtime_sha256": sha256_file(args.java) if args.kind in ("elk", "hermit") else None,
        "command": argv,
        "environment": explicit_env,
        "output_format": output_format,
        "primary_output": str(primary_output),
        "primary_output_exists": primary_output.exists(),
        "primary_output_bytes": primary_output.stat().st_size if primary_output.exists() else 0,
        "primary_output_sha256": sha256_file(primary_output) if primary_output.exists() else None,
        "stderr_tail": stderr_tail,
    }
    result_tmp = args.output_dir / "run.json.tmp"
    result_tmp.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    result_tmp.replace(args.output_dir / "run.json")
    print(json.dumps(record, sort_keys=True), flush=True)
    return 0 if status == "ok" else 1


if __name__ == "__main__":
    raise SystemExit(main())

