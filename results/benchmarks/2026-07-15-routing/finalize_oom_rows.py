#!/usr/bin/env python3
"""Publish missing production rows only from explicit Slurm OOM evidence."""

import argparse
import glob
import hashlib
import json
import os
import tempfile


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--tag", required=True)
    ap.add_argument("--binary", required=True)
    ap.add_argument(
        "--runner",
        required=True,
        help="exact benchmark runner used by the worker array",
    )
    ap.add_argument("--worker-job", required=True)
    ap.add_argument("--indices", required=True, help="comma-separated array indices")
    ap.add_argument("--memcap-mb", type=int, default=20480)
    args = ap.parse_args()

    expected_sha = sha256(args.binary)
    runner_sha = sha256(args.runner)
    onts = [line.strip() for line in open(os.path.join(args.root, "onts.txt")) if line.strip()]
    result_dir = os.path.join(args.root, "production-sweeps", args.tag, "results")
    os.makedirs(result_dir, exist_ok=True)

    for index in [int(value) for value in args.indices.split(",")]:
        ont = onts[index]
        result = os.path.join(result_dir, ont + ".jsonl")
        if os.path.exists(result) and os.path.getsize(result) > 0:
            continue
        logs = glob.glob(os.path.join(args.root, "slurm", f"prod-{args.worker_job}_{index}.out"))
        if len(logs) != 1:
            raise SystemExit(f"expected one Slurm log for {ont}, found {logs}")
        text = open(logs[0], errors="replace").read()
        if "oom_kill event" not in text and "OUT_OF_MEMORY" not in text:
            raise SystemExit(f"refusing to adjudicate {ont}: no Slurm OOM evidence")
        row = {
            "ont": ont,
            "arm": "production_all",
            "kind": "km",
            "status": "memout",
            "verdict": "memout",
            "rc": 137,
            "wall_s": None,
            "peak_mb": args.memcap_mb,
            "binary_sha256": expected_sha,
            "runner_sha256": runner_sha,
            "requested_route": "production_all",
            "solved": False,
            "checkpointed": False,
            "finalized_from_slurm_oom": True,
            "worker_job_id": args.worker_job,
            "worker_array_task_id": index,
            "slurm_log_sha256": sha256(logs[0]),
        }
        fd, tmp = tempfile.mkstemp(prefix=ont + ".", suffix=".partial", dir=result_dir)
        try:
            with os.fdopen(fd, "w") as handle:
                handle.write(json.dumps(row, sort_keys=True) + "\n")
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(tmp, result)
        finally:
            if os.path.exists(tmp):
                os.unlink(tmp)
        print(f"FINALIZED ontology={ont} status=memout sha={expected_sha}")


if __name__ == "__main__":
    main()
