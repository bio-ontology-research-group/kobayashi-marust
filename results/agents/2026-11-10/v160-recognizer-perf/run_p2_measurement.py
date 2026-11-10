#!/usr/bin/env python3
import collections
import concurrent.futures
import csv
import os
import shutil
import subprocess
import sys
import time

REPO_ROOT = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v160-nary-conjunction"
SCRATCH_ROOT = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/v160-recognizer-perf"
TSV_PATH = os.path.join(REPO_ROOT, "results/agents/2026-10-30/checkers-on-suite/per-input.tsv")
KM_BIN = os.path.join(REPO_ROOT, "engine/target/release/km")
REF_BIN = os.path.join(REPO_ROOT, "lean/.lake/build/bin/km-el-reference")
OUT_DIR = os.path.join(REPO_ROOT, "results/agents/2026-11-10/v160-recognizer-perf")
OUT_TSV = os.path.join(OUT_DIR, "p2-recognition.tsv")

OLD_WORKTREE_PREFIX = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-checkers-on-suite/"


def resolve_input_path(raw_path: str) -> str:
    if os.path.exists(raw_path):
        return raw_path
    if raw_path.startswith(OLD_WORKTREE_PREFIX):
        remapped = os.path.join(REPO_ROOT, raw_path[len(OLD_WORKTREE_PREFIX):])
        if os.path.exists(remapped):
            return remapped
    raise FileNotFoundError(raw_path)


def normalize_reason(raw_reason: str) -> str:
    s = raw_reason.strip()
    if " (clause " in s and s.endswith(")"):
        return s.split(" (clause ", 1)[0]
    return s


def process_one(idx: int, row: dict, tmp_root: str) -> dict:
    t0 = time.monotonic()
    raw_input = row["input"]
    ont_path = resolve_input_path(raw_input)
    work_dir = os.path.join(tmp_root, f"item_{idx}")
    os.makedirs(work_dir, exist_ok=True)
    clauses_path = os.path.join(work_dir, "clauses.json")
    try:
        env = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "HOME": os.environ.get("HOME", "/home/leechuck"),
            "TMPDIR": work_dir,
            "KM_THREADS": "1",
            "KM_KEEP_CLAUSES": work_dir,
            "KM_REFERENCE_FORCE": "1",
            "KM_REFERENCE_STAGE": "0",
        }
        subprocess.run(
            ["timeout", "300", KM_BIN, "classify", "--route", "auto", ont_path],
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            check=False,
        )
        t_dump = time.monotonic() - t0
        if not os.path.isfile(clauses_path):
            return {
                "idx": idx,
                "family": row["family"],
                "input": raw_input,
                "status": "no_clauses",
                "exit_code": -1,
                "raw_reason": "clauses.json was not produced",
                "reason_group": "clauses.json was not produced",
                "wall_s": round(t_dump, 3),
                "dump_s": round(t_dump, 3),
                "rec_s": 0.0,
            }
        t1 = time.monotonic()
        proc = subprocess.run(
            ["timeout", "300", "taskset", "-c", "0,1", REF_BIN, "--recognize-only", clauses_path],
            env={"PATH": env["PATH"], "HOME": env["HOME"], "TMPDIR": work_dir},
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        t_rec = time.monotonic() - t1
        out_line = (proc.stdout.strip() or proc.stderr.strip()).splitlines()
        first_line = out_line[0].strip() if out_line else f"exit {proc.returncode}"
        status = "accepted" if proc.returncode == 0 else "rejected"
        return {
            "idx": idx,
            "family": row["family"],
            "input": raw_input,
            "status": status,
            "exit_code": proc.returncode,
            "raw_reason": first_line,
            "reason_group": "recognised" if status == "accepted" else normalize_reason(first_line),
            "wall_s": round(time.monotonic() - t0, 3),
            "dump_s": round(t_dump, 3),
            "rec_s": round(t_rec, 3),
        }
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)


def main() -> None:
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else None
    with open(TSV_PATH, newline="") as f:
        rows = [r for r in csv.DictReader(f, delimiter="\t") if r["route_off"] == "elc"]
    if limit is not None:
        rows = rows[:limit]
    tmp_root = os.path.join(SCRATCH_ROOT, "p2_tmp")
    os.makedirs(tmp_root, exist_ok=True)
    os.makedirs(OUT_DIR, exist_ok=True)

    results = [None] * len(rows)
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        futs = {
            pool.submit(process_one, idx, row, tmp_root): idx
            for idx, row in enumerate(rows)
        }
        done_count = 0
        for fut in concurrent.futures.as_completed(futs):
            idx = futs[fut]
            res = fut.result()
            results[idx] = res
            done_count += 1
            if done_count % 50 == 0 or done_count == len(rows):
                print(
                    f"[{done_count}/{len(rows)}] last={res['status']} ({res['raw_reason']}) "
                    f"wall={res['wall_s']}s (dump={res['dump_s']}s, rec={res['rec_s']}s)",
                    flush=True,
                )

    if limit is None:
        with open(OUT_TSV, "w", newline="") as f:
            writer = csv.DictWriter(
                f,
                fieldnames=[
                    "family",
                    "input",
                    "status",
                    "exit_code",
                    "reason_group",
                    "raw_reason",
                    "wall_s",
                    "dump_s",
                    "rec_s",
                ],
                delimiter="\t",
            )
            writer.writeheader()
            for r in results:
                writer.writerow({k: r[k] for k in writer.fieldnames})

    counts = collections.Counter(r["status"] for r in results)
    reasons = collections.Counter(r["reason_group"] for r in results if r["status"] != "accepted")
    print("SUMMARY:", dict(counts))
    for reason, cnt in reasons.most_common():
        print(f"  {cnt:4d}  {reason}")


if __name__ == "__main__":
    main()
