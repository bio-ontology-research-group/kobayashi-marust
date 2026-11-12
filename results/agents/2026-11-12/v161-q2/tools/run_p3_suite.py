#!/usr/bin/env python3
"""Acceptance clause P3 runner: forced reference-stage suite evaluation.

Runs `km classify --lines` twice per input across the 1,781-input checkers-on
suite (`results/agents/2026-10-30/checkers-on-suite/per-input.tsv`), at most
4 processes at a time (`--jobs 4`), with `KM_THREADS=1` under `timeout 300`:

  1. Unforced (production): `KM_REFERENCE_STAGE=0`
  2. Forced (reference):    `KM_REFERENCE_FORCE=1`,
                            `KM_EL_REFERENCE_CHECKER=<km-el-reference>`

Usage:
  python3 -I results/agents/2026-11-10/v160-p3-suite/tools/run_p3_suite.py run \
      --km engine/target/release/km \
      --checker lean/.lake/build/bin/km-el-reference \
      --suite results/agents/2026-10-30/checkers-on-suite/per-input.tsv \
      --p2 results/agents/2026-11-10/v160-recognizer-perf/p2-recognition.tsv \
      --out-tsv results/agents/2026-11-10/v160-p3-suite/data/p3-results.tsv \
      --scratch-dir .work/agent-scratch/v160-p3-suite \
      [--jobs 4] [--timeout 300]

  python3 -I results/agents/2026-11-10/v160-p3-suite/tools/run_p3_suite.py summarize \
      --tsv results/agents/2026-11-10/v160-p3-suite/data/p3-results.tsv \
      --p2 results/agents/2026-11-10/v160-recognizer-perf/p2-recognition.tsv
"""

import argparse
import concurrent.futures as cf
import csv
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
from collections import Counter

OLD_WORKTREE_PREFIX = (
    "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/"
    ".work/worktrees/fix-checkers-on-suite"
)
ROUTE_RE = re.compile(r"frontend done @ [0-9.]+s route=(\S+)")


def strip_iri(name: str) -> str:
    return name.lstrip(":").split("#")[-1].split(">")[0]


def parse_answer_digest(text: str):
    """Compute the checkers-on suite 16-hex-char SHA-256 answer digest."""
    cons = None
    subs = set()
    uns = set()
    for line in text.splitlines():
        parts = line.split("\t")
        if parts[0].startswith("CONSISTENT"):
            cons = parts[0].strip().endswith("1")
        elif parts[0] == "SUB" and len(parts) == 3:
            subs.add((strip_iri(parts[1]), strip_iri(parts[2])))
        elif parts[0] == "UNSAT" and len(parts) == 2:
            uns.add(strip_iri(parts[1]))
    if cons is None:
        return None
    # Normalisation (v1.6.0 P3 rerun): `U SUB X` is entailed for every X when
    # U is unsatisfiable, and the production routes print a route-dependent
    # subset of those rows, so rows with an unsatisfiable subclass are dropped.
    # A row with a satisfiable subclass and an unsatisfiable superclass cannot
    # occur; it is reported as an anomaly by prefixing the digest with ANOMALY-, not dropped.
    anomalies = [(a, b) for (a, b) in sorted(subs) if a not in uns and b in uns]
    subs = {(a, b) for (a, b) in subs if a not in uns}
    if not cons:
        return hashlib.sha256(b"[false,[],[]]").hexdigest()[:16]
    blob = json.dumps(
        [True, sorted(subs), sorted(uns)],
        separators=(",", ":"),
    ).encode()
    return ("ANOMALY-" if anomalies else "") + hashlib.sha256(blob).hexdigest()[:16]


def resolve_input_path(raw_path: str, worktree: str) -> str:
    if raw_path.startswith(OLD_WORKTREE_PREFIX):
        return raw_path.replace(OLD_WORKTREE_PREFIX, worktree, 1)
    return raw_path


def run_km_once(
    km_bin: str,
    input_path: str,
    tmp_dir: str,
    timeout_s: int,
    extra_env: dict,
):
    os.makedirs(tmp_dir, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    env.update({
        "KM_THREADS": "1",
        "KM_TIMING": "1",
        "LEAN_STACK_SIZE_KB": "262144",
        "TMPDIR": tmp_dir,
    })
    env.update(extra_env)

    t0 = time.monotonic()
    proc = subprocess.Popen(
        [km_bin, "classify", input_path, "--lines"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout_s)
        wall_s = time.monotonic() - t0
        status = "ok" if proc.returncode == 0 else f"exit{proc.returncode}"
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
        wall_s = time.monotonic() - t0
        status = "timeout"
    finally:
        subprocess.run(["rm", "-rf", tmp_dir], check=False)

    routes = []
    ref_stage_line = ""
    ref_phases = []
    last_err = ""
    for line in stderr.splitlines():
        s = line.strip()
        m_route = ROUTE_RE.search(s)
        if m_route:
            routes.append(m_route.group(1))
        if s.startswith("KM_TIMING KM_REFERENCE_TIMING phase="):
            parts = dict(kv.split("=", 1) for kv in s.split()[2:] if "=" in kv)
            ref_phases.append(f"{parts.get('phase','?')}:{parts.get('ms','?')}")
        if "KM_REFERENCE_STAGE" in s:
            ref_stage_line = s[:400]
        if s and not s.startswith("KM_TIMING") and not s.startswith("KM_LEAN_CHECK"):
            last_err = s[:300]

    digest = parse_answer_digest(stdout) if status == "ok" else None
    return {
        "status": status,
        "wall_s": round(wall_s, 3),
        "route": routes[-1] if routes else "-",
        "digest": digest,
        "ref_stage_line": ref_stage_line,
        "ref_phases": ref_phases,
        "last_err": last_err,
    }


def probe_reference_procedure(km_bin: str, checker_bin: str, input_path: str, tmp_dir: str) -> str:
    """Determine whether a published reference-stage answer used EL or ALC."""
    os.makedirs(tmp_dir, exist_ok=True)
    try:
        env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
        env.update({
            "KM_THREADS": "1",
            "KM_REFERENCE_FORCE": "1",
            "KM_EL_REFERENCE_CHECKER": "/bin/false",
            "KM_KEEP_CLAUSES": tmp_dir,
            "TMPDIR": tmp_dir,
        })
        subprocess.run(
            [km_bin, "classify", input_path, "--lines"],
            env=env,
            capture_output=True,
            timeout=60,
        )
        cjson = os.path.join(tmp_dir, "clauses.json")
        if not os.path.exists(cjson):
            return "-"
        r_el = subprocess.run(
            [checker_bin, "--recognize-only", "--procedure", "el", cjson],
            env={**env, "LEAN_STACK_SIZE_KB": "262144"},
            capture_output=True,
            text=True,
            timeout=60,
        )
        if r_el.returncode == 0:
            return "EL"
        r_alc = subprocess.run(
            [checker_bin, "--recognize-only", "--procedure", "alc", cjson],
            env={**env, "LEAN_STACK_SIZE_KB": "262144"},
            capture_output=True,
            text=True,
            timeout=60,
        )
        if r_alc.returncode == 0:
            return "ALC"
        return "-"
    finally:
        subprocess.run(["rm", "-rf", tmp_dir], check=False)


def classify_forced_outcome(
    forced_res: dict,
    km_bin: str,
    checker_bin: str,
    input_path: str,
    tmp_dir: str,
) -> tuple[str, str]:
    """Return (forced_outcome, procedure) from a forced run record."""
    ref_line = forced_res.get("ref_stage_line", "")
    status = forced_res["status"]
    if status == "timeout":
        return ("timeout", "-")
    if ref_line.startswith("KM_TIMING KM_REFERENCE_STAGE published"):
        parts = ref_line.split()
        proc = parts[3] if len(parts) > 3 else probe_reference_procedure(
            km_bin, checker_bin, input_path, tmp_dir
        )
        return ("published", proc)
    if ref_line.startswith("KM_TIMING KM_REFERENCE_STAGE declined: "):
        reason = ref_line[len("KM_TIMING KM_REFERENCE_STAGE declined: "):].strip()
        return (f"declined: {reason}", "-")
    if status == "ok":
        return ("published (unguarded production path)", "production_unguarded")
    if status == "exit3":
        reason = forced_res.get("last_err", "").removeprefix("unsupported: ").strip()
        return (f"declined: {reason or 'out of fragment'}", "-")
    return ("error", "-")


def load_p2_map(p2_path: str) -> dict[str, str]:
    p2 = {}
    with open(p2_path, newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            p2[row["input"]] = row["status"]
    return p2


def run_suite(args):
    worktree = os.getcwd()
    p2_map = load_p2_map(args.p2)
    with open(args.suite, newline="") as f:
        suite_rows = list(csv.DictReader(f, delimiter="\t"))

    os.makedirs(os.path.dirname(args.out_tsv), exist_ok=True)
    os.makedirs(args.scratch_dir, exist_ok=True)

    def eval_input(idx_row):
        idx, row = idx_row
        raw_path = row["input"]
        path = resolve_input_path(raw_path, worktree)
        unf = run_km_once(
            args.km,
            path,
            os.path.join(args.scratch_dir, f"tmp_unf_{idx}"),
            args.timeout,
            {"KM_REFERENCE_STAGE": "0"},
        )
        frc = run_km_once(
            args.km,
            path,
            os.path.join(args.scratch_dir, f"tmp_frc_{idx}"),
            args.timeout,
            {
                "KM_REFERENCE_FORCE": "1",
                "KM_REFERENCE_TIMING": "1",
                "KM_EL_REFERENCE_CHECKER": args.checker,
            },
        )
        forced_outcome, proc = classify_forced_outcome(
            frc,
            args.km,
            args.checker,
            path,
            os.path.join(args.scratch_dir, f"tmp_prb_{idx}"),
        )
        return {
            "family": row["family"],
            "input": raw_path,
            "p2_status": p2_map.get(raw_path, "-"),
            "unforced_route": unf["route"],
            "unforced_status": unf["status"],
            "unforced_digest": unf["digest"] or "-",
            "unforced_wall_s": f"{unf['wall_s']:.3f}",
            "forced_status": frc["status"],
            "forced_outcome": forced_outcome,
            "forced_procedure": proc,
            "forced_digest": frc["digest"] or "-",
            "forced_wall_s": f"{frc['wall_s']:.3f}",
            "forced_ref_phases": ",".join(frc.get("ref_phases", [])) or "-",
        }

    fieldnames = [
        "family", "input", "p2_status", "unforced_route", "unforced_status",
        "unforced_digest", "unforced_wall_s", "forced_status", "forced_outcome",
        "forced_procedure", "forced_digest", "forced_wall_s", "forced_ref_phases",
    ]
    # Resumable: each finished row is appended at once, so a crash of this
    # driver (the host is short of commit memory) loses nothing.
    import threading
    lock = threading.Lock()
    done = set()
    if os.path.exists(args.out_tsv):
        with open(args.out_tsv, newline="") as f:
            done = {r["input"] for r in csv.DictReader(f, delimiter="\t")}
    new_file = not os.path.exists(args.out_tsv)
    out_f = open(args.out_tsv, "a", newline="")
    writer = csv.DictWriter(out_f, fieldnames=fieldnames, delimiter="\t")
    if new_file:
        writer.writeheader()

    def guarded(idx_row):
        if idx_row[1]["input"] in done:
            return
        while True:
            try:
                res = eval_input(idx_row)
                break
            except (MemoryError, OSError):
                time.sleep(60)
        with lock:
            writer.writerow(res)
            out_f.flush()

    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        list(ex.map(guarded, enumerate(suite_rows)))
    out_f.close()


def summarize_tsv(tsv_path: str, p2_path: str):
    p2_map = load_p2_map(p2_path)
    with open(tsv_path, newline="") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))

    print(f"Total rows in {tsv_path}: {len(rows)}")
    p2_rec_rows = [r for r in rows if p2_map.get(r["input"]) == "accepted"]
    p2_pub = [
        r for r in p2_rec_rows
        if r["forced_outcome"] == "published"
        and r["forced_digest"] == r["unforced_digest"]
        and r["unforced_digest"] != "-"
    ]
    print(f"Check 1 (P2 recognised={len(p2_rec_rows)}): reference-published & matching={len(p2_pub)}")

    other_pub = [
        r for r in rows
        if p2_map.get(r["input"]) != "accepted"
        and r["forced_outcome"].startswith("published")
    ]
    other_pub_matching = [
        r for r in other_pub
        if r["unforced_digest"] != "-" and r["forced_digest"] == r["unforced_digest"]
    ]
    print(
        f"Check 2 (other forced publications={len(other_pub)}): "
        f"matching unforced={len(other_pub_matching)}"
    )

    diffs = [
        r for r in rows
        if r["unforced_digest"] != "-"
        and r["forced_digest"] != "-"
        and r["unforced_digest"] != r["forced_digest"]
    ]
    print(f"Check 3 (answer digest mismatches anywhere): {len(diffs)}")

    unforced_nonpub = [r for r in rows if r["unforced_digest"] == "-"]
    print(
        f"Check 4 (unforced published nothing={len(unforced_nonpub)}): "
        f"{Counter(r['forced_outcome'] for r in unforced_nonpub)}"
    )


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_run = sub.add_parser("run")
    p_run.add_argument("--km", required=True)
    p_run.add_argument("--checker", required=True)
    p_run.add_argument("--suite", required=True)
    p_run.add_argument("--p2", required=True)
    p_run.add_argument("--out-tsv", required=True)
    p_run.add_argument("--scratch-dir", required=True)
    p_run.add_argument("--jobs", type=int, default=4)
    p_run.add_argument("--timeout", type=int, default=300)

    p_sum = sub.add_parser("summarize")
    p_sum.add_argument("--tsv", required=True)
    p_sum.add_argument("--p2", required=True)

    args = ap.parse_args()
    if args.cmd == "run":
        run_suite(args)
    elif args.cmd == "summarize":
        summarize_tsv(args.tsv, args.p2)


if __name__ == "__main__":
    main()
