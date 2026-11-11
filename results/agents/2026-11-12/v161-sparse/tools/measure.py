#!/usr/bin/env python3
"""Forced reference-stage measurement for v161-sparse (Part D).

usage: measure.py <km> <checker> <runner.py> <inputs.tsv> <out.tsv> <scratch> [n] [jobs]
inputs.tsv: size, family, input, unforced_digest, unforced_wall, v160_outcome
"""
import concurrent.futures as cf
import importlib.util
import os
import re
import subprocess
import sys
import time

km, checker, runner, inputs, out_tsv, scratch = sys.argv[1:7]
n = int(sys.argv[7]) if len(sys.argv) > 7 else 20
jobs = int(sys.argv[8]) if len(sys.argv) > 8 else 2
spec = importlib.util.spec_from_file_location("runner", runner)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

rows = [l.rstrip("\n").split("\t") for l in open(inputs) if l.strip()][:n]
done = set()
if os.path.exists(out_tsv):
    done = {l.split("\t")[1] for l in open(out_tsv) if not l.startswith("size")}


def run(row):
    size, fam, inp, udig, uwall, v160 = row
    tag = os.path.basename(inp)
    tmp = os.path.join(scratch, "run-" + tag)
    os.makedirs(tmp, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    env.update({
        "KM_THREADS": "1", "KM_TIMING": "1", "KM_REFERENCE_FORCE": "1",
        "KM_EL_REFERENCE_CHECKER": checker, "LEAN_STACK_SIZE_KB": os.environ.get("MEASURE_STACK_KB", "262144"),
        "TMPDIR": tmp,
    })
    tv = os.path.join(tmp, "time.txt")
    t0 = time.monotonic()
    p = subprocess.run(
        ["/usr/bin/time", "-v", "-o", tv, "timeout", "300", km, "classify", inp, "--lines"],
        env=env, capture_output=True, text=True)
    wall = time.monotonic() - t0
    rss_kb = "-"
    try:
        for line in open(tv):
            if "Maximum resident set size" in line:
                rss_kb = line.split(":")[1].strip()
    except OSError:
        pass
    status = "ok" if p.returncode == 0 else ("timeout" if p.returncode == 124 else f"exit{p.returncode}")
    stage = "-"
    timing = []
    for line in p.stderr.splitlines():
        if "KM_REFERENCE_STAGE" in line:
            stage = line.strip()[:200]
        if line.startswith("KM_TIMING") and ("reference" in line.lower() or "frontend done" in line):
            timing.append(line.strip()[:120])
    published = "yes" if "KM_REFERENCE_STAGE published" in p.stderr else "no"
    digest = mod.parse_answer_digest(p.stdout) if p.returncode == 0 else None
    match = "-" if digest is None or udig in ("", "-") else ("match" if digest == udig else "MISMATCH")
    subprocess.run(["rm", "-rf", tmp], check=False)
    return [size, inp, fam, status, f"{wall:.1f}", rss_kb, published, digest or "-", udig, match,
            stage.replace("\t", " "), v160, " | ".join(timing).replace("\t", " ")]


hdr = ["size", "input", "family", "status", "wall_s", "max_rss_kb", "published", "forced_digest",
       "unforced_digest", "digest", "stage_line", "v160_forced_outcome", "timing"]
new = not os.path.exists(out_tsv)
with open(out_tsv, "a") as f:
    if new:
        f.write("\t".join(hdr) + "\n")
    todo = [r for r in rows if r[2] not in done]
    with cf.ThreadPoolExecutor(max_workers=jobs) as ex:
        for res in ex.map(run, todo):
            f.write("\t".join(res) + "\n")
            f.flush()
            print("\t".join(res[:10]), flush=True)
