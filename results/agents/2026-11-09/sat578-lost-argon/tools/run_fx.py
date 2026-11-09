#!/usr/bin/env python3
"""Run KM on engine/tests/fixtures/sat578/*.ofn RUNS times (default 20) on
both auto and ht_bridge routes, 2 KM processes at a time, release flags.
"""
import concurrent.futures as cf
import glob
import json
import os
import subprocess
import sys
import time

KM_BIN = sys.argv[1]
FX_DIR = sys.argv[2]
OUT_TSV = sys.argv[3]
RUNS = int(sys.argv[4]) if len(sys.argv) > 4 else 20

RELEASE = {
    "KM_HT_DDB": "1",
    "KM_HT_NATIVE_FULL": "1",
    "KM_CACHE_CONFORMANCE": "1",
    "KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE": "1",
    "KM_FAST_IRI_GRAMMAR": "1",
    "KM_THREADS": "1",
}


def loc(x):
    return x.split("#")[-1].split(":")[-1].strip("<>")


def compare(g, k):
    if g["consistent"] != k.get("consistent"):
        return "WRONG", f"consistency gold={g['consistent']} km={k.get('consistent')}"
    gs = {(loc(a), loc(b)) for a, b in g["subsumptions"]}
    ks = {(loc(a), loc(b)) for a, b in k.get("subsumptions", [])}
    ks = {p for p in ks if p[0] != p[1] and p[1] != "Thing" and p[0] != "Nothing"}
    gu = {loc(x) for x in g["unsatisfiable"]}
    ku = {loc(x) for x in k.get("unsatisfiable", [])}
    gs = {p for p in gs if p[0] not in gu and p[1] not in gu}
    ks = {p for p in ks if p[0] not in ku and p[1] not in ku}
    if not g["consistent"]:
        return "ok", ""
    if (gs, gu) == (ks, ku):
        return "ok", ""
    return "WRONG", f"missing={sorted(gs - ks)[:4]} extra={sorted(ks - gs)[:4]}"


def run_job(args):
    path, spec, run = args
    gp = os.path.splitext(path)[0] + ".hermit.json"
    with open(gp) as f:
        g = json.load(f)
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    env.update(RELEASE)
    if spec != "auto":
        env["KM_ROUTE"] = spec
    t0 = time.time()
    try:
        p = subprocess.run(
            [KM_BIN, "classify", path], env=env, capture_output=True, text=True, timeout=60
        )
    except subprocess.TimeoutExpired:
        return f"{path}\t{spec}\t{run}\tTIMEOUT\t{time.time() - t0:.2f}\t"
    dt = time.time() - t0
    if p.returncode != 0 or not p.stdout.strip():
        return f"{path}\t{spec}\t{run}\tERR\t{dt:.2f}\trc={p.returncode}"
    k = json.loads(p.stdout)
    v, d = compare(g, k)
    return f"{path}\t{spec}\t{run}\t{v}\t{dt:.2f}\t{d}"


def main():
    files = sorted(glob.glob(os.path.join(FX_DIR, "*.ofn")))
    jobs = [(f, s, r) for f in files for s in ["ht_bridge", "auto"] for r in range(1, RUNS + 1)]
    os.makedirs(os.path.dirname(os.path.abspath(OUT_TSV)), exist_ok=True)
    with open(OUT_TSV, "w") as out, cf.ThreadPoolExecutor(2) as ex:
        for line in ex.map(run_job, jobs):
            out.write(line + "\n")
            out.flush()


if __name__ == "__main__":
    main()
