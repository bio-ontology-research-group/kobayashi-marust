#!/usr/bin/env python3
"""Run a KM binary on the unique (pool, seed, route) rows of lost-answers-base.tsv
RUNS times each (default 3), 2 KM processes at a time, 300 s cap, release flags.
"""
import concurrent.futures as cf
import json
import os
import signal
import subprocess
import sys
import time

KM_BIN = sys.argv[1]
BASE_TSV = sys.argv[2]
OUT_TSV = sys.argv[3]
RUNS = int(sys.argv[4]) if len(sys.argv) > 4 else 3
TIMEOUT = int(os.environ.get("KM_CAP", "300"))
THREADS = int(os.environ.get("KM_JOBS", "2"))

SCRATCH = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch"
GOLD_MAP = {
    "sat578-fam": f"{SCRATCH}/sat578/famgold",
    "bridge-nn-rule-fam": f"{SCRATCH}/bridge-nn-rule/fam/gold",
    "bridge-reflexive-fam": f"{SCRATCH}/bridge-reflexive/fam/gold",
}

RELEASE = {
    "KM_HT_DDB": "1",
    "KM_HT_NATIVE_FULL": "1",
    "KM_CACHE_CONFORMANCE": "1",
    "KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE": "1",
    "KM_FAST_IRI_GRAMMAR": "1",
    "KM_THREADS": "1",
    "KM_TIMING": "1",
}


def strip(name):
    return name.lstrip(":").split("#")[-1]


def gold_dir(pool):
    if pool in GOLD_MAP:
        return GOLD_MAP[pool]
    if pool == "bridge-satcache-fam":
        return f"{SCRATCH}/bridge-satcache/famgold"
    if pool.startswith("bridge-self-pools-"):
        sub = pool[len("bridge-self-pools-") :]
        return f"{SCRATCH}/bridge-self/pools/{sub}/gold"
    raise KeyError(pool)


def load_gold(pool, path):
    stem = os.path.splitext(os.path.basename(path))[0]
    gp = os.path.join(gold_dir(pool), stem + ".json")
    with open(gp) as f:
        d = json.load(f)
    uns = frozenset(strip(c) for c in d["unsatisfiable"])
    subs = frozenset(
        (strip(a), strip(b))
        for a, b in d["subsumptions"]
        if strip(a) not in uns and strip(b) not in uns and strip(a) != strip(b)
    )
    return bool(d["consistent"]), subs, uns


def run_one(item):
    pool, path, route = item
    gold = load_gold(pool, path)
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    env.update(RELEASE)
    if route != "auto":
        env["KM_ROUTE"] = route
    t0 = time.time()
    cap = 60 if "refl1213" in path else TIMEOUT
    p = subprocess.Popen(
        [KM_BIN, "classify", "--lines", path],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        start_new_session=True,
    )
    try:
        out, err = p.communicate(timeout=cap)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.communicate()
        dt = time.time() - t0
        return f"{pool}\t{path}\t{route}\tTIMEOUT\t{dt:.2f}\t\t\t\t\t"
    dt = time.time() - t0
    cons, subs, uns = None, set(), set()
    for line in out.splitlines():
        t = line.split("\t")
        if t[0].startswith("CONSISTENT"):
            cons = t[0].endswith("1")
        elif t[0] == "SUB" and len(t) == 3:
            subs.add((strip(t[1]), strip(t[2])))
        elif t[0] == "UNSAT" and len(t) == 2:
            uns.add(strip(t[1]))
    if cons is None:
        return f"{pool}\t{path}\t{route}\tERR\t{dt:.2f}\t\t\t\t\t"
    subs = frozenset(
        s for s in subs if s[0] not in uns and s[1] not in uns and s[0] != s[1]
    )
    if not gold[0]:
        verdict = "ok" if not cons else "WRONG"
        return f"{pool}\t{path}\t{route}\t{verdict}\t{dt:.2f}\t0\t0\t0\t0\t{int(cons != gold[0])}"
    ms, es = len(gold[1] - subs), len(subs - gold[1])
    mu, eu = len(gold[2] - uns), len(uns - gold[2])
    cm = int(cons != gold[0])
    verdict = "ok" if (ms, es, mu, eu, cm) == (0, 0, 0, 0, 0) else "WRONG"
    return f"{pool}\t{path}\t{route}\t{verdict}\t{dt:.2f}\t{ms}\t{es}\t{mu}\t{eu}\t{cm}"


def main():
    seen = []
    with open(BASE_TSV) as f:
        for line in f:
            if line.startswith("#") or not line.strip():
                continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 3:
                key = (parts[0], parts[1], parts[2])
                if key not in seen:
                    seen.append(key)
    jobs = []
    for _ in range(RUNS):
        for key in seen:
            jobs.append(key)
    os.makedirs(os.path.dirname(os.path.abspath(OUT_TSV)), exist_ok=True)
    with open(OUT_TSV, "w") as out, cf.ThreadPoolExecutor(THREADS) as ex:
        for line in ex.map(run_one, jobs):
            out.write(line + "\n")
            out.flush()
            print(line, flush=True)


if __name__ == "__main__":
    main()
