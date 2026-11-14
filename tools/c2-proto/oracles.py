"""External references: HermiT (batch JVM) and the km binary.

Paths come from the environment (C2_SCRATCH, C2_HERMIT_CP, C2_KM); outputs
go to $C2_SCRATCH/ofn. Never /tmp.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
from concurrent.futures import ThreadPoolExecutor

from kb import KB, to_ofn

SCRATCH = os.environ.get("C2_SCRATCH", "/mnt/data1/leechuck/km-work/v170/scratch/c2")
HERMIT_CP = os.environ.get(
    "C2_HERMIT_CP",
    f"{SCRATCH}/jclasses:" + open(
        "/mnt/data1/leechuck/km-work/wt/v170-plugin/protege-parity/target/classpath.txt").read().strip())
KM = os.environ.get("C2_KM", "/mnt/data1/leechuck/km-work/v170/scratch/w2p/km")
TMP = os.path.join(SCRATCH, "tmp")


def ofn_path(kb: KB) -> str:
    text = to_ofn(kb)
    h = hashlib.sha1(text.encode()).hexdigest()[:16]
    d = os.path.join(SCRATCH, "ofn")
    os.makedirs(d, exist_ok=True)
    p = os.path.join(d, f"{h}.ofn")
    if not os.path.exists(p):
        with open(p, "w") as f:
            f.write(text)
    return p


def hermit_batch(paths):
    """Map path -> 'true' | 'false' | 'timeout' | 'error:...'."""
    out = {}
    paths = list(dict.fromkeys(paths))
    env = dict(os.environ, TMPDIR=TMP)
    for i in range(0, len(paths), 400):
        chunk = paths[i:i + 400]
        r = subprocess.run(
            ["java", "-Xms64m", "-Xmx1g", "-XX:+UseSerialGC", f"-Djava.io.tmpdir={TMP}",
             "-cp", HERMIT_CP, "HermitBatch", *chunk],
            capture_output=True, text=True, env=env)
        for line in r.stdout.splitlines():
            if "\t" in line:
                p, v = line.split("\t", 1)
                out[p] = v
        for p in chunk:
            out.setdefault(p, "error:no output")
    return out


def km_one(path: str) -> str:
    env = dict(os.environ, TMPDIR=TMP, KM_THREADS="1")
    try:
        r = subprocess.run(["timeout", "300", KM, "classify", path], capture_output=True,
                           text=True, env=env, timeout=320)
    except subprocess.TimeoutExpired:
        return "timeout"
    try:
        line = next(l for l in r.stdout.splitlines() if l.startswith("{"))
        return "true" if json.loads(line)["consistent"] else "false"
    except (StopIteration, json.JSONDecodeError, KeyError):
        return "error:" + (r.stderr.strip().splitlines() or ["rc %d" % r.returncode])[-1][:200]


def km_batch(paths):
    paths = list(dict.fromkeys(paths))
    with ThreadPoolExecutor(max_workers=2) as ex:  # at most two km runs at once
        return dict(zip(paths, ex.map(km_one, paths)))
