#!/usr/bin/env python3
"""Build the (reasoner, ontology) job list for the ORE DL+EL classification
sweep and split it into K chunk files for an exclusive-node SLURM array.

Jobs are shuffled with a fixed seed so each chunk gets a balanced mix of
reasoners and ontology sizes (no single chunk inherits all the slow runs).
"""
import os
import random
import sys

HOME = os.path.expanduser("~")
UNION = "/tmp/union_class.txt"
ONTDIR = os.path.join(HOME, "ore2015", "pool_sample", "files")
JOBDIR = os.path.join(HOME, "bench", "ore_jobs")
REASONERS = ["konclude", "hermit", "elk", "sequoia", "km"]
K = int(sys.argv[1]) if len(sys.argv) > 1 else 60

os.makedirs(JOBDIR, exist_ok=True)
with open(UNION) as f:
    onts = [l.strip() for l in f if l.strip()]

# order onts large-first so chunks interleave heavy parses
onts_sized = []
for o in onts:
    p = os.path.join(ONTDIR, o)
    sz = os.path.getsize(p) if os.path.exists(p) else 0
    onts_sized.append((sz, o))
onts_sized.sort(reverse=True)

jobs = [(r, o) for _, o in onts_sized for r in REASONERS]
random.seed(20260604)
random.shuffle(jobs)

chunks = [[] for _ in range(K)]
for i, job in enumerate(jobs):
    chunks[i % K].append(job)

for ci, ch in enumerate(chunks):
    with open(os.path.join(JOBDIR, f"chunk_{ci:03d}.txt"), "w") as f:
        for r, o in ch:
            f.write(f"{r} {o}\n")

print(f"onts={len(onts)} reasoners={len(REASONERS)} jobs={len(jobs)} chunks={K} "
      f"~{len(jobs)//K}/chunk")
