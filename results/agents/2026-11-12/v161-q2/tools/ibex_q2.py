#!/usr/bin/env python3
"""Run one shard of the v1.6.1 Q2 forced suite on Ibex with run_p3_suite.py.

Usage: ibex_q2.py ROOT SHARD NSHARDS. Inputs keep their ws path in the
`input` column (so rows join with the v1.6.0 P3 data); the file is read from
ROOT/inputs/<ws path>, where the ws worktree prefix of fixtures is mapped to
the v1.6.1 worktree path used when the inputs were copied."""
import argparse, csv, os, sys
root, shard, nshards = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
sys.path.insert(0, root)
import run_p3_suite as p3
WT = "/mnt/data1/leechuck/km-work/wt/v1.6.1"
def resolve(raw_path, _worktree):
    p = raw_path
    if p.startswith(p3.OLD_WORKTREE_PREFIX):
        p = WT + p[len(p3.OLD_WORKTREE_PREFIX):]
    return os.path.join(root, "inputs") + p
p3.resolve_input_path = resolve
rows = list(csv.DictReader(open(os.path.join(root, "suite.tsv")), delimiter="\t"))
mine = [r for i, r in enumerate(rows) if i % nshards == shard]
shard_tsv = os.path.join(root, "shards", f"suite-{shard:03d}.tsv")
os.makedirs(os.path.dirname(shard_tsv), exist_ok=True)
with open(shard_tsv, "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0].keys()), delimiter="\t")
    w.writeheader(); w.writerows(mine)
args = argparse.Namespace(
    km=os.path.join(root, "bin/km"), checker=os.path.join(root, "bin/km-el-reference"),
    suite=shard_tsv, p2=os.path.join(root, "p2-recognition.tsv"),
    out_tsv=os.path.join(root, "out", f"p3-{shard:03d}.tsv"),
    scratch_dir=os.path.join(root, "scratch", f"{shard:03d}"), jobs=1, timeout=300)
os.chdir(root)
p3.run_suite(args)
