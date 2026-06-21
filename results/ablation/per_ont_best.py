#!/usr/bin/env python3
"""Per-ont best-config analysis: for each ont, among the configs that solve it
CLEANLY, find the min-wall and min-mem config and the spread vs a reference
config. Surface only LARGE differences (the user does not care about tiny %).
Join with structural features to see if the best flag is structurally
predictable.

Usage: per_ont_best.py <results_dir> <feats.jsonl> <ref_arm>
       [--minwall 0.5] [--minmem 80] [--pct 0.25]
"""
import glob
import json
import os
import sys

d, featf, ref = sys.argv[1], sys.argv[2], sys.argv[3]
MINWALL = 0.5   # seconds absolute
MINMEM = 80.0   # MB absolute
PCT = 0.25      # and at least this fractional improvement
for i, a in enumerate(sys.argv):
    if a == "--minwall": MINWALL = float(sys.argv[i + 1])
    if a == "--minmem": MINMEM = float(sys.argv[i + 1])
    if a == "--pct": PCT = float(sys.argv[i + 1])

F = {json.loads(l)["ont"]: json.loads(l) for l in open(featf)}
data = {}
for fp in glob.glob(os.path.join(d, "*.jsonl")):
    for ln in open(fp):
        ln = ln.strip()
        if not ln: continue
        r = json.loads(ln)
        data.setdefault(r["ont"], {})[r["arm"]] = r


def clean(r): return r.get("status") == "ok" and r.get("cmp_gold_match") is True


def feat(ont):
    o = ont.replace("ore_ont_", "").replace(".owl", "")
    r = F.get(o, {})
    return ("union=%s all=%s inv=%s nom=%s card=%s d_nonEL=%s ax=%s sz=%sMB" % (
        r.get("union"), r.get("all"), r.get("inverse"), r.get("nominal"),
        r.get("card"), r.get("d_nonEL"), r.get("axioms"),
        round((r.get("size") or 0) / 1e6, 1)))


big_wall, big_mem = [], []
win_wall, win_mem = {}, {}
for ont, arms in data.items():
    cl = {a: r for a, r in arms.items() if clean(r)}
    if ref not in cl:
        continue
    rw, rm = cl[ref]["wall_s"], cl[ref]["peak_mb"]
    bw_a = min(cl, key=lambda a: cl[a]["wall_s"]); bw = cl[bw_a]["wall_s"]
    bm_a = min(cl, key=lambda a: cl[a]["peak_mb"]); bm = cl[bm_a]["peak_mb"]
    if rw - bw >= MINWALL and (rw - bw) >= PCT * rw:
        big_wall.append((rw - bw, ont, ref, round(rw, 2), bw_a, round(bw, 2)))
        win_wall[bw_a] = win_wall.get(bw_a, 0) + 1
    if rm - bm >= MINMEM and (rm - bm) >= PCT * rm:
        big_mem.append((rm - bm, ont, ref, round(rm, 0), bm_a, round(bm, 0)))
        win_mem[bm_a] = win_mem.get(bm_a, 0) + 1

print("ref=%s   thresholds: wall>=%ss & >=%d%%, mem>=%dMB & >=%d%%\n"
      % (ref, MINWALL, PCT * 100, MINMEM, PCT * 100))
print("=== onts with LARGE wall improvement over ref (%d) ===" % len(big_wall))
for sp, ont, rf, rw, ba, bw in sorted(big_wall, reverse=True):
    oid = ont.replace("ore_ont_", "").replace(".owl", "")
    print("  %-7s %5.1fs->%-5.1fs (save %5.1fs) via %-14s | %s"
          % (oid, rw, bw, sp, ba, feat(ont)))
print("  WINNERS:", dict(sorted(win_wall.items(), key=lambda x: -x[1])))

print("\n=== onts with LARGE mem improvement over ref (%d) ===" % len(big_mem))
for sp, ont, rf, rm, ba, bm in sorted(big_mem, reverse=True):
    oid = ont.replace("ore_ont_", "").replace(".owl", "")
    print("  %-7s %6.0f->%-6.0f MB (save %5.0f) via %-14s | %s"
          % (oid, rm, bm, sp, ba, feat(ont)))
print("  WINNERS:", dict(sorted(win_mem.items(), key=lambda x: -x[1])))
