#!/usr/bin/env python3
"""Per-ont optimal-config analysis from the lattice sweep + generalization.
Usage: lattice_analyze.py <latt_res_dir> <feats.jsonl> [ref=full16]"""
import glob
import json
import statistics as st
import sys

d = sys.argv[1]
F = {json.loads(l)["ont"]: json.loads(l) for l in open(sys.argv[2])}
REF = sys.argv[3] if len(sys.argv) > 3 else "full16"

data = {}
for fp in glob.glob(d + "/*.jsonl"):
    for ln in open(fp):
        ln = ln.strip()
        if not ln: continue
        r = json.loads(ln)
        data.setdefault(r["ont"], {})[r["arm"]] = r


def clean(r): return r.get("status") == "ok" and r.get("cmp_gold_match") is True
def oid(o): return o.replace("ore_ont_", "").replace(".owl", "")


cfgs = sorted({a for o in data for a in data[o]})
onts = [o for o in data if REF in data[o] and clean(data[o][REF])]
print("lattice: %d configs, %d onts clean under %s\n" % (len(cfgs), len(onts), REF))

# ---- lever main effects: median peak_mb / wall with lever toggled ----
def has(cfg, tok): return tok in cfg
LEVERS = [("threads=1", lambda c: "t1" in c or c.endswith("_t1")),
          ("noelc", lambda c: "noelc" in c or "lean" in c or "lowmem" in c or "min" in c),
          ("noht", lambda c: "noht" in c or "lean" in c or "leanmax" in c or c == "min_t1"),
          ("nocentral", lambda c: "nocentral" in c or "lowmem" in c or "leanmax" in c or c == "min_t1"),
          ("noabsorb", lambda c: "noabsorb" in c or c == "min_t1")]

# ---- per-ont optimum (only over CLEAN configs for that ont) ----
print("=== corpus-level router potential (over %d onts) ===" % len(onts))
ref_mem = [data[o][REF]["peak_mb"] for o in onts]
ref_wall = [data[o][REF]["wall_s"] for o in onts]
best_mem, best_wall = [], []
win_mem, win_wall = {}, {}
pareto_rows = []
for o in onts:
    cl = {a: r for a, r in data[o].items() if clean(r)}
    bm = min(cl, key=lambda a: cl[a]["peak_mb"]); bw = min(cl, key=lambda a: cl[a]["wall_s"])
    best_mem.append(cl[bm]["peak_mb"]); best_wall.append(cl[bw]["wall_s"])
    win_mem[bm] = win_mem.get(bm, 0) + 1
    win_wall[bw] = win_wall.get(bw, 0) + 1
    pareto_rows.append((o, bm, cl[bm]["peak_mb"], data[o][REF]["peak_mb"]))
print("median peak_mb:  %s (ref) -> %s (per-ont best)  [%.1fx]" % (
    round(st.median(ref_mem)), round(st.median(best_mem)),
    st.median(ref_mem) / max(st.median(best_mem), 1)))
print("median wall_s :  %s (ref) -> %s (per-ont best)" % (
    round(st.median(ref_wall), 2), round(st.median(best_wall), 2)))
print("total GB-s of peak (ref) %.0f -> (best) %.0f" % (
    sum(ref_mem) / 1024, sum(best_mem) / 1024))
print("\nbest-MEM config frequency:", dict(sorted(win_mem.items(), key=lambda x: -x[1])))
print("best-WALL config frequency:", dict(sorted(win_wall.items(), key=lambda x: -x[1])))

# ---- generalization: feature medians per best-mem config group ----
def feat(o, k):
    return F.get(oid(o), {}).get(k)
print("\n=== generalize: feature medians by best-MEM config ===")
print("%-18s%6s%10s%10s%9s%7s%7s%7s" % ("best_mem_cfg", "n", "med_ax", "med_szMB", "d_nonEL", "union", "inv", "card"))
groups = {}
for o in onts:
    cl = {a: r for a, r in data[o].items() if clean(r)}
    bm = min(cl, key=lambda a: cl[a]["peak_mb"])
    groups.setdefault(bm, []).append(o)
for cfg, gonts in sorted(groups.items(), key=lambda x: -len(x[1])):
    def m(k):
        xs = [feat(o, k) for o in gonts if feat(o, k) is not None]
        return round(st.median(xs), 3) if xs else None
    print("%-18s%6d%10s%10s%9s%7s%7s%7s" % (
        cfg, len(gonts), m("axioms"), round((m("size") or 0) / 1e6, 1),
        m("d_nonEL"), m("union"), m("inverse"), m("card")))
