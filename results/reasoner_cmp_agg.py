#!/usr/bin/env python3
"""Aggregate the side-by-side reasoner comparison (cmp_res/ont_*.jsonl).

Each per-ont file holds one JSON record per reasoner (from ore_runone.py) plus
one {"gold_cmp":...} line per reasoner. Emits:
  - per-reasoner status counts (ok/timeout/memout/error/unsupported)
  - per-reasoner gold MATCH/DIFF/NOSIG counts (correctness)
  - a time x mem grid: how many onts each reasoner solves within (<=T, <=M),
    using the recorded actual wall_s / peak_mb of the OK runs
  - wall/peak percentiles for the OK runs
"""
import json
import os
import sys
from collections import defaultdict

RES = sys.argv[1] if len(sys.argv) > 1 else "cmp_res"
REASONERS = ["konclude", "elk", "hermit", "km"]

recs = defaultdict(dict)      # ont -> reasoner -> record
gold = defaultdict(dict)      # ont -> reasoner -> MATCH/DIFF/NOSIG

for fn in os.listdir(RES):
    if not fn.endswith(".jsonl"):
        continue
    for line in open(os.path.join(RES, fn)):
        line = line.strip()
        if not line:
            continue
        try:
            o = json.loads(line)
        except Exception:
            continue
        if "gold_cmp" in o:
            gold[o["ont"]][o["gold_cmp"]] = o["gold"]
        elif "reasoner" in o:
            ont = o["ont"].replace("ore_ont_", "").replace(".owl", "")
            recs[ont][o["reasoner"]] = o

onts = sorted(recs.keys(), key=lambda x: int(x) if x.isdigit() else 0)
N = len(onts)
print(f"# ontologies with >=1 record: {N}\n")

# ---- status counts ----
print("## Status counts (per reasoner)")
hdr = f"{'reasoner':<10} {'ok':>5} {'timeout':>8} {'memout':>7} {'error':>6} {'unsup':>6} {'parse':>6} {'noresult':>9}"
print(hdr)
for r in REASONERS:
    c = defaultdict(int)
    for ont in onts:
        rec = recs[ont].get(r)
        if rec is None:
            c["noresult"] += 1
        else:
            c[rec.get("status", "?")] += 1
    print(f"{r:<10} {c['ok']:>5} {c['timeout']:>8} {c['memout']:>7} {c['error']:>6} "
          f"{c['unsupported']:>6} {c['parse_error']:>6} {c['noresult']:>9}")

# ---- correctness vs gold ----
print("\n## Correctness vs Konclude-gold (sig.gz byte-identical)")
print(f"{'reasoner':<10} {'MATCH':>6} {'DIFF':>5} {'NOSIG':>6}")
for r in REASONERS:
    c = defaultdict(int)
    for ont in onts:
        c[gold[ont].get(r, "NOSIG")] += 1
    print(f"{r:<10} {c['MATCH']:>6} {c['DIFF']:>5} {c['NOSIG']:>6}")

# ---- time x mem solvability grid (OK runs only, actual wall/peak) ----
TS = [1, 5, 10, 30, 60, 120, 300, 600]
MS = [2, 4, 8, 16, 32, 56]
print("\n## Solvable-within grid: count of onts with status=ok AND wall<=T AND peak<=M")
for r in REASONERS:
    print(f"\n### {r}   (rows=mem GB, cols=time s)")
    print("memGB\\t  " + "".join(f"{t:>6}" for t in TS))
    for m in MS:
        row = []
        for t in TS:
            n = 0
            for ont in onts:
                rec = recs[ont].get(r)
                if rec and rec.get("status") == "ok":
                    w = rec.get("wall_s") or 1e9
                    p = rec.get("peak_mb") or 1e9
                    if w <= t and p <= m * 1024:
                        n += 1
            row.append(n)
        print(f"{m:>5}    " + "".join(f"{n:>6}" for n in row))

# ---- wall/peak percentiles of OK runs ----
def pct(vals, q):
    if not vals:
        return None
    vals = sorted(vals)
    i = min(len(vals) - 1, int(q * len(vals)))
    return vals[i]

print("\n## Wall (s) / Peak (MB) percentiles over OK runs")
print(f"{'reasoner':<10} {'n_ok':>5} | {'wall_p50':>8} {'wall_p90':>8} {'wall_p99':>8} {'wall_max':>8} | "
      f"{'peak_p50':>8} {'peak_p90':>8} {'peak_max':>8}")
for r in REASONERS:
    ws = [recs[o][r]["wall_s"] for o in onts
          if recs[o].get(r) and recs[o][r].get("status") == "ok" and recs[o][r].get("wall_s") is not None]
    ps = [recs[o][r]["peak_mb"] for o in onts
          if recs[o].get(r) and recs[o][r].get("status") == "ok" and recs[o][r].get("peak_mb") is not None]
    print(f"{r:<10} {len(ws):>5} | {pct(ws,.5):>8} {pct(ws,.9):>8} {pct(ws,.99):>8} {max(ws) if ws else 0:>8} | "
          f"{pct(ps,.5):>8} {pct(ps,.9):>8} {max(ps) if ps else 0:>8}")

# ---- onts no reasoner solved / KM-unique solves / Konclude-unique ----
print("\n## Coverage relationships")
ok = {r: {o for o in onts if recs[o].get(r) and recs[o][r].get("status") == "ok"} for r in REASONERS}
allok = set.union(*ok.values()) if ok else set()
print(f"solved by >=1 reasoner: {len(allok)} / {N}")
none_ok = [o for o in onts if o not in allok]
print(f"solved by NONE: {len(none_ok)}: {','.join(none_ok)}")
for r in REASONERS:
    others = set.union(*[ok[x] for x in REASONERS if x != r]) if len(REASONERS) > 1 else set()
    uniq = sorted(ok[r] - others, key=lambda x: int(x) if x.isdigit() else 0)
    print(f"{r}-only (no other reasoner solves): {len(uniq)}: {','.join(uniq)}")
