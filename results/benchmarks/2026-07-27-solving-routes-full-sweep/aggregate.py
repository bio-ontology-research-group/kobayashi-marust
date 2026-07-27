#!/usr/bin/env python3
"""Validate and summarize the 50-way solving-routes sweep."""

import argparse, csv, gzip, hashlib, json, statistics
from collections import Counter, defaultdict
from pathlib import Path
from full_panel_contract import panel

p=argparse.ArgumentParser()
p.add_argument("--run-root",type=Path,required=True)
p.add_argument("--output",type=Path,required=True)
a=p.parse_args()
a.output.mkdir(parents=True,exist_ok=True)
arms=[x["arm"] for x in panel()]
files=sorted((a.run_root/"results").glob("ore_ont_*.owl.jsonl"))
if len(files)!=592: raise SystemExit(f"expected 592 result files, found {len(files)}")
rows=[]
for f in files:
    rs=[json.loads(x) for x in f.read_text().splitlines() if x]
    if [x.get("arm") for x in rs]!=arms:
        raise SystemExit(f"contract mismatch: {f}")
    rows.extend(rs)
if len(rows)!=592*len(arms): raise SystemExit("row-count mismatch")

raw=a.output/"full-results.jsonl.gz"
with gzip.open(raw,"wt",encoding="utf-8") as out:
    for r in rows: out.write(json.dumps(r,sort_keys=True)+"\n")

fields=("procedure","kind","runs","status_ok","sound_yes","complete_yes",
        "sound_and_complete_yes","timeouts","memouts","errors",
        "wall_mean_s_ok","wall_median_s_ok","peak_mean_mib_ok","peak_median_mib_ok")
summary=[]
for arm in arms:
    rs=[r for r in rows if r["arm"]==arm]
    ok=[r for r in rs if r.get("status")=="ok"]
    walls=[float(r["wall_s"]) for r in ok if r.get("wall_s") is not None]
    peaks=[float(r["peak_mb"]) for r in ok if r.get("peak_mb") is not None]
    statuses=Counter(r.get("status") for r in rs)
    summary.append({
      "procedure":arm,"kind":rs[0]["procedure_kind"],"runs":len(rs),
      "status_ok":len(ok),"sound_yes":sum(r.get("sound")=="yes" for r in rs),
      "complete_yes":sum(r.get("complete")=="yes" for r in rs),
      "sound_and_complete_yes":sum(r.get("sound")=="yes" and r.get("complete")=="yes" for r in rs),
      "timeouts":statuses["timeout"],"memouts":statuses["memout"],
      "errors":sum(v for k,v in statuses.items() if k not in ("ok","timeout","memout","unsupported")),
      "wall_mean_s_ok":statistics.fmean(walls) if walls else "",
      "wall_median_s_ok":statistics.median(walls) if walls else "",
      "peak_mean_mib_ok":statistics.fmean(peaks) if peaks else "",
      "peak_median_mib_ok":statistics.median(peaks) if peaks else "",
    })
table=a.output/"full-benchmark-table.tsv"
with table.open("w",newline="") as out:
    w=csv.DictWriter(out,fieldnames=fields,delimiter="\t");w.writeheader();w.writerows(summary)
receipt={"schema_version":1,"ontologies":592,"procedures":len(arms),"rows":len(rows),
         "array_tasks":50,"raw_sha256":hashlib.sha256(raw.read_bytes()).hexdigest(),
         "table_sha256":hashlib.sha256(table.read_bytes()).hexdigest()}
(a.output/"receipt.json").write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
print(json.dumps(receipt,sort_keys=True))
