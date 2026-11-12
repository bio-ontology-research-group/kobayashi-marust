#!/usr/bin/env python3
"""Aggregate the v1.6.1 Q2 forced-suite shards against the v1.6.0 P3 rerun.

Usage: aggregate_q2.py OUT_DIR V160_P3_TSV REPORT_MD MERGED_TSV
"""
import csv, glob, os, re, sys
from collections import Counter

out_dir, v160_tsv, report, merged = sys.argv[1:5]

def read(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f, delimiter="\t"))

rows = []
for p in sorted(glob.glob(os.path.join(out_dir, "p3-*.tsv"))):
    rows += read(p)
old = {r["input"]: r for r in read(v160_tsv)}
new = {r["input"]: r for r in rows}

def cause(r):
    o = r["forced_outcome"]
    if o == "published":
        return "published"
    if r["forced_status"] == "timeout":
        return "km timeout (300 s)"
    m = re.match(r"declined: (budget|not recognised|out of fragment|io error|failed to read)", o)
    if m:
        return m.group(1)
    if "Stack overflow" in o:
        return "stack overflow"
    if "out of memory" in o.lower() or "failed to create thread" in o:
        return "memory"
    return "other: " + o[:80]

recognised = [i for i, r in old.items() if r["p2_status"] == "accepted"]
old_pub = {i for i, r in old.items() if r["forced_outcome"] == "published"}
new_pub = {i for i, r in new.items() if r["forced_outcome"] == "published"}
missing = sorted(set(old) - set(new))

mismatch = []
for i in sorted(new_pub):
    r = new[i]
    if r["unforced_status"] == "ok" and r["forced_digest"] != r["unforced_digest"]:
        mismatch.append(i)
pub_no_unforced = sorted(i for i in new_pub if new[i]["unforced_status"] != "ok")

rec_new = [i for i in recognised if i in new_pub]
rec_old = [i for i in recognised if i in old_pub]
lost = sorted(old_pub - new_pub)
gained = sorted(new_pub - old_pub)

def phases(r):
    d = {}
    for kv in r.get("forced_ref_phases", "-").split(","):
        if ":" in kv:
            k, v = kv.split(":", 1)
            if v.isdigit():
                d[k] = int(v)
    return d

miss_causes = Counter(cause(new[i]) for i in recognised if i in new and i not in new_pub)

with open(report, "w") as f:
    w = f.write
    w("# v1.6.1 Q2: forced reference stage on the checkers-on suite (Ibex)\n\n")
    w(f"Rows: {len(new)} of {len(old)} v1.6.0 inputs; missing rows: {len(missing)}.\n\n")
    w("| measure | v1.6.0 | v1.6.1 |\n|---|---:|---:|\n")
    w(f"| published, all inputs | {len(old_pub)} | {len(new_pub)} |\n")
    w(f"| published, recognised (of {len(recognised)}) | {len(rec_old)} | {len(rec_new)} |\n\n")
    w(f"- Lost (published in v1.6.0, not now): {len(lost)}\n")
    for i in lost:
        w(f"  - `{os.path.basename(i)}`: {new.get(i, {}).get('forced_outcome', 'no row')}\n")
    w(f"- Gained: {len(gained)}\n")
    w(f"- Digest mismatches (forced vs unforced, both ok): {len(mismatch)}\n")
    for i in mismatch:
        w(f"  - `{i}`\n")
    w(f"- Published while the unforced run failed (no digest to compare): {len(pub_no_unforced)}\n")
    for i in pub_no_unforced:
        w(f"  - `{os.path.basename(i)}`: unforced {new[i]['unforced_status']}\n")
    w("\n## Misses among the recognised inputs, by cause\n\n| cause | inputs |\n|---|---:|\n")
    for c, n in miss_causes.most_common():
        w(f"| {c} | {n} |\n")
    w("\n## Recognised inputs whose v1.6.0 recognition status was accepted but the stage declines as not recognised\n\n")
    for i in recognised:
        if i in new and cause(new[i]) == "not recognised":
            w(f"- `{i}`: {new[i]['forced_outcome'][:160]}\n")
    w("\n## Phase timing of the inputs that hit the stage budget\n\n")
    w("Phases that finished before the kill (ms); the phase after the last one listed was running at the budget.\n\n")
    w("| input | phases |\n|---|---|\n")
    last = Counter()
    for i in sorted(new):
        r = new[i]
        if cause(r) in ("budget", "km timeout (300 s)"):
            ph = r.get("forced_ref_phases", "-")
            w(f"| `{os.path.basename(i)}` | {ph} |\n")
            names = [kv.split(":")[0] for kv in ph.split(",") if ":" in kv]
            last[names[-1] if names else "none"] += 1
    w("\nLast completed phase before the budget: " +
      ", ".join(f"{k} {v}" for k, v in last.most_common()) + "\n")
    w("\n## Published inputs: phase totals\n\n")
    tot = Counter()
    for i in new_pub:
        for k, v in phases(new[i]).items():
            tot[k] += v
    for k, v in tot.most_common():
        w(f"- {k}: {v / 1000:.1f} s\n")

with open(merged, "w", newline="") as f:
    fn = list(rows[0].keys())
    wr = csv.DictWriter(f, fieldnames=fn, delimiter="\t")
    wr.writeheader()
    wr.writerows(sorted(rows, key=lambda r: r["input"]))
print(open(report).read()[:3000])
