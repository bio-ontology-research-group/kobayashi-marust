#!/usr/bin/env python3
"""Per-route / per-reason counts and the list of recognised-but-unpublished inputs."""
import csv, re, sys, collections
tsv, p2 = sys.argv[1], sys.argv[2]
rows = list(csv.DictReader(open(tsv), delimiter="\t"))
p2m = {r["input"]: r["status"] for r in csv.DictReader(open(p2), delimiter="\t")}
def cat(r):
    o = r["forced_outcome"]
    if o == "published": return "ref published " + r["forced_procedure"]
    if o.startswith("published"): return "unguarded production"
    if o == "timeout": return "forced timeout"
    if o.startswith("declined"):
        m = re.sub(r"\d+", "N", o)[:70]
        return m
    return o
print("== per route x outcome")
c = collections.Counter((r["unforced_route"], cat(r)) for r in rows)
for k, v in sorted(c.items()): print(v, *k, sep="\t")
print("== checks")
rec = [r for r in rows if p2m.get(r["input"]) == "accepted"]
pub = lambda r: r["forced_outcome"] == "published"
print("check1 recognised", len(rec), "published", sum(map(pub, rec)),
      "match", sum(pub(r) and r["forced_digest"] == r["unforced_digest"] != "-" for r in rec))
oth = [r for r in rows if p2m.get(r["input"]) != "accepted" and r["forced_outcome"].startswith("published")]
print("check2 other publications", len(oth), "match", sum(r["forced_digest"] == r["unforced_digest"] != "-" for r in oth))
diff = [r for r in rows if "-" not in (r["unforced_digest"], r["forced_digest"]) and r["unforced_digest"] != r["forced_digest"]]
print("check3 mismatches", len(diff))
for r in diff: print("  DIFF", r["input"], r["unforced_digest"], r["forced_digest"])
print("anomalies", [r["input"] for r in rows if "ANOMALY" in r["forced_digest"] + r["unforced_digest"]])
nopub = [r for r in rows if r["unforced_digest"] == "-"]
print("check4 unforced published nothing", len(nopub), collections.Counter(cat(r) for r in nopub))
print("== recognised not published (input, unforced_route, outcome, unforced_wall, forced_wall)")
for r in rec:
    if not pub(r): print(r["input"], r["forced_outcome"], r["forced_status"], r["forced_wall_s"], sep="\t")
