import json, os
from collections import defaultdict

MISS = "541,1603,2669,3215,4604,5303,6934,7246,7499,7581,7914,9024,9540,9635,9663,9724,10621,10702,11460,12141,12653,14817,15491,15516,15672,15803".split(",")
D = "/ibex/scratch/hohndor/km/cmp2_res"
R = ["konclude", "elk", "hermit", "km"]
rec = defaultdict(dict)
gold = defaultdict(dict)
for fn in os.listdir(D):
    if not fn.endswith(".jsonl"):
        continue
    for ln in open(os.path.join(D, fn)):
        ln = ln.strip()
        if not ln:
            continue
        try:
            o = json.loads(ln)
        except Exception:
            continue
        if "reasoner" in o:
            ont = o["ont"].replace("ore_ont_", "").replace(".owl", "")
            rec[ont][o["reasoner"]] = o
        elif "gold_cmp" in o:
            ont = str(o["ont"])
            gold[ont][o["gold_cmp"]] = o["gold"]

def cell(ont, r):
    x = rec[ont].get(r)
    if not x:
        return "  --   "
    st = x.get("status")
    if st != "ok":
        return " %-6s" % st[:6]
    g = gold[ont].get(r, "?")
    tag = {"MATCH": "OK", "DIFF": "WRONG", "NOSIG": "ok?"}.get(g, g)
    return "%6.1f%s" % (x.get("wall_s", -1), "" if tag == "OK" else "!" + tag[:1])

print("%-7s %-12s %-12s %-12s %-12s" % ("ont", "konclude", "elk", "hermit", "km"))
print("-" * 60)
solv = {"konclude": [], "hermit": [], "elk": []}
for ont in MISS:
    row = []
    for r in R:
        row.append(cell(ont, r))
    print("%-7s %-12s %-12s %-12s %-12s" % (ont, row[0], row[1], row[2], row[3]))
    for r in ["konclude", "hermit", "elk"]:
        x = rec[ont].get(r)
        g = gold[ont].get(r)
        if x and x.get("status") == "ok" and g == "MATCH":
            solv[r].append(ont)

print()
for r in ["konclude", "hermit", "elk"]:
    print("# %s solves gold-clean (%d): %s" % (r, len(solv[r]), ",".join(solv[r])))
# hermit solves that konclude also solves vs uniquely
h = set(solv["hermit"]); k = set(solv["konclude"])
print("# hermit-clean AND konclude-clean: %s" % ",".join(sorted(h & k, key=int)))
print("# hermit-clean only (not konclude): %s" % ",".join(sorted(h - k, key=int)))
print("# konclude-clean only (not hermit): %s" % ",".join(sorted(k - h, key=int)))
print("# neither hermit nor konclude clean: %s" % ",".join(sorted(set(MISS) - h - k, key=int)))
