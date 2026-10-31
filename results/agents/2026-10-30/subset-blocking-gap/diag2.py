# usage: python3 -I diag2.py CERT.json [own]
# Rebuilds SubsetUnravelling.materialize (Lean) and reports failures by kind:
#   unwitnessed (obligation at a blocked position / elsewhere), clash, clause.
# Body matching is a backtracking join over edges, so it is fast on large
# terminals. Diagnostics only; Lean is the checker.
import json, sys
from collections import defaultdict
d = json.load(open(sys.argv[1])); b = d["base"]
relabel = d.get("relabel", True) and not (len(sys.argv) > 2 and sys.argv[2] == "own")
lit = lambda l: (l["concept"], l["neg"])
labels = {(x["node"], lit(x["literal"])) for x in b["labels"]}
edges = {(e["role"], e["source"], e["target"]) for e in b["edges"]}
obl = {(o["role"], lit(o["filler"]), o["node"]) for o in b["obligations"]}
parents = {(p["source"], p["target"]) for p in d["parents"]}
folds = [(f["source"], f["target"]) for f in d["folds"]]
blocked = {w for w, _ in folds}; blocker = dict(folds)
if relabel:
    ml = {(n, l) for (n, l) in labels if n not in blocked}
    for w, m in folds: ml |= {(w, l) for (n, l) in labels if n == m}
    mo = set(obl)
    for w, m in folds: mo |= {(r, f, w) for (r, f, n) in obl if n == m}
else:
    ml, mo = set(labels), set(obl)
me = set(edges)
for w, m in folds:
    for (r, s, t) in edges:
        if s == m and (t, m) in parents: me.add((r, w, t))
        if t == m and (s, m) in parents: me.add((r, s, w))
N = b["node_count"]
out = defaultdict(set)
for (r, s, t) in me: out[(r, s)].add(t)
inn = defaultdict(set)
for (r, s, t) in me: inn[(r, t)].add(s)
bylit = defaultdict(set)
for (n, l) in ml: bylit[l].add(n)
fails = []
for (n, (c, neg)) in ml:
    if (n, (c, not neg)) in ml: fails.append(("clash", n, c))
for (r, f, n) in mo:
    if not any(True for t in out[(r, n)] if (t, f) in ml):
        fails.append(("unwitnessed", r, f, n, "blocked" if n in blocked else "", "blocker=%s" % blocker.get(n)))
def holds(a, asg):
    k, v = next(iter(a.items()))
    if k == "concept": return (asg[v["node"]], lit(v["literal"])) in ml
    if k == "role": return (v["role"], asg[v["source"]], asg[v["target"]]) in me
    if k == "exists_": return (v["role"], lit(v["filler"]), asg[v["node"]]) in mo
    return asg[v["left"]] == asg[v["right"]]
def vars_of(a):
    k, v = next(iter(a.items()))
    if k == "concept" or k == "exists_": return [v["node"]]
    if k == "role": return [v["source"], v["target"]]
    return [v["left"], v["right"]]
def match(body, asg, i, cb):
    # choose next unbound var via a role atom with one bound endpoint
    unbound = {x for a in body for x in vars_of(a) if x not in asg}
    if not unbound:
        if all(holds(a, asg) for a in body): cb(asg)
        return
    for a in body:
        k, v = next(iter(a.items()))
        if k == "role":
            s, t, r = v["source"], v["target"], v["role"]
            if s in asg and t not in asg:
                for y in out[(r, asg[s])]:
                    asg[t] = y; match(body, asg, i, cb); del asg[t]
                return
            if t in asg and s not in asg:
                for y in inn[(r, asg[t])]:
                    asg[s] = y; match(body, asg, i, cb); del asg[s]
                return
    x = min(unbound)
    cands = range(N)
    for a in body:
        k, v = next(iter(a.items()))
        if k == "concept" and v["node"] == x: cands = bylit[lit(v["literal"])]; break
        if k == "role" and (v["source"] == x or v["target"] == x):
            cands = {s for (r, s, t) in me if r == v["role"]} if v["source"] == x else {t for (r, s, t) in me if r == v["role"]}
            break
    for y in list(cands):
        asg[x] = y; match(body, asg, i, cb); del asg[x]
for i, cl in enumerate(b["ontology"]):
    hv = {x for a in cl["head"] for x in vars_of(a)} | {x for a in cl["body"] for x in vars_of(a)}
    bad = []
    def cb(asg):
        full = dict(asg)
        for x in hv:
            full.setdefault(x, 0)
        if not any(holds(a, full) for a in cl["head"]): bad.append(dict(asg))
    match(cl["body"], {}, i, cb)
    for asg in bad[:2]:
        fails.append(("clause", i, asg, "blocked" if any(v in blocked for v in asg.values()) else ""))
kinds = defaultdict(int)
for f in fails: kinds[f[0] + (":" + f[4] if f[0] == "unwitnessed" else "")] += 1
print("relabel" if relabel else "own", dict(kinds))
for f in fails[:8]: print(" ", f)
