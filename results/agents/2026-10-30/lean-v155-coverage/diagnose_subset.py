# usage: python3 -I diagnose_subset.py CERT.json
# Re-implements SubsetUnravelling.materialize / check of
# lean/ContextCalculus/HypertableauSubsetUnravelling.lean in Python and prints
# the first failing condition (diagnostics only; Lean is the checker).
import json, sys, itertools
d = json.load(open(sys.argv[1])); b = d["base"]
lit = lambda l: (l["concept"], l["neg"])
labels = {(x["node"], lit(x["literal"])) for x in b["labels"]}
edges = {(e["role"], e["source"], e["target"]) for e in b["edges"]}
obl = {(o["role"], lit(o["filler"]), o["node"]) for o in b["obligations"]}
parents = {(p["source"], p["target"]) for p in d["parents"]}
folds = [(f["source"], f["target"]) for f in d["folds"]]
blocked = {w for w, _ in folds}
for w, m in folds:
    for (n, l) in labels:
        if n == w and (m, l) not in labels: print("not subset", w, m, l)
ml = {(n, l) for (n, l) in labels if n not in blocked}
me, mo = set(edges), set(obl)
for w, m in folds:
    ml |= {(w, l) for (n, l) in labels if n == m}
    for (r, s, t) in edges:
        if s == m and (t, m) in parents: me.add((r, w, t))
        if t == m and (s, m) in parents: me.add((r, s, w))
    mo |= {(r, f, w) for (r, f, n) in obl if n == m}
N = b["node_count"]; V = b["variable_count"]
for (n, (c, neg)) in ml:
    if (n, (c, not neg)) in ml: print("clash", n, c)
for (r, f, n) in mo:
    if not any((r, n, t) in me and (t, f) in ml for t in range(N)): print("unwitnessed", r, f, n)
def holds(a, asg):
    k, v = next(iter(a.items()))
    if k == "concept": return (asg[v["node"]], lit(v["literal"])) in ml
    if k == "role": return (v["role"], asg[v["source"]], asg[v["target"]]) in me
    if k == "exists_": return (v["role"], lit(v["filler"]), asg[v["node"]]) in mo
    return asg[v["left"]] == asg[v["right"]]
bad = 0
for i, cl in enumerate(b["ontology"]):
    for asg in itertools.product(range(N), repeat=V):
        if all(holds(a, asg) for a in cl["body"]) and not any(holds(a, asg) for a in cl["head"]):
            print("clause", i, cl, "assignment", asg, "blocked" if any(x in blocked for x in asg) else "")
            bad += 1
            break
    if bad > 5: break
print("folds", folds, "parents", sorted(parents))
