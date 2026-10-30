#!/usr/bin/env python3
"""incr7278.py KM INPUT OUT_JSON [ENV=VAL...]: legacy incremental session on INPUT,
then a revision adding one class assertion; records rows and wall times."""
import json, os, subprocess, sys, time
km, src, out = sys.argv[1:4]
env = dict(os.environ, KM_SOURCE_SESSION="legacy", KM_TIMING="1")
for kv in sys.argv[4:]:
    k, v = kv.split("=", 1); env[k] = v
text = open(src).read()
axiom = "ObjectPropertyAssertion(<http://ontology.dumontierlab.com/isPartOf> <http://ontology.dumontierlab.com/III_2004> <http://ontology.dumontierlab.com/_2005>)\n"
close = text.rstrip().rfind(")")
revised = text[:close] + axiom + text[close:]
p = subprocess.Popen([km, "incremental-source"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=open(out + ".err", "w"), env=env, text=True)
rows = []
for op, doc in [("init", text), ("replace", revised)]:
    t = time.time()
    p.stdin.write(json.dumps({"op": op, "functional_syntax": doc}) + "\n"); p.stdin.flush()
    line = p.stdout.readline()
    row = json.loads(line); row["_wall"] = time.time() - t
    res = row.get("result", {})
    rows.append({"op": op, "wall": row["_wall"], "route": row.get("route"), "receipt": row.get("receipt"),
                 "consistent": res.get("consistent"), "n_subs": len(res.get("subsumptions", []))})
p.stdin.close(); p.wait()
json.dump(rows, open(out, "w"), indent=1)
for r in rows:
    print(r["op"], round(r["wall"], 2), r["route"], (r["receipt"] or {}).get("strategy"), r["consistent"], r["n_subs"])
