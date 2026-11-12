#!/usr/bin/env python3
"""Compare a v1.6.0 dense answer with a v1.6.1 sparse answer bit by bit.
usage: cmp_dense_sparse.py dense.json sparse.json"""
import json, sys
d = json.load(open(sys.argv[1]))
s = json.load(open(sys.argv[2]))
assert s["format"] == "sparse-v1"
assert d["named"] == s["named"], "named differ"
assert d.get("procedure") == s.get("procedure"), (d.get("procedure"), s.get("procedure"))
named = s["named"]
assert [r["sub"] for r in s["rows"]] == named
rows = {r["sub"]: (r["unsat"], set(r["sups"])) for r in s["rows"]}
assert len(d["cells"]) == len(named) ** 2
k = 0
for sub in named:
    for sup in named:
        c = d["cells"][k]; k += 1
        assert (c["sub"], c["sup"]) == (sub, sup)
        u, ss = rows[sub]
        assert c["answer"] == (u or sup in ss), (sub, sup, c["answer"])
print(f"equal: {len(named)} names, {len(d['cells'])} cells, procedure={s.get('procedure')}")
