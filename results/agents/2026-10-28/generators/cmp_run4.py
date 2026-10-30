import json,sys
raw, out = sys.argv[1], sys.argv[2]
g=json.load(open(raw))
gs={tuple(p) for p in g.get("subsumptions",[])}; gu=set(g.get("unsatisfiable",[])); gc=g.get("consistent")
subs=set(); uns=set(); cons=None; dropped=None
for l in open(out):
    t=l.rstrip("\n").split("\t")
    if t[0].startswith("CONSISTENT"): cons=t[0].endswith("1")
    elif t[0].startswith("DROPPED"): dropped=int(t[0].split()[1])
    elif t[0]=="SUB": subs.add((t[1],t[2]))
    elif t[0]=="UNSAT": uns.add(t[1])
print(f"consistent {cons}/{gc} dropped={dropped} subs {len(subs)}/{len(gs)} missing={len(gs-subs)} extra={len(subs-gs)} unsat {len(uns)}/{len(gu)} diff={len(gu^uns)}", "IDENTICAL" if (cons==gc and subs==gs and uns==gu) else "DIFFERENT")
