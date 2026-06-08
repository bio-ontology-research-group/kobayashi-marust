import json, sys
d = json.load(open(sys.argv[1]))
ftbl = d["ftbl"]
pps = d["pps"]
def frames(pp, n=4):
    out = []
    for fi in pp.get("fs", [])[:n]:
        s = ftbl[fi]
        # strip address noise; keep function-ish tail
        out.append(s)
    return out
def site_label(pp):
    # pick the first frame that mentions our code (tableau.rs) else first non-alloc frame
    for fi in pp.get("fs", []):
        s = ftbl[fi]
        if "tableau" in s or "Graph" in s or "find_model" in s or "expand" in s or "horn" in s:
            return s
    fs = pp.get("fs", [])
    for fi in fs:
        s = ftbl[fi]
        if "alloc" not in s.lower() and "dhat" not in s.lower():
            return s
    return ftbl[fs[0]] if fs else "?"

def top(key, title, n=12):
    print(f"\n===== TOP by {title} ({key}) =====")
    ranked = sorted(pps, key=lambda p: p.get(key,0), reverse=True)
    tot = sum(p.get(key,0) for p in pps)
    for p in ranked[:n]:
        v = p.get(key,0)
        blk = p.get("tbk" if key=="tb" else "gbk", 0)
        pct = 100*v/tot if tot else 0
        print(f"  {v:>14,} ({pct:5.1f}%) blocks={blk:>10,}  {site_label(p)}")
    print(f"  ---- total {key} = {tot:,}")

print("t-gmax (peak live bytes):", f"{d.get('tg'):,}" if isinstance(d.get('tg'),int) else d.get('tg'))
top("gb", "PEAK live bytes at t-gmax", 14)
top("tb", "TOTAL bytes allocated (churn)", 14)
