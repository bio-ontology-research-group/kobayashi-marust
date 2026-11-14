#!/usr/bin/env python3
"""Compare prototype rows (KM_SRIQF_ROWS=1 stdout) with km classify --lines.
usage: cmp_km.py <proto.out> <km.lines>   prints AGREE or a diff summary."""
import sys
SKIP = ("http://www.w3.org/2002/07/owl#Thing", "http://www.w3.org/2002/07/owl#Nothing",
        "urn:km:owl-reference:probe-a", "urn:km:owl-reference:probe-b")
def proto(path):
    subs, uns, names = set(), set(), set()
    for l in open(path):
        if not l.startswith("row "): continue
        p = l.split()
        a = p[1]; names.add(a)
        if a in SKIP: continue
        if p[2:] == ["unsat"]: uns.add(a); continue
        for b in p[2:]:
            if b != a and b not in SKIP: subs.add((a, b))
    return subs, uns, names
def km(path):
    subs, uns = set(), set()
    for l in open(path):
        p = l.rstrip("\n").split("\t")
        if p[0] == "SUB" and p[1] not in SKIP and p[2] not in SKIP and p[1] != p[2]: subs.add((p[1], p[2]))
        elif p[0] == "UNSAT" and p[1] not in SKIP: uns.add(p[1])
    return subs, uns
ps, pu, names = proto(sys.argv[1]); ks, ku = km(sys.argv[2])
# km abbreviates the default prefix as ":X"; expand it with the prototype's IRIs
full = {}
for n in names:
    for sep in ("#", "/"):
        if sep in n: full[":" + n.rsplit(sep, 1)[1]] = n; break
fx = lambda x: full.get(x, x) if x.startswith(":") else x
ks = {(fx(a), fx(b)) for (a, b) in ks}; ku = {fx(a) for a in ku}
ks = {(a, b) for (a, b) in ks if a not in ku}
ps = {(a, b) for (a, b) in ps if a not in pu}
d1, d2, u1, u2 = ps - ks, ks - ps, pu - ku, ku - pu
if not (d1 or d2 or u1 or u2):
    print(f"AGREE subs={len(ps)} unsat={len(pu)}")
else:
    print(f"DIFF proto_only_subs={len(d1)} km_only_subs={len(d2)} proto_only_unsat={len(u1)} km_only_unsat={len(u2)}")
    for x in sorted(d1)[:5]: print("  proto-only", *x)
    for x in sorted(d2)[:5]: print("  km-only", *x)
    for x in sorted(u1)[:5]: print("  proto-only-unsat", x)
    for x in sorted(u2)[:5]: print("  km-only-unsat", x)
