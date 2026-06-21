#!/usr/bin/env python3
"""Analyze structural-feature separability of the engine-escalation onts and the
18 unsolved, from feat_extract.py output. Usage: feat_analyze.py feats.jsonl"""
import json
import statistics as st
import sys

F = {json.loads(l)["ont"]: json.loads(l) for l in open(sys.argv[1])}
HT5 = ["5303", "9024", "12141", "9635", "15491"]
ELC4 = ["11460", "2397", "4604", "7246"]
UNS = ["541", "1603", "2669", "3215", "6934", "7499", "7581", "7914", "9540",
       "9663", "9724", "10621", "10702", "12653", "14817", "15516", "15672", "15803"]
special = set(HT5 + ELC4 + UNS)
BULK = [o for o in F if o not in special]


def med(group, k):
    xs = [F[o][k] for o in group if o in F]
    return round(st.median(xs), 3) if xs else None


keys = ["size", "axioms", "union", "d_union", "all", "d_all", "compl",
        "inverse", "nominal", "card", "trans", "chain", "swrl", "nonEL", "d_nonEL"]
print("median by group:")
print("%-10s%12s%10s%10s%10s" % ("feat", "BULK", "HT5", "ELC4", "UNS18"))
for k in keys:
    print("%-10s%12s%10s%10s%10s" % (k, med(BULK, k), med(HT5, k), med(ELC4, k), med(UNS, k)))


def line(o):
    r = F.get(o, {})
    return ("  %-7s sz=%9s ax=%6s union=%5s d_union=%6s all=%5s inv=%4s nom=%4s "
            "card=%4s trans=%3s chain=%3s swrl=%3s d_nonEL=%s" % (
                o, r.get("size"), r.get("axioms"), r.get("union"), r.get("d_union"),
                r.get("all"), r.get("inverse"), r.get("nominal"), r.get("card"),
                r.get("trans"), r.get("chain"), r.get("swrl"), r.get("d_nonEL")))


print("\n=== HT5 (need HT fallback) ===")
for o in HT5:
    print(line(o))
print("\n=== ELC4 (need certified-elc) ===")
for o in ELC4:
    print(line(o))
print("\n=== UNSOLVED 18 ===")
for o in sorted(UNS, key=int):
    print(line(o))

# crude separability checks
print("\n=== separability probes ===")
bu = [F[o]["union"] for o in BULK]
print("BULK union: median=%s p90=%s max=%s" % (
    st.median(bu), sorted(bu)[int(len(bu) * 0.9)], max(bu)))
print("BULK with union>0: %d/%d" % (sum(1 for x in bu if x > 0), len(bu)))
hi_union = [o for o in F if F[o]["union"] >= 50]
print("onts with union>=50 (%d): %s" % (len(hi_union), sorted(hi_union, key=int)))
inv_nom = [o for o in (HT5 + UNS) if F[o]["inverse"] > 0 or F[o]["nominal"] > 0]
print("HT5+UNS with inverse or nominal: %s" % sorted(inv_nom, key=int))
swrl = [o for o in F if F[o]["swrl"] > 0]
print("onts with SWRL/DLSafeRule (%d): %s" % (len(swrl), sorted(swrl, key=int)))
