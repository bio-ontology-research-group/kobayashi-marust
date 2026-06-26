#!/usr/bin/env python3
"""Fast soundness/completeness vs Konclude+HermiT gold for the router sweep.

Trick: the gold .sig.gz CONTAINS exactly the canonical blob that router_runone
hashes into `sig_sha`. So sha256(gunzip(gold)) == km record's sig_sha IFF the two
signatures are byte-identical ⇒ AGREE, with no set parsing. Only sha-mismatches
get the (rare) full set-diff to classify unsound vs incomplete.

Contested gold (Konclude wrong, HermiT authority): 15516 2669 8941 13912 10621.

Usage: fast_soundness.py <mode> [<mode> ...]   (reads res_router_<mode>_*.jsonl)
"""
import sys, os, json, gzip, glob, hashlib
from collections import Counter

BENCH = "/home/hohndor/bench"
JOBS = os.path.join(BENCH, "ore_jobs")
GOLD = os.path.join(BENCH, "ore_out")
CONTESTED = {"15516", "2669", "8941", "13912", "10621"}

_gold_sha = {}
_gold_set = {}

def gold_blob_sha(ref, ont):
    key = (ref, ont)
    if key in _gold_sha:
        return _gold_sha[key]
    p = os.path.join(GOLD, "%s__ore_ont_%s.owl.sig.gz" % (ref, ont))
    if not os.path.exists(p):
        _gold_sha[key] = None
        return None
    with gzip.open(p, "rb") as f:
        blob = f.read()
    _gold_sha[key] = hashlib.sha256(blob).hexdigest()
    return _gold_sha[key]

def load_set(path):
    if path in _gold_set:
        return _gold_set[path]
    s = set(); u = set(); inu = False; cons = True
    try:
        with gzip.open(path, "rt") as f:
            cons = (f.readline().strip() == "1")
            for l in f:
                l = l.rstrip("\n")
                if l.startswith("#"):
                    inu = "UNSAT" in l; continue
                if inu:
                    u.add(l.strip())
                elif "\t" in l:
                    a, b = l.split("\t", 1); s.add((a, b))
    except Exception:
        _gold_set[path] = None; return None
    _gold_set[path] = (cons, s, u)
    return _gold_set[path]

def km_path(mode, ont):
    return os.path.join(BENCH, "ore_out_router_%s" % mode, "km__ore_ont_%s.owl.sig.gz" % ont)

def main():
    modes = sys.argv[1:] or ["default", "cb", "ht"]
    for mode in modes:
        recs = {}
        for f in glob.glob(os.path.join(JOBS, "res_router_%s_*.jsonl" % mode)):
            for l in open(f):
                l = l.strip()
                if not l: continue
                try: r = json.loads(l)
                except: continue
                recs[r["ont"]] = r
        print("\n" + "=" * 70)
        print("MODE %s : %d records" % (mode, len(recs)))
        for ref in ["konclude", "hermit"]:
            agree = unsound = incomplete = both = cmpn = missing = 0
            us_list = []; inc_list = []; both_list = []
            for ont, r in recs.items():
                if r.get("status") != "ok":
                    continue
                gsha = gold_blob_sha(ref, ont)
                if gsha is None:
                    missing += 1; continue
                cmpn += 1
                ksha = r.get("sig_sha")
                contested = ont in CONTESTED
                if ksha == gsha:
                    agree += 1; continue
                # mismatch: full set-diff
                g = load_set(os.path.join(GOLD, "%s__ore_ont_%s.owl.sig.gz" % (ref, ont)))
                k = load_set(km_path(mode, ont))
                if g is None or k is None:
                    continue
                gc, gs, gu = g; kc, ks, ku = k
                us = len(ks - gs) + len(ku - gu)
                inc = len(gs - ks) + len(gu - ku)
                if kc != gc:
                    both += 1; both_list.append("%s%s(cons %s vs %s)" % (ont, "*" if contested else "", kc, gc))
                elif us and inc:
                    both += 1; both_list.append("%s%s" % (ont, "*" if contested else ""))
                elif us:
                    unsound += 1; us_list.append("%s%s(%d)" % (ont, "*" if contested else "", us))
                elif inc:
                    incomplete += 1; inc_list.append("%s%s(%d)" % (ont, "*" if contested else "", inc))
                else:
                    agree += 1
            print("  vs %-8s: compared=%d agree=%d unsound=%d incomplete=%d both=%d (gold-missing=%d)"
                  % (ref, cmpn, agree, unsound, incomplete, both, missing))
            if us_list:   print("     UNSOUND   (*contested):", " ".join(us_list[:50]))
            if inc_list:  print("     INCOMPLETE(*contested):", " ".join(inc_list[:50]))
            if both_list: print("     BOTH/CONS (*contested):", " ".join(both_list[:50]))

if __name__ == "__main__":
    main()
