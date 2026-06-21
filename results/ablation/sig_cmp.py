#!/usr/bin/env python3
"""Compare a KM .sig.gz against the gold (Konclude) .sig.gz and emit a JSON
summary that splits any disagreement into UNSOUND (km derived a subsumption /
unsat gold lacks) vs INCOMPLETE (gold has one km missed).

sig.gz blob format (written by ore_runone.py):
    <"1"|"0" consistent>\n
    a\tb\n ... (sorted subsumptions)\n
    #UNSAT\n
    <sorted unsat concept names>

Usage: sig_cmp.py KM.sig.gz GOLD.sig.gz  -> one JSON line on stdout.
On any read failure prints {} so the caller can record "no comparison".
"""
import gzip
import json
import sys


def load(path):
    with gzip.open(path, "rb") as f:
        blob = f.read().decode("utf-8", "replace")
    lines = blob.split("\n")
    cons = lines[0].strip() if lines else ""
    subs, unsat, in_unsat = set(), set(), False
    for ln in lines[1:]:
        if ln == "#UNSAT":
            in_unsat = True
            continue
        if not ln:
            continue
        (unsat if in_unsat else subs).add(ln)
    return cons, subs, unsat


def main():
    try:
        kc, ks, ku = load(sys.argv[1])
        gc, gs, gu = load(sys.argv[2])
    except Exception:
        print("{}")
        return
    # unsound = km has, gold lacks ; incomplete = gold has, km lacks
    sub_unsound = len(ks - gs)
    sub_incomplete = len(gs - ks)
    unsat_unsound = len(ku - gu)
    unsat_incomplete = len(gu - ku)
    cons_mismatch = (kc != gc)
    rec = {
        "gold_match": (sub_unsound == 0 and sub_incomplete == 0
                       and unsat_unsound == 0 and unsat_incomplete == 0
                       and not cons_mismatch),
        "unsound": sub_unsound,
        "incomplete": sub_incomplete,
        "unsat_unsound": unsat_unsound,
        "unsat_incomplete": unsat_incomplete,
        "cons_mismatch": cons_mismatch,
        "km_nsub": len(ks),
        "gold_nsub": len(gs),
    }
    print(json.dumps(rec))


if __name__ == "__main__":
    main()
