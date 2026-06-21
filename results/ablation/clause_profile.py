#!/usr/bin/env python3
"""Categorize a KM clause set ({"clauses":[{body,head}]}) into EL normal forms
vs the residual (non-EL) shapes, to identify which fragment a giant needs.
atom: {"concept":N,"term":T} | {"role":R,"s":T,"t":T} | {"eq":..}
term: {"var":n} | {"ind":..} | {"aux":..} | {"fun":..}
Usage: clause_profile.py clauses.json"""
import json
import sys
from collections import Counter


def termkind(t):
    if "var" in t: return ("var", t["var"])
    if "fun" in t: return ("fun", None)
    if "ind" in t: return ("ind", None)
    if "aux" in t: return ("aux", None)
    return ("?", None)


def classify(cl):
    body, head = cl.get("body", []), cl.get("head", [])
    bc = [a for a in body if "concept" in a]
    br = [a for a in body if "role" in a]
    be = [a for a in body if "eq" in a]
    hc = [a for a in head if "concept" in a]
    hr = [a for a in head if "role" in a]
    he = [a for a in head if "eq" in a]
    # eq anywhere -> nominal/cardinality/equality
    if be or he:
        return "eq/nominal/card"
    # empty head -> A(..)⊑⊥  (NF5) ; EL-ok
    if not head:
        return "EL:bottom"
    # disjunction: 2+ head concept atoms (on same or different terms)
    if len(hc) >= 2:
        return "DISJUNCTION"
    # head has a role atom
    if hr:
        # NF3 existential: head = role(x,fun)+concept(fun), body concept(x)
        if len(hr) == 1 and len(hc) <= 1:
            return "EL:exists(NF3)"
        return "head-role-other"
    # head is a single concept atom on term ht
    if len(hc) == 1:
        ht = termkind(hc[0]["term"])
        # value restriction (∀): body has role(x,y) and head concept on y (role target)
        if br:
            # collect role target terms
            rtargets = {termkind(r["target"]) for r in br}
            rsources = {termkind(r["source"]) for r in br}
            if ht in rtargets and ht not in rsources:
                return "VALUE_RESTR(forall)"
            if ht in rsources:
                return "EL:exists-elim(NF4)"  # ∃r.B⊑C shape
            return "body-role-other"
        # pure concept body -> NF1/NF2
        if len(bc) == 1: return "EL:NF1"
        if len(bc) == 2: return "EL:NF2"
        if len(bc) >= 3: return "many-body-concepts"
        if len(bc) == 0: return "EL:top-sub"
    return "OTHER"


def main():
    data = json.load(open(sys.argv[1]))
    cls = data["clauses"] if isinstance(data, dict) else data
    cnt = Counter()
    examples = {}
    for c in cls:
        k = classify(c)
        cnt[k] += 1
        if k not in examples and not k.startswith("EL:"):
            examples[k] = c
    tot = sum(cnt.values())
    print(f"total clauses: {tot}")
    for k, n in cnt.most_common():
        print(f"  {k:<22} {n:>9}  ({100*n/tot:.1f}%)")
    print("\n--- non-EL examples ---")
    for k, c in examples.items():
        print(f"  {k}: {json.dumps(c)[:200]}")


if __name__ == "__main__":
    main()
