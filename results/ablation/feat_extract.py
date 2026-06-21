#!/usr/bin/env python3
"""Cheap structural feature extraction over the ORE scored corpus (OWL functional
syntax). One pass per file, substring counts only -- no parsing, no reasoning.
Emits one JSON line per ont with construct counts + derived densities, so we can
test whether the engine-escalation onts (HT / elc) and the 18 unsolved onts are
separable by structure (expressivity, size, disjunction density, EL fraction).

Usage: feat_extract.py <corpus_dir> <scored_onts.txt>  > feats.jsonl
"""
import json
import os
import sys

# functional-syntax construct -> feature key
CONSTRUCTS = {
    "ObjectUnionOf": "union",
    "ObjectAllValuesFrom": "all",
    "ObjectSomeValuesFrom": "some",
    "ObjectComplementOf": "compl",
    "ObjectInverseOf": "inv_of",
    "InverseObjectProperties": "inv_prop",
    "ObjectOneOf": "oneof",
    "ObjectHasValue": "hasval",
    "ObjectMinCardinality": "mincard",
    "ObjectMaxCardinality": "maxcard",
    "ObjectExactCardinality": "exactcard",
    "TransitiveObjectProperty": "trans",
    "ObjectPropertyChain": "chain",
    "SubObjectPropertyOf": "subprop",
    "DisjointClasses": "disjoint",
    "EquivalentClasses": "equiv",
    "SubClassOf": "subclass",
    "DataSomeValuesFrom": "data_some",
    "DataAllValuesFrom": "data_all",
    "DatatypeDefinition": "datatype_def",
    "DataPropertyDomain": "data_dom",
    "DLSafeRule": "swrl",
    "FunctionalObjectProperty": "func",
    "SymmetricObjectProperty": "sym",
}


def main():
    corpus, listf = sys.argv[1], sys.argv[2]
    for ln in open(listf):
        o = ln.strip()
        if not o:
            continue
        p = os.path.join(corpus, f"ore_ont_{o}.owl")
        try:
            sz = os.path.getsize(p)
        except OSError:
            continue
        # giants: count on a capped read (constructs are uniformly distributed
        # enough for density; flag as capped).
        capped = sz > 80 * 1024 * 1024
        with open(p, "r", errors="replace") as f:
            txt = f.read(80 * 1024 * 1024) if capped else f.read()
        cnt = {v: txt.count(k) for k, v in CONSTRUCTS.items()}
        # ObjectInverseOf double-counts InverseObjectProperties? no, distinct
        inverse = cnt["inv_of"] + cnt["inv_prop"]
        nominal = cnt["oneof"] + cnt["hasval"]
        card = cnt["mincard"] + cnt["maxcard"] + cnt["exactcard"]
        # axiom proxy = SubClassOf + EquivalentClasses + DisjointClasses
        ax = cnt["subclass"] + cnt["equiv"] + cnt["disjoint"]
        ax = max(ax, 1)
        rec = {
            "ont": o, "size": sz, "capped": capped, "axioms": ax,
            **cnt,
            "inverse": inverse, "nominal": nominal, "card": card,
            # densities (per axiom)
            "d_union": round(cnt["union"] / ax, 4),
            "d_all": round(cnt["all"] / ax, 4),
            "d_some": round(cnt["some"] / ax, 4),
            # non-EL construct load (union/all/compl/inverse/nominal/card)
            "nonEL": cnt["union"] + cnt["all"] + cnt["compl"] + inverse + nominal + card,
            "d_nonEL": round((cnt["union"] + cnt["all"] + cnt["compl"] + inverse + nominal + card) / ax, 4),
        }
        print(json.dumps(rec))


if __name__ == "__main__":
    main()
