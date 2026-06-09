#!/usr/bin/env python3
"""Reasoner-free structural validation of the Rust normalisation frontend.

For each construct in an embedded SROIQ battery, compares the canonical
(rename-invariant) clause multiset produced by the Python frontend
(`frontend.ofn_to_clauses`, pure normalisation — NO engine) against the Rust
`ofn` frontend binary (also NO engine). The two must be EQUAL.

This NEVER runs the KM reasoner. It only runs the two frontends.

    OFN_BIN=../target/release/ofn python3 compare_frontends.py [--verbose]
"""
from __future__ import annotations
import json, os, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import frontend          # noqa: E402  pure Python normalisation frontend
import dump_clauses      # noqa: E402  canon()

OFN_BIN = os.environ.get("OFN_BIN", str(HERE.parent / "target" / "release" / "ofn"))
VERBOSE = "--verbose" in sys.argv[1:]

PFX = 'Prefix(:=<http://ex.org/>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'


def ont(body: str) -> str:
    return PFX + "Ontology(<http://ex.org/o>\n" + body + "\n)\n"


# Declarations helper: declare classes A..H, roles r,s,t, individuals a,b,c
DECL = "".join(f"Declaration(Class(:{c}))\n" for c in "ABCDEFGH") + \
       "".join(f"Declaration(ObjectProperty(:{r}))\n" for r in ("r", "s", "t")) + \
       "".join(f"Declaration(NamedIndividual(:{i}))\n" for i in ("a", "b", "c"))

BATTERY = {
    "subclass":        "SubClassOf(:A :B)",
    "equiv":           "EquivalentClasses(:A :B)",
    "disjoint":        "DisjointClasses(:A :B)",
    "and":             "SubClassOf(:A ObjectIntersectionOf(:B :C))",
    "and_nary":        "SubClassOf(:A ObjectIntersectionOf(:B :C :D :E))",
    "or":              "SubClassOf(:A ObjectUnionOf(:B :C))",
    "some":            "SubClassOf(:A ObjectSomeValuesFrom(:r :B))",
    "some_back":       "SubClassOf(ObjectSomeValuesFrom(:r :B) :C)",
    "all_pos":         "SubClassOf(:A ObjectAllValuesFrom(:r :B))",
    "all_neg":         "SubClassOf(ObjectAllValuesFrom(:r :B) :C)",
    "not":             "SubClassOf(:A ObjectComplementOf(:B))",
    "min":             "SubClassOf(:A ObjectMinCardinality(2 :r :B))",
    "min1":            "SubClassOf(:A ObjectMinCardinality(1 :r :B))",
    "max":             "SubClassOf(:A ObjectMaxCardinality(2 :r :B))",
    "max0":            "SubClassOf(:A ObjectMaxCardinality(0 :r :B))",
    "exact":           "SubClassOf(:A ObjectExactCardinality(2 :r :B))",
    "nominal":         "SubClassOf(:A ObjectOneOf(:a))",
    "hasself":         "SubClassOf(:A ObjectHasSelf(:r))",
    "not_hasself":     "SubClassOf(:A ObjectComplementOf(ObjectHasSelf(:r)))",
    "inverse_some":    "SubClassOf(:A ObjectSomeValuesFrom(ObjectInverseOf(:r) :B))",
    "subrole":         "SubObjectPropertyOf(:r :s)",
    "chain":           "SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)",
    "chain3":          "SubObjectPropertyOf(ObjectPropertyChain(:r :s :t) :r)",
    "transitive":      "TransitiveObjectProperty(:r)",
    "symmetric":       "SymmetricObjectProperty(:r)",
    "reflexive":       "ReflexiveObjectProperty(:r)",
    "irreflexive":     "IrreflexiveObjectProperty(:r)",
    "asymmetric":      "AsymmetricObjectProperty(:r)",
    "functional":      "FunctionalObjectProperty(:r)",
    "invfunctional":   "InverseFunctionalObjectProperty(:r)",
    "inverseroles":    "InverseObjectProperties(:r :s)",
    "disjointroles":   "DisjointObjectProperties(:r :s)",
    "domain":          "ObjectPropertyDomain(:r :A)",
    "range":           "ObjectPropertyRange(:r :B)",
    "abox_class":      "ClassAssertion(:A :a)",
    "abox_role":       "ObjectPropertyAssertion(:r :a :b)",
    "abox_same":       "SameIndividual(:a :b)",
    "abox_diff":       "DifferentIndividuals(:a :b)",
    # nested / shared sub-concepts exercising fresh-name reuse + polarity gating
    "nested_all_or":   "SubClassOf(ObjectAllValuesFrom(:r :B) ObjectAllValuesFrom(:r ObjectUnionOf(:B :C)))",
    "shared_some":     "SubClassOf(:A ObjectSomeValuesFrom(:r :B))\nSubClassOf(:C ObjectSomeValuesFrom(:r :B))",
    "deep_nest":       "SubClassOf(:A ObjectSomeValuesFrom(:r ObjectIntersectionOf(:B ObjectAllValuesFrom(:s :C))))",
    "equiv_complex":   "EquivalentClasses(:A ObjectIntersectionOf(:B ObjectSomeValuesFrom(:r :C)))",
    "mixed":           "SubClassOf(:A ObjectIntersectionOf(ObjectSomeValuesFrom(:r :B) ObjectAllValuesFrom(:s ObjectUnionOf(:C :D))))\nTransitiveObjectProperty(:r)\nSubObjectPropertyOf(ObjectPropertyChain(:r :s) :t)\nObjectPropertyDomain(:r :A)",
}


def py_canon(path):
    return dump_clauses.canon(frontend.ofn_to_clauses(path))


def rust_canon(path):
    p = subprocess.run([OFN_BIN, path], capture_output=True, text=True)
    if p.returncode != 0:
        return None, f"rc={p.returncode}: {p.stderr.strip()[:120]}"
    try:
        cl = json.loads(p.stdout)["clauses"]
    except Exception as e:
        return None, f"bad json: {e}"
    return dump_clauses.canon(cl), None


def main():
    npass = nfail = nerr = 0
    rows = []
    for name, body in BATTERY.items():
        with tempfile.NamedTemporaryFile("w", suffix=".ofn", delete=False) as f:
            f.write(ont(DECL + body))
            path = f.name
        try:
            pc = py_canon(path)
        except Exception as e:
            rows.append((name, "PY_ERR", str(e)[:90])); nerr += 1; os.unlink(path); continue
        rc, err = rust_canon(path)
        os.unlink(path)
        if rc is None:
            rows.append((name, "RUST_ERR", err)); nerr += 1; continue
        if pc == rc:
            rows.append((name, "PASS", f"{len(pc)} clauses")); npass += 1
        else:
            ps, rs = set(pc), set(rc)
            rows.append((name, "FAIL", f"py_only={len(ps - rs)} rust_only={len(rs - ps)} (py={len(pc)} rust={len(rc)})"))
            nfail += 1
            if VERBOSE:
                for l in list(ps - rs)[:6]:
                    print(f"    PY-only : {l}")
                for l in list(rs - ps)[:6]:
                    print(f"    RUST-onl: {l}")
    w = max(len(n) for n, _, _ in rows)
    for name, st, info in rows:
        mark = {"PASS": "ok", "FAIL": "XX", "RUST_ERR": "E!", "PY_ERR": "p!"}[st]
        print(f"[{mark}] {name.ljust(w)}  {st:8s} {info}")
    print(f"\n{npass} PASS, {nfail} FAIL, {nerr} ERR  / {len(BATTERY)} constructs")
    sys.exit(0 if nfail == 0 and nerr == 0 else 1)


if __name__ == "__main__":
    main()
