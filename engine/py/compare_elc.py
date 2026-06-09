#!/usr/bin/env python3
"""Differential test: Rust `elc` EL++ completion vs Python `el_route.classify`.

Both consume the *same* frontend clause set, so their raw outputs (internal
names and all) must be identical when the ontology is EL++. A comprehensive EL
battery exercises every normal form NF1-NF7, the two edge rules, the k>2
conjunction decomposition, single- and multi-bottom, backward-bottom
propagation, domain/range, role hierarchy, role chains and transitivity.

Runs the elc binary, so run on ws (a server), never the laptop.

    ELC_BIN=../target/release/elc python3 compare_elc.py [--verbose]
"""
from __future__ import annotations
import json, os, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import frontend          # noqa: E402
import el_route          # noqa: E402

ELC_BIN = os.environ.get("ELC_BIN", str(HERE.parent / "target" / "release" / "elc"))
VERBOSE = "--verbose" in sys.argv[1:]

PRE = ("Prefix(:=<http://x#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
       "Ontology(\n")


def ont(body: str) -> str:
    return PRE + body + "\n)\n"


# Each case: name -> functional-syntax body. All are EL++ (so to_nf accepts).
CASES = {
    # NF1: A⊑B, B⊑C  ⇒ A⊑C
    "nf1_chain": "SubClassOf(:A :B) SubClassOf(:B :C)",
    # NF2 (k=2): A⊑B, A⊑C, B⊓C⊑D ⇒ A⊑D
    "nf2_conj2": "SubClassOf(:A :B) SubClassOf(:A :C) "
                 "SubClassOf(ObjectIntersectionOf(:B :C) :D)",
    # NF2 (k>2): four-way conjunction in the subclass, decomposed into binary
    "nf2_conj4": "SubClassOf(:A :B) SubClassOf(:A :C) SubClassOf(:A :E) "
                 "SubClassOf(:A :G) "
                 "SubClassOf(ObjectIntersectionOf(:B :C :E :G) :D)",
    # NF3+NF4: A⊑∃r.C, ∃r.C⊑D ⇒ A⊑D
    "nf3_nf4": "SubClassOf(:A ObjectSomeValuesFrom(:r :C)) "
               "SubClassOf(ObjectSomeValuesFrom(:r :C) :D)",
    # NF5 (disjointness, k=2): A⊑B, A⊑C, Disjoint(B,C) ⇒ A unsat
    "nf5_disjoint2": "SubClassOf(:A :B) SubClassOf(:A :C) DisjointClasses(:B :C)",
    # NF5 (multi-bottom k>2): B⊓C⊓E ⊑ ⊥, A below all three ⇒ A unsat
    "nf5_disjoint3": "SubClassOf(:A :B) SubClassOf(:A :C) SubClassOf(:A :E) "
                     "DisjointClasses(:B :C :E)",
    # single-side bottom: A ⊑ Nothing ⇒ A unsat
    "nf5_single": "SubClassOf(:A owl:Nothing)",
    # backward-bottom along an edge: A⊑∃r.B, B⊑⊥ ⇒ A⊑⊥
    "bottom_edge": "SubClassOf(:A ObjectSomeValuesFrom(:r :B)) "
                   "SubClassOf(:B owl:Nothing)",
    # NF6 role hierarchy: r⊑s, A⊑∃r.B, ∃s.B⊑C ⇒ A⊑C
    "nf6_role": "SubObjectPropertyOf(:r :s) "
                "SubClassOf(:A ObjectSomeValuesFrom(:r :B)) "
                "SubClassOf(ObjectSomeValuesFrom(:s :B) :C)",
    # NF7 role chain: r∘s⊑t, A⊑∃r.B, B⊑∃s.C, ∃t.C⊑D ⇒ A⊑D
    "nf7_chain": "SubObjectPropertyOf(ObjectPropertyChain(:r :s) :t) "
                 "SubClassOf(:A ObjectSomeValuesFrom(:r :B)) "
                 "SubClassOf(:B ObjectSomeValuesFrom(:s :C)) "
                 "SubClassOf(ObjectSomeValuesFrom(:t :C) :D)",
    # transitivity (r∘r⊑r): A⊑∃r.B, B⊑∃r.C, ∃r.C⊑D ⇒ A⊑D
    "transitive": "TransitiveObjectProperty(:r) "
                  "SubClassOf(:A ObjectSomeValuesFrom(:r :B)) "
                  "SubClassOf(:B ObjectSomeValuesFrom(:r :C)) "
                  "SubClassOf(ObjectSomeValuesFrom(:r :C) :D)",
    # domain: domain(r)=A, B⊑∃r.C ⇒ B⊑A
    "domain": "ObjectPropertyDomain(:r :A) "
              "SubClassOf(:B ObjectSomeValuesFrom(:r :C))",
    # range: range(r)=A, B⊑∃r.C ⇒ (filler C ⊑ A via range)
    "range": "ObjectPropertyRange(:r :A) "
             "SubClassOf(:B ObjectSomeValuesFrom(:r :C))",
    # equivalence both directions
    "equiv": "EquivalentClasses(:A :B) SubClassOf(:B :C)",
    # larger mixed: a small class hierarchy with shared conjunctions
    "mixed": "SubClassOf(:A :B) SubClassOf(:B :C) SubClassOf(:C :D) "
             "SubClassOf(:A ObjectSomeValuesFrom(:r :E)) "
             "SubClassOf(:E :F) SubClassOf(ObjectSomeValuesFrom(:r :F) :G) "
             "SubClassOf(ObjectIntersectionOf(:D :G) :H)",
}


def run_elc(clauses):
    payload = json.dumps({"clauses": clauses})
    proc = subprocess.run([ELC_BIN], input=payload, capture_output=True, text=True)
    if proc.returncode == 3:
        return None
    if proc.returncode != 0:
        raise RuntimeError(f"elc failed rc={proc.returncode}: {proc.stderr}")
    return json.loads(proc.stdout)


def norm(out):
    """Canonicalise a classify result for comparison."""
    if out is None:
        return None
    subs = {k: sorted(v) for k, v in out["subsumptions"].items() if v}
    return (out.get("inconsistent", False), subs)


def main():
    npass = nfail = nexercise = 0
    for name, body in CASES.items():
        with tempfile.NamedTemporaryFile("w", suffix=".ofn", delete=False) as f:
            f.write(ont(body))
            path = f.name
        try:
            clauses = frontend.ofn_to_clauses(path)
        finally:
            os.unlink(path)
        py = norm(el_route.classify(clauses))
        rs = norm(run_elc(clauses))
        # The gate is agreement: elc must produce exactly what el_route produces
        # on identical clauses. Both declining (None) is agreement too, but does
        # not exercise the saturation, so flag those separately.
        ok = (py == rs)
        nexercise += ok and py is not None
        npass += ok
        nfail += not ok
        tag = "" if py is not None else "  (both decline: not EL-routable)"
        status = "PASS" if ok else "FAIL"
        print(f"  [{status}] {name}{tag}")
        if not ok or VERBOSE:
            print(f"      py  : {py}")
            print(f"      rust: {rs}")
            if py is not None and rs is not None:
                pk, rk = set(py[1]), set(rs[1])
                if pk != rk:
                    print(f"      keys only-py: {sorted(pk - rk)}")
                    print(f"      keys only-rs: {sorted(rk - pk)}")
                for k in sorted(pk & rk):
                    if py[1][k] != rs[1].get(k):
                        print(f"      diff[{k}]: py={py[1][k]} rs={rs[1].get(k)}")
    print(f"\n{npass}/{npass + nfail} cases identical (elc == el_route); "
          f"{nexercise} exercised the saturation")
    sys.exit(1 if nfail else 0)


if __name__ == "__main__":
    main()
