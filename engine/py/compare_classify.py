#!/usr/bin/env python3
"""Authoritative frontend validation via CLASSIFICATION equality.

Runs BOTH frontends (Python `frontend.ofn_to_clauses` and the Rust `ofn`
binary) and feeds each clause set through the engine, then compares the
resulting subsumptions/inconsistency RESTRICTED TO NAMED concepts (internal
Q_/f_/__* symbols differ between frontends by construction, so they are
projected out). If the named-concept classifications match, the two frontends
are semantically equivalent for classification — which is all that matters.

This runs the KM ENGINE, so run it ONLY on a server (ws), never the laptop.

    OFN_BIN=../target/release/ofn ENGINE_BIN=../target/release/kobayashi-marust \
        python3 compare_classify.py [--verbose]
"""
from __future__ import annotations
import json, os, subprocess, sys, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import frontend          # noqa: E402
from compare_frontends import BATTERY, DECL, ont  # reuse the battery

OFN_BIN = os.environ.get("OFN_BIN", str(HERE.parent / "target" / "release" / "ofn"))
ENGINE_BIN = os.environ.get("ENGINE_BIN", str(HERE.parent / "target" / "release" / "kobayashi-marust"))
VERBOSE = "--verbose" in sys.argv[1:]

# Discriminating ontologies: each FORCES a named subsumption or an
# unsatisfiability THROUGH a tricky construct, so a wrong clausification of that
# construct changes the named-concept classification (unlike the bare battery,
# where the proxy clauses may stay dormant). These target exactly the 5
# constructs whose structural canon differed (forall-intro / exact / not-self).
DISCRIM = {
    # forall-intro: A=∀r.C, B=∀r.(C⊔D)  ⇒  A ⊑ B (needs the ∀-intro clause to
    # CONCLUDE membership in the universal restriction B).
    "forall_subsume": "EquivalentClasses(:A ObjectAllValuesFrom(:r :C))\n"
                      "EquivalentClasses(:B ObjectAllValuesFrom(:r ObjectUnionOf(:C :D)))\n",
    # forall-intro via told ∀: A ⊑ ∀r.C, B ≡ ∀r.C  ⇒  A ⊑ B.
    "forall_told":    "SubClassOf(:A ObjectAllValuesFrom(:r :C))\n"
                      "EquivalentClasses(:B ObjectAllValuesFrom(:r :C))\n",
    # exact lower bound: A=(=2 r.C), B=(>=2 r.C)  ⇒ A ⊑ B.
    "exact_min":      "EquivalentClasses(:A ObjectExactCardinality(2 :r :C))\n"
                      "EquivalentClasses(:B ObjectMinCardinality(2 :r :C))\n",
    # exact clash: A ⊑ (=2 r.C) and A ⊑ (<=1 r.C)  ⇒  A unsatisfiable (A ⊑ ⊥).
    "exact_clash":    "SubClassOf(:A ObjectExactCardinality(2 :r :C))\n"
                      "SubClassOf(:A ObjectMaxCardinality(1 :r :C))\n",
    # max clash: A ⊑ ∃r.C ⊓ ∃r.D-distinct... simpler: A ⊑ (>=2 r.C) ⊓ (<=1 r.C) ⇒ unsat.
    "min_max_clash":  "SubClassOf(:A ObjectIntersectionOf(ObjectMinCardinality(2 :r :C) ObjectMaxCardinality(1 :r :C)))\n",
    # not-self clash: C ⊑ ∃r.Self and C ⊑ ¬∃r.Self  ⇒  C unsatisfiable.
    "notself_clash":  "SubClassOf(:C ObjectHasSelf(:r))\n"
                      "SubClassOf(:C ObjectComplementOf(ObjectHasSelf(:r)))\n",
    # self subsumption: A ⊑ ∃r.Self, B ≡ ∃r.Self ⇒ A ⊑ B.
    "self_subsume":   "SubClassOf(:A ObjectHasSelf(:r))\n"
                      "EquivalentClasses(:B ObjectHasSelf(:r))\n",
    # nested forall in superclass forcing subsumption.
    "nested_forall":  "SubClassOf(:A ObjectAllValuesFrom(:r :C))\n"
                      "EquivalentClasses(:B ObjectAllValuesFrom(:r ObjectUnionOf(:C :D)))\n"
                      "SubClassOf(:C :D)\n",
}

_INTERNAL = ("Q_", "f_", "__nom__", "__inv__", "__conj__", "__trans__", "def_", "aux_", "Q_minus")
BOTTOM = {"Nothing", "owl:Nothing", "⊥", "BOTTOM"}


def is_internal(s: str) -> bool:
    base = frontend.local_name(s) if not s.startswith("__") else s
    return any(s.startswith(p) for p in _INTERNAL) or any(base.startswith(p) for p in _INTERNAL)


def run_engine(clauses):
    p = subprocess.run([ENGINE_BIN], input=json.dumps({"clauses": clauses}),
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(p.stderr[:200])
    return json.loads(p.stdout)


def named_projection(engine_out):
    """Set of (sub, super) over named concepts only, plus inconsistency flag.
    Internal proxy names are projected out (they are frontend-private)."""
    pairs = set()
    for a, sups in engine_out.get("subsumptions", {}).items():
        if is_internal(a):
            continue
        for s in sups:
            sl = frontend.local_name(s)
            if sl in BOTTOM:
                pairs.add((frontend.local_name(a), "BOTTOM"))
            elif not is_internal(s) and frontend.local_name(s) != frontend.local_name(a):
                pairs.add((frontend.local_name(a), frontend.local_name(s)))
    return pairs, bool(engine_out.get("inconsistent", False))


def py_clauses(path):
    return frontend.ofn_to_clauses(path)


def rust_clauses(path):
    p = subprocess.run([OFN_BIN, path], capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError(f"ofn rc={p.returncode}: {p.stderr[:150]}")
    return json.loads(p.stdout)["clauses"]


def main():
    npass = nfail = nerr = 0
    rows = []
    cases = dict(BATTERY)
    cases.update(DISCRIM)
    for name, body in cases.items():
        with tempfile.NamedTemporaryFile("w", suffix=".ofn", delete=False) as f:
            f.write(ont(DECL + body)); path = f.name
        try:
            py = named_projection(run_engine(py_clauses(path)))
            ru = named_projection(run_engine(rust_clauses(path)))
        except Exception as e:
            rows.append((name, "ERR", str(e)[:90])); nerr += 1; os.unlink(path); continue
        os.unlink(path)
        if py == ru:
            rows.append((name, "PASS", f"{len(py[0])} subs incons={py[1]}")); npass += 1
        else:
            ps, rs = py[0], ru[0]
            rows.append((name, "FAIL", f"py_only={sorted(ps - rs)} rust_only={sorted(rs - ps)} incons py={py[1]} rust={ru[1]}"))
            nfail += 1
    w = max(len(n) for n, _, _ in rows)
    for name, st, info in rows:
        mark = {"PASS": "ok", "FAIL": "XX", "ERR": "E!"}[st]
        print(f"[{mark}] {name.ljust(w)}  {st:5s} {info}")
    print(f"\n{npass} PASS, {nfail} FAIL, {nerr} ERR  / {len(cases)} constructs (named-concept classification)")
    sys.exit(0 if nfail == 0 and nerr == 0 else 1)


if __name__ == "__main__":
    main()
