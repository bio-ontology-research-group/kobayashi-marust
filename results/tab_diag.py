#!/usr/bin/env python3
"""Diagnose why each disjunction-family ont is NOT solved by KM's tableau racer.
For each ont: run ofn -> clauses, run cb_to_ht.convert, report the feature flags
the routing gate (owl_classify._spawn_tableau) keys on, plus clause/disjunction
counts. This splits the targets into:
  - CLEAN  (no fenced/dropped/inverse/number/nominals)  -> eligible; fails = non-convergence
  - FEAT   (number/inverse/nominals but dropped==0, fenced==[]) -> faithfully encoded but GATED OFF
  - OOF    (fenced or dropped>0) -> out-of-fragment for the current tableau
"""
import json, os, subprocess, sys, tempfile
KM = "/ibex/scratch/hohndor/km"
sys.path.insert(0, KM + "/harness")
import cb_to_ht

OFN = KM + "/engine/target/release/ofn"
CORPUS = KM + "/corpus"
onts = sys.argv[1:]

print(f"{'ont':>7} {'ncl':>7} {'disj':>5} {'htcl':>7} {'drop':>5} {'fenced':>6} "
      f"{'inv':>4} {'num':>4} {'nom':>4}  category")
for ont in onts:
    f = f"{CORPUS}/ore_ont_{ont}.owl"
    mfd, meta = tempfile.mkstemp(suffix=".meta.json")
    os.close(mfd)
    try:
        with tempfile.TemporaryFile("w+") as cf:
            p = subprocess.run([OFN, f, "--meta", meta], stdout=cf, stderr=subprocess.DEVNULL)
            cf.seek(0)
            data = json.load(cf)
        cl = data["clauses"]
        ncl = len(cl)
        disj = sum(1 for c in cl if len(c.get("head", [])) >= 2)
        tin = cb_to_ht.convert(cl, None)
        htcl = len(tin.get("clauses", []))
        drop = tin.get("dropped", 0)
        fenced = len(tin.get("fenced", []) or [])
        inv = bool(tin.get("inverse"))
        num = bool(tin.get("number"))
        nom = bool(tin.get("nominals"))
        if fenced or drop:
            cat = "OOF (fenced/dropped)"
        elif inv or num or nom:
            cat = "FEAT (gated, faithful)"
        else:
            cat = "CLEAN (eligible->non-converge)"
        print(f"{ont:>7} {ncl:>7} {disj:>5} {htcl:>7} {drop:>5} {fenced:>6} "
              f"{str(inv):>4} {str(num):>4} {str(nom):>4}  {cat}")
    except Exception as e:
        print(f"{ont:>7}  ERROR: {repr(e)[:120]}")
    finally:
        try: os.unlink(meta)
        except OSError: pass
