#!/usr/bin/env python3
"""Validate the hypertableau (HT) pipeline against the HermiT oracle.

For each ontology the pipeline is
    .owl ──frontend.ofn_to_clauses + ofn_rbox──▶ {clauses, rbox}
         ──cb_to_ht.convert──▶ TInput (HT-clauses) ──tableau_cli──▶ TOutput
and the entailed atomic subsumptions / unsatisfiable classes / consistency are
compared with HermiT (oracle/run_oracle.sh, or a pre-dumped oracle JSON).

Per-ontology verdicts:
  OUT-OF-FRAGMENT  the converter fenced an RBox axiom or dropped a TBox clause
                   it cannot encode losslessly (inverse, transitive, number,
                   nominal, ...). Honest: we do NOT compare, because a missing
                   axiom would make classification incomplete.
  MATCH            tableau output equals HermiT (consistency, subs, unsat).
  MISMATCH         tableau output differs (reported with the diff).
  TABLEAU-TIMEOUT  tableau exceeded the time budget (a perf gap, not a bug).
  CBERR / HERMITERR a stage failed to run.

Usage:  validate_ht.py <dir-or-file...> [--timeout S] [--oracle-dir D]
"""
from __future__ import annotations
import json, os, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "engine" / "py"))
_moose = ([Path(os.environ["MOOSE_HOME"])] if os.environ.get("MOOSE_HOME") else [])
_moose += [ROOT.parent / "moose", ROOT / "moose"]
for _c in _moose:
    if (_c / "moose" / "sroiq").is_dir():
        sys.path.insert(0, str(_c)); break

import frontend
import cb_to_ht

TABLEAU = ROOT / "engine" / "target" / "release" / "tableau_cli"
HERMIT_LIB = os.environ.get(
    "HERMIT_LIB",
    "/home/leechuck/Documents/papers/ai-biomed-summer-school/notebooks/mowl/"
    "gateway/build/distributions/gateway/lib",
)


def short(n):
    return n.rsplit("#", 1)[-1].rsplit("/", 1)[-1]


def hermit(owl, timeout):
    cp = ".:%s/*" % HERMIT_LIB
    out = subprocess.run(["java", "-cp", cp, "Oracle", str(Path(owl).resolve())],
                         cwd=str(ROOT / "oracle"), capture_output=True,
                         text=True, timeout=timeout)
    return json.loads(out.stdout)


def norm_subs(subs):
    return {(short(a), short(b)) for a, b in subs}


def run_one(owl, timeout):
    # 1. frontend: CB clauses + RBox records
    clauses = frontend.ofn_to_clauses(owl)
    rbox = frontend.ofn_rbox(owl)
    # 2. convert to HT-clauses (fenced/dropped surface out-of-fragment axioms)
    tin = cb_to_ht.convert(clauses, rbox)
    if tin["dropped"] or tin["fenced"]:
        reasons = sorted({f["reason"] for f in tin["fenced"]})
        return ("OUT-OF-FRAGMENT",
                "dropped=%d fenced=%d %s" % (tin["dropped"], len(tin["fenced"]), reasons))
    # 3. tableau
    try:
        p = subprocess.run([str(TABLEAU)], input=json.dumps(tin),
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return ("TABLEAU-TIMEOUT", "")
    if p.returncode != 0:
        return ("TABLEAUERR", p.stderr.strip()[:200])
    tout = json.loads(p.stdout)
    # 4. HermiT oracle
    try:
        h = hermit(owl, timeout)
    except Exception as e:
        return ("HERMITERR", str(e)[:200])
    ts, hs = norm_subs(tout["subsumptions"]), norm_subs(h["subsumptions"])
    tu = {short(x) for x in tout["unsatisfiable"]}
    hu = {short(x) for x in h["unsatisfiable"]}
    if tout["consistent"] == h["consistent"] and ts == hs and tu == hu:
        return ("MATCH", "subs=%d unsat=%d" % (len(ts), len(tu)))
    t_only, h_only = ts - hs, hs - ts
    return ("MISMATCH",
            "cons t=%s h=%s | t-only-subs=%d h-only-subs=%d | unsatdiff=%d"
            % (tout["consistent"], h["consistent"], len(t_only), len(h_only),
               len(tu ^ hu)))


def main():
    timeout = 30
    args, i = [], 1
    while i < len(sys.argv):
        a = sys.argv[i]
        if a == "--timeout":
            timeout = float(sys.argv[i + 1]); i += 2; continue
        if a.startswith("--"):
            i += 1; continue
        args.append(a); i += 1
    files = []
    for a in args:
        p = Path(a)
        files += sorted(p.glob("*.owl")) if p.is_dir() else [p]
    tally = {}
    for owl in files:
        try:
            verdict, detail = run_one(owl, timeout)
        except Exception as e:
            verdict, detail = "CBERR", str(e)[:200]
        tally[verdict] = tally.get(verdict, 0) + 1
        print("%-40s %-16s %s" % (owl.name, verdict, detail), flush=True)
    print("=== SUMMARY total=%d  %s ===" %
          (len(files), "  ".join("%s=%d" % kv for kv in sorted(tally.items()))))


if __name__ == "__main__":
    main()
