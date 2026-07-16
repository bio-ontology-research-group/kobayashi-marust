#!/usr/bin/env python3
"""Self-check for analyze_profiles expressivity accounting.

Runs the analyzer end-to-end on a synthetic corpus in a temp dir:
    python3 results/benchmarks/2026-07-15-routing/test_analyze_profiles.py

Guards the regression where an ontology with NO Konclude expressivity reference
(konclude_expressivity is None) was scored as a KM/Konclude *mismatch* because
`None == code` is False, inflating expressivity_mismatches in the committed
profile-summary.json.
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def _profile(ont, code):
    return {
        "ont": ont,
        "status": "ok",
        "el_rbox_safe": True,
        "profile": {
            "schema_version": 2,
            "positive_abox_tbox_separable": False,
            "expressivity": {"code": code},
            "source": {"logical_axioms": 1, "file_bytes": 10},
            "clauses": {"clauses": 1, "horn_clauses": 1, "disjunctive_clauses": 0},
        },
    }


def check():
    with tempfile.TemporaryDirectory() as root:
        prof = os.path.join(root, "profiles")
        kon = os.path.join(root, "konclude-expressivity")
        os.makedirs(prof)
        os.makedirs(kon)
        # A: Konclude reference present and matching
        # B: Konclude reference present and DIFFERING -> a real mismatch
        # C: NO Konclude reference -> unreferenced, must NOT be a mismatch
        json.dump(_profile("A", "EL"), open(os.path.join(prof, "A.json"), "w"))
        json.dump(_profile("B", "SROIQ"), open(os.path.join(prof, "B.json"), "w"))
        json.dump(_profile("C", "SHIQ"), open(os.path.join(prof, "C.json"), "w"))
        json.dump({"ont": "A", "expressivity": "EL"},
                  open(os.path.join(kon, "A.json"), "w"))
        json.dump({"ont": "B", "expressivity": "ALC"},
                  open(os.path.join(kon, "B.json"), "w"))
        # deliberately no konclude-expressivity/C.json

        subprocess.run(
            [sys.executable, os.path.join(HERE, "analyze_profiles.py"),
             "--root", root, "--output-dir", root],
            check=True, stdout=subprocess.DEVNULL,
        )
        summary = json.load(open(os.path.join(root, "profile-summary.json")))

    assert summary["profile_rows"] == 3, summary
    assert summary["expressivity_matches"] == 1, summary            # only A
    mm = {m["ont"] for m in summary["expressivity_mismatches"]}
    assert mm == {"B"}, summary                                     # only B, NOT C
    assert summary["expressivity_unreferenced"] == ["C"], summary
    print("analyze_profiles expressivity: OK (unreferenced ont not scored a mismatch)")


if __name__ == "__main__":
    check()
