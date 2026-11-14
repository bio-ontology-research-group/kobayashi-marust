#!/usr/bin/env python3
"""Apply the verdict rules added to ParityRun after a run to the stored JSON results.

  parity_reverdict.py <json dir>

ParityRun marks isEntailmentCheckingSupported (HermiT true, KM false), isPrecomputed (HermiT true, KM
false) and getPrecomputableInferenceTypes (KM a strict subset) as km_unsupported. A result file written
before a rule existed keeps the old verdict; this script rewrites it from the stored answers, so the
report needs no new run. It touches only differ_content verdicts and is idempotent.
"""
import json, sys, glob


def rule(method, h, k):
    if h.get("status") != "ok" or k.get("status") != "ok":
        return None
    ha, ka = h["ans"], k["ans"]
    if method in ("isEntailmentCheckingSupported", "isPrecomputed"):
        if ha["t"] == "bool" and ka["t"] == "bool" and ha["v"] and not ka["v"]:
            return "km_unsupported"
    if method == "getPrecomputableInferenceTypes" and ha["t"] == "set" and ka["t"] == "set":
        hs, ks = set(ha["items"]), set(ka["items"])
        if hs >= ks and hs != ks:
            return "km_unsupported"
    return None


changed = 0
for f in sorted(glob.glob(sys.argv[1] + "/*.json")):
    d = json.load(open(f))
    dirty = False
    for c in d["calls"]:
        if c.get("verdict") == "differ_content" and "hermit" in c and "km" in c:
            v = rule(c["method"], c["hermit"], c["km"])
            if v:
                c["verdict"] = v
                dirty = True
                changed += 1
    if dirty:
        json.dump(d, open(f, "w"), indent=2)
print("verdicts rewritten:", changed)
