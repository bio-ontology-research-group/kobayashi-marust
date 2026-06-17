#!/usr/bin/env python3
"""Production-faithful KM_HT correctness check. Drives the HT exactly like the
real pipeline (ofn -> cb_to_ht -> tableau_cli KM_HT=1), maps output via iri_map,
filters internal concepts, then canonicalises with the SAME ore_canon.canonicalize
(transitive closure + SCC condensation) that produced the gold signatures, and
compares the resulting frozensets. This removes the flat-pair / slash-localname /
_hasValue artifacts of the old loc() runner. GENERAL routing guard only (lossless
conversion + no inverse); no ontology identity is used."""
import sys, os, json, gzip, subprocess, time
KM = "/ibex/scratch/hohndor/km"; HP = "/ibex/scratch/hohndor/km-htport"
sys.path.insert(0, f"{HP}/engine/py"); sys.path.insert(0, f"{KM}/harness")
import cb_to_ht, ore_canon
OFN = f"{HP}/engine/target/release/ofn"
TAB = f"{HP}/engine/target/release/tableau_cli"
TIMEOUT = int(os.environ.get("HT_TIMEOUT", "180"))

BOTTOM = {"Nothing", "owl:Nothing"}

def gold_sig(o):
    p = f"{KM}/gold/konclude__ore_ont_{o}.owl.sig.gz"
    if not os.path.exists(p): return None, None, None
    subs = set(); unsat = set(); cons = True
    with gzip.open(p, "rt") as f:
        for i, ln in enumerate(f):
            ln = ln.rstrip("\n")
            if i == 0 and ln.strip() in ("0", "1"):
                cons = (ln.strip() == "1"); continue
            if ln.startswith("#UNSAT"):  # unsat block marker, if any
                continue
            if "\t" in ln:
                a, b = ln.split("\t", 1)
                subs.add((a, b))
    return cons, subs, unsat

def main():
    ont = sys.argv[1]; res = {"ont": ont}
    owl = f"{KM}/corpus/ore_ont_{ont}.owl"
    if not os.path.exists(owl):
        res["status"] = "no_owl"; print(json.dumps(res)); return
    try:
        of = subprocess.run([OFN, owl], capture_output=True, text=True, timeout=180)
    except subprocess.TimeoutExpired:
        res["status"] = "ofn_timeout"; print(json.dumps(res)); return
    if of.returncode == 3:
        res["status"] = "ofn_unsupported"; print(json.dumps(res)); return
    if of.returncode != 0 or not of.stdout.strip():
        res["status"] = "ofn_fail"; print(json.dumps(res)); return
    d = json.loads(of.stdout)
    clauses = d["clauses"]; iri_map = d.get("iri_map", {}); named = set(d.get("named", []))
    try:
        tin = cb_to_ht.convert(clauses, [])
    except Exception as e:
        res["status"] = "convert_fail"; res["err"] = str(e)[:120]; print(json.dumps(res)); return
    fenced = tin.get("fenced", []); dropped = tin.get("dropped", 0) or 0
    inverse = bool(tin.get("inverse"))
    routable = (dropped == 0) and (not fenced) and (not inverse)
    res.update({"routable": routable, "inverse": inverse, "number": bool(tin.get("number")),
                "concepts": len(tin.get("concepts", [])), "clauses": len(tin.get("clauses", []))})
    if not routable:
        res["status"] = "skip_route"; print(json.dumps(res)); return
    t0 = time.time()
    try:
        p = subprocess.run([TAB], input=json.dumps(tin), capture_output=True, text=True,
                           timeout=TIMEOUT, env=dict(os.environ, KM_HT="1"))
    except subprocess.TimeoutExpired:
        res["status"] = "timeout"; res["wall"] = TIMEOUT; print(json.dumps(res)); return
    res["wall"] = round(time.time() - t0, 2)
    try:
        out = json.loads(p.stdout)
    except Exception:
        res["status"] = "run_fail"; res["stderr"] = p.stderr[-160:]; print(json.dumps(res)); return
    # build a production-shape classification json, then canonicalise it the SAME
    # way gold was canonicalised. is_internal operates on the INTERNAL name with
    # the named-iri escape (a real OWL class whose local name happens to start
    # with Q_/__ or contain ':' — e.g. Q_Fever, _MGI:101757 — is NOT internal),
    # exactly as owl_classify does; then map the name to its full IRI.
    def is_internal(name):
        if name in named:
            return False
        s = ore_canon.localname(str(iri_map.get(name, name)))
        return (s.startswith("Q_") or s.startswith("__") or s.startswith("aux_")
                or s.startswith("def_") or (":" in s and s not in BOTTOM))
    pairs = []
    for a, b in out.get("subsumptions", []):
        if is_internal(a) or is_internal(b):
            continue
        pairs.append([iri_map.get(a, a), iri_map.get(b, b)])
    clsjson = json.dumps({"consistent": out.get("consistent", True),
                          "subsumptions": pairs, "unsatisfiable": []})
    hc, hsubs, hunsat, capped = ore_canon.canonicalize(clsjson, "json")
    gc, gsubs, gunsat = gold_sig(ont)
    if gsubs is None:
        res["status"] = "ok_nogold"; res["ht_nsub"] = len(hsubs); print(json.dumps(res)); return
    if gc is not None and hc != gc:
        res["status"] = "DIFF_consistency"; res["ht_cons"] = hc; res["gold_cons"] = gc
        print(json.dumps(res)); return
    us = hsubs - gsubs; inc = gsubs - hsubs
    res["ht_nsub"] = len(hsubs); res["gold_nsub"] = len(gsubs)
    res["unsound"] = len(us); res["incomplete"] = len(inc); res["capped"] = capped
    res["status"] = "GOLD_CLEAN" if not us and not inc else ("UNSOUND" if us else "INCOMPLETE")
    if us: res["sample_unsound"] = ["%s<=%s" % pr for pr in sorted(us)[:4]]
    if inc: res["sample_incomplete"] = ["%s<=%s" % pr for pr in sorted(inc)[:4]]
    print(json.dumps(res))

if __name__ == "__main__":
    main()
