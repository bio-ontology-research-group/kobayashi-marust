#!/usr/bin/env python3
"""Route one ORE ont to the fixed KM_HT hypertableau IF it is ALC(H) and
non-transitive (where anywhere-subset blocking is sound + complete), run it, and
compare the classification to Konclude gold. Emits one JSON result line.

Routing guard (sound): skip number restrictions / inverse roles / nominals
(out of the ALC(H) fragment) AND transitive roles / role chains (subset blocking
can be incomplete there, e.g. 5303). Skipped onts are left to the production
CB/elc pipeline, so KM_HT routing can only ADD recoveries, never regress.
"""
import sys, os, json, gzip, subprocess, time

HP = "/ibex/scratch/hohndor/km-htport"
KM = "/ibex/scratch/hohndor/km"
TAB = f"{HP}/engine/target/release/tableau_cli"
TIMEOUT = int(os.environ.get("HT_TIMEOUT", "240"))

def gold_pairs(p):
    cons = None; s = set()
    with gzip.open(p, "rt") as f:
        for i, ln in enumerate(f):
            ln = ln.rstrip("\n")
            if i == 0 and ln.strip() in ("0", "1"):
                cons = (ln.strip() == "1"); continue
            if "\t" in ln:
                a, b = ln.split("\t", 1); s.add((a, b))
    return cons, s

def main():
    ont = sys.argv[1]
    owl = f"{KM}/corpus/ore_ont_{ont}.owl"
    res = {"ont": ont}
    if not os.path.exists(owl):
        res["status"] = "no_owl"; print(json.dumps(res)); return
    # transitivity / role-composition detection (functional syntax)
    try:
        txt = open(owl, encoding="utf-8", errors="ignore").read()
    except Exception as e:
        res["status"] = "read_fail"; res["err"] = str(e); print(json.dumps(res)); return
    transitive = ("TransitiveObjectProperty(" in txt) or ("ObjectPropertyChain(" in txt)
    # emit TInput (ofn -> cb_to_ht)
    try:
        em = subprocess.run(["python3", f"{HP}/emit2.py", owl],
                            capture_output=True, text=True, timeout=120)
        tin = em.stdout
        tj = json.loads(tin)
    except Exception as e:
        res["status"] = "emit_fail"; res["err"] = str(e)[:120]; print(json.dumps(res)); return
    alc = (not tj.get("inverse")) and (not tj.get("number")) and (len(tj.get("nominals", [])) == 0)
    res.update({"alc": bool(alc), "transitive": bool(transitive),
                "concepts": len(tj.get("concepts", [])), "clauses": len(tj.get("clauses", []))})
    if not (alc and not transitive):
        res["status"] = "skip_route"; print(json.dumps(res)); return
    # run KM_HT
    env = dict(os.environ); env["KM_HT"] = "1"
    t0 = time.time()
    try:
        p = subprocess.run([TAB], input=tin, capture_output=True, text=True,
                           timeout=TIMEOUT, env=env)
    except subprocess.TimeoutExpired:
        res["status"] = "timeout"; res["wall"] = TIMEOUT; print(json.dumps(res)); return
    res["wall"] = round(time.time() - t0, 2)
    try:
        out = json.loads(p.stdout)
    except Exception:
        res["status"] = "run_fail"; res["stderr"] = p.stderr[-160:]; print(json.dumps(res)); return
    km_cons = out.get("consistent", True)
    km = set((a, b) for a, b in out.get("subsumptions", []))
    res["km_nsub"] = len(km)
    gp = f"{KM}/gold/konclude__ore_ont_{ont}.owl.sig.gz"
    if not os.path.exists(gp):
        res["status"] = "ok_nogold"; print(json.dumps(res)); return
    gcons, g = gold_pairs(gp)
    if gcons is not None and km_cons != gcons:
        res["status"] = "DIFF_consistency"; res["km_cons"] = km_cons; res["gold_cons"] = gcons
        print(json.dumps(res)); return
    only_km = km - g; only_g = g - km
    res["unsound"] = len(only_km); res["incomplete"] = len(only_g)
    res["status"] = "GOLD_CLEAN" if not only_km and not only_g else "DIFF"
    if res["status"] == "DIFF":
        res["sample_km_only"] = ["%s<=%s" % p for p in list(only_km)[:3]]
        res["sample_gold_only"] = ["%s<=%s" % p for p in list(only_g)[:3]]
    print(json.dumps(res))

if __name__ == "__main__":
    main()
