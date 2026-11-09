# usage: python3 -I ht_seeds.py KM_BIN CHECKER OUT.tsv [lo hi]
# Runs `km classify --lines` on route ht_general for the ALC seeds of
# .work/agent-assets/2026-10-28-scratch (sq/g<seed>.ofn or bridge/seeds/g<seed>.ofn)
# with KM_HT_SUBSET_MODEL_CERT, KM_HT_SUBSET_MODEL_CHECKER and
# KM_HT_INCRBLOCK2_CHECK=1, and compares the answer with the cached HermiT gold.
# Per seed: seed, status (ok | wrong | km-error | no-gold), terminals accepted,
# accepted with folds, rejected, not emitted (with the first reason).
import subprocess, json, os, sys, tempfile, shutil, concurrent.futures as cf
A = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch"
km, checker, out = sys.argv[1], sys.argv[2], sys.argv[3]
lo, hi = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (1, 700)
scratch = os.environ.get("SCRATCH", os.path.dirname(os.path.abspath(out)))
# OFFLINE=1: the run only writes certificates and Lean checks them afterwards,
# so a rejection does not change the published answer; APPROX=1 sets
# KM_ALLOW_APPROXIMATE; KEEP=<dir> keeps rejected certificates.
offline = os.environ.get("OFFLINE") == "1"
approx = os.environ.get("APPROX") == "1"
keep = os.environ.get("KEEP")

def path(seed):
    for p in (f"{A}/sq/g{seed}.ofn", f"{A}/bridge/seeds/g{seed}.ofn"):
        if os.path.exists(p):
            return p
    return None

def norm(cons, subs, uns):
    if not cons:
        return (False, frozenset(), frozenset())
    uns = frozenset(uns)
    return (True, frozenset((a, b) for a, b in subs if a not in uns and b not in uns and a != b), uns)

def one(seed):
    p = path(seed)
    g = f"{A}/bridge/gold/{seed}.json"
    if p is None or not os.path.exists(g):
        return [seed, "no-input", 0, 0, 0, 0, ""]
    gold = json.load(open(g))
    if gold is None:
        return [seed, "no-gold", 0, 0, 0, 0, ""]
    d = tempfile.mkdtemp(dir=scratch)
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    env.update(KM_ROUTE="ht_general", KM_HT_SUBSET_MODEL_CERT=d,
               KM_HT_INCRBLOCK2_CHECK="1", TMPDIR=d, KM_THREADS="1", RAYON_NUM_THREADS="1")
    if not offline:
        env["KM_HT_SUBSET_MODEL_CHECKER"] = checker
    if approx:
        env["KM_ALLOW_APPROXIMATE"] = "1"
    try:
        r = subprocess.run(["timeout", "120", km, "classify", "--lines", p], capture_output=True, text=True, env=env)
        lines = r.stderr.splitlines()
        if offline:
            # Run the Lean checker on every written certificate after the run.
            lines = [l for l in lines if not l.endswith(" written")]
            for f in sorted(os.listdir(d)):
                if f.endswith(".json"):
                    fp = os.path.join(d, f)
                    ok = subprocess.run([checker, fp], capture_output=True).returncode == 0
                    doc = json.load(open(fp))
                    folds = len(doc["folds"])
                    variant = "relabel"
                    if not ok and folds and os.environ.get("OWN") == "1":
                        # The fold that keeps the blocked node's own label.
                        doc["relabel"] = False
                        own = fp[:-5] + ".own"
                        json.dump(doc, open(own, "w"))
                        ok = subprocess.run([checker, own], capture_output=True).returncode == 0
                        variant = "own-label"
                    lines.append(f"KM_HT_SUBSET_MODEL_CERT file={f} folds={folds} variant={variant} " + ("accepted" if ok else "rejected"))
                    if not ok and keep:
                        shutil.copy(os.path.join(d, f), os.path.join(keep, f"seed{seed}-{f}"))
    finally:
        shutil.rmtree(d, ignore_errors=True)
    acc = accf = rej = ne = 0
    reason = ""
    for l in lines:
        if not l.startswith("KM_HT_SUBSET_MODEL_CERT "):
            continue
        if l.endswith(" accepted"):
            acc += 1
            accf += " folds=0 " not in l
        elif l.endswith(" rejected"):
            rej += 1
        elif "not emitted" in l:
            ne += 1
            reason = reason or l.split("not emitted: ", 1)[1]
    cons = None; subs = set(); uns = set()
    for l in r.stdout.splitlines():
        t = l.split("\t")
        if t[0].startswith("CONSISTENT"): cons = t[0].endswith("1")
        elif t[0] == "SUB": subs.add((t[1].lstrip(":"), t[2].lstrip(":")))
        elif t[0] == "UNSAT": uns.add(t[1].lstrip(":"))
    if cons is None:
        status = "km-error"
        reason = reason or (r.stderr.strip().splitlines() or [""])[-1][:200]
    else:
        h = norm(gold["consistent"], [tuple(x) for x in gold["subsumptions"]], gold["unsatisfiable"])
        k = norm(cons, subs, uns)
        status = "ok" if h == k else "wrong"
    return [seed, status, acc, accf, rej, ne, reason]

with cf.ThreadPoolExecutor(int(os.environ.get("JOBS", "12"))) as ex:
    rows = list(ex.map(one, range(lo, hi + 1)))
with open(out, "w") as f:
    for row in rows:
        f.write("\t".join(map(str, row)) + "\n")
from collections import Counter
print(Counter(r[1] for r in rows))
print("terminals accepted", sum(r[2] for r in rows), "with folds", sum(r[3] for r in rows),
      "rejected", sum(r[4] for r in rows), "not emitted", sum(r[5] for r in rows))
print("seeds with an accepted folded terminal", sum(1 for r in rows if r[3] > 0))
print(Counter(r[6].split(" (")[0][:80] for r in rows if r[5] or r[1] == "km-error"))
