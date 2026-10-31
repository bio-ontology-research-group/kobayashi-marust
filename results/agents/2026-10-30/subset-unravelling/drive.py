# usage: python3 -I drive.py KM CHECKER GEN.py OUTDIR lo hi
# For each seed: generate an ontology, compute HermiT gold (cached), run
# `km classify --lines` on route ht_general writing subset-model certificates
# (no inline checker, so the published answer is the default route's), then
# check every certificate offline with the Lean checker (relabel, then the
# own-label variant). Row: seed status acc rej timeout_cert noemit reason
import subprocess, json, os, sys, tempfile, shutil, concurrent.futures as cf
km, checker, gen, outd = sys.argv[1:5]
lo, hi = int(sys.argv[5]), int(sys.argv[6])
ORACLE = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch/oracle"
os.makedirs(f"{outd}/ont", exist_ok=True); os.makedirs(f"{outd}/gold", exist_ok=True); os.makedirs(f"{outd}/keep", exist_ok=True)
route = os.environ.get("ROUTE", "ht_general")
extra = dict(kv.split("=", 1) for kv in os.environ.get("EXTRA", "").split() if kv)
def gold(seed, p):
    g = f"{outd}/gold/{seed}.json"
    if not os.path.exists(g):
        cp = open(f"{ORACLE}/cp.txt").read().strip()
        r = subprocess.run(["timeout", "120", "java", "-Xmx1g", "-XX:ActiveProcessorCount=1", "-cp", f"{ORACLE}:{cp}", "Oracle", p], capture_output=True, text=True)
        try:
            json.loads(r.stdout); open(g, "w").write(r.stdout)
        except Exception:
            return None
    return json.load(open(g))
def norm(cons, subs, uns):
    if not cons: return (False, frozenset(), frozenset())
    uns = frozenset(uns)
    return (True, frozenset((a, b) for a, b in subs if a not in uns and b not in uns and a != b), uns)
def check(fp):
    # 0 accepted, 1 rejected (the checker printed "rejected"), 124 timeout;
    # anything else (a failed spawn on the loaded host) is retried.
    for _ in range(5):
        try:
            r = subprocess.run(["timeout", os.environ.get("CTO", "60"), checker, fp], capture_output=True, text=True)
        except Exception:
            continue
        if r.returncode == 124: return 124
        if "accepted" in r.stdout: return 0
        if "rejected" in r.stdout: return 1
    return 124
A = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-assets/2026-10-28-scratch"
def one(seed):
    if gen == "CORPUS":
        p = next((q for q in (f"{A}/sq/g{seed}.ofn", f"{A}/bridge/seeds/g{seed}.ofn") if os.path.exists(q)), None)
        g = f"{A}/bridge/gold/{seed}.json"
        if p is None or not os.path.exists(g):
            return [seed, "no-input", 0, 0, 0, 0, ""]
        gd = json.load(open(g))
    else:
        p = f"{outd}/ont/g{seed}.ofn"
        if not os.path.exists(p):
            subprocess.run(["python3", "-I", gen, str(seed), p], check=True)
        gd = gold(seed, p)
    d = tempfile.mkdtemp(dir=outd)
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    env.update(KM_ROUTE=route, KM_HT_SUBSET_MODEL_CERT=d, KM_HT_INCRBLOCK2_CHECK="1", TMPDIR=d, KM_THREADS="1", RAYON_NUM_THREADS="1")
    env.update(extra)
    acc = rej = cto = 0; reason = ""
    try:
        for attempt in range(4):
            r = subprocess.run(["timeout", "120", km, "classify", "--lines", p], capture_output=True, text=True, env=env)
            if "WouldBlock" not in r.stderr and "Resource temporarily" not in r.stderr and "fork" not in r.stderr:
                break
        ne = sum(1 for l in r.stderr.splitlines() if "not emitted" in l)
        for l in r.stderr.splitlines():
            if "not emitted" in l and not reason: reason = l.split("not emitted: ", 1)[1][:100]
        for f in sorted(os.listdir(d)):
            if not f.endswith(".json"): continue
            fp = os.path.join(d, f)
            rc = check(fp)
            if rc != 0 and rc != 124:
                doc = json.load(open(fp))
                if doc["folds"]:
                    doc["relabel"] = False; own = fp[:-5] + ".own"; json.dump(doc, open(own, "w"))
                    rc2 = check(own)
                    if rc2 == 0: rc = 0
                    elif rc2 == 124: rc = 124
            if rc == 0: acc += 1
            elif rc == 124: cto += 1
            else:
                rej += 1
                shutil.copy(fp, f"{outd}/keep/seed{seed}-{f}")
    finally:
        shutil.rmtree(d, ignore_errors=True)
    cons = None; subs = set(); uns = set()
    for l in r.stdout.splitlines():
        t = l.split("\t")
        if t[0].startswith("CONSISTENT"): cons = t[0].endswith("1")
        elif t[0] == "SUB": subs.add((t[1].lstrip(":"), t[2].lstrip(":")))
        elif t[0] == "UNSAT": uns.add(t[1].lstrip(":"))
    if gd is None: status = "no-gold"
    elif cons is None:
        status = "km-error"; reason = reason or (r.stderr.strip().splitlines() or [""])[-1][:150]
    else:
        status = "ok" if norm(gd["consistent"], [tuple(x) for x in gd["subsumptions"]], gd["unsatisfiable"]) == norm(cons, subs, uns) else "WRONG"
    row = [seed, status, acc, rej, cto, ne, reason]
    print("\t".join(map(str, row)), flush=True)
    return row
with cf.ThreadPoolExecutor(int(os.environ.get("JOBS", "4"))) as ex:
    rows = list(ex.map(one, range(lo, hi + 1)))
from collections import Counter
print("SUMMARY", Counter(r[1] for r in rows), "acc", sum(r[2] for r in rows), "rej", sum(r[3] for r in rows),
      "cert-timeout", sum(r[4] for r in rows), "noemit", sum(r[5] for r in rows),
      "seeds-with-rej", sum(1 for r in rows if r[3]), "WRONG-with-rej", sum(1 for r in rows if r[3] and r[1] == "WRONG"))
