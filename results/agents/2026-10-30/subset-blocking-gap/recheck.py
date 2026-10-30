# usage: python3 -I recheck.py CHECKER KEEPDIR
# Re-runs the Lean checker on every certificate drive.py classified as
# rejected (relabel, then own-label), retrying spawn failures, and reports
# per file: accepted / rejected (checker printed "rejected") / timeout / error.
import subprocess, sys, os, json, collections
checker, keep = sys.argv[1], sys.argv[2]
def run(fp):
    for _ in range(5):
        try:
            r = subprocess.run(["timeout", "300", checker, fp], capture_output=True, text=True)
        except OSError:
            continue
        if r.returncode == 124: return "timeout"
        if "accepted" in r.stdout: return "accepted"
        if "rejected" in r.stdout or "reject" in r.stderr.lower(): return "rejected"
    return "error"
res = collections.Counter(); rows = []
for f in sorted(os.listdir(keep)):
    if not f.endswith(".json") or f.endswith(".own.json"): continue
    fp = os.path.join(keep, f)
    v = run(fp)
    if v == "rejected":
        doc = json.load(open(fp))
        if doc["folds"]:
            doc["relabel"] = False; own = fp[:-5] + ".own.json"; json.dump(doc, open(own, "w"))
            if run(own) == "accepted": v = "accepted-own"
    res[v] += 1; rows.append((f, v)); print(f, v, flush=True)
print("RECHECK", dict(res))
