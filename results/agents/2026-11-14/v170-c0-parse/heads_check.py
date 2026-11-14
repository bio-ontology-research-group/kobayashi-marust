"""Rerun heads.py on every accepted input of the given results files and
check that it completes and agrees with the stored Lean axiom counts.
usage: heads_check.py RESULTS.jsonl..."""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
n = agree = crash = 0
for f in sys.argv[1:]:
    for line in open(f):
        r = json.loads(line)
        if r["lean"]["status"] != "ok":
            continue
        n += 1
        p = subprocess.run(["nice", "python3", "-I", os.path.join(HERE, "heads.py"), r["path"]],
                           capture_output=True, text=True)
        try:
            h = json.loads(p.stdout)
        except Exception:
            crash += 1
            print("crash", r["path"], flush=True)
            continue
        lc = {k: v for k, v in r["axiomCounts"].items() if v}
        if h == lc:
            agree += 1
        else:
            print("differ", r["path"], flush=True)
print(f"heads.py completed on {n - crash} of {n} accepted inputs; counts agree on {agree}")
