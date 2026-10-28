import json, subprocess, sys, os, glob, concurrent.futures as cf
S = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
km, famdir = sys.argv[1], sys.argv[2]
routes = sys.argv[3].split(",") if len(sys.argv) > 3 else ["auto"]
import re
def expected(name, f=None):
    e = expected_full(name.split("__")[0])
    if f is None: return e
    present = set(re.findall(r"Declaration\(Class\(:(\w+)\)\)", open(f).read()))
    return {"unsatisfiable": [u for u in e["unsatisfiable"] if u in present],
            "subsumptions": [s for s in e["subsumptions"] if s[0] in present and s[1] in present]}
def expected_full(name):
    if name.startswith("E_"): return json.load(open(f"{S}/probe/expect_E.json"))
    if name.startswith("U_"): return json.load(open(f"{S}/probe/expect_U.json"))
    if name.startswith("bottom"): return json.load(open(f"{S}/probe/expect_bottom.json"))
    return json.load(open(f"{S}/probe/hermit/{name}.json"))
def run(f, route):
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    if route != "auto": env["KM_ROUTE"] = route
    try:
        p = subprocess.run(["timeout", "40", km, "classify", "--lines", f], capture_output=True, text=True, env=env)
    except Exception as e:
        return ("ERR", str(e))
    if p.returncode != 0: return ("ERR", f"rc={p.returncode} " + p.stderr.strip().splitlines()[-1][:120] if p.stderr.strip() else f"rc={p.returncode}")
    uns, subs = set(), set()
    for l in p.stdout.splitlines():
        t = l.split("\t")
        if t[0] == "UNSAT": uns.add(t[1].lstrip(":"))
        elif t[0] == "SUB": subs.add((t[1].lstrip(":"), t[2].lstrip(":")))
    return ("OK", uns, subs)
jobs = []
with cf.ThreadPoolExecutor(12) as ex:
    for f in sorted(glob.glob(famdir + "/*.ofn")):
        for r in routes: jobs.append((f, r, ex.submit(run, f, r)))
    for f, r, fut in jobs:
        name = os.path.basename(f)[:-4]; e = expected(name, f); res = fut.result()
        if res[0] != "OK": print(f"{name:28s} {r:24s} {res[0]} {res[1]}"); continue
        _, uns, subs = res
        eu = set(e["unsatisfiable"]); es = set(map(tuple, e["subsumptions"]))
        subs = {s for s in subs if s[0] not in uns and s[1] not in uns and "owl:" not in s[0]+s[1] and s[0] != s[1]}
        if uns == eu and subs == es: print(f"{name:28s} {r:24s} CORRECT"); continue
        print(f"{name:28s} {r:24s} WRONG missing_unsat={sorted(eu-uns)} extra_unsat={sorted(uns-eu)} missing_sub={sorted(es-subs)[:6]}{'...' if len(es-subs)>6 else ''}({len(es-subs)}) extra_sub={sorted(subs-es)[:6]}({len(subs-es)})")
