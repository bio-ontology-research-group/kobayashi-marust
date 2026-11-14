"""Regression on the v1.6.2 fragment-F inputs: the C0 km-owl-parse must give
the same accept/reject, class and object-property names and the 12 old
axiom counts as the v1.6.3 km-owl-parse.

usage: regress_f.py INPUTS.tsv OLD_EXE NEW_EXE OUT.jsonl"""
import csv, json, subprocess, sys
OLD12 = ["subClassOf", "equivalentClasses", "disjointClasses", "domain", "range",
         "subObjectPropertyOf", "equivalentObjectProperties", "inverseObjectProperties",
         "transitive", "symmetric", "declareClass", "declareObjectProperty"]
inputs, old_exe, new_exe, out_path = sys.argv[1:5]
out = open(out_path, "w")
n = same = 0
for r in csv.DictReader(open(inputs), delimiter="\t"):
    if r["inF"] != "1":
        continue
    def dump(exe):
        p = subprocess.run(["nice", "timeout", "300", exe, r["path"]], capture_output=True, text=True)
        try:
            return json.loads(p.stdout.strip().splitlines()[-1])
        except Exception:
            return {"status": "crash"}
    a, b = dump(old_exe), dump(new_exe)
    key = lambda d: (d.get("status"), sorted(d.get("classes", [])), sorted(d.get("objectProperties", [])),
                     [d.get("axiomCounts", {}).get(k, 0) for k in OLD12])
    ok = key(a) == key(b)
    n += 1; same += ok
    out.write(json.dumps({"path": r["path"], "same": ok, "old": a.get("status"), "new": b.get("status")}) + "\n")
print(f"{same}/{n} fragment-F inputs give identical status, names and old axiom counts")
