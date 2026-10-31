# usage: python3 -I module_timing.py KM
# Item 2: the count=1 negative case of
# common_data_core_prefers_plain_module_before_full_common_path. Times the
# replace revisions (module reuse) against a fresh session init of the same
# source (full classification), 5 repetitions each, KM_THREADS=1.
import json, subprocess, sys, time, os
km = sys.argv[1]
HEADER = "Prefix(:=<http://example.org/m#>)\nOntology(<http://example.org/m>\n"
def ont(axioms):
    t = HEADER + "".join(f"Declaration(Class(:{n}))\n" for n in "ABCDEFGHK")
    t += "Declaration(ObjectProperty(:r))\nDeclaration(NamedIndividual(:a))\n"
    return t + "".join(a + "\n" for a in axioms) + ")\n"
ax = ["Declaration(DataProperty(:p))", "DataPropertyRange(:p xsd:string)", "SubClassOf(:E :F)", "SubClassOf(:G :H)",
      'NegativeDataPropertyAssertion(:p :a "0")']
old = ont(ax); ax.append("SubClassOf(:A :B)"); addition = ont(ax)
ax.remove("SubClassOf(:E :F)"); ax.append("SubClassOf(:B :C)"); mixed = ont(ax)
env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}; env["KM_THREADS"] = "1"
def run(revs):
    inp = "".join(json.dumps({"op": "init" if i == 0 else "replace", "functional_syntax": s}) + "\n" for i, s in enumerate(revs))
    t = time.time()
    r = subprocess.run([km, "incremental-source"], input=inp, capture_output=True, text=True, env=env)
    wall = time.time() - t
    return [json.loads(l) for l in r.stdout.splitlines()], wall
for rep in range(5):
    rows, w = run([old, addition, mixed])
    f1, w1 = run([addition]); f2, w2 = run([mixed])
    print(rep, "reuse", [(r["receipt"]["strategy"], round(r["receipt"]["seconds"] * 1e3, 2)) for r in rows[1:]],
          "fresh-init", [(f[0]["receipt"]["strategy"], round(f[0]["receipt"]["seconds"] * 1e3, 2)) for f in (f1, f2)])
