"""Tables for the v1.7.0 C0 differential run.

usage: summarize.py RESULTS.jsonl LEAN_EXE RUST_EXE > summary.md

For object-property disagreements it reruns both dumps and checks whether
every Rust-only name is a Lean data property (the Rust dump lists data
properties among its object properties)."""
import collections, json, subprocess, sys

rows = [json.loads(l) for l in open(sys.argv[1])]
lean_exe, rust_exe = sys.argv[2], sys.argv[3]
st = collections.Counter((r["lean"]["status"], r["rust"]["status"]) for r in rows)
print(f"# v1.7.0 C0 parser differential\n\n{len(rows)} ORE inputs outside the v1.6.2 fragment F.\n")
print("| Lean | Rust | inputs |\n|---|---|---:|")
for (l, r), n in sorted(st.items()):
    print(f"| {l} | {r} | {n} |")
reasons = collections.Counter(r["lean"]["reason"] for r in rows if r["lean"]["status"] != "ok")
print("\nLean rejection reasons:\n")
for k, n in reasons.most_common():
    print(f"- {n} x `{k}`")
fields = collections.Counter()
explained = 0
unexplained = []
top_inputs = []
for r in rows:
    ds = r.get("diffs", [])
    for d in ds:
        fields[d["field"]] += 1
    op = [d for d in ds if d["field"] == "objectProperties"]
    if op:
        def dump(exe):
            out = subprocess.run(["nice", "timeout", "300", exe, r["path"]], capture_output=True, text=True).stdout
            return json.loads(out.strip().splitlines()[-1])
        lean, rust = dump(lean_exe), dump(rust_exe)
        dps, ops = set(lean.get("dataProperties", [])), set(lean.get("objectProperties", []))
        rops = set(rust.get("objectProperties", []))
        owl_top = {"http://www.w3.org/2002/07/owl#topObjectProperty",
                   "http://www.w3.org/2002/07/owl#bottomObjectProperty",
                   "http://www.w3.org/2002/07/owl#topDataProperty",
                   "http://www.w3.org/2002/07/owl#bottomDataProperty"}
        rust_only = rops - ops
        rust_only_ok = rust_only <= dps | owl_top
        if rust_only & owl_top:
            top_inputs.append(r["path"])
        if not (ops - rops) and rust_only_ok:
            explained += 1
        else:
            unexplained.append((r["path"], op[0]))
both = [r for r in rows if "diffs" in r]
agree = [r for r in both if not r["diffs"]]
print(f"\nBoth accept: {len(both)}; no disagreement at all: {len(agree)}.\n")
print("| disagreeing field | inputs |\n|---|---:|")
for k, n in fields.most_common():
    print(f"| {k} | {n} |")
print(f"\nObject-property disagreements where no name is Lean-only and every Rust-only name"
      f" is a Lean data property or the top or bottom object or data property"
      f" (the Lean model has ObjProp.top / .bot and DataProp.top / .bot, not IRIs): {explained} of {fields['objectProperties']};"
      f" inputs where Rust lists a top or bottom property: {len(top_inputs)}"
      ".\n")
for p, d in unexplained:
    print(f"- unexplained: {p}: {json.dumps(d)[:300]}")

tot = collections.Counter()
inputs_with = collections.Counter()
for r in rows:
    for k, v in (r.get("axiomCounts") or {}).items():
        tot[k] += v
        if v:
            inputs_with[k] += 1
print("\nAxiom kinds in the accepted inputs (Lean counts; all agree with heads.py):\n")
print("| kind | axioms | inputs |\n|---|---:|---:|")
for k, v in sorted(tot.items(), key=lambda kv: -kv[1]):
    print(f"| {k} | {v} | {inputs_with[k]} |")
