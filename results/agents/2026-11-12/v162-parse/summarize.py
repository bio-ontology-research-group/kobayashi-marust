"""Summarise OUTDIR/results.jsonl of differential.py into the hand-back tables.

usage: summarize.py RESULTS.jsonl
"""
import collections, json, sys

rows = [json.loads(l) for l in open(sys.argv[1])]
F = [r for r in rows if r["inF"]]
N = [r for r in rows if not r["inF"]]

print(f"## F inputs ({len(F)})\n")
acc = [r for r in F if r["lean"]["status"] == "ok"]
agree = [r for r in acc if r["rust"]["status"] == "ok" and not r.get("diffs")]
dis = [r for r in acc if r["rust"]["status"] == "ok" and r.get("diffs")]
rust_bad = [r for r in acc if r["rust"]["status"] != "ok"]
print("| outcome | inputs |\n|---|---:|")
print(f"| Lean accepts | {len(acc)} |")
print(f"| Lean accepts, Rust agrees (names and counts) | {len(agree)} |")
print(f"| Lean accepts, Rust disagrees | {len(dis)} |")
print(f"| Lean accepts, Rust rejects or crashes | {len(rust_bad)} |")
print(f"| Lean rejects | {len(F) - len(acc)} |")
for r in dis:
    print(f"\n- disagreement {r['path']}: {json.dumps(r['diffs'])[:600]}")
for r in rust_bad:
    print(f"\n- Rust {r['rust']['status']} {r['path']}: {r['rust']['reason']}")
for r in F:
    if r["lean"]["status"] != "ok":
        print(f"\n- Lean {r['lean']['status']} {r['path']}: {r['lean']['reason']}")
extra = collections.Counter()
for r in acc:
    e = (r["rust"].get("extra") or {})
    for k in ("collisions", "ambiguous", "undeclaredPrefix"):
        if e.get(k):
            extra[k] += 1
    if e.get("iriPrefixCheck") not in (None, "ok"):
        extra["iriPrefixCheck failed"] += 1
    if e.get("dropped"):
        extra["Rust dropped source axioms"] += 1
print("\nRust registry flags on accepted F inputs:", dict(extra) or "none")

print("\n### Five largest F inputs\n")
print("| input | MB | axioms | Lean wall s | Lean parse (stderr) | Lean max RSS MB | Rust wall s | Rust max RSS MB |\n|---|---:|---:|---:|---|---:|---:|---:|")
for r in sorted(F, key=lambda r: -r["size"])[:5]:
    n = sum((r.get("axiomCounts") or {}).values())
    print(f"| {r['path'].split('/')[-1]} | {r['size']/1e6:.0f} | {n} | {r['lean']['wall']:.1f} | {r['lean']['times']} | "
          f"{(r['lean']['maxrssKiB'] or 0)/1024:.0f} | {r['rust']['wall']:.1f} | {(r['rust']['maxrssKiB'] or 0)/1024:.0f} |")
print(f"\nLean wall time over all F inputs: {sum(r['lean']['wall'] for r in F):.0f} s; max {max(r['lean']['wall'] for r in F):.1f} s")

if N:
    print(f"\n## Non-F inputs ({len(N)})\n")
    st = collections.Counter(r["lean"]["status"] for r in N)
    print("Lean status:", dict(st))
    reasons = collections.Counter(r["lean"]["reason"] for r in N if r["lean"]["status"] == "rejected")
    cat = collections.Counter()
    for k, v in reasons.items():
        key = k
        if k.startswith("syntax error: undeclared prefix"):
            key = "syntax error: undeclared prefix"
        elif k.startswith("syntax error: ") and " is not an IRI" in k:
            key = "syntax error: bare word is not an IRI"
        elif k.startswith("out of fragment: anonymous individual"):
            key = "out of fragment: anonymous individual"
        cat[key] += v
    print("\n| rejection reason | inputs |\n|---|---:|")
    for k, v in cat.most_common():
        print(f"| {k} | {v} |")
    for r in N:
        if r["lean"]["status"] != "rejected":
            print(f"\n- non-F input with Lean status {r['lean']['status']}: {r['path']} ({r['lean']['reason']})")
    rs = collections.Counter(r["rust"]["status"] for r in N)
    print("\nRust status on non-F inputs:", dict(rs))
    for r in N:
        if r["rust"]["status"] in ("panic", "crash"):
            print(f"- Rust {r['rust']['status']} {r['path']}: {r['rust']['reason']}")
