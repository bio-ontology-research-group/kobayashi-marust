#!/usr/bin/env python3
"""Audit inverse-role bridges and the positional uses of every role they touch.

Reads the DL-clause JSON payload the frontend emits and reports, per role:
  * how many clauses use it, split by the syntactic position it occupies;
  * which roles form mutual (S = R^-) or one-way bridges.

Position classes (var-only shapes; `f(x)` counted as a functional term):
  nf3_head      A(x) -> R(x, f(x))          existential witness edge
  nf4_body      C(y) & R(x,y) -> D(x)       exists R.C subsumed  (filler on target)
  nf4_body_rev  C(x) & R(x,y) -> D(y)       already reverse-shaped in the source
  domain        R(x,y) -> D(x)              (filler-free, target unconstrained)
  range         R(x,y) -> D(y)
  chain_body    two role atoms in the body
  bridge        R(x,y) -> S(y,x)
  role_head     any other role-atom head
  other         everything else
"""
import json
import sys
from collections import Counter, defaultdict

path = sys.argv[1] if len(sys.argv) > 1 else "/tmp/1194.clauses.json"
with open(path) as fh:
    clauses = json.load(fh)["clauses"]

print(f"clauses: {len(clauses)}")


def term(t):
    k = t["kind"]
    if k == "var":
        return ("v", t["name"])
    if k == "fun":
        return ("f", t["function"])
    return (k, t.get("name") or t.get("individual") or "?")


pos = defaultdict(Counter)          # role -> Counter(position)
bridge_dir = defaultdict(set)       # role -> {roles it implies as inverse}
shape_count = Counter()

for c in clauses:
    body, head = c["body"], c["head"]
    broles = [a for a in body if a["kind"] == "role"]
    bconc = [a for a in body if a["kind"] == "concept"]
    hroles = [a for a in head if a["kind"] == "role"]
    hconc = [a for a in head if a["kind"] == "concept"]

    # inverse bridge: R(x,y) -> S(y,x)
    if (len(body) == 1 and len(head) == 1 and len(broles) == 1 and len(hroles) == 1):
        r, s = broles[0], hroles[0]
        rs, rt = term(r["source"]), term(r["target"])
        ss, st = term(s["source"]), term(s["target"])
        if rs[0] == rt[0] == ss[0] == st[0] == "v" and rs == st and rt == ss and rs != rt:
            bridge_dir[r["role"]].add(s["role"])
            pos[r["role"]]["bridge_body"] += 1
            pos[s["role"]]["bridge_head"] += 1
            continue

    for a in broles + hroles:
        role = a["role"]
        src, tgt = term(a["source"]), term(a["target"])
        in_head = a in hroles
        if len(broles) >= 2 and not in_head:
            pos[role]["chain_body"] += 1
        elif in_head:
            if tgt[0] == "f" or src[0] == "f":
                pos[role]["nf3_head"] += 1
            else:
                pos[role]["role_head"] += 1
        elif len(broles) == 1 and len(hconc) == 1 and not hroles:
            hv = term(hconc[0]["term"])
            fillers = [term(x["term"]) for x in bconc]
            if hv == src and (not fillers or all(f == tgt for f in fillers)):
                pos[role]["nf4_body" if fillers else "domain"] += 1
            elif hv == tgt and (not fillers or all(f == src for f in fillers)):
                pos[role]["nf4_body_rev" if fillers else "range"] += 1
            else:
                pos[role]["other_body"] += 1
        else:
            pos[role]["other_body"] += 1

    shape_count[
        f"b{len(body)}c{len(bconc)}r{len(broles)}/h{len(head)}c{len(hconc)}r{len(hroles)}"
    ] += 1

print("\n=== bridges ===")
mutual, oneway = [], []
for r, ss in sorted(bridge_dir.items()):
    for s in sorted(ss):
        if r in bridge_dir.get(s, ()):
            if r < s:
                mutual.append((r, s))
        else:
            oneway.append((r, s))
print(f"mutual pairs ({len(mutual)}):")
for r, s in mutual:
    print(f"  {r} <-> {s}")
print(f"one-way ({len(oneway)}):")
for r, s in oneway:
    print(f"  {r} -> {s}^-")

print("\n=== positional use of bridge roles ===")
involved = sorted({r for r, s in mutual} | {s for r, s in mutual}
                  | {r for r, s in oneway} | {s for r, s in oneway})
hdr = ["nf3_head", "nf4_body", "nf4_body_rev", "domain", "range",
       "chain_body", "role_head", "other_body", "bridge_body", "bridge_head"]
print(f"{'role':34} " + " ".join(f"{h:>12}" for h in hdr))
for r in involved:
    print(f"{r:34} " + " ".join(f"{pos[r][h]:>12}" for h in hdr))

print("\n=== top roles overall ===")
tot = sorted(((sum(v.values()), k) for k, v in pos.items()), reverse=True)[:15]
for n, r in tot:
    print(f"  {n:>10}  {r}  {dict(pos[r])}")

print("\n=== clause shapes ===")
for s, n in shape_count.most_common(20):
    print(f"  {n:>10}  {s}")
