#!/usr/bin/env python3
"""Which roles never occur in a clause head, and what do their body clauses cost?

A role that occurs in no head is unconstrained from below: setting R^I = empty
satisfies every clause that mentions R only in its body, so all such clauses can
be deleted without changing any entailment over concept names.
"""
import json
import sys
from collections import Counter, defaultdict

path = sys.argv[1] if len(sys.argv) > 1 else "/tmp/1194.clauses.json"
clauses = json.load(open(path))["clauses"]

head_roles, body_roles = set(), set()
for c in clauses:
    for a in c["head"]:
        if a["kind"] == "role":
            head_roles.add(a["role"])
    for a in c["body"]:
        if a["kind"] == "role":
            body_roles.add(a["role"])

vacuous = body_roles - head_roles
print(f"roles in heads: {len(head_roles)}  in bodies: {len(body_roles)}")
print(f"head-free (vacuous) roles: {len(vacuous)}")
for r in sorted(vacuous):
    print(f"  {r}")

droppable = [c for c in clauses
             if any(a["kind"] == "role" and a["role"] in vacuous for a in c["body"])]
print(f"\nclauses deletable by vacuous-role elimination: {len(droppable)}")
shapes = Counter()
for c in droppable:
    br = [a for a in c["body"] if a["kind"] == "role"]
    bc = [a for a in c["body"] if a["kind"] == "concept"]
    hr = [a for a in c["head"] if a["kind"] == "role"]
    hc = [a for a in c["head"] if a["kind"] == "concept"]
    shapes[f"b{len(c['body'])}c{len(bc)}r{len(br)}/h{len(c['head'])}c{len(hc)}r{len(hr)}"] += 1
for s, n in shapes.most_common():
    print(f"  {n:>8}  {s}")

# How many of those are inverse bridges?
print("\nsample:")
for c in droppable[:6]:
    print("  " + json.dumps(c)[:220])
