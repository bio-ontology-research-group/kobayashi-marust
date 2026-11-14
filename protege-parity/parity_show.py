#!/usr/bin/env python3
"""Print both reasoners' answers for the calls of a ParityRun result that match a text.

  parity_show.py <result.json> <text in the call id> [--limit N]

Use it to reproduce an entry of PARITY.md: the call id names the OWLReasoner method and its arguments.
"""
import argparse, json

ap = argparse.ArgumentParser()
ap.add_argument("result")
ap.add_argument("text")
ap.add_argument("--limit", type=int, default=5)
a = ap.parse_args()
r = json.load(open(a.result))
n = 0
for c in r["calls"]:
    if a.text in c["id"]:
        print(c["id"], "->", c.get("verdict"))
        for who in ("hermit", "km"):
            x = c.get(who, {})
            body = json.dumps(x.get("ans")) if x.get("status") == "ok" else f"{x.get('status')} {x.get('exc', '')} {x.get('msg', '')}"
            print(f"  {who:7s} {body[:600]}")
        n += 1
        if n >= a.limit:
            break
