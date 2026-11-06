"""Summarise the sibling family runs (fam_run.py rows).

usage: python3 -I fam_summary.py NEW1.tsv BASE.tsv NEW23.tsv...

Prints, per route, the verdict counts of the new binary over all its runs
and of the base over its single run, every seed-route that is not ok on the
new binary in some run (with its base verdict), every seed-route that is ok
on the base and not ok on the new binary, and every seed-route that is WRONG
on the base and ok in every new run.
"""
import collections
import os
import sys


def load(path):
    rows = []
    for line in open(path):
        f = line.rstrip('\n').split('\t')
        if len(f) < 5:
            continue
        rows.append((os.path.basename(f[0]), f[1], f[3], f[5] if len(f) > 5 else ''))
    return rows


new = load(sys.argv[1])
for p in sys.argv[3:]:
    new += load(p)
base = load(sys.argv[2])
bv = {(s, r): v for s, r, v, _ in base}
nv = collections.defaultdict(list)
detail = {}
for s, r, v, d in new:
    nv[(s, r)].append(v)
    if v != 'ok':
        detail[(s, r)] = d
for route in ('auto', 'ht_bridge'):
    c = collections.Counter(v for (s, r), vs in nv.items() if r == route for v in vs)
    b = collections.Counter(v for (s, r), v in bv.items() if r == route)
    print(f'{route}: new {dict(sorted(c.items()))} | base {dict(sorted(b.items()))}')
print('\nnot ok on the new binary in some run (verdicts of the new runs; base):')
for key in sorted(nv):
    vs = nv[key]
    if any(v not in ('ok', 'NOGOLD') for v in vs):
        print(f'  {key[0]} {key[1]}: new {vs} base {bv.get(key)} {detail.get(key, "")[:160]}')
print('\nok on the base, not ok on the new binary in some run:')
for key in sorted(nv):
    if bv.get(key) == 'ok' and any(v != 'ok' for v in nv[key]):
        print(f'  {key[0]} {key[1]}: new {nv[key]}')
fixed = [k for k in nv if bv.get(k) == 'WRONG' and all(v == 'ok' for v in nv[k])]
print(f'\nWRONG on the base, ok in every new run: {len(fixed)} seed-routes, '
      f'{len({k[0] for k in fixed})} seeds')
wrong_base = [k for k, v in bv.items() if v == 'WRONG']
print(f'WRONG on the base: {len(wrong_base)} seed-routes, {len({k[0] for k in wrong_base})} seeds')
