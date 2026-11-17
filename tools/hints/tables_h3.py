#!/usr/bin/env python3
"""Markdown tables for the H3 note from an aggregate_h3.py TSV:
tables_h3.py TABLE.tsv > tables.md

Outcome classes per input:
  no rows      km failed, km says inconsistent, or the route's dump failed
  model        the producer built self-checked models covering every negative row (unchecked)
  confirmed    the proved checker certified every negative row in this run
  too slow     the checker timed out or ran out of memory on a model
"""
import sys
from collections import defaultdict

rows = []
with open(sys.argv[1]) as f:
    head = f.readline().rstrip('\n').split('\t')
    for line in f:
        w = line.rstrip('\n').split('\t')
        rows.append(dict(zip(head, w)))


def num(r, k):
    try:
        return int(float(r.get(k) or 0))
    except ValueError:
        return 0


def cls(r):
    st = r['status']
    if st in ('km-failed', 'km-inconsistent', 'dump-failed', 'driver-timeout', 'producer-failed', 'producer-memout'):
        return st
    return 'ok'


def table(key):
    agg = defaultdict(lambda: defaultdict(int))
    for r in rows:
        k = r[key] if key else 'all'
        a = agg[k]
        a['inputs'] += 1
        c = cls(r)
        if c != 'ok':
            a['no rows'] += 1
            a[c] += 1
            continue
        model_full = r['status'] == 'model-full'
        conf = r.get('status_checked') == 'certified-full'
        slow = any(x in (r.get('chk_results') or '') for x in ('timeout', 'out of memory')) or 'over the checker budget' in (r.get('chk_results') or '')
        a['model full'] += model_full
        a['confirmed full'] += conf
        a['model full, checker too slow'] += model_full and slow and not conf
        a['partial'] += r.get('status_checked') == 'certified-partial' or (not conf and not (model_full and slow) and r['status'] == 'model-partial')
        a['none'] += r['status'] == 'model-none' or (r.get('status_checked') == 'certified-none' and not (model_full and slow) and r['status'] != 'model-partial')
        a['rows'] += num(r, 'rows')
        a['unchecked'] += num(r, 'unchecked')
        a['certified'] += num(r, 'cert_rows')
    cols = ['inputs', 'confirmed full', 'model full, checker too slow', 'partial', 'none', 'no rows',
            'km-inconsistent', 'km-failed', 'dump-failed', 'model full', 'rows', 'unchecked', 'certified']
    out = ['| %s | %s |' % (key or '', ' | '.join(cols)), '|---|' + '---:|' * len(cols)]
    for k in sorted(agg):
        a = agg[k]
        out.append('| %s | %s |' % (k, ' | '.join('{:,}'.format(a[c]) for c in cols)))
    return '\n'.join(out)


print(table(None))
print()
print(table('size'))
print()
print(table('fragment'))
