"""Compare two diff_run.py result files per (seed, route).
usage: python3 -I cmp_pools.py BEFORE.tsv AFTER.tsv
Prints per-route verdict counts for both, the transition table, every seed
whose verdict changed, and every WRONG row of AFTER."""
import collections, csv, sys

def load(p):
    d = {}
    for r in csv.reader(open(p), delimiter='\t'):
        if len(r) >= 3:
            d[(r[0].split('/')[-1], r[1])] = r
    return d

a, b = load(sys.argv[1]), load(sys.argv[2])
for name, d in (('before', a), ('after', b)):
    c = collections.Counter((k[1], v[2]) for k, v in d.items())
    print(name, ' '.join(f'{r}:{v}={n}' for (r, v), n in sorted(c.items())))
t = collections.Counter((a[k][2], b[k][2] if k in b else 'MISSING') for k in a)
print('transitions', dict(t))
for k in sorted(a):
    va, vb = a[k][2], b[k][2] if k in b else 'MISSING'
    if va != vb:
        print('changed', k[0], k[1], va, '->', vb)
for k in sorted(b):
    if b[k][2] == 'WRONG':
        print('wrong', k[0], k[1], 'miss_sub', b[k][4], 'extra_sub', b[k][5], 'miss_uns', b[k][6], 'extra_uns', b[k][7], 'cons', b[k][8])
