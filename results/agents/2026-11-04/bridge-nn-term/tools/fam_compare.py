"""Compare family runs per seed-route: NEW against BASE and 48a.

usage: python3 -I fam_compare.py NEW.tsv BASE.tsv N48.tsv
Rows of fam_run.py (file, spec, run, verdict, seconds, detail). A seed-route
is summarised by its verdict multiset. Prints the counts per binary and
route, then every seed-route that is not ok in all NEW runs, with the BASE
and 48a verdicts and times.
"""
import collections
import os
import sys

def load(p):
    d = collections.defaultdict(list)
    for line in open(p):
        f = line.rstrip('\n').split('\t')
        if len(f) < 5:
            continue
        stem = os.path.splitext(os.path.basename(f[0]))[0]
        d[(stem, f[1])].append((f[3], float(f[4]), f[5] if len(f) > 5 else ''))
    return d

new, base, n48 = (load(p) for p in sys.argv[1:4])
for name, d in (('new', new), ('base', base), ('48a', n48)):
    for spec in ('auto', 'ht_bridge'):
        c = collections.Counter(v for (s, sp), rows in d.items() if sp == spec for v, _, _ in rows)
        print(name, spec, dict(sorted(c.items())))
def fmt(rows):
    return ' '.join('%s:%.1f' % (v, t) for v, t, _ in rows) if rows else '-'
print()
print('seed\troute\tnew\tbase\t48a')
for key in sorted(new):
    rows = new[key]
    if all(v in ('ok', 'NOGOLD') for v, _, _ in rows):
        continue
    print('%s\t%s\t%s\t%s\t%s' % (key[0], key[1], fmt(rows), fmt(base.get(key, [])), fmt(n48.get(key, []))))
# wrong on new but right on base or 48a
print()
for key in sorted(new):
    if any(v == 'WRONG' for v, _, _ in new[key]):
        b = [v for v, _, _ in base.get(key, [])]; n = [v for v, _, _ in n48.get(key, [])]
        print('WRONG-NEW', key[0], key[1], 'base', b, '48a', n, new[key][0][2][:200])
