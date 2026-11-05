"""Compare two pool runs (diff_run.py rows: file, spec, verdict, seconds, ...).

usage: python3 -I pool_compare.py AFTER_DIR BEFORE_DIR
Prints per pool the verdict counts of both runs and every seed-route whose
verdict differs, then the totals, and writes the differing rows (pool, file,
spec) to AFTER_DIR/differ.tsv for a rerun of the reference binary.
"""
import collections, glob, os, sys
after, before = sys.argv[1:3]
tot = collections.Counter(); diffs = []
for p in sorted(glob.glob(os.path.join(after, '*.tsv'))):
    name = os.path.basename(p)[:-4]
    if name == 'differ':
        continue
    q = os.path.join(before, name + '.tsv')
    def load(f):
        d = {}
        if os.path.exists(f):
            for line in open(f):
                c = line.rstrip('\n').split('\t')
                if len(c) >= 3:
                    d[(c[0], c[1])] = c[2]
        return d
    a, b = load(p), load(q)
    ca = collections.Counter(a.values()); cb = collections.Counter(b.values())
    print(name, 'after', dict(sorted(ca.items())), 'before', dict(sorted(cb.items())))
    for k in sorted(a):
        tot[a[k]] += 1
        if k in b and a[k] != b[k]:
            diffs.append((name, k[0], k[1], b[k], a[k]))
print('total after', dict(sorted(tot.items())))
print('differences', len(diffs))
for d in diffs:
    print('DIFF', d[0], os.path.basename(d[1]), d[2], d[3], '->', d[4])
with open(os.path.join(after, 'differ.tsv'), 'w') as f:
    for d in diffs:
        f.write('%s\t%s\t%s\n' % (d[0], d[1], d[2]))
