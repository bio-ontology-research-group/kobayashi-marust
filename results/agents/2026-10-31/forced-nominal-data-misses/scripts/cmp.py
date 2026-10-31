"""usage: python3 -I cmp.py NEW.tsv OLD.tsv; verdict transitions per (file, route) of two diff_run.py tables."""
import csv, sys
from collections import Counter
def load(p):
    d = {}
    for r in csv.reader(open(p), delimiter='\t'):
        if len(r) >= 3:
            d[(r[0].split('/')[-1], r[1])] = r[2]
    return d
new, old = load(sys.argv[1]), load(sys.argv[2])
print('old->new', dict(Counter((old.get(k, 'NA'), v) for k, v in new.items())))
for k, v in sorted(new.items()):
    if old.get(k) != v:
        print(' ', k[0], k[1], old.get(k, 'NA'), '->', v)
