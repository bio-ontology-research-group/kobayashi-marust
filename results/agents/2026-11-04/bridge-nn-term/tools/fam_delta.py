"""Seed-route deltas of a family run against base (1 run) and 48a (3 runs).

usage: python3 -I fam_delta.py NEW.tsv BASE.tsv N48.tsv
"""
import collections, os, sys
def load(p):
    d = collections.defaultdict(list)
    for line in open(p):
        f = line.rstrip('\n').split('\t')
        if len(f) >= 5:
            d[(os.path.splitext(os.path.basename(f[0]))[0], f[1])].append(f[3])
    return d
new, base, n48 = (load(p) for p in sys.argv[1:4])
def allok(v): return v and all(x == 'ok' for x in v)
bw = [k for k, v in base.items() if 'WRONG' in v]
rec = [k for k in bw if allok(new.get(k))]
rec48 = [k for k in bw if allok(n48.get(k))]
print('base WRONG seed-routes', len(bw), 'ok in all new runs', len(rec), 'ok in all 48a runs', len(rec48))
print('recovered on 48a but not on new:', sorted(set(rec48) - set(rec)))
print('recovered on new but not on 48a:', sorted(set(rec) - set(rec48)))
lost = [k for k, v in base.items() if allok(v) and not allok(new.get(k))]
print('ok on base, not ok in every new run:', [(k, new[k], n48.get(k)) for k in sorted(lost)])
lost48 = [k for k, v in n48.items() if allok(v) and not allok(new.get(k))]
print('ok in all 48a runs, not in every new run:', [(k, new[k]) for k in sorted(lost48)])
gain48 = [k for k, v in new.items() if allok(v) and not allok(n48.get(k))]
print('ok in all new runs, not in every 48a run:', len(gain48), sorted(gain48))
