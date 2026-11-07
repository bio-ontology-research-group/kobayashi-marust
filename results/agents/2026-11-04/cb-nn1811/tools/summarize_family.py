"""Summarise the family runs of fam_all.sh.

usage: python3 -I summarize_family.py NEW.tsv BASE.tsv

Per route: verdict counts of the new binary (all runs) and of the base (one run),
then every seed on which the new binary has a WRONG or NOANSWER row, every
seed that times out in some new run (with the base verdict of that seed) and
the seeds whose three runs differ.
"""
import collections
import sys


def rows(path):
    out = collections.defaultdict(list)
    for line in open(path):
        f, spec, run, verdict, secs, detail = line.rstrip('\n').split('\t')
        out[(f.split('/')[-1].replace('.ofn', ''), spec)].append((int(run), verdict, float(secs), detail))
    return out


new, base = rows(sys.argv[1]), rows(sys.argv[2])
routes = sorted({spec for _, spec in new})
for spec in routes:
    cn = collections.Counter(v for (s, sp), r in new.items() if sp == spec for _, v, _, _ in r)
    cb = collections.Counter(v for (s, sp), r in base.items() if sp == spec for _, v, _, _ in r)
    seeds_n = len({s for (s, sp) in new if sp == spec})
    seeds_b = len({s for (s, sp) in base if sp == spec})
    print('%-10s new  (%d seeds, %d runs): %s' % (spec, seeds_n, sum(cn.values()), dict(sorted(cn.items()))))
    print('%-10s base (%d seeds, %d runs): %s' % (spec, seeds_b, sum(cb.values()), dict(sorted(cb.items()))))
print()
for spec in routes:
    bad = sorted((s, r) for (s, sp), r in new.items() if sp == spec and any(v in ('WRONG', 'NOANSWER', 'ERR') for _, v, _, _ in r))
    print('%s: seeds with a WRONG/NOANSWER/ERR row in the new binary: %d' % (spec, len(bad)))
    for s, r in bad:
        b = base.get((s, spec), [])
        print('  %s new=%s base=%s %s' % (s, ','.join(v for _, v, _, _ in sorted(r)), ','.join(v for _, v, _, _ in sorted(b)),
                                         next((d for _, v, _, d in r if d), '')[:100]))
    to = sorted((s, r) for (s, sp), r in new.items() if sp == spec and any(v == 'TIMEOUT' for _, v, _, _ in r))
    print('%s: seeds with a TIMEOUT in some new run: %d' % (spec, len(to)))
    for s, r in to:
        b = base.get((s, spec), [])
        print('  %s new=%s base=%s' % (s, ','.join(v for _, v, _, _ in sorted(r)), ','.join(v for _, v, _, _ in sorted(b))))
    mixed = sorted(s for (s, sp), r in new.items() if sp == spec and len({v for _, v, _, _ in r}) > 1)
    print('%s: seeds whose runs differ: %d %s' % (spec, len(mixed), mixed[:20]))
    newly = sorted(s for (s, sp), r in new.items() if sp == spec and any(v != 'ok' for _, v, _, _ in r)
                   and base.get((s, sp)) and all(v == 'ok' for _, v, _, _ in base[(s, sp)]))
    print('%s: seeds not ok in the new binary but ok in the base: %d %s' % (spec, len(newly), newly[:20]))
    print()
