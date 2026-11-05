"""List the pool rows that are not ok.

usage: python3 -I nonok_list.py POOLS_DIR LIST_OUT [SUMMARY_OUT]

POOLS_DIR holds NAME.tsv files written by pools.sh (file, route, verdict, ...).
LIST_OUT gets one `NAME<TAB>file` row per seed that is not ok on some route
(the input of `pools.sh BIN LABEL LIST`, which reruns those seeds with the
base binary). SUMMARY_OUT gets the per-pool, per-route verdict counts.
"""
import collections
import glob
import os
import sys

pools_dir, list_out = sys.argv[1], sys.argv[2]
summary_out = sys.argv[3] if len(sys.argv) > 3 else None
rows = []
summary = []
for path in sorted(glob.glob(os.path.join(pools_dir, '*.tsv'))):
    name = os.path.basename(path)[:-4]
    count = collections.Counter()
    seen = set()
    for line in open(path):
        parts = line.rstrip('\n').split('\t')
        if len(parts) < 3:
            continue
        f, route, verdict = parts[:3]
        count[(route, verdict)] += 1
        if verdict != 'ok' and f not in seen:
            seen.add(f)
            rows.append((name, f))
    summary.append('%-48s %s' % (name, ' '.join('%s/%s=%d' % (r, v, n) for (r, v), n in sorted(count.items()))))
with open(list_out, 'w') as out:
    for name, f in rows:
        out.write('%s\t%s\n' % (name, f))
text = '\n'.join(summary) + '\n%d seeds not ok on some route\n' % len(rows)
if summary_out:
    open(summary_out, 'w').write(text)
print(text)
