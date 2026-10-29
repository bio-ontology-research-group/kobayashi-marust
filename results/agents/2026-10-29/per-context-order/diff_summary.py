"""Summarise a context-regime differential run against its reference rerun.

usage: python3 -I diff_summary.py CTX.tsv [REF.tsv]

CTX.tsv: diff_run.py output under the context regime (auto-selected).
REF.tsv: diff_run.py output with KM_NO_SEQ_ORDER=1 on the files that were not
`ok` under the context regime. Prints verdict counts per route and, for every
(file, route) that was not `ok`, the reference verdict next to it.
"""
import collections
import os
import sys


def load(path):
    rows = {}
    if path and os.path.exists(path):
        for line in open(path):
            t = line.rstrip('\n').split('\t')
            if len(t) >= 4:
                rows[(os.path.basename(t[0]), t[1])] = (t[2], t[3])
    return rows


ctx = load(sys.argv[1])
ref = load(sys.argv[2] if len(sys.argv) > 2 else None)
files = {f for f, _ in ctx}
print('files', len(files), 'runs', len(ctx))
count = collections.Counter((r, v[0]) for (f, r), v in ctx.items())
for route in sorted({r for _, r in ctx}):
    print(route, ' '.join(f'{v}={count[(route, v)]}' for v in ('ok', 'WRONG', 'TIMEOUT', 'ERR', 'NOGOLD')
                         if count[(route, v)]))
pairs = collections.Counter()
for key, (verdict, _) in sorted(ctx.items()):
    if verdict == 'ok':
        continue
    rv = ref.get(key, ('not-run',))[0]
    pairs[(verdict, rv)] += 1
    if rv == 'ok' or verdict == 'WRONG':
        print('  ', key[0], key[1], 'ctx', verdict, 'ref', rv)
print('non-ok under ctx, by reference verdict:', dict(pairs))
