"""Compare the context-regime ORE timing run with the v1.5.4 baselines.

usage: python3 -I ore_compare.py BASELINE.tsv CTX_TIMES.tsv CTX_OUT REF_TIMES.tsv REF_OUT OUT.tsv

BASELINE.tsv: results/agents/2026-10-28/cost/seq-order-gate-times.tsv
(h7 = v1.5.4 before the fix, plain Sequoia auto-selected in nominal mode;
sq1 = v1.5.4, unordered regime in nominal mode). CTX/REF: ore_time.sh output
of this run (ctx = context regime auto-selected; ref = same binary with
KM_NO_SEQ_ORDER=1, the unordered regime). A run counts as answered when
rc == 0; taxonomies are compared on the sorted SUB/UNSAT/CONSISTENT lines.
"""
import gzip
import os
import sys

base_path, ctx_path, ctx_out, ref_path, ref_out, out_path = sys.argv[1:7]


def load(path):
    rows = {}
    if not os.path.exists(path):
        return rows
    for line in open(path):
        t = line.rstrip('\n').split('\t')
        if len(t) < 4:
            continue
        rows.setdefault(t[0], {})[t[1]] = (int(t[2]), float(t[3]))
    return rows


def sig(directory, name):
    p = os.path.join(directory, name + '.sig.gz')
    if not os.path.exists(p):
        return None
    with gzip.open(p, 'rt') as f:
        return f.read()


base = load(base_path)
ctx = load(ctx_path)
ref = load(ref_path)
names = sorted(ctx)
cap = 300.0
tot = {'h7': 0.0, 'sq1': 0.0, 'ctx': 0.0, 'ref': 0.0}
timeouts = {k: [] for k in tot}
diffs = []
with open(out_path, 'w') as out:
    out.write('file\th7_s\tsq1_s\tctx_s\tref_s\tctx_rc\tref_rc\ttaxonomy\n')
    for n in names:
        h7 = base.get(n, {}).get('h7')
        sq1 = base.get(n, {}).get('sq1')
        c = ctx[n].get('ctx')
        r = ref.get(n, {}).get('ref')
        vals = {'h7': h7, 'sq1': sq1, 'ctx': c, 'ref': r}
        for k, v in vals.items():
            if v is None:
                continue
            tot[k] += min(v[1], cap) if v[0] == 0 else cap
            if v[0] != 0:
                timeouts[k].append(n)
        tax = 'na'
        if c and r and c[0] == 0 and r[0] == 0:
            a, b = sig(ctx_out, n), sig(ref_out, n)
            tax = 'same' if a == b else 'DIFF'
            if a != b:
                diffs.append(n)
        f = lambda v: '' if v is None else (f'{v[1]:.2f}' if v[0] == 0 else f'TIMEOUT(rc={v[0]})')
        out.write(f'{n}\t{f(h7)}\t{f(sq1)}\t{f(c)}\t{f(r)}\t'
                  f'{"" if c is None else c[0]}\t{"" if r is None else r[0]}\t{tax}\n')
print('files', len(names))
raw = {k: sum(v[1] for n in names for v in [{'h7': base.get(n, {}).get('h7'), 'sq1': base.get(n, {}).get('sq1'),
                                              'ctx': ctx[n].get('ctx'), 'ref': ref.get(n, {}).get('ref')}[k]] if v)
       for k in tot}
print('raw sums (seconds as measured, any rc):', ' '.join(f'{k}={raw[k]:.1f}' for k in raw))
both = [n for n in names if ctx[n].get('ctx', (1, 0))[0] == 0 and ref.get(n, {}).get('ref', (1, 0))[0] == 0]
print('files answered by ctx and ref:', len(both),
      f"ctx={sum(ctx[n]['ctx'][1] for n in both):.1f} ref={sum(ref[n]['ref'][1] for n in both):.1f}")
for k in tot:
    print(f'{k}: total {tot[k]:.1f} s (non-zero rc counted as {cap:.0f} s), '
          f'non-zero rc {len(timeouts[k])}: {" ".join(timeouts[k])}')
print('taxonomy differences (both answered):', len(diffs), ' '.join(diffs))
