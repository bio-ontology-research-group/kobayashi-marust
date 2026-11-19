#!/usr/bin/env python3
"""Tables for a stage H3 run: aggregate_h3.py RUNDIR [LIST] > table.tsv; summary on stderr.

LIST (optional, column 1 input, column 2 fragment, column 3 size bin, as
tools/hints/results/sample.tsv) adds strata. Unchecked counts come from the
producer's own self-checked models; certified counts only from checker runs.
"""
import json
import os
import sys
from collections import Counter, defaultdict

run_dirs = sys.argv[1].split(',')
meta = {}


def sbin(b):
    return 'a<100K' if b < 100000 else 'b<1M' if b < 1000000 else 'c<10M' if b < 10000000 else 'd>=10M'


cpath = '/mnt/data1/leechuck/km-work/v170/reports/census-per-input.tsv'
if os.path.exists(cpath):
    with open(cpath) as f:
        hdr = f.readline().rstrip('\n').split('\t')
        bi = hdr.index('bytes')
        fi = hdr.index('fragment')
        for line in f:
            w = line.rstrip('\n').split('\t')
            if w[0].startswith('ore_ont_'):
                meta[w[0]] = (w[fi], sbin(int(w[bi])))

if len(sys.argv) > 2:
    for line in open(sys.argv[2]):
        w = line.rstrip('\n').split('\t')
        if len(w) >= 3 and w[1] != '?' and w[2] in ('a<100K', 'b<1M', 'c<10M', 'd>=10M'):
            meta[w[0]] = (w[1], w[2])

cols = ['input', 'fragment', 'size', 'bytes', 'status', 'classes', 'individuals', 'concepts', 'gci', 'data_clauses',
        'km_s', 'km_mb', 'dump_s', 'dump_mb', 'prod_s', 'prod_mb', 'models', 'elements', 'edges', 'violations',
        'general', 'split', 'partial', 'none', 'split_wit', 'polluted', 'rows', 'unchecked', 'unc_nonsub', 'unc_nontype',
        'chk_calls', 'chk_s', 'chk_rss', 'chk_results', 'status_checked', 'cert_rows', 'thing_rows', 'cert_consistency', 'disagree', 'reason']
print('\t'.join(cols))
S = defaultdict(Counter)
allr = []
entries = []
seen_d = set()
for rdir in run_dirs:
    if not os.path.exists(rdir):
        continue
    for d in os.listdir(rdir):
        if d not in seen_d and os.path.exists(os.path.join(rdir, d, 'result.json')):
            seen_d.add(d)
            entries.append((d, os.path.join(rdir, d, 'result.json')))
for d, p in sorted(entries):
    try:
        R = json.load(open(p))
    except Exception:
        continue
    b = R.get('bytes', 0)
    frag, size = meta.get(d, ('?', sbin(b)))
    P = R.get('producer') or {}
    C = R.get('checker') or {}
    row = {'input': d, 'fragment': frag, 'size': size, 'bytes': b, 'status': R.get('status')}
    km = R.get('km') or {}
    row.update(km_s=km.get('secs'), km_mb=km.get('rss_mb'))
    dp = R.get('dump') or {}
    row.update(dump_s=dp.get('secs'), dump_mb=dp.get('rss_mb'))
    pr = R.get('producer_run') or {}
    row.update(prod_s=pr.get('secs'), prod_mb=pr.get('rss_mb'))
    reason = ''
    if P and 'nf' in P and 'witness' in P:
        ms = P['models']
        W = P['witness']
        row.update(classes=P['classes'], individuals=P['individuals'], concepts=P['nf']['concepts'], gci=P['nf']['gci'],
                   data_clauses=P['nf']['data_clauses'], models=len(ms), elements=sum(m['elements'] for m in ms),
                   edges=sum(m['edges'] for m in ms), violations=sum(m['violations'] for m in ms),
                   general=W['general'], split=W['split'], partial=W['partial'], none=W['none'],
                   split_wit=W['split_witnesses'], polluted=W['polluted_moves'], rows=R.get('rows_total'),
                   unchecked=R.get('rows_unchecked'),
                   unc_nonsub=P['rows']['nonsub'] - P['unchecked']['nonsub'],
                   unc_nontype=0 if R.get('km', {}).get('realized') is False else (P['rows']['nontype'] - P['unchecked']['nontype']))
        if R.get('status') != 'model-full':
            if not P['base']['ok']:
                reason = 'no base model: ' + P['base']['why']
            elif P.get('stopped'):
                reason = P['stopped']
            elif W['fail']:
                reason = 'witness: ' + ', '.join('%s %d' % kv for kv in W['fail'].items())
            elif row['unc_nontype']:
                reason = 'individual types not general'
            elif row['unc_nonsub']:
                reason = 'split witnesses incomplete'
            if ms and all(m['violations'] > 0 for m in ms):
                fv = next((m.get('first_violation') for m in ms if m.get('first_violation')), None)
                reason = 'self-check: ' + str(fv)[:80]
    elif P:
        ms = P.get('models') or []
        row.update(models=len(ms), elements=sum(m.get('elements', 0) for m in ms),
                   edges=sum(m.get('edges', 0) for m in ms), violations=sum(m.get('violations', 0) for m in ms),
                   rows=R.get('rows_total'), unchecked=R.get('rows_unchecked'))
    if C:
        cert = C.get('certified', {})
        tried = C.get('rows_tried', {})
        row.update(chk_calls=C.get('calls'), chk_s=C.get('secs'), chk_results=json.dumps(C.get('results', {})),
                   cert_rows=sum(cert.values()), cert_consistency=cert.get('consistency'), chk_rss=C.get('rss_mb'))
        tn = C.get('thing_nonsub')
        if tn is None and P and C.get('calls'):
            tn = 0
        row['thing_rows'] = tn
        row['status_checked'] = R.get('status_checked')
        if R.get('status_checked') and R.get('rows_total') is not None and tn is not None and \
                row['cert_rows'] + tn == R['rows_total'] and row['cert_rows'] < R['rows_total']:
            row['status_checked'] = 'certified-full-but-thing'
        row['disagree'] = len(C.get('disagreements') or [])
        if C.get('skipped'):
            row['chk_results'] = C['skipped']
    if not reason and R.get('status') not in ('model-full',):
        reason = 'memory cap (8 GB)' if R.get('status') == 'producer-memout' else R.get('status')
    row['reason'] = reason
    print('\t'.join('' if row.get(c) is None else str(row.get(c)) for c in cols))
    allr.append(row)
    for key in ('all', 'size:' + size, 'frag:' + frag):
        s = S[key]
        s['inputs'] += 1
        st = R.get('status')
        s[st] += 1
        s['rows'] += row.get('rows') or 0
        s['unchecked'] += row.get('unchecked') or 0
        if R.get('export_used'):
            s['export_used'] += 1
        if R.get('km', {}).get('realized') is False:
            s['no_realize'] += 1
            ns = R.get('nontype_separate') or (P.get('nontype_separate') if P else None) or {}
            s['nontype_sep_inds'] += ns.get('individuals', 0)
            s['nontype_sep_pairs'] += ns.get('pairs', 0)
            s['nontype_sep_cert'] += ns.get('certified_outside', 0)
        if P and P.get('base', {}).get('ok') and 'classes' in P:
            s['general'] += row.get('general') or 0
            s['split'] += row.get('split') or 0
            s['partial'] += row.get('partial') or 0
            s['none'] += row.get('none') or 0
            s['classes'] += P['classes'] + 1
        if C and not C.get('skipped') and C.get('calls'):
            s['checked_inputs'] += 1
            if C.get('certified', {}).get('consistency'):
                s['consistency_certified'] += 1
            s['cert_rows'] += row.get('cert_rows') or 0
            sc = row.get('status_checked') or ''
            s[sc] += 1
            s['thing_rows'] += row.get('thing_rows') or 0
            s['disagree'] += row.get('disagree') or 0
            for kk, vv in (C.get('results') or {}).items():
                s['chk:' + kk] += vv
out = sys.stderr
for key in sorted(S, key=lambda k: (k != 'all', k)):
    s = S[key]
    print('%-14s inputs %4d | producer: model-full %4d partial %3d none %3d other %3d | classes %7d general %7d split %5d partial %4d none %4d | rows %d unchecked %d | checker: inputs %d consistency %d full %d full-but-Thing %d partial %d none %d | certified rows %d (+ Thing rows %d) | calls %s | disagreements %d' % (
        key, s['inputs'], s['model-full'], s['model-partial'], s['model-none'],
        s['inputs'] - s['model-full'] - s['model-partial'] - s['model-none'],
        s['classes'], s['general'], s['split'], s['partial'], s['none'], s['rows'], s['unchecked'],
        s['checked_inputs'], s['consistency_certified'], s['certified-full'], s['certified-full-but-thing'],
        s['certified-partial'], s['certified-none'], s['cert_rows'], s['thing_rows'],
        {k[4:]: v for k, v in s.items() if k.startswith('chk:')}, s['disagree']), file=out)
all_s = S['all']
if all_s['no_realize'] or all_s['export_used']:
    print('separate nontype (no-realize): inputs %d individuals %d pairs %d certified_outside %d | export_used inputs %d' % (
        all_s['no_realize'], all_s['nontype_sep_inds'], all_s['nontype_sep_pairs'], all_s['nontype_sep_cert'], all_s['export_used']), file=out)
reasons = Counter((r['reason'] or '').split(':')[0] for r in allr if r['reason'])
print('reasons:', dict(reasons), file=out)
