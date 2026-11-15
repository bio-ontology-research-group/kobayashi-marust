#!/usr/bin/env python3
"""aggregate.py SAMPLE.tsv RUNROOT OUT.tsv: one line per sampled input and
summary tables (full / partial / none, rows certified, failure classes)."""
import collections
import json
import os
import sys

sample = [l.rstrip('\n').split('\t') for l in open(sys.argv[1])]
root = sys.argv[2]
out = open(sys.argv[3], 'w')
out.write('input\tfragment\tsize\tclasses\tindividuals\tstatus\trows\tcertified\tkm_s\tdump_s\tfind_s\tcheck_s\tcheck_mb\tform\treason\n')
by = collections.Counter()
byfrag = collections.defaultdict(collections.Counter)
rows_tot = rows_cert = 0
reasons = collections.Counter()
for r in sample:
    o, frag, size = r[0], r[1], r[2]
    p = os.path.join(root, o, 'result.json')
    if not os.path.exists(p):
        st, R = 'no-result (driver killed or still running)', {}
    else:
        R = json.load(open(p))
        st = R['status']
    rows = sum(R['rows'].values()) if isinstance(R.get('rows'), dict) else 0
    cert = sum(R.get('certified', {}).values()) if R.get('certified') else 0
    if st.startswith('km-inconsistent'):
        st = 'no-negative-rows'
    rows_tot += rows
    rows_cert += cert
    stages = R.get('stages', [])
    reason = ''
    for s in stages:
        if s['status'] != 'certified' and s.get('kind') != 'accepted-part' or s['status'] not in ('certified', 'no-model'):
            pr = s.get('producer', {})
            ck = s.get('checker', {})
            if s['status'] == 'checker-rejected-or-slow':
                reason = 'checker: ' + ('timeout' if ck.get('rc') == 124 else (ck.get('err') or ck.get('out') or '')[-80:])
            elif s['status'] == 'dump-failed':
                reason = 'dump: ' + ('timeout' if s['dump'].get('rc') == 124 else (s['dump'].get('err') or '')[-80:])
            elif s['status'] != 'certified':
                reason = s['status'] + ': ' + str(pr.get('reason', ''))[:80]
            if reason:
                break
    if R.get('stopped') and not reason:
        reason = 'wall budget'
    if st == 'km-failed':
        reason = 'km: rc %s' % R['km'].get('rc')
    if st in ('partial', 'none', 'km-failed', 'signature-failed') or st.startswith('no-result'):
        reasons[reason.split(':')[0] + (': ' + reason.split(':')[1].strip()[:40] if ':' in reason else '')] += 1
    by[st] += 1
    byfrag[frag][st] += 1

    def ssum(key, sub):
        v = [s.get(key, {}).get(sub) for s in stages]
        v = [x for x in v if x is not None]
        return round(sum(v), 1) if v else ''
    form = ','.join(sorted(set(s.get('producer', {}).get('form', '') for s in stages if s.get('producer'))))
    mb = max([s.get('checker', {}).get('rss_mb') or 0 for s in stages] or [0])
    out.write('\t'.join(map(str, [o, frag, size, R.get('classes', ''), R.get('individuals', ''), st, rows, cert,
                                  R.get('km', {}).get('secs', ''), ssum('dump', 'secs'), ssum('producer', 'secs'),
                                  ssum('checker', 'secs'), mb, form, reason])) + '\n')
print('inputs', len(sample), dict(by))
print('rows', rows_tot, 'certified', rows_cert, '%.1f%%' % (100.0 * rows_cert / max(1, rows_tot)))
for f in sorted(byfrag):
    print(' ', f, dict(byfrag[f]))
print('failure classes:')
for k, v in reasons.most_common():
    print('  %3d %s' % (v, k))
