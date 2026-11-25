#!/usr/bin/env python3
"""aggregate5.py SAMPLE.tsv RUNROOT OUT.tsv: driver5 results, one line per
input, and summaries (full / partial / none, rows, failure classes)."""
import collections
import json
import os
import sys

sample = [l.rstrip('\n').split('\t') for l in open(sys.argv[1])]
root = sys.argv[2]
out = open(sys.argv[3], 'w')
out.write('input\tfragment\tsize\tbytes\tclasses\tindividuals\tstatus\trows\tcertified\tkm_s\tnf_s\tfind_s'
          '\tcheck_s\tcheck_mb\tcalls\tresults\tproducer_fail\treason\n')
by = collections.Counter()
byfrag = collections.defaultdict(collections.Counter)
bysize = collections.defaultdict(collections.Counter)
rows_tot = rows_cert = 0
rowsk = collections.Counter()
certk = collections.Counter()
reasons = collections.Counter()
for r in sample:
    o, frag, size = r[0], r[1], r[2]
    p = os.path.join(root, o, 'result.json')
    if not os.path.exists(p):
        continue
    R = json.load(open(p))
    st = R['status']
    if st.startswith('km-inconsistent'):
        st = 'no negative rows (km: inconsistent)'
    rows = R.get('rows') or {}
    cert = R.get('certified') or {}
    rows_tot += sum(rows.values())
    rows_cert += sum(cert.values())
    rowsk.update(rows)
    certk.update(cert)
    P = R.get('producer', {})
    C = R.get('checker', {})
    res = C.get('results', {})
    reason = ''
    if st in ('partial', 'none'):
        bad = {k: v for k, v in res.items() if k != 'certified'}
        if R.get('stopped'):
            reason = 'producer wall budget'
        if C.get('stopped'):
            reason = 'checker budget'
        if bad:
            k = max(bad, key=bad.get)
            reason = 'checker ' + k.split(':')[0] + (' ' + k.split(':', 1)[1][:40] if ':' in k else '')
        if P.get('fail') and not reason:
            reason = 'producer: ' + max(P['fail'], key=P['fail'].get)
        if not reason and P.get('fail'):
            reason = 'producer: ' + max(P['fail'], key=P['fail'].get)
        reasons[reason or '?'] += 1
    elif st in ('km-failed', 'signature-failed'):
        reason = st + ' ' + str(R.get('km', {}).get('err', '') or R.get('sig', {}).get('err', ''))[:60]
        reasons[st] += 1
    by[st] += 1
    byfrag[frag][st] += 1
    bysize[size][st] += 1
    out.write('\t'.join(map(str, [o, frag, size, R.get('bytes'), R.get('classes', ''), R.get('individuals', ''),
                                  st, sum(rows.values()), sum(cert.values()), R.get('km', {}).get('secs', ''),
                                  round(P.get('nf_secs', 0), 1), round(P.get('find_secs', 0), 1),
                                  C.get('secs', ''), C.get('rss_mb', ''), C.get('calls', ''),
                                  json.dumps(res), json.dumps(P.get('fail', {})), reason])) + '\n')
n = sum(by.values())
print('inputs', n, dict(by))
print('rows', rows_tot, 'certified', rows_cert, '%.2f%%' % (100.0 * rows_cert / max(1, rows_tot)))
print('by kind (rows/certified):', {k: (rowsk[k], certk[k]) for k in rowsk})
for f in sorted(byfrag):
    print('  fragment', f, dict(byfrag[f]))
for f in sorted(bysize):
    print('  size', f, dict(bysize[f]))
print('reasons for partial/none:')
for k, v in reasons.most_common():
    print('  %3d %s' % (v, k))
