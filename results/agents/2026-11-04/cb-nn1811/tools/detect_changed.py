"""Exact detector for the entailed-functionality pass.

Runs the new binary with KM_HT_STATS=1 on each seed under ht_bridge and the
automatic route (release flags, CAP seconds) and keeps a seed when some HT
view gained a clause (`cb_to_ht [entailed-functional] +N`, N > 0) or when a
run ended at the cap without any conversion line (unknown). Every other seed
converts to the same HT view on both binaries, and the pass changes nothing
else, so its verdicts are those of the base.

usage: python3 -I detect_changed.py KM_BIN LIST_IN LIST_OUT [CAP]
"""
import os, re, subprocess, sys
KM, LIN, LOUT = sys.argv[1:4]
CAP = int(sys.argv[4]) if len(sys.argv) > 4 else 20
REL = dict(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
           KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1', KM_THREADS='1',
           KM_HT_STATS='1')
base = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
line = re.compile(rb'entailed-functional\] \+(\d+)')
rows = [l.rstrip('\n').split('\t') for l in open(LIN) if l.strip()]
keep, counts = [], {'added': 0, 'unknown': 0, 'same': 0}
for name, f in rows:
    verdict = 'same'
    for route in ('ht_bridge', 'auto'):
        env = dict(base, **REL)
        if route != 'auto':
            env['KM_ROUTE'] = route
        try:
            p = subprocess.run([KM, 'classify', f], env=env, capture_output=True, timeout=CAP)
            err, timed_out = p.stderr, False
        except subprocess.TimeoutExpired as e:
            err, timed_out = e.stderr or b'', True
        found = [int(m) for m in line.findall(err)]
        if any(found):
            verdict = 'added'
            break
        if timed_out and not found:
            verdict = 'unknown'
    counts[verdict] += 1
    if verdict != 'same':
        keep.append((name, f, verdict))
with open(LOUT, 'w') as out:
    for name, f, v in keep:
        out.write('%s\t%s\t%s\n' % (name, f, v))
print('screened %d: %s' % (len(rows), counts))
