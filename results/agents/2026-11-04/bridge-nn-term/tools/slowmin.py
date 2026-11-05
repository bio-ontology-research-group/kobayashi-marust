"""Greedy axiom deletion keeping a KM run slow (a performance reduction).

usage: python3 -I slowmin.py KM_BIN IN.ofn OUT.ofn THRESHOLD_S [K=V ...]
Deletes one axiom at a time (declarations kept) while `km classify` on the
forced bridge still takes at least THRESHOLD_S seconds (cap 3x threshold).
With SLOWMIN_REF=BIN the reference binary must stay under THRESHOLD_S/5.
"""
import os, subprocess, sys, time
km, src, dst, thr = sys.argv[1], sys.argv[2], sys.argv[3], float(sys.argv[4])
extra = dict(kv.split('=', 1) for kv in sys.argv[5:])
S = os.path.dirname(os.path.abspath(dst))
lines = open(src).read().splitlines()
env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
env.update(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
           KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1',
           KM_THREADS='1', KM_ROUTE='ht_bridge', **extra)
def axiom(l):
    l = l.strip()
    return l and not l.startswith(('Prefix', 'Ontology', 'Declaration', ')'))
REF = os.environ.get('SLOWMIN_REF')
def run(b, p, cap):
    t = time.time()
    try:
        r = subprocess.run([b, 'classify', p], env=env, capture_output=True, timeout=cap)
    except subprocess.TimeoutExpired:
        return None
    return time.time() - t if r.returncode == 0 else -1
def slow(ls):
    p = os.path.join(S, '.slowmin.ofn'); open(p, 'w').write('\n'.join(ls) + '\n')
    t = run(km, p, 3 * thr)
    if not (t is None or t >= thr):
        return False
    if REF:
        tr = run(REF, p, thr)
        return tr is not None and 0 <= tr < thr / 5
    return True
assert slow(lines), 'input not slow'
i = 0
while i < len(lines):
    if axiom(lines[i]):
        cand = lines[:i] + lines[i + 1:]
        if slow(cand):
            lines = cand
            print('dropped', file=sys.stderr)
            continue
    i += 1
open(dst, 'w').write('\n'.join(lines) + '\n')
print(sum(axiom(l) for l in lines), 'axioms')
