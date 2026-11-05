"""Resume-capable runner for KM on a seed family against HermiT gold.

usage: python3 -I fam_resume.py KM_BIN GOLD_DIR OUT.tsv SPECS RUNS FILE...

Identical to fam_run.py, except any (file, spec, run) tuple already recorded in
OUT.tsv is skipped.
"""
import concurrent.futures as cf
import json
import os
import subprocess
import sys
import time

KM, GOLD, OUT, SPECS, RUNS = sys.argv[1:6]
FILES = sys.argv[6:]
RUNS = int(RUNS)
TIMEOUT = int(os.environ.get('FAM_TIMEOUT', '60'))
FORCED_TIMEOUT = int(os.environ.get('FAM_FORCED_TIMEOUT', '15'))
THREADS = int(os.environ.get('FAM_THREADS', '2'))
RELEASE = dict(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
               KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1',
               KM_THREADS='1')


def loc(x):
    return x.split('#')[-1].split(':')[-1].strip('<>')


def compare(g, k):
    if g['consistent'] != k.get('consistent'):
        return 'WRONG', 'consistency gold=%s km=%s' % (g['consistent'], k.get('consistent'))
    gs = {(loc(a), loc(b)) for a, b in g['subsumptions']}
    ks = {(loc(a), loc(b)) for a, b in k.get('subsumptions', [])}
    ks = {p for p in ks if p[0] != p[1] and p[1] != 'Thing' and p[0] != 'Nothing'}
    gu = {loc(x) for x in g['unsatisfiable']}
    ku = {loc(x) for x in k.get('unsatisfiable', [])}
    gs = {p for p in gs if p[0] not in gu and p[1] not in gu}
    ks = {p for p in ks if p[0] not in ku and p[1] not in ku}
    if not g['consistent']:
        return 'ok', ''
    if (gs, gu) == (ks, ku):
        return 'ok', ''
    return 'WRONG', 'missing=%s extra=%s unsat_missing=%s unsat_extra=%s dropped=%s' % (
        sorted(gs - ks)[:4], sorted(ks - gs)[:4], sorted(gu - ku), sorted(ku - gu), k.get('dropped'))


def job(args):
    path, spec, run = args
    stem = os.path.splitext(os.path.basename(path))[0]
    gp = os.path.join(GOLD, stem + '.json')
    if not os.path.exists(gp):
        return path, spec, run, 'NOGOLD', 0.0, ''
    g = json.load(open(gp))
    env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    env.update(RELEASE)
    if spec == 'seq':
        env['KM_ELC_SEQUENTIAL'] = '1'
    elif spec != 'auto':
        env['KM_ROUTE'] = spec
    t = time.time()
    try:
        p = subprocess.run([KM, 'classify', path], env=env, capture_output=True,
                           timeout=TIMEOUT if spec == 'auto' else FORCED_TIMEOUT)
    except subprocess.TimeoutExpired:
        return path, spec, run, 'TIMEOUT', time.time() - t, ''
    dt = time.time() - t
    out = p.stdout.decode(errors='replace').strip()
    if p.returncode != 0 or not out:
        err = p.stderr.decode(errors='replace').strip().splitlines()
        return path, spec, run, 'NOANSWER', dt, (err[-1][:160] if err else 'rc=%d' % p.returncode)
    try:
        k = json.loads(out)
    except ValueError:
        return path, spec, run, 'ERR', dt, 'bad json'
    v, d = compare(g, k)
    return path, spec, run, v, dt, d


done = set()
if os.path.exists(OUT):
    for line in open(OUT):
        parts = line.rstrip('\n').split('\t')
        if len(parts) >= 4:
            done.add((parts[0], parts[1], int(parts[2])))

jobs = [(f, s, r) for f in FILES for s in SPECS.split(',') for r in range(1, RUNS + 1)
        if (f, s, r) not in done]
print(f"fam_resume: {len(done)} already done, {len(jobs)} remaining -> {OUT}", flush=True)
with open(OUT, 'a') as out, cf.ThreadPoolExecutor(THREADS) as ex:
    for row in ex.map(job, jobs):
        path, spec, run, v, dt, d = row
        out.write('%s\t%s\t%d\t%s\t%.2f\t%s\n' % (path, spec, run, v, dt, d))
        out.flush()
