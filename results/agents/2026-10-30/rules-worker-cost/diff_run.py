"""Differential runner: KM routes against cached HermiT answers.

usage: python3 -I diff_run.py KM_BIN ORACLE_DIR GOLD_DIR OUT.tsv ROUTES FILE...

ROUTES is a comma-separated list of KM_ROUTE values (`auto` leaves KM_ROUTE
unset). Every KM_* variable of the caller is removed, except those listed in
the optional environment variable DIFF_KEEP (comma-separated KM_NAME=VALUE
pairs added to every KM run). HermiT answers are cached as GOLD_DIR/<stem>.json.
Output columns: file, route, verdict (ok / WRONG / TIMEOUT / ERR / NOGOLD),
seconds, miss_sub, extra_sub, miss_unsat, extra_unsat, consistency_mismatch.
"""
import concurrent.futures as cf
import json
import os
import subprocess
import sys
import time

KM, ORACLE, GOLD, OUT, ROUTES = sys.argv[1:6]
FILES = sys.argv[6:]
ROUTES = ROUTES.split(',')
KM_TIMEOUT = int(os.environ.get('DIFF_KM_TIMEOUT', '240'))
THREADS = int(os.environ.get('DIFF_THREADS', '8'))
KEEP = [kv.split('=', 1) for kv in os.environ.get('DIFF_KEEP', '').split(',') if kv]


def strip(name):
    return name.lstrip(':').split('#')[-1]


def hermit(path):
    stem = os.path.splitext(os.path.basename(path))[0]
    cache = os.path.join(GOLD, stem + '.json')
    if os.path.exists(cache):
        with open(cache) as f:
            d = json.load(f)
    else:
        cp = open(os.path.join(ORACLE, 'cp.txt')).read().strip()
        o = subprocess.run(['timeout', '300', 'java', '-cp', '.:' + cp, 'Oracle',
                            os.path.abspath(path)], cwd=ORACLE,
                           capture_output=True, text=True).stdout
        try:
            d = json.loads(o)
        except ValueError:
            return None
        with open(cache, 'w') as f:
            json.dump(d, f)
    uns = frozenset(strip(c) for c in d['unsatisfiable'])
    subs = frozenset((strip(a), strip(b)) for a, b in d['subsumptions']
                     if strip(a) not in uns and strip(b) not in uns and strip(a) != strip(b))
    return bool(d['consistent']), subs, uns


def km(path, route):
    env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    for k, v in KEEP:
        env[k] = v
    if route != 'auto':
        env['KM_ROUTE'] = route
    t0 = time.time()
    try:
        p = subprocess.run([KM, 'classify', '--lines', path], capture_output=True,
                           text=True, env=env, timeout=KM_TIMEOUT)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', time.time() - t0, None
    dt = time.time() - t0
    cons, subs, uns = None, set(), set()
    for line in p.stdout.splitlines():
        t = line.split('\t')
        if t[0].startswith('CONSISTENT'):
            cons = t[0].endswith('1')
        elif t[0] == 'SUB' and len(t) == 3:
            subs.add((strip(t[1]), strip(t[2])))
        elif t[0] == 'UNSAT' and len(t) == 2:
            uns.add(strip(t[1]))
    if cons is None:
        return 'ERR', dt, None
    subs = frozenset(s for s in subs if s[0] not in uns and s[1] not in uns and s[0] != s[1])
    return 'RUN', dt, (cons, subs, frozenset(uns))


def one(path):
    h = hermit(path)
    rows = []
    for r in ROUTES:
        if h is None:
            rows.append((path, r, 'NOGOLD', 0.0, '', '', '', '', ''))
            continue
        status, dt, k = km(path, r)
        if k is None:
            rows.append((path, r, status, dt, '', '', '', '', ''))
            continue
        if not h[0]:
            verdict = 'ok' if not k[0] else 'WRONG'
            rows.append((path, r, verdict, dt, 0, 0, 0, 0, int(k[0] != h[0])))
            continue
        ms, es = len(h[1] - k[1]), len(k[1] - h[1])
        mu, eu = len(h[2] - k[2]), len(k[2] - h[2])
        cm = int(k[0] != h[0])
        verdict = 'ok' if (ms, es, mu, eu, cm) == (0, 0, 0, 0, 0) else 'WRONG'
        rows.append((path, r, verdict, dt, ms, es, mu, eu, cm))
    return rows


with open(OUT, 'a') as out, cf.ThreadPoolExecutor(THREADS) as ex:
    for rows in ex.map(one, FILES):
        for row in rows:
            out.write('\t'.join(str(x) if not isinstance(x, float) else f'{x:.2f}'
                                for x in row) + '\n')
        out.flush()
