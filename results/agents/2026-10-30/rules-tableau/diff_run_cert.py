"""Differential runner: KM routes against cached HermiT answers, with the
rule-route Lean checker on (lean-rules-route, 2026-10-30; based on the
fr282-dropped-rules diff_run.py).

Every KM run gets KM_RULES_LEAN_CERT=CERT_ROOT/<stem> and
KM_RULES_LEAN_CHECKER=$DIFF_RULES_CHECKER, so the rule worker writes one
certificate per answer and fails closed on a rejection or a missing
certificate. An extra column `cert` reports: accepted (certificates written
and each accepted again by the checker here), rejected (the worker reported a
Lean rejection, or a written certificate fails the re-check), nocert (the
worker had no certificate for an answer), none (no rule-worker answer was
used: the route did not reach the rule worker), timeout. Column `certs` is
the number of certificate files.

usage: python3 -I diff_run.py KM_BIN ORACLE_DIR GOLD_DIR OUT.tsv ROUTES FILE...

ROUTES is a comma-separated list of KM_ROUTE values (`auto` leaves KM_ROUTE
unset). Every KM_* variable of the caller is removed, except those listed in
the optional environment variable DIFF_KEEP (comma-separated KM_NAME=VALUE
pairs added to every KM run). HermiT answers are cached as GOLD_DIR/<stem>.json.
Output columns: file, route, verdict (ok / WRONG / DROPPED / REFUSED / TIMEOUT /
ERR / NOGOLD), seconds, miss_sub, extra_sub, miss_unsat, extra_unsat,
consistency_mismatch, dropped.

A consistent answer with `DROPPED N`, N > 0, is an incomplete answer KM flags
itself: it is reported as DROPPED when it is otherwise sound (no extra
subsumption or unsatisfiable class, the consistency verdict agrees), and as
WRONG when it also asserts something the gold does not entail. An
inconsistent answer is exact whatever DROPPED says (entailment is monotone).
(2026-10-30, fr282-dropped-rules: the earlier version ignored DROPPED.)
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
CHECKER = os.environ['DIFF_RULES_CHECKER']
CERT_ROOT = os.environ['DIFF_CERT_ROOT']
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
    stem = os.path.splitext(os.path.basename(path))[0]
    cdir = os.path.join(CERT_ROOT, stem + '-' + route)
    subprocess.run(['rm', '-rf', cdir])
    env['KM_RULES_LEAN_CERT'] = cdir
    env['KM_RULES_LEAN_CHECKER'] = CHECKER
    t0 = time.time()
    try:
        p = subprocess.run([KM, 'classify', '--lines', path], capture_output=True,
                           text=True, env=env, timeout=KM_TIMEOUT)
    except subprocess.TimeoutExpired:
        CERT[(path, route)] = ('timeout', 0, '')
        return 'TIMEOUT', time.time() - t0, None
    dt = time.time() - t0
    files = sorted(f for f in os.listdir(cdir) if f.endswith('.json')) if os.path.isdir(cdir) else []
    recheck = all(subprocess.run([CHECKER, os.path.join(cdir, f)], capture_output=True).returncode == 0
                  for f in files)
    err = p.stderr
    if 'rejected the rule-route certificate' in err or (files and not recheck):
        cert = 'rejected'
    elif 'no rule-route certificate' in err:
        cert = 'nocert'
    elif files:
        cert = 'accepted'
    else:
        cert = 'none'
    reason = ''
    for line in err.splitlines():
        if 'rule-route certificate' in line:
            reason = line.strip()[:300]
            break
    CERT[(path, route)] = (cert, len(files), reason)
    cons, subs, uns, dropped = None, set(), set(), 0
    for line in p.stdout.splitlines():
        t = line.split('\t')
        if t[0].startswith('DROPPED'):
            dropped = int(t[0].split()[-1] if len(t) == 1 else t[1])
        elif t[0].startswith('CONSISTENT'):
            cons = t[0].endswith('1')
        elif t[0] == 'SUB' and len(t) == 3:
            subs.add((strip(t[1]), strip(t[2])))
        elif t[0] == 'UNSAT' and len(t) == 2:
            uns.add(strip(t[1]))
    if cons is None:
        # Exit 3 with `unsupported:` is KM refusing the input with a reason.
        if p.returncode == 3 and 'unsupported:' in p.stderr:
            return 'REFUSED', dt, None
        return 'ERR', dt, None
    subs = frozenset(s for s in subs if s[0] not in uns and s[1] not in uns and s[0] != s[1])
    return 'RUN', dt, (cons, subs, frozenset(uns), dropped)


CERT = {}


def one(path):
    h = hermit(path)
    rows = []
    for r in ROUTES:
        if h is None:
            rows.append((path, r, 'NOGOLD', 0.0, '', '', '', '', '', ''))
            continue
        status, dt, k = km(path, r)
        if k is None:
            rows.append((path, r, status, dt, '', '', '', '', '', '') + CERT.get((path, r), ('', 0, '')))
            continue
        dropped = k[3] if k[0] else 0
        if not h[0]:
            verdict = 'ok' if not k[0] else ('DROPPED' if dropped else 'WRONG')
            rows.append((path, r, verdict, dt, 0, 0, 0, 0, int(k[0] != h[0]), dropped) + CERT[(path, r)])
            continue
        ms, es = len(h[1] - k[1]), len(k[1] - h[1])
        mu, eu = len(h[2] - k[2]), len(k[2] - h[2])
        cm = int(k[0] != h[0])
        if es or eu or cm:
            verdict = 'WRONG'
        elif dropped:
            verdict = 'DROPPED'
        else:
            verdict = 'ok' if (ms, mu) == (0, 0) else 'WRONG'
        rows.append((path, r, verdict, dt, ms, es, mu, eu, cm, dropped) + CERT[(path, r)])
    return rows


with open(OUT, 'a') as out, cf.ThreadPoolExecutor(THREADS) as ex:
    for rows in ex.map(one, FILES):
        for row in rows:
            out.write('\t'.join(str(x) if not isinstance(x, float) else f'{x:.2f}'
                                for x in row) + '\n')
        out.flush()
