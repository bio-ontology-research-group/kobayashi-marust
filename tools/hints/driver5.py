#!/usr/bin/env python3
"""Stage H1 driver for the hint-only route `sroiq-hint` (stage C5).

    driver5.py ONTOLOGY OUTDIR [--wall S] [--timeout S]

km's negative rows become proved rows of the route: `consistent`, one
`nonsubs A owl:Nothing B1 ... Bk` per satisfiable class A (owl:Nothing
gives sat(A)), one `nontypes a C1 ... Cj` per named individual. For each
row the driver reads the row's normal form (`--print-index --row`,
`--print-clauses --row`), builds a hint with the finder, checks it with the
Python mirror, and sends every (row, hint) pair of the input to one
`--batch` call. A row counts as certified only when the batch printed
`"result":"certified"` for it in this run. Rows whose hint the finder
cannot build are split (localisation over the guard gcis of the row) into
a part that has a model and a rest that becomes a new row.
"""
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)

import nf as nfm
import hintcheck
from finder import Fail, solve, flat_hint
from driver import run, km_answers, rows_of, THING

REF = os.environ.get('H1_REF', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-owl-reference-c5')
NOTHING = 'http://www.w3.org/2002/07/owl#Nothing'
BUDGET = {'max_nodes': 200000, 'max_close': 200000}


def ref(args, path, timeout, out=None):
    return run([REF, '--procedure', 'sroiq-hint'] + args + [path], timeout, out=out)


def row_nf(path, row, timeout):
    rc1, s1, m1, idx, e1 = ref(['--print-index', '--row', row], path, timeout)
    if rc1 != 0:
        return None, {'rc': rc1, 'secs': s1, 'err': (e1 or '')[-200:]}
    rc2, s2, m2, cls, e2 = ref(['--print-clauses', '--row', row], path, timeout)
    if rc2 != 0:
        return None, {'rc': rc2, 'secs': s2, 'err': (e2 or '')[-200:]}
    return nfm.from_route(idx, cls), {'rc': 0, 'secs': round((s1 or 0) + (s2 or 0), 2),
                                      'rss_mb': max(m1 or 0, m2 or 0)}


def build(N, part=None, deadline=None):
    """A hint for the normal form, or (None, reason)."""
    p = part if part is not None else N.parts[0]
    ix = nfm.Index(N, p)
    if ix.long_chains:
        return None, 'chain of length > 1', None
    try:
        F = solve(ix, deadline=deadline, **BUDGET)
    except Fail as e:
        return None, 'no model: ' + str(e), None
    h = F.hint()
    why = hintcheck.check(ix, h)
    if why:
        return None, 'mirror rejects: ' + why, None
    form = 'certificate'
    # the route decides certificates in time exponential in the record types (R2)
    if h.recs:
        hf = flat_hint(F)
        if hf is not None and not hintcheck.check(ix, hf):
            h, form = hf, 'flat'
    return h, form, F.stats


def guards(N, nu, Bs):
    """B -> the gci `nu ⊑ D_B` of the guard D_B ⊓ B ⊑ ⊥ of a nonsubs row."""
    p = N.parts[0]
    named = set(N.cname.values())
    heads = {g[1][0]: g for g in p.gci if g[0] == (nu,) and len(g[1]) == 1 and g[1][0] not in named}
    out = {}
    for g in p.gci:
        if not g[1] and len(set(g[0])) == 2:
            a, b = g[0]
            for D, X in ((a, b), (b, a)):
                if D in heads:
                    for B in Bs:
                        if N.cname.get(B) == X:
                            out[B] = heads[D]
    return out


def localize(N, nu, Bs, deadline):
    """Keep a maximal set of the B's (halves, greedy), the rest is left."""
    import copy
    gm = guards(N, nu, Bs)
    if len(gm) < len([B for B in Bs if B in N.cname]):
        return None, None
    allg = set(gm.values())
    base = [g for g in N.parts[0].gci if g not in allg]

    def ok(sel):
        if time.time() > deadline:
            raise TimeoutError
        p2 = copy.copy(N.parts[0])
        p2.gci = base + [gm[B] for B in sel]
        try:
            solve(nfm.Index(N, p2), restarts=10, deadline=deadline, **BUDGET)
            return True
        except Fail:
            return False
    acc, left = [], []
    try:
        if not ok([]):
            return [], list(Bs)

        def add(items):
            if not items:
                return
            if ok(acc + items):
                acc.extend(items)
            elif len(items) == 1:
                left.extend(items)
            else:
                h = len(items) // 2
                add(items[:h])
                add(items[h:])
        add([B for B in Bs if B in gm])
    except TimeoutError:
        return None, None
    return acc, left


def main():
    a = sys.argv[1:]
    src, outdir = a[0], a[1]
    T = int(a[a.index('--timeout') + 1]) if '--timeout' in a else 120
    wall = int(a[a.index('--wall') + 1]) if '--wall' in a else 600
    os.makedirs(outdir, exist_ok=True)
    t0 = time.time()
    R = {'input': os.path.basename(src).rsplit('.', 1)[0], 'bytes': os.path.getsize(src), 'route': 'sroiq-hint'}
    kr, ans = km_answers(src, outdir, 300)
    R['km'] = kr
    if ans is None:
        R['status'] = 'km-failed'
        return finish(R, outdir, t0)
    R['km']['consistent'] = ans['consistent']
    if ans['consistent'] is False:
        R['status'] = 'km-inconsistent (no negative rows)'
        return finish(R, outdir, t0)
    rc, secs, rss, idx, err = ref(['--print-index'], src, T)
    if rc != 0:
        R['status'] = 'signature-failed'
        R['sig'] = {'rc': rc, 'err': (err or '')[-200:]}
        return finish(R, outdir, t0)
    classes = [l.split(' ', 2)[2] for l in idx.split('\n') if l.startswith('concept ') and
               not l.split(' ', 2)[2].startswith('urn:km:')]
    inds = [l.split(' ', 2)[2] for l in idx.split('\n') if l.startswith('nominal ') and
            not l.split(' ', 2)[2].startswith('urn:km:') and not l.split(' ', 2)[2].startswith('#')]
    nonsub, nontype = rows_of(classes, inds, ans)
    R['classes'], R['individuals'] = len(classes), len(inds)
    R['rows'] = {'consistency': 1, 'sat': len(nonsub), 'nonsub': sum(map(len, nonsub.values())),
                 'nontype': sum(map(len, nontype.values()))}
    # the queue of rows: (kind, key, list)
    queue = [('consistent', None, [])]
    # a row is one command-line argument: split long lists (argv limit, request R9)
    G = 300
    for A, Bs in nonsub.items():
        for i in range(0, max(1, len(Bs)), G):
            queue.append(('nonsubs', A, Bs[i:i + G]))
    for x, Cs in nontype.items():
        for i in range(0, len(Cs), G):
            queue.append(('nontypes', x, Cs[i:i + G]))
    pairs, meta = [], []
    R['producer'] = {'rows': 0, 'hints': 0, 'nf_secs': 0.0, 'find_secs': 0.0, 'forms': {}, 'fail': {}}
    P = R['producer']
    stopped = None
    qi = 0
    while qi < len(queue):
        if time.time() - t0 > wall:
            stopped = 'wall budget after %d of %d rows' % (qi, len(queue))
            break
        kind, key, Ls = queue[qi]
        qi += 1
        if kind == 'consistent':
            row = 'consistent'
        elif kind == 'nonsubs':
            row = ' '.join(['nonsubs', key, NOTHING] + Ls)
        else:
            row = ' '.join(['nontypes', key] + Ls)
        P['rows'] += 1
        N, st = row_nf(src, row, T)
        P['nf_secs'] += st.get('secs') or 0
        if N is None:
            P['fail']['row index: ' + (st.get('err') or 'rc %s' % st.get('rc')).strip()[:60]] = \
                P['fail'].get('row index: ' + (st.get('err') or 'rc %s' % st.get('rc')).strip()[:60], 0) + 1
            continue
        t1 = time.time()
        h, form, stats = build(N, deadline=min(t0 + wall, time.time() + T))
        P['find_secs'] += time.time() - t1
        if h is None:
            r = form.split(':')[0] + ': ' + form.split(':', 1)[1].strip()[:50] if ':' in form else form
            P['fail'][r] = P['fail'].get(r, 0) + 1
            if kind == 'nonsubs' and len(Ls) > 1 and form.startswith('no model'):
                nu = next((i for k, i in N.nominal.items() if k.startswith('#')), None)
                acc, left = localize(N, nu, Ls, min(t0 + wall, time.time() + T))
                if acc is not None and (acc or left) and left != Ls:
                    if acc:
                        queue.append(('nonsubs', key, acc))
                    for B in left:
                        queue.append(('nonsubs', key, [B]))
                    P['split'] = P.get('split', 0) + 1
            continue
        P['hints'] += 1
        P['forms'][form] = P['forms'].get(form, 0) + 1
        hp = os.path.join(outdir, 'h%d.hint' % len(pairs))
        hintcheck.write(h, hp)
        pairs.append((row, hp))
        meta.append((kind, key, Ls))
    R['stopped'] = stopped
    cert = {'consistency': 0, 'sat': 0, 'nonsub': 0, 'nontype': 0}
    R['checker'] = {'pairs': len(pairs)}
    if pairs:
        # one call per row: the batch reader cuts lines at '#', so rows with
        # IRIs that contain '#' do not survive it (request R8)
        res = {}
        tchk, mchk, ncall = 0.0, 0, 0
        deadline = t0 + 2 * wall
        badrun = 0
        for i, (row, hp) in enumerate(pairs):
            if badrun >= 3:
                R['checker']['stopped'] = 'three timeouts or memory failures in a row after %d of %d pairs' % (i, len(pairs))
                break
            if time.time() > deadline:
                R['checker']['stopped'] = 'check budget after %d of %d pairs' % (i, len(pairs))
                break
            cmd = ['bash', '-c', 'ulimit -v 12000000; exec "$@"', 'chk', REF, '--procedure', 'sroiq-hint',
                   '--row', row, '--hint', hp, src]
            rc, secs, rss, out, err = run(cmd, T)
            ncall += 1
            tchk += secs or 0
            mchk = max(mchk, rss or 0)
            badrun = badrun + 1 if (rc == 124 or 'out of memory' in (err or '')) else 0
            if rc == 0 and '"certified":true' in (out or ''):
                res[i] = 'certified'
            elif rc == 124:
                res[i] = 'timeout'
            elif 'out of memory' in (err or ''):
                res[i] = 'out of memory'
            else:
                res[i] = 'rejected: ' + (err or '').strip()[:60]
        R['checker'].update({'calls': ncall, 'secs': round(tchk, 1), 'rss_mb': mchk})
        R['checker']['results'] = {k: list(res.values()).count(k) for k in set(res.values())}
        sat_done = set()
        for i, (kind, key, Ls) in enumerate(meta):
            if res.get(i) != 'certified':
                continue
            if kind == 'consistent':
                cert['consistency'] = 1
            elif kind == 'nonsubs':
                cert['consistency'] = 1
                if key not in sat_done:
                    sat_done.add(key)
                    cert['sat'] += 1
                cert['nonsub'] += len(Ls)
            else:
                cert['nontype'] += len(Ls)
                cert['consistency'] = 1
    R['certified'] = cert
    tot, got = sum(R['rows'].values()), sum(cert.values())
    R['status'] = 'full' if got == tot else ('partial' if got else 'none')
    return finish(R, outdir, t0)


def finish(R, outdir, t0):
    R['wall'] = round(time.time() - t0, 1)
    with open(os.path.join(outdir, 'result.json'), 'w') as f:
        json.dump(R, f)
    print(json.dumps(R))


if __name__ == '__main__':
    main()
