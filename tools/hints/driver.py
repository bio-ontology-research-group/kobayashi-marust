#!/usr/bin/env python3
"""Stage H1 driver: source ontology -> km answers -> witness ontology ->
normal form -> hint -> proved checker.

    driver.py ONTOLOGY OUTDIR [--chunk N] [--timeout S]

The negative rows of km's answer (consistency, satisfiable classes,
non-subsumptions, non-types) are certified by consistency of a *witness
ontology*: the source plus, for every class A in a chunk, a fresh
individual x_A with ClassAssertion(A x_A) and ClassAssertion(NB x_A) for
each class B that km says does not subsume A, where NB is a fresh class
with DisjointClasses(B NB); and, for every named individual a,
ClassAssertion(NC a) for each non-type C. Every model of the witness is a
model of the source in which x_A lies in A outside B and a outside C, so
the checker's `consistent: true` on the witness certifies all those rows
at once. A row counts as certified only when the proved checker printed
`"consistent":true` for a witness carrying it in this run.

Writes OUTDIR/result.json (one object) and the witness, normal form and
hint files.
"""
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)

import nf as nfm
import hintcheck
from finder import Finder, Fail, solve, flat_hint

SCR = '/mnt/data1/leechuck/km-work/v170/scratch/h1'
KM = os.environ.get('H1_KM', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-06f5b9b4')
REF = os.environ.get('H1_REF', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-owl-reference-c3c')
LEAN = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
LEANPATH = open(os.environ.get('H1_LEANPATH', '/mnt/data1/leechuck/km-work/v170/scratch/h1/leanpath.txt')).read().strip()
THING = 'http://www.w3.org/2002/07/owl#Thing'
NOTHING = 'http://www.w3.org/2002/07/owl#Nothing'
NBP = 'urn:km:h1:nb:'
XP = 'urn:km:h1:x:'


def run(cmd, timeout, out=None, env=None):
    """Run under /usr/bin/time; returns (rc, seconds, maxrss_mb, stdout, stderr)."""
    tf = os.path.join(SCR, 'tmp', 'time.%d' % os.getpid())
    e = dict(os.environ)
    for k in list(e):
        if k.startswith('KM_'):
            del e[k]
    e['KM_THREADS'] = '1'
    e['TMPDIR'] = os.path.join(SCR, 'tmp')
    if env:
        e.update(env)
    full = ['/usr/bin/time', '-f', '%e %M', '-o', tf, 'timeout', str(timeout)] + cmd
    for attempt in range(4):
        fo = open(out, 'w') if out else subprocess.PIPE
        p = subprocess.run(full, stdout=fo, stderr=subprocess.PIPE, env=e, text=True)
        if out:
            fo.close()
        # the host sometimes refuses new threads under load: retry
        if 'failed to create thread' not in p.stderr and 'Resource temporarily unavailable' not in p.stderr:
            break
        time.sleep(15)
    try:
        w = open(tf).read().split('\n')
        last = [l for l in w if re.match(r'^[0-9.]+ [0-9]+$', l)][-1].split()
        secs, rss = float(last[0]), int(last[1]) // 1024
    except Exception:
        secs, rss = None, None
    return p.returncode, secs, rss, (None if out else p.stdout), p.stderr


def clean_km_tmp():
    d = os.path.join(SCR, 'tmp')
    for f in os.listdir(d):
        m = re.match(r'^km-(?:run-)?(\d+)-', f)
        if m:
            try:
                os.kill(int(m.group(1)), 0)
            except OSError:
                p = os.path.join(d, f)
                subprocess.run(['rm', '-rf', p])


def km_answers(path, outdir, timeout):
    o = os.path.join(outdir, 'km.lines')
    rc, secs, rss, _, err = run([KM, 'classify', '--lines', '--realize', '--top', path], timeout, out=o)
    clean_km_tmp()
    res = {'rc': rc, 'secs': secs, 'rss_mb': rss}
    if rc != 0:
        res['err'] = err[-300:]
        return res, None
    ans = {'consistent': None, 'sub': set(), 'unsat': set(), 'type': set(), 'top': set(), 'dropped': 0}
    for line in open(o):
        w = line.rstrip('\n').split('\t')
        if w[0].startswith('CONSISTENT'):
            ans['consistent'] = w[0].split()[-1] == '1'
        elif w[0].startswith('DROPPED'):
            ans['dropped'] = int(w[0].split()[-1])
        elif w[0] == 'SUB':
            ans['sub'].add((w[1], w[2]))
        elif w[0] == 'UNSAT':
            ans['unsat'].add(w[1])
        elif w[0] == 'TYPE':
            ans['type'].add((w[1], w[2]))
        elif w[0] == 'TOP':
            ans['top'].add(w[1])
    return res, ans


def signature(path, timeout):
    rc, secs, rss, out, err = run([REF, '--procedure', 'sroiq-c2a', '--print-index', path], timeout)
    if rc != 0:
        return None, None, {'rc': rc, 'secs': secs, 'err': (err or '')[-300:]}
    classes, inds = [], []
    for line in out.split('\n'):
        w = line.split(' ', 2)
        if len(w) == 3 and w[0] == 'concept' and not w[2].startswith('urn:km:'):
            classes.append(w[2])
        elif len(w) == 3 and w[0] == 'nominal' and not w[2].startswith('urn:km:'):
            inds.append(w[2])
    return classes, inds, {'rc': rc, 'secs': secs, 'rss_mb': rss}


def rows_of(classes, inds, ans):
    """km's negative rows: {A: [B, ...]} for satisfiable A (owl:Thing
    included) and {a: [C, ...]} for named individuals."""
    top = ans['top'] | {THING}
    sup = {}
    for (a, b) in ans['sub']:
        sup.setdefault(a, set()).add(b)
    cls = [c for c in classes if c not in (THING, NOTHING)]
    nonsub = {}
    for A in [THING] + cls:
        if A in ans['unsat']:
            continue
        s = sup.get(A, set())
        nonsub[A] = [B for B in cls if B != A and B not in s and B not in top]
    typ = {}
    for (a, c) in ans['type']:
        typ.setdefault(a, set()).add(c)
    nontype = {a: [C for C in cls if C not in typ.get(a, set()) and C not in top] for a in inds}
    return nonsub, nontype


def neg(Bs):
    if len(Bs) == 1:
        return 'ObjectComplementOf(<%s>)' % Bs[0]
    return 'ObjectComplementOf(ObjectUnionOf(%s))' % ' '.join('<%s>' % B for B in Bs)


def witness_text(src, groups, nontype, nbidx=None):
    """groups: list of (A, [B...]) -> one fresh individual x_j each with
    ClassAssertion(A x_j) and ClassAssertion(not(B1 or ... or Bk) x_j);
    nontype: {a: [C...]} -> ClassAssertion(not(C1 or ...) a)."""
    ax = []
    for j, (A, Bs) in enumerate(groups):
        x = XP + str(j)
        ax.append('Declaration(NamedIndividual(<%s>))' % x)
        ax.append('ClassAssertion(<%s> <%s>)' % (A, x))
        if Bs:
            ax.append('ClassAssertion(%s <%s>)' % (neg(Bs), x))
    for a, Cs in nontype.items():
        if Cs:
            ax.append('ClassAssertion(%s <%s>)' % (neg(Cs), a))
    i = src.rindex(')')
    return src[:i] + '\n# stage H1 witness axioms\n' + '\n'.join(ax) + '\n' + src[i:]


def neg_gcis(N, part, nu, Bs):
    """The gcis of ClassAssertion(not(B1 or ...) u) for the individual with
    nominal name nu: {B: gci} whose removal drops B from the union."""
    named = set(N.cname.values())
    heads = [g[1][0] for g in part.gci if g[0] == (nu,) and len(g[1]) == 1 and g[1][0] not in named]
    bi = {N.cname[B]: B for B in Bs if B in N.cname}
    for D in heads:
        for g in part.gci:
            if not g[1] and len(set(g[0])) == 2 and D in g[0]:
                U = [x for x in g[0] if x != D][0]
                if len(Bs) == 1 and U in bi:
                    return {bi[U]: g}
                out = {}
                for g2 in part.gci:
                    if g2[1] == (U,) and len(g2[0]) == 1 and g2[0][0] in bi:
                        out[bi[g2[0][0]]] = g2
                if len(out) == len(bi):
                    return out
    return None


def dump_nf(wpath, nfpath, timeout):
    err = ''
    env = {'LEAN_PATH': LEANPATH, 'LEAN_NUM_THREADS': '1'}
    for attempt in range(3):
        # the default stack first; a larger one when the interpreter recurses deeply
        # (a large stack limit makes thread creation fail under load)
        st = 'ulimit -s 1048576; ' if attempt and 'recursion' in (err or '') else ''
        cmd = ['bash', '-c', st + 'exec "$0" --tstack=4000000 --run "$1" "$2"',
               LEAN, os.path.join(HERE, 'NFDump.lean'), wpath]
        rc, secs, rss, _, err = run(cmd, timeout, out=nfpath, env=env)
        if 'failed to create thread' not in (err or '') and 'recursion' not in (err or ''):
            break
        time.sleep(5)
    return {'rc': rc, 'secs': secs, 'rss_mb': rss, 'err': (err or '')[-300:] if rc else '', 'tries': attempt + 1}


def find_hint(nfpath, hpath, budget):
    t0 = time.time()
    N = nfm.parse(nfpath)
    r = {'n': N.n, 'm': N.m, 'parts': len(N.parts), 'route': N.route}
    if N.error or not N.parts:
        r.update(status='no-nf', reason=N.error or 'no parts')
        return r, None, None
    ix = nfm.Index(N, N.parts[0])
    r['clauses'] = sum(len(x) for x in (N.parts[0].gci, N.parts[0].ex, N.parts[0].all,
                                         N.parts[0].ge, N.parts[0].le))
    try:
        F = solve(ix, **budget)
    except Fail as e:
        r.update(status='no-model', reason=str(e), secs=round(time.time() - t0, 2))
        return r, N, ix
    h = F.hint()
    r.update(F.stats)
    r['core'], r['recs'] = h.k, len(h.recs)
    why = hintcheck.check(ix, h)
    r['form'] = 'certificate'
    if not why and h.recs:
        # the checker decides certificates in exponential time today: prefer a flat core
        hf = flat_hint(F)
        whyf = hintcheck.check(ix, hf) if hf is not None else 'folding failed'
        r['flat'] = whyf or 'ok'
        if not whyf:
            h = hf
            r['form'] = 'flat'
            r['core'] = h.k
    r['secs'] = round(time.time() - t0, 2)
    hintcheck.write(h, hpath)
    r['_types'] = h.ty
    r['hint_bytes'] = os.path.getsize(hpath)
    r['status'] = 'selfcheck-reject' if why else 'hint'
    if why:
        r['reason'] = why
    return r, N, ix


def localize(N, groups, nt, nbidx, budget, deadline):
    """Split the NB assertions of a witness whose normal form has no model
    the finder can build: keep a maximal set greedily (whole individuals
    first, then halves), leave the rest for the next round."""
    import copy
    part = N.parts[0]
    units = []   # (kind, key, B, gci)
    for j, (A, Bs) in enumerate(groups):
        if not Bs:
            continue
        m = neg_gcis(N, part, N.nominal.get(XP + str(j)), Bs)
        if m is None:
            return {'status': 'witness gcis not found', 'runs': 0}
        units.append([('x', j, B, m[B]) for B in Bs])
    for a, Cs in nt.items():
        if not Cs:
            continue
        m = neg_gcis(N, part, N.nominal.get(a), Cs)
        if m is None:
            return {'status': 'witness gcis not found', 'runs': 0}
        units.append([('i', a, C, m[C]) for C in Cs])
    allg = set(u[3] for us in units for u in us)
    base = [g for g in part.gci if g not in allg]
    runs = [0]

    def ok(sel):
        if time.time() > deadline:
            raise TimeoutError
        runs[0] += 1
        p2 = copy.copy(part)
        p2.gci = base + [u[3] for u in sel]
        ix = nfm.Index(N, p2)
        try:
            solve(ix, restarts=10, **budget)
            return True
        except Fail:
            return False
    acc, left = [], []
    try:
        if not ok([]):
            return {'status': 'no model even without the NB assertions', 'runs': runs[0]}

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
        for us in units:
            add(us)
    except TimeoutError:
        return {'status': 'localize timeout', 'runs': runs[0]}
    accset = set((u[0], u[1], u[2]) for u in acc)
    accG = [(A, [B for B in Bs if ('x', j, B) in accset]) for j, (A, Bs) in enumerate(groups)]
    accN = {a: [C for C in Cs if ('i', a, C) in accset] for a, Cs in nt.items()}
    accN = {a: c for a, c in accN.items() if c}
    leftG = [(A, [B for B in Bs if ('x', j, B) not in accset]) for j, (A, Bs) in enumerate(groups)]
    leftG = [(A, b) for A, b in leftG if b]
    leftN = {a: [C for C in Cs if ('i', a, C) not in accset] for a, Cs in nt.items()}
    leftN = {a: c for a, c in leftN.items() if c}
    return {'status': 'ok', 'runs': runs[0], 'acc_groups': accG, 'acc_nt': accN,
            'left_groups': leftG, 'left_nt': leftN}


def check(wpath, hpath, timeout, memkb=12000000):
    cmd = ['bash', '-c', 'ulimit -v %d; exec "$@"' % memkb, 'chk',
           REF, '--procedure', 'sroiq-c2a', '--hint', hpath, wpath]
    rc, secs, rss, out, err = run(cmd, timeout)
    ok = rc == 0 and '"consistent":true' in (out or '')
    return {'rc': rc, 'secs': secs, 'rss_mb': rss, 'accepted': ok,
            'out': (out or '').strip()[-200:], 'err': (err or '').strip()[-300:]}


def main():
    a = a_ = sys.argv[1:]
    src, outdir = a[0], a[1]
    chunk = int(a[a.index('--chunk') + 1]) if '--chunk' in a else 0
    T = int(a[a.index('--timeout') + 1]) if '--timeout' in a else 300
    max_pairs = int(a[a.index('--max-pairs') + 1]) if '--max-pairs' in a else 40000
    os.makedirs(outdir, exist_ok=True)
    name = os.path.basename(src).rsplit('.', 1)[0]
    R = {'input': name, 'bytes': os.path.getsize(src), 'km_bin': os.path.basename(KM)}
    t0 = time.time()
    kr, ans = km_answers(src, outdir, 300)
    R['km'] = kr
    if ans is None:
        R['status'] = 'km-failed'
        return finish(R, outdir, t0)
    R['km']['consistent'] = ans['consistent']
    R['km']['dropped'] = ans['dropped']
    if ans['consistent'] is False:
        R['status'] = 'km-inconsistent (no negative rows)'
        R['rows'] = 0
        return finish(R, outdir, t0)
    classes, inds, sr = signature(src, 120)
    R['sig'] = sr
    if classes is None:
        R['status'] = 'signature-failed'
        return finish(R, outdir, t0)
    nonsub, nontype = rows_of(classes, inds, ans)
    nrows_sub = sum(len(v) for v in nonsub.values())
    nrows_sat = len(nonsub)
    nrows_type = sum(len(v) for v in nontype.values())
    R['classes'], R['individuals'] = len(classes), len(inds)
    R['rows'] = {'consistency': 1, 'sat': nrows_sat, 'nonsub': nrows_sub, 'nontype': nrows_type}
    nbidx = {}
    for B in classes:
        nbidx.setdefault(B, len(nbidx))
    As = list(nonsub)
    wall = int(a_[a_.index('--wall') + 1]) if '--wall' in a_ else 1200
    text = open(src).read()
    cert = {'consistency': 0, 'sat': 0, 'nonsub': 0, 'nontype': 0}
    R['stages'] = []
    R['unresolved'] = []
    budget = {'max_nodes': 300000, 'max_close': 300000}
    tag = [0]

    def attempt(groups, nt, st):
        """One witness: dump, produce, check. Returns (status, N, part)."""
        i = tag[0]
        tag[0] += 1
        wpath = os.path.join(outdir, 'w%d.ofn' % i)
        open(wpath, 'w').write(witness_text(text, groups, nt, nbidx))
        nfpath = os.path.join(outdir, 'w%d.nf' % i)
        st['dump'] = dump_nf(wpath, nfpath, T)
        if st['dump']['rc'] != 0:
            return 'dump-failed', None
        hpath = os.path.join(outdir, 'w%d.hint' % i)
        fr, N, ix = find_hint(nfpath, hpath, budget)
        types = fr.pop('_types', None)
        st['producer'] = fr
        if fr['status'] != 'hint':
            return fr['status'], N
        # readout: named classes outside the type of each x_j and named individual
        ro = 0
        if types is not None:
            for j, (A, Bs) in enumerate(groups):
                nu = N.nominal.get(XP + str(j))
                t = next((t for t in types if nu in t), None)
                if t is not None:
                    ro += sum(1 for B in nonsub[A] if N.cname.get(B) not in t)
            if cur_ci[0] == 0:
                for a, Cs in nontype.items():
                    nu = N.nominal.get(a)
                    t = next((t for t in types if nu in t), None)
                    if t is not None:
                        ro += sum(1 for C in Cs if N.cname.get(C) not in t)
        st['readout_rows'] = ro
        form = fr.get('form')
        st['checker'] = check(wpath, hpath, T if form != 'certificate' or not fr.get('recs') else 60)
        return ('certified' if st['checker']['accepted'] else 'checker-rejected-or-slow'), N

    def credit(groups, nt):
        cert['consistency'] = 1
        for (A, Bs) in groups:
            if A not in credited_sat:
                credited_sat.add(A)
                cert['sat'] += 1
            cert['nonsub'] += len(Bs)
        cert['nontype'] += sum(len(v) for v in nt.values())
    credited_sat = set()
    mirror = {'rows': 0, 'readout': 0}
    R['mirror_only'] = mirror

    # chunks of classes; the size adapts to keep the flat core near 300 elements
    rowcap = int(a_[a_.index('--row-cap') + 1]) if '--row-cap' in a_ else 30000
    readout = nrows_sub + nrows_type > rowcap
    R['mode'] = 'readout' if readout else 'witness'
    cur_ci = [0]
    cs = chunk or 40
    pos, ci = 0, 0
    R['chunk_sizes'] = []
    while pos < len(As) or ci == 0:
        if time.time() - t0 > wall:
            R['stopped'] = 'wall budget after %d of %d classes' % (pos, len(As))
            break
        ch = As[pos:pos + cs]
        pos += len(ch)
        R['chunk_sizes'].append(len(ch))
        cur_ci[0] = ci
        if readout:
            groups = [(A, []) for A in ch]
            nt = {}
        else:
            groups = [(A, nonsub[A]) for A in ch]
            nt = dict(nontype) if ci == 0 else {}
        for rnd in range(4):
            st = {'chunk': ci, 'round': rnd, 'xs': len(groups),
                  'pairs': sum(len(b) for _, b in groups) + sum(len(v) for v in nt.values())}
            status, N = attempt(groups, nt, st)
            st['status'] = status
            R['stages'].append(st)
            if status == 'checker-rejected-or-slow':
                mirror['rows'] += sum(len(b) for _, b in groups) + sum(len(v) for v in nt.values()) + \
                    len([A for A, _ in groups if A not in credited_sat])
                mirror['readout'] += st.get('readout_rows', 0)
                break
            if status == 'certified':
                credit(groups, nt)
                if readout:
                    R['readout_rows'] = R.get('readout_rows', 0) + st.get('readout_rows', 0)
                break
            if status != 'no-model' or N is None:
                break
            # localise in normal-form space: which NB assertions can stay
            t1 = time.time()
            loc = localize(N, groups, nt, nbidx, budget, deadline=t1 + T)
            st['localize'] = {'secs': round(time.time() - t1, 1), 'runs': loc['runs'],
                              'status': loc['status']}
            if loc['status'] != 'ok':
                break
            accG, accN, leftG, leftN = loc['acc_groups'], loc['acc_nt'], loc['left_groups'], loc['left_nt']
            st2 = {'chunk': ci, 'round': rnd, 'kind': 'accepted-part', 'xs': len(accG),
                   'pairs': sum(len(b) for _, b in accG) + sum(len(v) for v in accN.values())}
            status2, _ = attempt(accG, accN, st2)
            st2['status'] = status2
            R['stages'].append(st2)
            if status2 == 'certified':
                credit(accG, accN)
            if not leftG and not leftN:
                break
            if (leftG, leftN) == (groups, nt):
                break
            groups, nt = leftG, leftN
        else:
            pass
        cores = [x.get('producer', {}).get('core') for x in R['stages'] if x.get('chunk') == ci]
        cores = [c for c in cores if c]
        if cores and not chunk:
            per = max(cores) / max(1, len(ch))
            cs = max(5, min(400, int(300 / max(per, 0.5))))
            if any(x.get('checker', {}).get('rc') == 124 for x in R['stages'] if x.get('chunk') == ci):
                cs = max(2, len(ch) // 4)
        ci += 1
        if groups and status != 'certified':
            R['unresolved'].append({'chunk': ci, 'groups': [[A, len(B)] for A, B in groups][:20],
                                    'nontype': {a: len(c) for a, c in list(nt.items())[:20]}})
    R['certified'] = cert
    tot = sum(R['rows'].values())
    got = sum(cert.values())
    R['status'] = 'full' if got == tot else ('partial' if got else 'none')
    return finish(R, outdir, t0)


def finish(R, outdir, t0):
    R['wall'] = round(time.time() - t0, 1)
    with open(os.path.join(outdir, 'result.json'), 'w') as f:
        json.dump(R, f)
    print(json.dumps(R))


if __name__ == '__main__':
    main()
