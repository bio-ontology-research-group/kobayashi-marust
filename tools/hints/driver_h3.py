#!/usr/bin/env python3
"""Stage H3 driver: km answers -> checker normal form -> one global model
(the Rust producer `tools/hints-rs`) -> proved checker.

    driver_h3.py ONTOLOGY OUTDIR [--ptime S] [--checks N] [--check-timeout S]
                 [--check-budget S] [--max-concepts N]

Steps, each timed with /usr/bin/time:
  1. km classify --lines --realize --top (KM_THREADS=1, 300 s)
  2. km-owl-reference --procedure sroiq-hint --print-index / --print-clauses
  3. km-hints produce (self-checks every model; its counts are "unchecked")
  4. the proved checker on the producer's models, with the per-row routes of
     today's binary (until the H2 witness row exists): row `consistent` with
     model 0 as the hint, then up to N `nonsubs A owl:Nothing B1 ... Bk`
     rows (the B's the witness of A leaves out) and `nontypes a C1 ...`
     rows, each through `km-hints rowhint` (the model renamed to the row's
     normal form). A row counts as certified only when the checker printed
     `"certified":true` for it in this run.

With H3_WITNESS=1 and a checker that supports `--witness TABLE`, step 4
uses the global witness row instead (format to follow H2).
"""
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SCR = os.environ.get('H3_SCR', '/mnt/data1/leechuck/km-work/v170/scratch/h3')
KM = os.environ.get('H3_KM', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-6f2c0a8e')
REF = os.environ.get('H3_REF', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-owl-reference-c5')
PROD = os.environ.get('H3_PROD', os.path.join(SCR, 'target/release/km-hints'))
THING = 'http://www.w3.org/2002/07/owl#Thing'
NOTHING = 'http://www.w3.org/2002/07/owl#Nothing'
TMP = os.path.join(SCR, 'tmp')


def run(cmd, timeout, out=None, mem_kb=None):
    """(rc, secs, maxrss_mb, stdout, stderr) under /usr/bin/time and timeout."""
    tf = os.path.join(TMP, 'time.%d' % os.getpid())
    e = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    e['KM_THREADS'] = '1'
    e['TMPDIR'] = TMP
    full = ['/usr/bin/time', '-f', '%e %M', '-o', tf, 'timeout', str(timeout)] + cmd
    if mem_kb:
        full = ['bash', '-c', 'ulimit -v %d; exec "$@"' % mem_kb, 'x'] + full
    fo = open(out, 'w') if out else subprocess.PIPE
    p = subprocess.run(full, stdout=fo, stderr=subprocess.PIPE, env=e, text=True)
    if out:
        fo.close()
    try:
        w = open(tf).read().split('\n')
        last = [l for l in w if re.match(r'^[0-9.]+ [0-9]+$', l)][-1].split()
        secs, rss = float(last[0]), int(last[1]) // 1024
    except Exception:
        secs, rss = None, None
    return p.returncode, secs, rss, (None if out else p.stdout), p.stderr


def clean_km_tmp():
    for f in os.listdir(TMP):
        m = re.match(r'^km-(?:run-)?(\d+)-', f)
        if m:
            try:
                os.kill(int(m.group(1)), 0)
            except OSError:
                subprocess.run(['rm', '-rf', os.path.join(TMP, f)])


def ref(args, src, timeout, out=None):
    return run([REF, '--procedure', 'sroiq-hint'] + args + [src], timeout, out=out, mem_kb=16000000)


def read_hint_types(path):
    ty = {}
    with open(path) as f:
        for line in f:
            if line.startswith('ty '):
                w = line.split()
                ty[int(w[1])] = set(int(x) for x in w[2:])
    return ty


def read_table(path):
    rows = []
    if not os.path.exists(path):
        return rows
    with open(path) as f:
        for line in f:
            w = line.rstrip('\n').split(' ')
            if len(w) == 3:
                rows.append((w[0], w[1], int(w[2])))
    return rows


def km_rows(km_path, idx_path):
    """km's negative rows over the route's signature (as driver5.rows_of)."""
    sup, unsat, types, top = {}, set(), {}, {THING}
    for line in open(km_path):
        w = line.rstrip('\n').split('\t')
        if w[0] == 'SUB':
            sup.setdefault(w[1], set()).add(w[2])
        elif w[0] == 'UNSAT':
            unsat.add(w[1])
        elif w[0] == 'TYPE':
            types.setdefault(w[1], set()).add(w[2])
        elif w[0] == 'TOP':
            top.add(w[1])
    cname, inds = {}, []
    for line in open(idx_path):
        w = line.rstrip('\n').split(' ', 2)
        if len(w) == 3 and w[0] == 'concept' and not w[2].startswith('urn:km:'):
            cname[w[2]] = int(w[1])
        elif len(w) == 3 and w[0] == 'nominal' and not w[2].startswith('urn:km:') and not w[2].startswith('#'):
            inds.append(w[2])
    cls = [c for c in cname if c not in (THING, NOTHING)]
    return sup, unsat, types, top, cname, cls, inds


def main():
    a = sys.argv[1:]
    src, outdir = a[0], a[1]

    def opt(k, d):
        return type(d)(a[a.index(k) + 1]) if k in a else d
    ptime = opt('--ptime', 300)
    nchecks = opt('--checks', 20)
    ctime = opt('--check-timeout', 60)
    cbudget = opt('--check-budget', 300)
    maxc = opt('--max-concepts', 5000)
    os.makedirs(outdir, exist_ok=True)
    t0 = time.time()
    R = {'input': os.path.basename(src).rsplit('.', 1)[0], 'bytes': os.path.getsize(src)}
    kl = os.path.join(outdir, 'km.lines')
    rc, s, m, _, err = run([KM, 'classify', '--lines', '--realize', '--top', src], 300, out=kl)
    clean_km_tmp()
    R['km'] = {'rc': rc, 'secs': s, 'rss_mb': m}
    if rc != 0:
        R['status'] = 'km-failed'
        R['km']['err'] = (err or '')[-200:]
        return finish(R, outdir, t0)
    cons = None
    for line in open(kl):
        if line.startswith('CONSISTENT'):
            cons = line.split()[-1] == '1'
    if cons is False:
        R['status'] = 'km-inconsistent'
        return finish(R, outdir, t0)
    bi, bc = os.path.join(outdir, 'base.idx'), os.path.join(outdir, 'base.cl')
    rc1, s1, m1, _, e1 = ref(['--print-index'], src, 300, out=bi)
    rc2, s2, m2, _, e2 = (None, None, None, None, None)
    if rc1 == 0:
        rc2, s2, m2, _, e2 = ref(['--print-clauses'], src, 300, out=bc)
    R['dump'] = {'rc': rc2 if rc1 == 0 else rc1, 'secs': round((s1 or 0) + (s2 or 0), 2), 'rss_mb': max(m1 or 0, m2 or 0)}
    if rc1 != 0 or rc2 != 0:
        R['status'] = 'dump-failed'
        R['dump']['err'] = ((e1 or '') + (e2 or ''))[-200:]
        return finish(R, outdir, t0)
    R['dump']['bytes'] = os.path.getsize(bi) + os.path.getsize(bc)
    rc, s, m, out, err = run([PROD, 'produce', '--index', bi, '--clauses', bc, '--km', kl, '--out', outdir,
                              '--time', str(ptime)], ptime + 120, mem_kb=24000000)
    R['producer_run'] = {'rc': rc, 'secs': s, 'rss_mb': m}
    if rc != 0 or not out:
        R['status'] = 'producer-failed'
        R['producer_run']['err'] = (err or '')[-300:]
        return finish(R, outdir, t0)
    P = json.loads(out)
    R['producer'] = P
    tot = P['rows']
    unc = P['unchecked']
    R['rows_total'] = 1 + tot['sat'] + tot['nonsub'] + tot['nontype']
    R['rows_unchecked'] = unc['consistency'] + unc['sat'] + unc['nonsub'] + unc['nontype']
    R['status'] = ('model-full' if R['rows_unchecked'] == R['rows_total'] else
                   'model-partial' if R['rows_unchecked'] else 'model-none')
    # ---- the proved checker ----
    C = {'calls': 0, 'secs': 0.0, 'results': {}, 'certified': {'consistency': 0, 'sat': 0, 'nonsub': 0, 'nontype': 0},
         'rows_tried': {'consistency': 0, 'sat': 0, 'nonsub': 0, 'nontype': 0}}
    R['checker'] = C
    h0 = os.path.join(outdir, 'model0.hint')
    if not P['base']['ok'] or not os.path.exists(h0) or P['models'][0]['violations'] != 0:
        C['skipped'] = 'no self-checked model 0'
        return finish(R, outdir, t0)
    if '--no-check' in a:
        C['skipped'] = 'not requested'
        return finish(R, outdir, t0)
    if P['nf']['concepts'] > maxc:
        C['skipped'] = 'over %d concepts (checker time grows with the names, R1)' % maxc
        return finish(R, outdir, t0)
    tc = time.time()
    bad = [0]

    def check(row, hint):
        if bad[0] >= 3 or time.time() - tc > cbudget:
            return 'skipped'
        args = (['--row', row] if row != 'consistent' else []) + ['--hint', hint]
        rc, s, m, out, err = ref(args, src, ctime)
        C['calls'] += 1
        C['secs'] += s or 0
        C['rss_mb'] = max(C.get('rss_mb', 0), m or 0)
        if rc == 0 and '"certified":true' in (out or ''):
            res = 'certified'
            bad[0] = 0
        elif rc == 124:
            res = 'timeout'
            bad[0] += 1
        elif 'out of memory' in (err or '') or rc in (134, 137, 139) or 'memory' in (err or ''):
            res = 'out of memory'
            bad[0] += 1
        else:
            res = 'rejected'
            C.setdefault('reject_examples', []).append((row[:120], (err or '').strip()[-160:]))
        C['results'][res] = C['results'].get(res, 0) + 1
        return res
    C['rows_tried']['consistency'] = 1
    if check('consistent', h0) == 'certified':
        C['certified']['consistency'] = 1
    # rows from the witnesses: per class, the non-subsumers its first witness leaves out
    sup, unsat, types, top, cname, cls, inds = km_rows(kl, bi)
    tabs, tys = [], []
    k = 0
    while os.path.exists(os.path.join(outdir, 'model%d.hint' % k)):
        tabs.append(read_table(os.path.join(outdir, 'model%d.wit' % k)))
        tys.append(read_hint_types(os.path.join(outdir, 'model%d.hint' % k)))
        k += 1
    first = {}
    for mk, tab in enumerate(tabs):
        for kind, iri, e in tab:
            if kind == 'class' and iri not in first and P['models'][mk]['violations'] == 0:
                first[iri] = (mk, e)
    ind_el = {iri: e for kind, iri, e in tabs[0] if kind == 'individual'} if tabs else {}
    jobs = []
    for A in [THING] + cls:
        if A in unsat or A not in first:
            continue
        mk, e = first[A]
        t = tys[mk].get(e, set())
        s = sup.get(A, set())
        Bs = [B for B in cls if B != A and B not in s and B not in top and cname[B] not in t]
        jobs.append(('nonsubs', A, Bs[:300]))
    for x in inds:
        if x not in ind_el:
            continue
        t = tys[0].get(ind_el[x], set())
        ty = types.get(x, set())
        Cs = [c for c in cls if c not in ty and c not in top and cname[c] not in t]
        if Cs:
            jobs.append(('nontypes', x, Cs[:300]))
    # spread the sample over classes and individuals
    step = max(1, len(jobs) // max(1, nchecks))
    sample = jobs[::step][:nchecks]
    for i, (kind, key, Ls) in enumerate(sample):
        if bad[0] >= 3 or time.time() - tc > cbudget:
            C['stopped'] = 'check budget or three timeouts after %d of %d sampled rows' % (i, len(sample))
            break
        if kind == 'nonsubs':
            row = ' '.join(['nonsubs', key, NOTHING] + Ls)
        else:
            row = ' '.join(['nontypes', key] + Ls)
        ri, rcl, rh = (os.path.join(outdir, 'row.idx'), os.path.join(outdir, 'row.cl'), os.path.join(outdir, 'row.hint'))
        rc1, _, _, _, _ = ref(['--print-index', '--row', row], src, ctime, out=ri)
        rc2, _, _, _, _ = ref(['--print-clauses', '--row', row], src, ctime, out=rcl) if rc1 == 0 else (1, 0, 0, 0, 0)
        if rc1 != 0 or rc2 != 0:
            C['results']['row dump failed'] = C['results'].get('row dump failed', 0) + 1
            continue
        sel = ['--class', key] if kind == 'nonsubs' else ['--individual', key]
        rc, s, m, out, err = run([PROD, 'rowhint', '--index', bi, '--clauses', bc, '--km', kl, '--row-index', ri,
                                  '--row-clauses', rcl, '--out', rh, '--time', str(ptime)] + sel, ptime + 60)
        if rc != 0:
            why = (out or err or '').strip()[-120:]
            C['results']['rowhint failed'] = C['results'].get('rowhint failed', 0) + 1
            C.setdefault('rowhint_fail', []).append((key[:100], why))
            continue
        res = check(row, rh)
        kk = 'nonsub' if kind == 'nonsubs' else 'nontype'
        C['rows_tried'][kk] += len(Ls)
        if kind == 'nonsubs':
            C['rows_tried']['sat'] += 1
        if res == 'certified':
            C['certified'][kk] += len(Ls)
            if kind == 'nonsubs':
                C['certified']['sat'] += 1
    C['secs'] = round(C['secs'], 2)
    for f in ('row.idx', 'row.cl', 'row.hint'):
        p = os.path.join(outdir, f)
        if os.path.exists(p):
            os.remove(p)
    return finish(R, outdir, t0)


def finish(R, outdir, t0):
    R['wall'] = round(time.time() - t0, 1)
    with open(os.path.join(outdir, 'result.json'), 'w') as f:
        json.dump(R, f)
    print(json.dumps({k: R.get(k) for k in ('input', 'status', 'rows_total', 'rows_unchecked', 'wall')}))


if __name__ == '__main__':
    main()
