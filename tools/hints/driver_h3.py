#!/usr/bin/env python3
"""Stage H3 driver: km answers -> checker normal form -> one global model
(the Rust producer `tools/hints-rs`) -> proved checker (H2 witness row).

    driver_h3.py ONTOLOGY OUTDIR [--ptime S] [--check-timeout S] [--no-check]

Steps, each timed with /usr/bin/time:
  1. km classify --lines --realize --top (KM_THREADS=1, 300 s)
  2. km-owl-reference --procedure sroiq-hint --witness-route --print-index /
     --print-clauses (the classes of the ontology requested)
  3. km-hints produce (self-checks every model; its counts are "unchecked")
  4. per model k: --witness model<k>.wit --hint model<k>.hint --out
     check<k>.jsonl. A row counts as certified only when the checker printed
     it in this run: consistency, sat(A) for every class line without an
     error, each km non-subsumption (A, B) with B outside A's witness type,
     each km non-type (a, C) with C outside a's element type (union over the
     models). A proved row that km answers positively is a disagreement.
  `km-hints rowhint` (rowmap.rs) still maps a model to a per-row normal form
  of the plain route, for the per-row checks of earlier binaries.
"""
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SCR = os.environ.get('H3_SCR', '/mnt/data1/leechuck/km-work/v170/scratch/h3')
KM = os.environ.get('H3_KM', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-f2eb0196')
KM_EXP = os.environ.get('H3_KM_EXP', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-7061a272')
REF = os.environ.get('H3_REF', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-owl-reference-h6-9873d697')
PROD = os.environ.get('H3_PROD', os.path.join(SCR, 'target/release/km-hints'))
THING = 'http://www.w3.org/2002/07/owl#Thing'
NOTHING = 'http://www.w3.org/2002/07/owl#Nothing'
TMP = os.path.join(SCR, 'tmp')
MAX_KEEP_BYTES = 50 * 1024 * 1024


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
            if w[1] == THING:
                top.add(w[2])
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
    ctime = opt('--check-timeout', 600)
    # a running sweep can be given a lower checker timeout through a file
    ov = os.path.join(SCR, 'check_timeout')
    if os.path.exists(ov):
        ctime = min(ctime, int(open(ov).read().strip()))
    cbudget = opt('--check-budget', 300)
    maxc = opt('--max-concepts', 5000)
    os.makedirs(outdir, exist_ok=True)
    t0 = time.time()
    R = {'input': os.path.basename(src).rsplit('.', 1)[0], 'bytes': os.path.getsize(src)}
    kl = os.path.join(outdir, 'km.lines')
    bi, bc = os.path.join(outdir, 'base.idx'), os.path.join(outdir, 'base.cl')
    cf = os.path.join(outdir, 'classes.txt')
    old_res_path = os.path.join(outdir, 'result.json')
    old_R = {}
    if '--fresh' not in a and os.path.exists(old_res_path):
        try:
            old_R = json.load(open(old_res_path))
        except Exception:
            old_R = {}
    if (old_R.get('km', {}).get('rc') == 0 and os.path.exists(kl) and os.path.getsize(kl) > 0
            and ('--no-realize' not in a or old_R.get('km', {}).get('realized') is False)):
        R['km'] = old_R['km']
        if 'km_realize' in old_R:
            R['km_realize'] = old_R['km_realize']
    elif '--no-realize' in a:
        if 'km_realize' in old_R:
            R['km_realize'] = old_R['km_realize']
        elif old_R.get('status') == 'km-failed' and 'km' in old_R:
            R['km_realize'] = old_R['km']
        rc, s, m, _, err = run([KM, 'classify', '--lines', '--top', src], 120, out=kl)
        clean_km_tmp()
        if rc != 0:
            rc, s, m, _, err = run([KM, 'classify', '--lines', src], 240, out=kl)
            clean_km_tmp()
        R['km'] = {'rc': rc, 'secs': s, 'rss_mb': m, 'realized': False}
        if rc != 0:
            R['status'] = 'km-failed'
            R['km']['err'] = (err or '')[-200:]
            return finish(R, outdir, t0)
    else:
        rc, s, m, _, err = run([KM, 'classify', '--lines', '--realize', '--top', src], 300, out=kl)
        clean_km_tmp()
        if rc == 0:
            R['km'] = {'rc': 0, 'secs': s, 'rss_mb': m, 'realized': True}
        else:
            R['km_realize'] = {'rc': rc, 'secs': s, 'rss_mb': m, 'err': (err or '')[-200:]}
            rc2, s2, m2, _, err2 = run([KM, 'classify', '--lines', '--top', src], 120, out=kl)
            clean_km_tmp()
            if rc2 != 0:
                rc2, s2, m2, _, err2 = run([KM, 'classify', '--lines', src], 240, out=kl)
                clean_km_tmp()
            R['km'] = {'rc': rc2, 'secs': s2, 'rss_mb': m2, 'realized': False, 'realize_timeout_secs': s}
            if rc2 != 0:
                R['status'] = 'km-failed'
                R['km']['err'] = (err2 or '')[-200:]
                return finish(R, outdir, t0)
    realized = R['km'].get('realized', True) is not False
    cons = None
    for line in open(kl):
        if line.startswith('CONSISTENT'):
            cons = line.split()[-1] == '1'
    if cons is False:
        R['status'] = 'km-inconsistent'
        return finish(R, outdir, t0)
    if (old_R.get('dump', {}).get('rc') == 0 and os.path.exists(bi) and os.path.getsize(bi) > 0
            and os.path.exists(bc) and os.path.getsize(bc) > 0 and os.path.exists(cf)
            and 'route' in old_R):
        R['dump'] = old_R['dump']
        R['route'] = old_R['route']
        o0 = R['route']
    else:
        # the witness route's translation, every class of the ontology requested
        rc1, s1, m1, _, e1 = ref(['--witness-route', '--print-index'], src, 300, out=bi)
        rc2, s2, m2, _, e2 = (None, None, None, None, None)
        s0 = 0
        if rc1 == 0:
            names = [l.split(' ', 2)[2].rstrip('\n') for l in open(bi) if l.startswith('concept ') and
                     len(l.split(' ', 2)) == 3 and not l.split(' ', 2)[2].startswith('urn:km:')]
            # owl:Thing and owl:Nothing listed: the route prints the owl:Thing row and
            # owl:Nothing in every list (satisfiability); they do not shift the indices
            add = [x for x in (THING, NOTHING) if x not in names]
            with open(cf, 'w') as f:
                f.write('\n'.join(names + add) + '\n')
        if rc1 == 0:
            extra = ['--classes', cf] if os.path.exists(cf) else []
            rc2, s2, m2, _, e2 = ref(['--witness-route'] + extra + ['--print-clauses'], src, 300, out=bc)
        R['dump'] = {'rc': rc2 if rc1 == 0 else rc1, 'secs': round((s1 or 0) + (s2 or 0), 2), 'rss_mb': max(m1 or 0, m2 or 0)}
        if rc1 != 0 or rc2 != 0:
            R['status'] = 'dump-failed'
            R['dump']['err'] = ((e1 or '') + (e2 or ''))[-200:]
            return finish(R, outdir, t0)
        R['dump']['bytes'] = os.path.getsize(bi) + os.path.getsize(bc)
        # the Self routes allow a loop only at a nominal element: no loops then
        o0 = None
        cpath = os.path.join(HERE, '../c3-census/census-h2-witness.tsv')
        if os.path.exists(cpath):
            for line in open(cpath):
                w = line.rstrip('\n').split('\t')
                if len(w) >= 3 and w[0] == R['input'] and w[2].startswith('accepted '):
                    o0 = ' '.join(w[2].split()[:2])
                    break
        if not o0:
            rc0, _, _, o0, _ = ref(['--witness-route', '--classes', cf, '--check'], src, 300)
        R['route'] = (o0 or '').strip()[-40:]
    loops = [] if 'self' not in (o0 or '') else ['--no-loops']
    prod_flags = list(loops) + ([] if realized else ['--no-realize'])
    old_P = old_R.get('producer', {})
    old_models = old_P.get('models', [])
    if ('--recheck' in a and old_R.get('status') in ('model-full', 'model-partial') and old_models and
            all(os.path.exists(os.path.join(outdir, f'model{m["model"]}.hint')) and
                os.path.exists(os.path.join(outdir, f'model{m["model"]}.wit')) for m in old_models)):
        R['producer_run'] = old_R.get('producer_run', {'rc': 0, 'secs': 0.0, 'rss_mb': 0})
        P = old_P
        R['producer'] = P
    else:
        for fn in os.listdir(outdir):
            if re.match(r'^(?:model\d+\.(?:hint|wit)|check\d+\.jsonl)$', fn):
                try:
                    os.remove(os.path.join(outdir, fn))
                except OSError:
                    pass
        rc, s, m, out, err = run([PROD, 'produce'] + prod_flags + ['--index', bi, '--clauses', bc, '--km', kl, '--out', outdir,
                                  '--time', str(ptime)], ptime + 120, mem_kb=8000000)
        R['producer_run'] = {'rc': rc, 'secs': s, 'rss_mb': m}
        if rc != 0 or not out:
            err_s = (err or '')[-300:]
            if 'memory' in err_s.lower() or 'allocation' in err_s.lower() or rc in (134, 137, 139) or (m or 0) >= 7500:
                R['status'] = 'producer-memout'
                R['producer_run']['reason'] = 'memory cap (8 GB)'
            else:
                R['status'] = 'producer-failed'
            R['producer_run']['err'] = err_s
            P = {'base': {'ok': False, 'why': err_s, 'secs': 0.0}, 'models': [], 'rows': {'consistency': 1, 'sat': 0, 'nonsub': 0, 'nontype': 0}, 'unchecked': {'consistency': 0, 'sat': 0, 'nonsub': 0, 'nontype': 0}}
            R['producer'] = P
        else:
            P = json.loads(out)
            R['producer'] = P
    sup, unsat, types, top, cname, cls, inds = km_rows(kl, bi)
    clsset = set(cls)
    nc = len(cls)
    tot = P['rows']
    unc_p = P['unchecked']
    if tot['sat'] == 0 and cls:
        # fallback if producer failed before computing row totals
        sat_cnt = sum(1 for A in [THING] + cls if A not in unsat)
        nsub_cnt = sum(nc - len([B for B in (sup.get(A, set()) | top | {A}) if B in clsset]) for A in [THING] + cls if A not in unsat)
        nt_cnt = 0 if not realized else sum(nc - len([c for c in (types.get(x, set()) | top) if c in clsset]) for x in inds)
        tot = {'consistency': 1, 'sat': sat_cnt, 'nonsub': nsub_cnt, 'nontype': nt_cnt}
        P['rows'] = tot
    R['rows_total'] = 1 + tot['sat'] + tot['nonsub'] + (tot['nontype'] if realized else 0)
    R['rows_unchecked'] = unc_p['consistency'] + unc_p['sat'] + unc_p['nonsub'] + (unc_p['nontype'] if realized else 0)
    if R.get('status') not in ('producer-memout', 'producer-failed'):
        R['status'] = ('model-full' if R['rows_unchecked'] == R['rows_total'] else
                       'model-partial' if R['rows_unchecked'] else 'model-none')
    # ---- the proved checker: the global witness row (H2), one call per model ----
    C = {'calls': 0, 'secs': 0.0, 'results': {}, 'certified': {'consistency': 0, 'sat': 0, 'nonsub': 0, 'nontype': 0}}
    R['checker'] = C
    if '--no-check' in a:
        C['skipped'] = 'not requested'
        return finish(R, outdir, t0)
    extra = ['--classes', cf] if os.path.exists(cf) else []
    unc = {}      # class -> uncovered km-negative B's (None: all still uncovered)
    satok = set()
    indunc = {}
    disagree = []

    def absorb_check_jsonl(op_path):
        for line in open(op_path):
            try:
                J = json.loads(line)
            except Exception:
                continue
            if J.get('consistent') is True:
                C['certified']['consistency'] = 1
            if 'class' in J and 'error' not in J:
                A = J['class']
                if NOTHING not in J.get('nonsub_except', [NOTHING]) or NOTHING in J.get('nonsub', []):
                    satok.add(A)
                sA = sup.get(A, set())
                if 'nonsub_except' in J:
                    inside = set(J['nonsub_except'])
                    bad = [B for B in sA if B in clsset and B not in inside]
                    cur = {B for B in inside if B in clsset and B != A and B not in sA and B not in top}
                    unc[A] = cur if unc.get(A) is None else (unc[A] & cur)
                else:
                    outside = set(J.get('nonsub', []))
                    bad = [B for B in sA if B in outside]
                    if unc.get(A) is None:
                        unc[A] = {B for B in cls if B != A and B not in sA and B not in top and B not in outside}
                    else:
                        unc[A] -= outside
                for B in bad[:3]:
                    disagree.append('proved %s not under %s; km lists the subsumption' % (A, B))
            elif 'class' in J:
                C.setdefault('table_errors', []).append(J)
            if 'individual' in J:
                x = J['individual']
                tx = types.get(x, set()) if realized else set()
                if 'nontype_except' in J:
                    inside = set(J['nontype_except'])
                    bad = [c for c in tx if c in clsset and c not in inside] if realized else []
                    cur = {c for c in inside if c in clsset and c not in tx and c not in top}
                else:
                    outside = set(J.get('nontype', []))
                    bad = [c for c in tx if c in outside] if realized else []
                    cur = {c for c in cls if c not in tx and c not in top and c not in outside}
                indunc[x] = cur if x not in indunc else (indunc[x] & cur)
                for c in bad[:3]:
                    disagree.append('proved %s not in %s; km lists the type' % (x, c))

    def recompute_certified():
        C['certified'] = {'consistency': C['certified'].get('consistency', 0), 'sat': 0, 'nonsub': 0, 'nontype': 0}
        for A in [THING] + cls:
            if A in unsat:
                continue
            if A in satok or (A == THING and C['certified']['consistency']):
                C['certified']['sat'] += 1
            if A in satok:
                sA = sup.get(A, set())
                nonsub = nc - len([B for B in (sA | top | {A}) if B in clsset])
                C['certified']['nonsub'] += nonsub - len(unc.get(A) or ())
        if realized:
            for x in inds:
                if x in indunc:
                    tx = types.get(x, set())
                    nontype = nc - len([c for c in (tx | top) if c in clsset])
                    C['certified']['nontype'] += nontype - len(indunc[x])
        else:
            sep_out = 0
            for x in inds:
                if x in indunc:
                    nontype = nc - len([c for c in top if c in clsset])
                    sep_out += nontype - len(indunc[x])
            R['nontype_separate'] = {
                'individuals': len(inds),
                'pairs': len(inds) * nc,
                'certified_outside': sep_out,
            }
        C['certified_rows'] = sum(C['certified'].values())

    if P.get('base', {}).get('ok') and P.get('models') and max(m['elements'] for m in P['models']) > 0:
        est = max(m['elements'] for m in P['models']) * max(1, P.get('nf', {}).get('gci', 1))
        C['cost_estimate'] = est
        if est > float(os.environ.get('H3_MAX_CHECK_COST', '1e13')):
            C['skipped'] = 'over the checker budget (elements x gcis = %.1e)' % est
        else:
            k = 0
            while k < len(P['models']) and os.path.exists(os.path.join(outdir, 'model%d.hint' % k)):
                if P['models'][k]['violations'] != 0 or P['models'][k]['elements'] == 0:
                    k += 1
                    continue
                hp, wp = os.path.join(outdir, 'model%d.hint' % k), os.path.join(outdir, 'model%d.wit' % k)
                op = os.path.join(outdir, 'check%d.jsonl' % k)
                for _ in range(3):
                    rc, sec, mem, out, err = ref(['--witness', wp, '--hint', hp, '--out', op] + extra, src, ctime)
                    if 'failed to create thread' not in (err or ''):
                        break
                    time.sleep(20)
                C['calls'] += 1
                C['secs'] += sec or 0
                C['rss_mb'] = max(C.get('rss_mb', 0), mem or 0)
                if rc == 124:
                    res = 'timeout'
                elif rc != 0 and ('memory' in (err or '') or rc in (134, 137, 139)):
                    res = 'out of memory'
                elif rc != 0:
                    res = 'rejected'
                    rc3, _, _, out3, err3 = ref(['--witness', wp, '--hint', hp, '--explain'] + extra, src, ctime)
                    C.setdefault('reject_examples', []).append((k, ((err or '') + ' | ' + (err3 or '') + (out3 or '')).strip()[-400:]))
                else:
                    res = 'certified'
                C['results'][res] = C['results'].get(res, 0) + 1
                if res == 'certified' and os.path.exists(op):
                    absorb_check_jsonl(op)
                try:
                    if os.path.exists(hp) and os.path.getsize(hp) > MAX_KEEP_BYTES:
                        os.remove(hp)
                    if os.path.exists(op) and os.path.getsize(op) > MAX_KEEP_BYTES:
                        os.remove(op)
                except OSError:
                    pass
                k += 1
    else:
        C['skipped'] = 'no model'

    recompute_certified()
    search_cert_rows = C['certified_rows']

    # Try `--export-model` fallback when search did not achieve `certified-full` (or `--try-export` requested)
    if (C['certified_rows'] < R['rows_total'] or '--try-export' in a) and '--no-export' not in a and os.path.exists(KM_EXP):
        exp_dir = os.path.join(outdir, 'export_try')
        os.makedirs(exp_dir, exist_ok=True)
        exp_jsonl = os.path.join(exp_dir, 'export.jsonl')
        exp_kl = os.path.join(exp_dir, 'km_exp.lines')
        rc_e, s_e, m_e, _, err_e = run([KM_EXP, 'classify', '--lines', '--export-model', exp_jsonl, src], 180, out=exp_kl)
        clean_km_tmp()
        try:
            if os.path.exists(exp_kl):
                os.remove(exp_kl)
        except OSError:
            pass
        exp_info = {'km_rc': rc_e, 'km_secs': s_e, 'km_rss_mb': m_e}
        if rc_e == 0 and os.path.exists(exp_jsonl) and os.path.getsize(exp_jsonl) > 0:
            rc_fe, s_fe, m_fe, out_fe, err_fe = run(
                [PROD, 'from-export'] + loops + ['--index', bi, '--clauses', bc, '--km', kl, '--export', exp_jsonl, '--out', exp_dir, '--time', str(min(ptime, 180))],
                min(ptime, 180) + 60,
                mem_kb=8000000,
            )
            exp_info['prod_rc'] = rc_fe
            exp_info['prod_secs'] = s_fe
            exp_info['prod_rss_mb'] = m_fe
            if rc_fe == 0 and out_fe:
                try:
                    J_fe = json.loads(out_fe)
                except Exception:
                    J_fe = {}
                exp_info['producer'] = J_fe
                ehp = os.path.join(exp_dir, 'model0.hint')
                ewp = os.path.join(exp_dir, 'model0.wit')
                eop = os.path.join(exp_dir, 'check0.jsonl')
                if J_fe.get('ok') and J_fe.get('violations', 1) == 0 and os.path.exists(ehp) and os.path.exists(ewp):
                    for _ in range(3):
                        rc_c, sec_c, mem_c, _, err_c = ref(['--witness', ewp, '--hint', ehp, '--out', eop] + extra, src, ctime)
                        if 'failed to create thread' not in (err_c or ''):
                            break
                        time.sleep(20)
                    exp_info['chk_rc'] = rc_c
                    exp_info['chk_secs'] = sec_c
                    exp_info['chk_rss_mb'] = mem_c
                    if rc_c == 0 and os.path.exists(eop):
                        absorb_check_jsonl(eop)
                        recompute_certified()
                        if C['certified_rows'] > search_cert_rows:
                            exp_info['kept'] = True
                            C.pop('skipped', None)
                            C['calls'] += 1
                            C['secs'] += sec_c or 0
                            C['rss_mb'] = max(C.get('rss_mb', 0), mem_c or 0)
                            C['results']['certified'] = C['results'].get('certified', 0) + 1
                            next_k = len(P.get('models', []))
                            dst_hp = os.path.join(outdir, f'model{next_k}.hint')
                            dst_wp = os.path.join(outdir, f'model{next_k}.wit')
                            dst_op = os.path.join(outdir, f'check{next_k}.jsonl')
                            try:
                                if os.path.getsize(ehp) <= MAX_KEEP_BYTES:
                                    os.replace(ehp, dst_hp)
                                os.replace(ewp, dst_wp)
                                if os.path.getsize(eop) <= MAX_KEEP_BYTES:
                                    os.replace(eop, dst_op)
                            except OSError:
                                pass
                            P.setdefault('models', []).append({
                                'model': next_k,
                                'elements': J_fe.get('elements', 0),
                                'alive': J_fe.get('elements', 0),
                                'edges': J_fe.get('edges', 0),
                                'type_entries': 0,
                                'bytes': J_fe.get('bytes', 0),
                                'witnesses': J_fe.get('witnesses', 0),
                                'violations': 0,
                                'first_violation': None,
                                'source': 'export',
                            })
                            P.setdefault('base', {})['ok'] = True
                            R['rows_unchecked'] = max(R['rows_unchecked'], C['certified_rows'])
                            R['status'] = ('model-full' if R['rows_unchecked'] == R['rows_total'] else
                                           'model-partial' if R['rows_unchecked'] else R['status'])
                            R['export_used'] = True
        subprocess.run(['rm', '-rf', exp_dir])
        R['export_try'] = exp_info

    C['secs'] = round(C['secs'], 2)
    # owl:Thing's own non-subsumption rows (Thing is not a requested class of the route)
    C['thing_nonsub'] = 0 if THING in unsat else nc - len([B for B in top if B in clsset])
    C['disagreements'] = disagree[:30]
    R['status_checked'] = ('certified-full' if C['certified_rows'] == R['rows_total'] else
                           'certified-partial' if C['certified_rows'] else 'certified-none')
    return finish(R, outdir, t0)


def finish(R, outdir, t0):
    p_kl = os.path.join(outdir, 'km.lines')
    try:
        if os.path.exists(p_kl) and os.path.getsize(p_kl) > MAX_KEEP_BYTES:
            os.remove(p_kl)
    except OSError:
        pass
    for fn in ('base.idx', 'base.cl'):
        p_tmp = os.path.join(outdir, fn)
        try:
            if os.path.exists(p_tmp) and os.path.getsize(p_tmp) > 5 * 1024 * 1024:
                os.remove(p_tmp)
        except OSError:
            pass
    R['wall'] = round(time.time() - t0, 1)
    with open(os.path.join(outdir, 'result.json'), 'w') as f:
        json.dump(R, f)
    print(json.dumps({k: R.get(k) for k in ('input', 'status', 'status_checked', 'rows_total', 'rows_unchecked', 'wall')} | {'certified': (R.get('checker') or {}).get('certified_rows'), 'realized': R.get('km', {}).get('realized', True), 'export_used': R.get('export_used', False)}))


if __name__ == '__main__':
    main()
