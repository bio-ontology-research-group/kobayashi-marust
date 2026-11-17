#!/usr/bin/env python3
"""Goal 5 evaluator: run `km classify --export-model` -> `km-hints from-export` ->
proved checker (`km-owl-reference-h6-9873d697 --procedure sroiq-hint`) on inputs
of `pool1m` and `poolrest` where export says `ok` or `partial`, with search only
for what the export lacks, and report per route:
  - confirmed full by export alone
  - confirmed full by export plus search
  - time against the search-only pipeline.
"""
import concurrent.futures
import glob
import json
import os
import shutil
import subprocess
import sys
import time
from collections import defaultdict

SCR = os.environ.get('H3_SCR', '/mnt/data1/leechuck/km-work/v170/scratch/h3')
KM_EXPORT = os.environ.get('H3_KM_EXPORT', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-77b79850')
REF = os.environ.get('H3_REF', '/mnt/data1/leechuck/km-work/v170/scratch/bin/km-owl-reference-h6-9873d697')
PROD = os.environ.get('H3_PROD', os.path.join(SCR, 'target/release/km-hints'))
CORPUS = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files'
TMP = os.path.join(SCR, 'tmp')
OUT_ROOT = os.path.join(SCR, 'runs/export_eval')
THING = 'http://www.w3.org/2002/07/owl#Thing'
NOTHING = 'http://www.w3.org/2002/07/owl#Nothing'


def run_cmd(cmd, timeout=300, mem_kb=8000000):
    t0 = time.time()
    env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    env['KM_THREADS'] = '1'
    env['TMPDIR'] = TMP
    full = ['taskset', '-c', '8-23', 'timeout', str(timeout)] + cmd
    if mem_kb:
        full = ['bash', '-c', 'ulimit -v %d; exec "$@"' % mem_kb, 'x'] + full
    p = subprocess.run(full, capture_output=True, text=True, env=env)
    return p.returncode, round(time.time() - t0, 2), p.stdout, p.stderr


def eval_one(item):
    ont, suite, rdir = item
    res_file = os.path.join(OUT_ROOT, f'{ont}.json')
    if os.path.exists(res_file):
        try:
            return json.load(open(res_file))
        except Exception:
            pass
    owl = os.path.join(CORPUS, f'{ont}.owl')
    bi = os.path.join(rdir, 'base.idx')
    bc = os.path.join(rdir, 'base.cl')
    kl = os.path.join(rdir, 'km.lines')
    cf = os.path.join(rdir, 'classes.txt')
    base_res_path = os.path.join(rdir, 'result.json')
    if not os.path.exists(base_res_path):
        return None
    base_R = json.load(open(base_res_path))
    if base_R.get('status') in ('km-failed', 'km-inconsistent', 'dump-failed'):
        return None
    search_prod_s = (base_R.get('producer_run') or {}).get('secs') or 0.0
    search_chk_s = (base_R.get('checker') or {}).get('secs') or 0.0
    search_km_s = (base_R.get('km') or {}).get('secs') or 0.0
    search_total_s = round(search_km_s + search_prod_s + search_chk_s, 2)
    search_conf_full = base_R.get('status_checked') == 'certified-full'

    wdir = os.path.join(TMP, f'exp_{ont}_{os.getpid()}')
    shutil.rmtree(wdir, ignore_errors=True)
    os.makedirs(wdir, exist_ok=True)
    try:
        exp_f = os.path.join(wdir, 'exp.jsonl')
        rc_e, km_exp_s, km_out, _ = run_cmd([KM_EXPORT, 'classify', '--lines', '--export-model', exp_f, owl], 240, 16000000)
        if rc_e != 0 or not os.path.exists(exp_f) or os.path.getsize(exp_f) == 0:
            res = {'input': ont, 'suite': suite, 'export_status': 'km-failed', 'route': None,
                   'km_exp_s': km_exp_s, 'search_total_s': search_total_s, 'search_conf_full': search_conf_full}
            json.dump(res, open(res_file, 'w'))
            return res
        hdr = json.loads(open(exp_f).readline())
        st = hdr.get('status')
        route = hdr.get('route')
        if st not in ('ok', 'partial'):
            res = {'input': ont, 'suite': suite, 'export_status': st, 'route': route,
                   'reason': hdr.get('reason'), 'km_exp_s': km_exp_s,
                   'search_total_s': search_total_s, 'search_conf_full': search_conf_full}
            json.dump(res, open(res_file, 'w'))
            return res

        # Ensure base.idx, base.cl, km.lines exist
        s1_dir = os.path.join(SCR, 'runs/sample1', ont)
        if not (os.path.exists(bi) and os.path.exists(bc)):
            if os.path.exists(os.path.join(s1_dir, 'base.idx')) and os.path.exists(os.path.join(s1_dir, 'base.cl')):
                bi = os.path.join(s1_dir, 'base.idx')
                bc = os.path.join(s1_dir, 'base.cl')
            else:
                bi = os.path.join(wdir, 'base.idx')
                bc = os.path.join(wdir, 'base.cl')
                rc1, _, o1, _ = run_cmd([REF, '--procedure', 'sroiq-hint', '--witness-route', '--print-index', owl], 300, 16000000)
                if rc1 != 0:
                    return None
                with open(bi, 'w') as f:
                    f.write(o1)
                rc2, _, o2, _ = run_cmd([REF, '--procedure', 'sroiq-hint', '--witness-route', '--classes', cf, '--print-clauses', owl], 300, 16000000)
                if rc2 != 0:
                    return None
                with open(bc, 'w') as f:
                    f.write(o2)
        if not os.path.exists(kl):
            if os.path.exists(os.path.join(s1_dir, 'km.lines')):
                kl = os.path.join(s1_dir, 'km.lines')
            else:
                kl = os.path.join(wdir, 'km.lines')
                with open(kl, 'w') as f:
                    f.write(km_out or '')

        odir = os.path.join(wdir, 'out')
        os.makedirs(odir, exist_ok=True)
        loops = ['--no-loops'] if 'self' in (base_R.get('route') or '') else []
        rc_p, conv_s, p_out, p_err = run_cmd(
            [PROD, 'from-export'] + loops + ['--index', bi, '--clauses', bc, '--export', exp_f, '--out', odir, '--km', kl, '--time', '120'],
            150, 8000000
        )
        try:
            pj = json.loads(p_out.strip().splitlines()[-1])
        except Exception:
            pj = {'ok': False, 'why': (p_out + p_err)[-200:]}
        hp = os.path.join(odir, 'model0.hint')
        wp = os.path.join(odir, 'model0.wit')
        if not pj.get('ok') or not os.path.exists(hp):
            res = {'input': ont, 'suite': suite, 'export_status': st, 'route': route,
                   'conv_ok': False, 'conv_s': conv_s, 'pj': pj, 'km_exp_s': km_exp_s,
                   'search_total_s': search_total_s, 'search_conf_full': search_conf_full}
            json.dump(res, open(res_file, 'w'))
            return res

        chk_f = os.path.join(wdir, 'chk.jsonl')
        rc_c, chk_s, _, c_err = run_cmd(
            [REF, '--procedure', 'sroiq-hint', '--witness', wp, '--hint', hp, '--out', chk_f, '--classes', cf, owl],
            300, 16000000
        )
        chk_ok = (rc_c == 0 and os.path.exists(chk_f))
        chk_full = False
        if chk_ok:
            cls = [l.rstrip('\n') for l in open(cf) if l.strip()]
            sup = {c: {c, THING} for c in cls}
            unsat, top = set(), set()
            for l in open(kl):
                x = l.rstrip('\n').split('\t') if '\t' in l else l.split()
                if not x:
                    continue
                if x[0] == 'SUB' and len(x) >= 3:
                    if x[1] == THING:
                        top.add(x[2])
                    sup.setdefault(x[1], {x[1], THING}).add(x[2])
                elif x[0] == 'UNSAT' and len(x) >= 2:
                    unsat.add(x[1])
                elif x[0] == 'TOP' and len(x) >= 2:
                    top.add(x[1])
            ch = True
            while ch:
                ch = False
                for a in list(sup):
                    n = set().union(*(sup.get(b, {b}) for b in sup[a])) | top
                    if not n <= sup[a]:
                        sup[a] |= n
                        ch = True
            cert = {}
            cons = False
            for l in open(chk_f):
                if not l.strip():
                    continue
                j = json.loads(l)
                if j.get('consistent'):
                    cons = True
                if 'class' in j and 'nonsub' in j:
                    cert.setdefault(j['class'], set()).update(j['nonsub'])
                if 'class' in j and 'nonsub_except' in j:
                    cert.setdefault(j['class'], set()).update(set(cls) - set(j['nonsub_except']))
            miss = wrong = 0
            allc = set(cls) - {NOTHING}
            for a in allc - unsat - {THING}:
                need = allc - sup[a] - {THING}
                got = cert.get(a, set()) - {NOTHING}
                miss += len(need - got)
                wrong += len(got & sup[a])
            chk_full = (cons and miss == 0 and wrong == 0)
        exp_only_full = bool(chk_full and pj.get('export_only_full'))
        plus_search_full = bool(chk_full and pj.get('plus_search_full'))
        res = {
            'input': ont,
            'suite': suite,
            'export_status': st,
            'route': route,
            'conv_ok': True,
            'chk_rc': rc_c,
            'chk_ok': chk_ok,
            'export_only_full': exp_only_full,
            'plus_search_full': plus_search_full,
            'witnesses_searched': pj.get('witnesses_searched', 0),
            'km_exp_s': km_exp_s,
            'conv_s': conv_s,
            'chk_s': chk_s,
            'export_total_s': round(km_exp_s + conv_s + chk_s, 2),
            'search_km_s': search_km_s,
            'search_prod_s': search_prod_s,
            'search_chk_s': search_chk_s,
            'search_total_s': search_total_s,
            'search_conf_full': search_conf_full,
        }
        json.dump(res, open(res_file, 'w'))
        return res
    finally:
        shutil.rmtree(wdir, ignore_errors=True)


def main():
    os.makedirs(OUT_ROOT, exist_ok=True)
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10000
    items = []
    for suite in ('pool1m', 'poolrest'):
        sdir = os.path.join(SCR, 'runs', suite)
        if not os.path.exists(sdir):
            continue
        for ont in sorted(os.listdir(sdir)):
            rdir = os.path.join(sdir, ont)
            rf = os.path.join(rdir, 'result.json')
            if os.path.exists(rf):
                try:
                    r = json.load(open(rf))
                    if r.get('status') in ('km-failed', 'km-inconsistent', 'dump-failed'):
                        continue
                    items.append((r.get('bytes', 0), ont, suite, rdir))
                except Exception:
                    pass
    items.sort(key=lambda x: (x[0], x[1]))
    items = [(ont, suite, rdir) for _, ont, suite, rdir in items[:limit]]
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
        results = [r for r in ex.map(eval_one, items) if r is not None]

    by_route = defaultdict(lambda: defaultdict(float))
    for r in results:
        st = r.get('export_status')
        if st not in ('ok', 'partial'):
            continue
        rt = r.get('route') or 'unknown'
        for k in (rt, 'ALL'):
            d = by_route[k]
            d['inputs'] += 1
            d['status_' + st] += 1
            if r.get('export_only_full'):
                d['conf_export_alone'] += 1
            if r.get('plus_search_full'):
                d['conf_export_plus_search'] += 1
            if r.get('search_conf_full'):
                d['conf_search_only'] += 1
            d['export_s'] += r.get('export_total_s') or (r.get('km_exp_s', 0) + r.get('conv_s', 0))
            d['search_s'] += r.get('search_total_s') or 0

    print('| route | ok + partial | ok | partial | confirmed full (export alone) | confirmed full (export + search) | confirmed full (search-only) | export pipeline s | search-only pipeline s |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---:|')
    for rt in sorted(by_route, key=lambda x: (x == 'ALL', x)):
        d = by_route[rt]
        print('| %s | %d | %d | %d | %d | %d | %d | %.1f | %.1f |' % (
            rt, d['inputs'], d['status_ok'], d['status_partial'],
            d['conf_export_alone'], d['conf_export_plus_search'], d['conf_search_only'],
            d['export_s'], d['search_s']
        ))


if __name__ == '__main__':
    main()
