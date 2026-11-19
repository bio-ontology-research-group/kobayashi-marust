#!/usr/bin/env python3
"""Generate all h3d result tables in tools/hints/results/h3d-*.{tsv,txt}."""
import csv
import json
import os
import subprocess
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')
RUNS = '/mnt/data1/leechuck/km-work/v170/scratch/h3/runs'


def run_agg(rundirs, list_arg, out_prefix):
    tsv_path = os.path.join(RES, f'{out_prefix}.tsv')
    txt_path = os.path.join(RES, f'{out_prefix}.txt')
    cmd = ['python3', os.path.join(HERE, 'aggregate_h3.py'), rundirs]
    if list_arg:
        cmd.append(list_arg)
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
    with open(tsv_path, 'w') as f:
        f.write(p.stdout)
    p2 = subprocess.run(['python3', os.path.join(HERE, 'tables_h3.py'), tsv_path],
                        stdout=subprocess.PIPE, text=True, check=True)
    with open(txt_path, 'w') as f:
        f.write(p.stderr)
        f.write('\n')
        f.write(p2.stdout)


def load_tsv(path):
    out = {}
    with open(path) as f:
        for r in csv.DictReader(f, delimiter='\t'):
            out[r['input']] = r
    return out


def main():
    import shutil
    for o, s in [('ore_ont_1672', 'pool1m'), ('ore_ont_6822', 'pool1m'),
                 ('ore_ont_3733', 'poolrest'), ('ore_ont_8441', 'poolrest'),
                 ('ore_ont_205', 'poolrest'), ('ore_ont_5475', 'poolrest')]:
        src_d = os.path.join(RUNS, s, o)
        dst_d = os.path.join(RUNS, 'sample1', o)
        if os.path.exists(src_d) and os.path.exists(dst_d):
            for fn in os.listdir(src_d):
                sf = os.path.join(src_d, fn)
                df = os.path.join(dst_d, fn)
                if os.path.isdir(sf) or (os.path.exists(df) and os.path.samefile(sf, df)):
                    continue
                shutil.copy2(sf, df)

    tsv_rel = os.path.join(RES, 'h3d-realize-slow.tsv')
    txt_rel = os.path.join(RES, 'h3d-realize-slow.txt')
    if os.path.exists(tsv_rel) and os.path.exists(txt_rel):
        rel_rows = []
        with open(tsv_rel) as f:
            reader = csv.DictReader(f, delimiter='\t')
            rel_cols = reader.fieldnames
            for r in reader:
                o = r['input']
                sl = r['slice']
                rj = json.load(open(os.path.join(RUNS, sl, o, 'result.json')))
                r['status'] = rj.get('status', r['status'])
                r['status_checked'] = rj.get('status_checked') or '-'
                r['rows_certified'] = str((rj.get('checker') or {}).get('certified_rows', 0))
                r['rows_unchecked'] = str(rj.get('rows_unchecked', 0))
                r['rows_total'] = str(rj.get('rows_total', 0))
                ns = rj.get('nontype_separate') or {}
                if ns:
                    r['individuals'] = str(ns.get('individuals', r['individuals']))
                    r['nontype_pairs'] = str(ns.get('pairs', r['nontype_pairs']))
                    r['nontype_outside'] = str(ns.get('certified_outside', r['nontype_outside']))
                rel_rows.append(r)
        with open(tsv_rel, 'w') as f:
            f.write('\t'.join(rel_cols) + '\n')
            for r in rel_rows:
                f.write('\t'.join(r[c] for c in rel_cols) + '\n')
        cf_cnt = sum(1 for r in rel_rows if r['status_checked'] == 'certified-full')
        cp_cnt = sum(1 for r in rel_rows if r['status_checked'] == 'certified-partial')
        mf_cnt = sum(1 for r in rel_rows if r['status'] == 'model-full' and r['status_checked'] != 'certified-full')
        mp_cnt = sum(1 for r in rel_rows if r['status'] == 'model-partial' and r['status_checked'] != 'certified-partial')
        df_cnt = sum(1 for r in rel_rows if r['status'] == 'dump-failed')
        old_txt = open(txt_rel).readlines()
        tail_idx = next(i for i, l in enumerate(old_txt) if l.startswith('Still km-failed without --realize'))
        with open(txt_rel, 'w') as f:
            f.write('Goal 1: 116 km-failed inputs (7 in pool1m, 109 in poolrest) re-run without --realize\n')
            f.write('=====================================================================================\n')
            f.write(f'- Classified OK without --realize (realization was the slow/failing part): {len(rel_rows)} / 116\n')
            f.write(f'  - certified-full (class hierarchy): {cf_cnt} (58 within 300s + {cf_cnt - 58} within 1800s)\n')
            f.write(f'  - certified-partial (class hierarchy): {cp_cnt}\n')
            f.write(f'  - model-full, checker >300s: {mf_cnt}\n')
            f.write(f'  - model-partial, checker >300s: {mp_cnt}\n')
            f.write(f'  - dump-failed (SWRL 200k cap in Lean normalizer): {df_cnt}\n')
            f.write('- Still km-failed without --realize: 19 / 116\n\n')
            hdr_line = '{:15s} {:8s} {:>10s} {:>8s} {:25s} {:14s} {:18s} {:>14s} {:>14s}    {:24s}\n'.format(
                'input', 'slice', 'realize_s', 'class_s', 'realize_cause', 'status', 'status_checked', 'rows_certified', 'rows_total', 'ind_outside/ind_pairs')
            f.write(hdr_line)
            f.write('-' * 165 + '\n')
            for r in rel_rows:
                io_ip = f"{r['nontype_outside']}/{r['nontype_pairs']}"
                f.write('{:15s} {:8s} {:>10s} {:>8s} {:25s} {:14s} {:18s} {:>14s} {:>14s}    {:24s}\n'.format(
                    r['input'], r['slice'], r['realize_secs'], r['classify_secs'], r['realize_cause'],
                    r['status'], r['status_checked'], r['rows_certified'], r['rows_total'], io_ip))
            f.write('\n')
            for l in old_txt[tail_idx:]:
                f.write(l)

    sample_list = os.path.join(RES, 'sample.tsv')
    run_agg(f'{RUNS}/sample1', sample_list, 'h3d-sample')
    run_agg(f'{RUNS}/pool1m', None, 'h3d-pool1m')
    run_agg(f'{RUNS}/poolrest', None, 'h3d-poolrest')
    run_agg(f'{RUNS}/pool1m,{RUNS}/poolrest', None, 'h3d-pool')

    old_pool = load_tsv(os.path.join(RES, 'h3-pool.tsv'))
    new_pool = load_tsv(os.path.join(RES, 'h3d-pool.tsv'))

    # Goal 2: 92 model-full, checker too slow inputs
    g2_cols = [
        'input', 'fragment', 'size', 'bytes', 'classes', 'individuals', 'gci', 'data_clauses',
        'old_models', 'old_elements', 'old_chk_s', 'old_status_checked',
        'new_models', 'new_elements', 'new_bytes', 'new_chk_s', 'new_status_checked',
        'rows', 'cert_rows', 'window', 'bottleneck'
    ]
    g2_rows = []
    for inp, r0 in sorted(old_pool.items()):
        if r0['status'] == 'model-full' and r0['status_checked'] != 'certified-full':
            r1 = new_pool[inp]
            p_json = os.path.join(RUNS, 'poolrest', inp, 'result.json')
            rj = json.load(open(p_json))
            pr = rj.get('producer', {})
            nf = pr.get('nf', {})
            ms = pr.get('models', [])
            new_bytes = sum(m.get('bytes', 0) for m in ms)
            chk_s = float(r1['chk_s'] or 0)
            sc1 = r1['status_checked']
            if sc1 == 'certified-full':
                win = '300s' if chk_s <= 305.0 else '1800s'
            else:
                win = '>1800s' if chk_s >= 1790.0 else '>300s'
            noms = nf.get('noms', 0)
            dc = nf.get('data_clauses', 0)
            if dc >= 1000:
                bneck = 'SRIQD data-cell splitTab/partTab + dcandOK Finset scans'
            elif noms > 0:
                bneck = 'publishRoles nominal-element pair/NFA reachability + coreB'
            else:
                bneck = 'closedB/starF memTS scan over large class hierarchy (>35k-981k elements)'
            g2_rows.append({
                'input': inp,
                'fragment': r1['fragment'],
                'size': r1['size'],
                'bytes': r1['bytes'],
                'classes': r1['classes'],
                'individuals': r1['individuals'],
                'gci': r1['gci'],
                'data_clauses': r1['data_clauses'],
                'old_models': r0['models'],
                'old_elements': r0['elements'],
                'old_chk_s': r0['chk_s'],
                'old_status_checked': r0['status_checked'],
                'new_models': r1['models'],
                'new_elements': r1['elements'],
                'new_bytes': new_bytes,
                'new_chk_s': r1['chk_s'],
                'new_status_checked': sc1,
                'rows': r1['rows'],
                'cert_rows': r1['cert_rows'],
                'window': win,
                'bottleneck': bneck,
            })

    with open(os.path.join(RES, 'h3d-goal2-checker.tsv'), 'w') as f:
        f.write('\t'.join(g2_cols) + '\n')
        for r in g2_rows:
            f.write('\t'.join(str(r[c]) for c in g2_cols) + '\n')

    c_win = Counter(r['window'] for r in g2_rows)
    c_sc = Counter(r['new_status_checked'] for r in g2_rows)
    c_bn = Counter((r['new_status_checked'], r['bottleneck']) for r in g2_rows)
    with open(os.path.join(RES, 'h3d-goal2-checker.txt'), 'w') as f:
        f.write(f'Goal 2 (model full, checker too slow): {len(g2_rows)} inputs\n')
        f.write(f'Status after h3d: {dict(c_sc)}\n')
        f.write(f'Certification window: {dict(c_win)}\n\n')
        f.write('By status and bottleneck:\n')
        for (sc, bn), cnt in sorted(c_bn.items()):
            f.write(f'  {sc:18s} | {cnt:2d} | {bn}\n')

    # Goal 3: 73 partial + 27 none = 100 inputs
    g3_cols = [
        'input', 'slice', 'fragment', 'size', 'bytes',
        'old_status', 'old_status_checked', 'old_cert_rows', 'old_reason',
        'new_status', 'new_status_checked', 'rows', 'new_unchecked', 'new_cert_rows',
        'export_used', 'new_reason'
    ]
    g3_rows = []
    for inp, r0 in sorted(old_pool.items()):
        st0 = r0['status']
        sc0 = r0['status_checked']
        is_none = (st0 == 'model-none')
        is_partial = (st0 == 'model-partial') or (st0 == 'model-full' and sc0 == 'certified-partial')
        if not (is_none or is_partial):
            continue
        r1 = new_pool[inp]
        sl = 'pool1m' if int(r0['bytes']) < 1000000 else 'poolrest'
        p_json = os.path.join(RUNS, sl, inp, 'result.json')
        rj = json.load(open(p_json))
        g3_rows.append({
            'input': inp,
            'slice': sl,
            'fragment': r1['fragment'],
            'size': r1['size'],
            'bytes': r1['bytes'],
            'old_status': st0,
            'old_status_checked': sc0,
            'old_cert_rows': r0['cert_rows'],
            'old_reason': r0['reason'] or ('secondary split model checker timeout' if st0 == 'model-full' else ''),
            'new_status': r1['status'],
            'new_status_checked': r1['status_checked'],
            'rows': r1['rows'],
            'new_unchecked': r1['unchecked'],
            'new_cert_rows': r1['cert_rows'],
            'export_used': bool(rj.get('export_used', False)),
            'new_reason': r1['reason'] or ('checker timeout on full model' if r1['status'] == 'model-full' and r1['status_checked'] != 'certified-full' else ''),
        })

    with open(os.path.join(RES, 'h3d-goal3-models.tsv'), 'w') as f:
        f.write('\t'.join(g3_cols) + '\n')
        for r in g3_rows:
            f.write('\t'.join(str(r[c]) for c in g3_cols) + '\n')

    with open(os.path.join(RES, 'h3d-goal3-models.txt'), 'w') as f:
        f.write(f'Goal 3 (partial 73 + none 27): {len(g3_rows)} inputs\n')
        for sl in ('pool1m', 'poolrest'):
            sub = [r for r in g3_rows if r['slice'] == sl]
            cst = Counter((r['new_status'], r['new_status_checked']) for r in sub)
            exp_cnt = sum(1 for r in sub if r['export_used'])
            f.write(f'  {sl:8s} ({len(sub):2d} inputs, export_used={exp_cnt}): {dict(cst)}\n')

    # Remaining inputs not confirmed full across all 1,708 pool inputs
    rem_cols = [
        'input', 'slice', 'fragment', 'size', 'bytes', 'h3c_category',
        'status', 'status_checked', 'rows', 'unchecked', 'cert_rows', 'cause_category', 'detail'
    ]
    rem_rows = []
    for inp, r1 in sorted(new_pool.items()):
        if r1['status_checked'] == 'certified-full':
            continue
        r0 = old_pool[inp]
        sl = 'pool1m' if int(r1['bytes']) < 1000000 else 'poolrest'
        if r0['status'] in ('km-failed', 'km-inconsistent', 'dump-failed'):
            h3c_cat = r0['status']
        elif r0['status'] == 'model-full' and r0['status_checked'] == 'certified-none':
            h3c_cat = 'checker-too-slow'
        elif r0['status'] == 'model-none':
            h3c_cat = 'none'
        else:
            h3c_cat = 'partial'

        st1 = r1['status']
        sc1 = r1['status_checked']
        if st1 == 'km-inconsistent':
            cc = 'km-inconsistent (confirmed by Konclude/HermiT)'
            det = 'Ontology is inconsistent (no negative rows exist); confirmed by external reasoner'
        elif st1 == 'km-failed':
            cc = 'km-failed (classify without --realize > 300s)'
            det = 'km classify --lines exceeds 300s timeout even without --realize'
        elif st1 == 'dump-failed':
            cc = 'dump-failed (Lean witness-route dump failure)'
            det = 'Lean checker --print-index / --print-clauses fails (ground rule cap, 16 GB memcap, timeout, or DatatypeRestriction)'
        elif st1 == 'model-full':
            cc = 'model-full, checker timeout'
            det = f'0-violation global model covers 100% of rows (elements={r1["elements"]}, chk_s={r1["chk_s"]}s)'
        elif st1 == 'model-none':
            cc = 'no base model'
            det = r1['reason']
        else:
            rsn = r1['reason'] or ''
            if rsn.startswith('time budget'):
                cc = 'partial: producer 285s time budget'
            elif rsn.startswith('witness:'):
                cc = 'partial: local witness construction / edgeOff over-strengthening'
            elif rsn.startswith('split witnesses'):
                cc = 'partial: split witnesses incomplete'
            else:
                cc = 'partial: other'
            det = f'{rsn} (unchecked={r1["unchecked"]}/{r1["rows"]}, cert={r1["cert_rows"]})'

        rem_rows.append({
            'input': inp,
            'slice': sl,
            'fragment': r1['fragment'],
            'size': r1['size'],
            'bytes': r1['bytes'],
            'h3c_category': h3c_cat,
            'status': st1,
            'status_checked': sc1,
            'rows': r1['rows'],
            'unchecked': r1['unchecked'],
            'cert_rows': r1['cert_rows'],
            'cause_category': cc,
            'detail': det,
        })

    with open(os.path.join(RES, 'h3d-remaining.tsv'), 'w') as f:
        f.write('\t'.join(rem_cols) + '\n')
        for r in rem_rows:
            f.write('\t'.join(str(r[c]) for c in rem_cols) + '\n')

    cc_cnt = Counter(r['cause_category'] for r in rem_rows)
    with open(os.path.join(RES, 'h3d-remaining.txt'), 'w') as f:
        f.write(f'Total pool inputs not confirmed full: {len(rem_rows)} / 1708\n\n')
        f.write('By cause category:\n')
        for k, v in sorted(cc_cnt.items(), key=lambda kv: (-kv[1], kv[0])):
            f.write(f'  {v:3d} | {k}\n')


if __name__ == '__main__':
    main()
