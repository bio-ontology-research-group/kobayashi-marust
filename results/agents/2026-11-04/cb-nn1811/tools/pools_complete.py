"""Complete the differential pool runs for km-p2 and compare against base.

1. Appends the remaining screened seeds of bridge-nn-rule-fam to
   .work/agent-scratch/cb-nn1811/pools/after/bridge-nn-rule-fam.tsv.
2. Runs km-p2 on every pool seed that was WRONG on base or after, or that
   mentions an individual and did not finish in < 5 s through the bridge
   (so the nominal CB arm with offer_root_reach can run on the automatic
   route), into .work/agent-scratch/cb-nn1811/pools/p2-cb-check.tsv.
3. Combines base rows (for unchanged unscreened seeds), pools/after/*.tsv,
   and p2-cb-check.tsv, and writes data/pools-summary.txt.
"""
import collections
import glob
import os
import subprocess
import sys

ROOT = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust'
SCR = f'{ROOT}/.work/agent-scratch/cb-nn1811'
TOOLS = f'{ROOT}/.work/worktrees/fix-cb-nn1811/results/agents/2026-11-04/cb-nn1811/tools'
DATA = f'{ROOT}/.work/worktrees/fix-cb-nn1811/results/agents/2026-11-04/cb-nn1811/data'
KM_P2 = f'{SCR}/bin/km-p2'

# Map pool name -> gold dir
A = f'{ROOT}/.work/agent-scratch'
GOLD_MAP = {}
for p in sorted(glob.glob(f'{A}/bridge-self/pools/*')):
    GOLD_MAP[f'bridge-self-pools-{os.path.basename(p)}'] = f'{p}/gold'
GOLD_MAP.update({
    'bridge-self-pool': f'{A}/bridge-self/pool/gold',
    'bridge-self-regress': f'{A}/bridge-self/regress/gold',
    'bridge-self-micro': f'{A}/bridge-self/micro/gold',
    'bridge-m413-respool': f'{A}/bridge-m413/respool/gold',
    'bridge-m413-k': f'{A}/bridge-m413/kgold',
    'bridge-m413-k2': f'{A}/bridge-m413/k2gold',
    'cb-s974-merge': f'{A}/cb-s974/fam-merge/gold',
    'cb-s974-vacuous': f'{A}/cb-s974/fam-vacuous/gold',
    'bridge-reflexive-fam': f'{A}/bridge-reflexive/fam/gold',
    'bridge-reflexive-seeds20': f'{A}/bridge-reflexive/seeds20/gold',
    'bridge-nn-rule-fam': f'{A}/bridge-nn-rule/fam/gold',
})


def load_base():
    base = {}
    for p in sorted(glob.glob(f'{A}/bridge-nn-rule/pools/after/*.tsv')):
        pool = os.path.basename(p)[:-4]
        for l in open(p):
            parts = l.rstrip('\n').split('\t')
            if len(parts) >= 4:
                base[(pool, parts[0], parts[1])] = (parts[2], float(parts[3]))
    nn_fam = collections.defaultdict(list)
    for l in open(f'{A}/bridge-nn-rule/famrun/new.tsv'):
        f, spec, run, v, s, d = l.rstrip('\n').split('\t')
        nn_fam[(f, spec)].append((v, float(s)))
    for (f, spec), runs in nn_fam.items():
        # If any of the 3 runs was WRONG on base (like nn1811), record WRONG; else first run
        v = 'WRONG' if any(r[0] == 'WRONG' for r in runs) else runs[0][0]
        base[('bridge-nn-rule-fam', f, spec)] = (v, runs[0][1])
    return base


def load_after():
    after = {}
    for p in sorted(glob.glob(f'{SCR}/pools/after/*.tsv')):
        pool = os.path.basename(p)[:-4]
        for l in open(p):
            parts = l.rstrip('\n').split('\t')
            if len(parts) >= 4:
                after[(pool, parts[0], parts[1])] = (parts[2], float(parts[3]))
    return after


def run_diff(pool, files, out_tsv):
    if not files:
        return
    env = os.environ.copy()
    env['TMPDIR'] = f'{SCR}/tmp'
    env['DIFF_THREADS'] = '2'
    env['DIFF_KM_TIMEOUT'] = '60'
    env['DIFF_KEEP'] = (
        'KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,'
        'KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1'
    )
    errdir = f'{SCR}/pools/after/err-{pool}'
    os.makedirs(errdir, exist_ok=True)
    env['DIFF_ERRDIR'] = errdir
    cmd = ['python3', '-I', f'{TOOLS}/diff_run.py', KM_P2, '/nonexistent',
           GOLD_MAP[pool], out_tsv, 'ht_bridge,auto'] + files
    subprocess.run(cmd, env=env, check=True)


def main():
    base = load_base()
    after = load_after()

    # Step 1: remaining screened seeds in bridge-nn-rule-fam
    rem_nn = []
    for l in open(f'{SCR}/pool-screened.tsv'):
        pool, f = l.rstrip('\n').split('\t')
        if pool == 'bridge-nn-rule-fam' and (pool, f, 'auto') not in after:
            rem_nn.append(f)
    print(f'Step 1: running {len(rem_nn)} remaining bridge-nn-rule-fam seeds...', flush=True)
    run_diff('bridge-nn-rule-fam', rem_nn, f'{SCR}/pools/after/bridge-nn-rule-fam.tsv')
    after = load_after()

    # Step 2: check seeds that were WRONG on base/after or nominal seeds where CB arm can run
    p2_tsv = f'{SCR}/pools/p2-cb-check.tsv'
    done_p2 = set()
    if os.path.exists(p2_tsv):
        for l in open(p2_tsv):
            parts = l.rstrip('\n').split('\t')
            if len(parts) >= 3:
                done_p2.add((parts[0], parts[1]))

    by_pool = collections.defaultdict(list)
    for l in open(f'{SCR}/pool-all.tsv'):
        pool, f = l.rstrip('\n').split('\t')
        if (f, 'auto') in done_p2 and (f, 'ht_bridge') in done_p2:
            continue
        vb_ht, sb_ht = base.get((pool, f, 'ht_bridge'), ('?', 0.0))
        vb_au, sb_au = base.get((pool, f, 'auto'), ('?', 0.0))
        va_ht, sa_ht = after.get((pool, f, 'ht_bridge'), (vb_ht, sb_ht))
        va_au, sa_au = after.get((pool, f, 'auto'), (vb_au, sb_au))
        need = False
        if 'WRONG' in (vb_ht, vb_au, va_ht, va_au):
            need = True
        elif (vb_ht != 'ok' or vb_au != 'ok' or sb_au >= 5.0) and vb_au != 'TIMEOUT' and va_au != 'TIMEOUT':
            txt = open(f).read()
            if any(k in txt for k in ('NamedIndividual', 'ObjectOneOf', 'ObjectHasValue',
                                      'ClassAssertion', 'ObjectPropertyAssertion',
                                      'SameIndividual', 'DifferentIndividuals')):
                need = True
        if need:
            by_pool[pool].append(f)

    total_need = sum(len(v) for v in by_pool.values())
    print(f'Step 2: running {total_need} CB-candidate / WRONG seeds on km-p2...', flush=True)
    for pool, files in sorted(by_pool.items()):
        print(f'  {pool}: {len(files)} seeds', flush=True)
        run_diff(pool, files, p2_tsv)

    p2_map = {}
    if os.path.exists(p2_tsv):
        for l in open(p2_tsv):
            parts = l.rstrip('\n').split('\t')
            if len(parts) >= 4:
                p2_map[(parts[0], parts[1])] = (parts[2], float(parts[3]))

    # Step 3: combine and summarize
    pools_order = sorted({l.split('\t')[0] for l in open(f'{SCR}/pool-all.tsv')})
    lines = []
    tot_base = collections.Counter()
    tot_new = collections.Counter()
    new_wrong_diffs = []
    fixed_wrong = []

    for pool in pools_order:
        cb = collections.Counter()
        cn = collections.Counter()
        for l in open(f'{SCR}/pool-all.tsv'):
            p, f = l.rstrip('\n').split('\t')
            if p != pool:
                continue
            for r in ('ht_bridge', 'auto'):
                vb, sb = base.get((pool, f, r), ('?', 0.0))
                if (f, r) in p2_map:
                    vn, sn = p2_map[(f, r)]
                elif (pool, f, r) in after:
                    vn, sn = after[(pool, f, r)]
                else:
                    vn, sn = vb, sb
                cb[(r, vb)] += 1
                cn[(r, vn)] += 1
                tot_base[(r, vb)] += 1
                tot_new[(r, vn)] += 1
                if vn == 'WRONG' and vb != 'WRONG':
                    new_wrong_diffs.append((pool, os.path.basename(f), r, vb, vn))
                if vb == 'WRONG' and vn == 'ok':
                    fixed_wrong.append((pool, os.path.basename(f), r, vb, vn))
        b_str = ' '.join(f'{r}/{v}={n}' for (r, v), n in sorted(cb.items()))
        n_str = ' '.join(f'{r}/{v}={n}' for (r, v), n in sorted(cn.items()))
        lines.append(f'{pool:44s} base: {b_str}\n{"":44s} new:  {n_str}')

    lines.append('')
    lines.append('TOTAL base: ' + ' '.join(f'{r}/{v}={n}' for (r, v), n in sorted(tot_base.items())))
    lines.append('TOTAL new:  ' + ' '.join(f'{r}/{v}={n}' for (r, v), n in sorted(tot_new.items())))
    lines.append(f'new wrong vs base: {len(new_wrong_diffs)} {new_wrong_diffs}')
    lines.append(f'base wrong fixed in new: {len(fixed_wrong)} {fixed_wrong}')
    text = '\n'.join(lines) + '\n'
    open(f'{DATA}/pools-summary.txt', 'w').write(text)
    print(text, flush=True)


if __name__ == '__main__':
    main()
