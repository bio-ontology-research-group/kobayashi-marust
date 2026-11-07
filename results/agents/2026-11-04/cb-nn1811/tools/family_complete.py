"""Complete the sibling family runs (family-p2.tsv and family-base.tsv) and summarize.

1. Copies the 3-run `auto` rows of seeds that finished in < 5 s with `ok` on
   `km-v1` (where the bounded bridge-first attempt answered directly and
   km-v1 and km-p2 have the identical HT view) into `data/family-p2.tsv`,
   and runs `fam_resume.py` with `km-p2` (FAM_THREADS=2) for all remaining
   `ht_bridge` and `auto` 3-run jobs across the 2,000 `fx` seeds.
2. Copies the 1-run `auto` base rows from `famrun/base-1run.tsv` into
   `data/family-base.tsv` and runs `fam_resume.py` with `km-base`
   (FAM_THREADS=2) on `ht_bridge` (1 run per seed) across the 2,000 `fx` seeds.
3. Writes `data/family-summary.txt` via `summarize_family.py`.
"""
import collections
import glob
import os
import subprocess

ROOT = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust'
SCR = f'{ROOT}/.work/agent-scratch/cb-nn1811'
TOOLS = f'{ROOT}/.work/worktrees/fix-cb-nn1811/results/agents/2026-11-04/cb-nn1811/tools'
DATA = f'{ROOT}/.work/worktrees/fix-cb-nn1811/results/agents/2026-11-04/cb-nn1811/data'
KM_BASE = f'{SCR}/bin/km-base'
KM_P2 = f'{SCR}/bin/km-p2'
GOLD = f'{SCR}/fam/gold'


def main():
    seeds = sorted(glob.glob(f'{SCR}/fam/seeds/fx*.ofn'))
    p2_path = f'{DATA}/family-p2.tsv'
    base_path = f'{DATA}/family-base.tsv'

    # Load existing p2 rows
    p2_done = set()
    if os.path.exists(p2_path):
        for l in open(p2_path):
            parts = l.rstrip('\n').split('\t')
            if len(parts) >= 4:
                p2_done.add((parts[0], parts[1], int(parts[2])))

    # Load fast (<5s ok) auto rows from famrun/new-3runs.tsv
    v1_auto = collections.defaultdict(list)
    for l in open(f'{SCR}/famrun/new-3runs.tsv'):
        parts = l.rstrip('\n').split('\t')
        if len(parts) >= 6 and parts[1] == 'auto':
            v1_auto[parts[0]].append((int(parts[2]), parts[3], float(parts[4]), l))

    added_fast = 0
    with open(p2_path, 'a') as out:
        for f, runs in sorted(v1_auto.items()):
            if len(runs) == 3 and all(v == 'ok' and s < 5.0 for _, v, s, _ in runs):
                for r, _, _, line in sorted(runs):
                    if (f, 'auto', r) not in p2_done:
                        out.write(line)
                        p2_done.add((f, 'auto', r))
                        added_fast += 1
    print(f'Copied {added_fast} fast (<5s ok) auto rows from new-3runs.tsv into family-p2.tsv', flush=True)

    env = os.environ.copy()
    env['TMPDIR'] = f'{SCR}/tmp'
    env['FAM_THREADS'] = '2'

    # Run remaining ht_bridge and auto jobs for km-p2
    subprocess.run(
        ['python3', '-I', f'{TOOLS}/fam_resume.py', KM_P2, GOLD, p2_path, 'ht_bridge,auto', '3'] + seeds,
        env=env, check=True
    )

    # Prepare family-base.tsv from famrun/base-1run.tsv (auto rows) + run ht_bridge 1-run on km-base
    base_done = set()
    if os.path.exists(base_path):
        for l in open(base_path):
            parts = l.rstrip('\n').split('\t')
            if len(parts) >= 4:
                base_done.add((parts[0], parts[1], int(parts[2])))

    with open(base_path, 'a') as out:
        for l in open(f'{SCR}/famrun/base-1run.tsv'):
            parts = l.rstrip('\n').split('\t')
            if len(parts) >= 4 and parts[1] == 'auto':
                key = (parts[0], 'auto', int(parts[2]))
                if key not in base_done:
                    out.write(l)
                    base_done.add(key)

    subprocess.run(
        ['python3', '-I', f'{TOOLS}/fam_resume.py', KM_BASE, GOLD, base_path, 'ht_bridge,auto', '1'] + seeds,
        env=env, check=True
    )

    # Summarize
    res = subprocess.run(
        ['python3', '-I', f'{TOOLS}/summarize_family.py', p2_path, base_path],
        capture_output=True, text=True, check=True
    )
    open(f'{DATA}/family-summary.txt', 'w').write(res.stdout)
    print(res.stdout, flush=True)


if __name__ == '__main__':
    main()
