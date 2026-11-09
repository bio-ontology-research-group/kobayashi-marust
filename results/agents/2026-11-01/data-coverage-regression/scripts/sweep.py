#!/usr/bin/env python3
"""Classify pool inputs in line mode; record CONSISTENT/DROPPED/status per input.
usage: sweep.py LABEL BINARY OUTDIR [NAMES_FILE]"""
import json, os, subprocess, sys, time, hashlib
from concurrent.futures import ThreadPoolExecutor
ROOT = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust'
label, binary, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
names = None
if len(sys.argv) > 4:
    names = set(l.strip() for l in open(sys.argv[4]) if l.strip())
man = json.load(open(f'{ROOT}/.work/v152-correctness-1920/full-candidate-inputs-ws.json'))
inputs = [x for x in man['inputs'] if x['input_admission'] == 'checks_passed']
if names is not None:
    inputs = [x for x in inputs if x['ontology'] in names]
os.makedirs(outdir, exist_ok=True)
res_path = f'{outdir}/{label}.jsonl'
done = set()
if os.path.exists(res_path):
    done = {json.loads(l)['ontology'] for l in open(res_path) if l.strip()}
env = dict(os.environ, KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
           KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_FAST_IRI_GRAMMAR='1', KM_THREADS='1',
           TMPDIR=f'{ROOT}/.work/agent-scratch/data-coverage-regression/tmp')
os.makedirs(env['TMPDIR'], exist_ok=True)
CPUS = [int(c) for c in os.environ.get('SWEEP_CPUS', '44,45,46').split(',')]
import threading
free = list(CPUS); lock = threading.Lock(); outlock = threading.Lock()
def run(x):
    with lock: cpu = free.pop()
    try:
        t0 = time.time()
        cmd = ['taskset', '-c', str(cpu), 'prlimit', f'--as={20*1024**3}', '--',
               'timeout', '-s', 'KILL', '240', binary, 'classify', '--lines', x['path']]
        p = subprocess.run(cmd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        wall = time.time() - t0
        out = p.stdout.decode(errors='replace')
        cons = dropped = None; nsub = nunsat = 0
        for line in out.splitlines():
            if line.startswith('CONSISTENT '): cons = int(line.split()[1])
            elif line.startswith('DROPPED '): dropped = int(line.split()[1])
            elif line.startswith('SUB\t'): nsub += 1
            elif line.startswith('UNSAT\t'): nunsat += 1
        h = hashlib.sha256(out.encode()).hexdigest()
        rec = dict(ontology=x['ontology'], sha256=x['sha256'], rc=p.returncode, wall=round(wall,2),
                   consistent=cons, dropped=dropped, nsub=nsub, nunsat=nunsat, out_sha256=h,
                   stderr_tail=p.stderr.decode(errors='replace')[-400:])
        with outlock:
            with open(res_path, 'a') as f: f.write(json.dumps(rec) + '\n')
    finally:
        with lock: free.append(cpu)
todo = [x for x in inputs if x['ontology'] not in done]
print(f'{label}: {len(todo)} to run', flush=True)
with ThreadPoolExecutor(len(CPUS)) as ex:
    list(ex.map(run, todo))
print('done', flush=True)
