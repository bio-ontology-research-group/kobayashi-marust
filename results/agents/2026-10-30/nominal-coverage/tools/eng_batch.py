"""Engine-level timing over clause JSONs. usage: eng_batch.py KM OUT.tsv TIMEOUT THREADS ENV(k=v,..|-) FILE..."""
import os, subprocess, sys, time, signal, concurrent.futures as cf
KM, OUT, T, TH, ENV = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
files = sys.argv[6:]
env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
env.update({'KM_NOMINALS': '1', 'KM_THREADS': '1'})
if ENV != '-':
    env.update(dict(kv.split('=', 1) for kv in ENV.split(',')))
def one(f):
    t0 = time.time()
    with open(f) as fin:
        p = subprocess.Popen([KM, 'engine'], stdin=fin, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env, start_new_session=True)
        try:
            out, err = p.communicate(timeout=T); st = 'ok' if p.returncode == 0 else f'rc{p.returncode}'
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL); p.communicate(); st = 'TIMEOUT'
    return f"{os.path.basename(f)}\t{st}\t{time.time()-t0:.2f}"
with open(OUT, 'w') as o, cf.ThreadPoolExecutor(TH) as ex:
    for r in ex.map(one, files):
        o.write(r + '\n'); o.flush()
