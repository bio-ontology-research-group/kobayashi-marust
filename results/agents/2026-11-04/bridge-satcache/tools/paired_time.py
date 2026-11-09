"""Paired timing of two KM binaries on family seeds.

usage: python3 -I paired_time.py BASE_BIN NEW_BIN GOLD_DIR OUT.tsv ROUTES RUNS FILE...

For every seed, route (`auto` or a KM_ROUTE value) and run, BASE and NEW
classify the seed at the same time (two KM processes, the same host load
for both), release flags, PAIR_TIMEOUT seconds (default 90). Rows: file,
route, run, base verdict, base seconds, new verdict, new seconds. The
verdict comes from fam_run.py's comparison with the HermiT gold.
"""
import concurrent.futures as cf
import importlib.util
import os
import sys

T = os.path.dirname(os.path.abspath(__file__))
BASE, NEW, GOLD, OUT, ROUTES, RUNS = sys.argv[1:7]
FILES = sys.argv[7:]
TIMEOUT = int(os.environ.get('PAIR_TIMEOUT', '90'))

# Reuse fam_run.py's job() (release flags, gold comparison) without running
# its main loop: load it with an empty file list.
os.environ['FAM_TIMEOUT'] = str(TIMEOUT)
os.environ['FAM_FORCED_TIMEOUT'] = str(TIMEOUT)


def load(km):
    argv = sys.argv
    sys.argv = ['fam_run.py', km, GOLD, os.devnull, 'auto', '1']
    spec = importlib.util.spec_from_file_location('fam_run_' + str(id(km)), os.path.join(T, 'fam_run.py'))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    sys.argv = argv
    return mod


mb, mn = load(BASE), load(NEW)
with open(OUT, 'a') as out, cf.ThreadPoolExecutor(2) as ex:
    for f in FILES:
        for r in ROUTES.split(','):
            for k in range(1, int(RUNS) + 1):
                fb = ex.submit(mb.job, (f, r, k))
                fn = ex.submit(mn.job, (f, r, k))
                b, n = fb.result(), fn.result()
                out.write('%s\t%s\t%d\t%s\t%.2f\t%s\t%.2f\n' % (os.path.basename(f), r, k, b[3], b[4], n[3], n[4]))
                out.flush()
