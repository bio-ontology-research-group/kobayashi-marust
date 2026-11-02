"""Cache HermiT answers for seed files (the oracle of diff_run.py).
usage: python3 -I prime_gold.py ORACLE_DIR GOLD_DIR THREADS FILE..."""
import concurrent.futures as cf, json, os, subprocess, sys
ORACLE, GOLD, TH = sys.argv[1], sys.argv[2], int(sys.argv[3])
def one(path):
    stem = os.path.splitext(os.path.basename(path))[0]
    cache = os.path.join(GOLD, stem + '.json')
    if os.path.exists(cache):
        return stem, 'cached'
    cp = open(os.path.join(ORACLE, 'cp.txt')).read().strip()
    o = subprocess.run(['timeout', '120', 'java', '-Xmx1g', '-XX:+UseSerialGC', '-cp', '.:' + cp, 'Oracle',
                        os.path.abspath(path)], cwd=ORACLE, capture_output=True, text=True).stdout
    try:
        d = json.loads(o)
    except ValueError:
        return stem, 'none'
    with open(cache, 'w') as f:
        json.dump(d, f)
    return stem, 'consistent' if d['consistent'] else 'inconsistent'
with cf.ThreadPoolExecutor(TH) as ex:
    for stem, st in ex.map(one, sys.argv[4:]):
        print(stem, st, flush=True)
